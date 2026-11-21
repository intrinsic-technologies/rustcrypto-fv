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

@[cfg_block] def b_l10f150 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f150 (pushR64Effect 0x10f150 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x10f150 (PushPre 0x10f150 1) (pushR64Effect 0x10f150 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x10f151 (pushR64Effect 0x10f151 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x10f151 (PushPre 0x10f151 2) (pushR64Effect 0x10f151 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x10f153 (pushR64Effect 0x10f153 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x10f153 (PushPre 0x10f153 2) (pushR64Effect 0x10f153 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x10f155 (pushR64Effect 0x10f155 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x10f155 (PushPre 0x10f155 2) (pushR64Effect 0x10f155 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x10f157 (pushR64Effect 0x10f157 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x10f157 (PushPre 0x10f157 2) (pushR64Effect 0x10f157 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x10f159 (pushR64Effect 0x10f159 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x10f159 (PushPre 0x10f159 1) (pushR64Effect 0x10f159 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10f15a (subR64Imm32Effect 0x10f15a 4 0x288) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10f15a (fun s => s.RIP = 0x10f15a) (subR64Imm32Effect 0x10f15a 4 0x288) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x10f161 (StorePre 0x10f161 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10f161 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f161 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 65]
    (.letOp (n := 68) (.out 0x10f169 (movR64R64Effect 0x10f169 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2]
    (.letOp (n := 69) (.exec 0x10f169 (fun s => s.RIP = 0x10f169) (movR64R64Effect 0x10f169 3 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 70) (.out 0x10f16c (movR64R64Effect 0x10f16c 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 71) (.exec 0x10f16c (fun s => s.RIP = 0x10f16c) (movR64R64Effect 0x10f16c 12 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 72) (.exec 0x10f16f (StorePre 0x10f16f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10f16f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f16f 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 73) (.out 0x10f174 (leaR64Effect 0x10f174 13 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 74) (.exec 0x10f174 (fun s => s.RIP = 0x10f174) (leaR64Effect 0x10f174 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.out 0x10f179 (movR64R64Effect 0x10f179 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[73]
    (.letOp (n := 76) (.exec 0x10f179 (fun s => s.RIP = 0x10f179) (movR64R64Effect 0x10f179 7 13) (Reg.operands [.gpr 13] [])) #v[73]
    (.letOp (n := 77) (.out 0x10f17c (movR64Imm32Effect 0x10f17c 2 0x202200) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 78) (.exec 0x10f17c (fun s => s.RIP = 0x10f17c) (movR64Imm32Effect 0x10f17c 2 0x202200) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x10f183 (callEffect (fun _ => 0x11b8f0) 0x10f188) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 80) (.exec 0x10f183 (PushPre 0x10f183 5) (callEffect (fun _ => 0x11b8f0) 0x10f188) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 81) (.const ⟨64, 0x10f188⟩) #v[]
    (.terminate (.call ⟨.l11b8f0, RegMap.args [(1, 1), (2, 77), (3, 68), (4, 79), (5, 5), (6, 6), (7, 75), (12, 70), (13, 73), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ { target := .l10f188, kept := #v[], arity := rfl, guard := some (Fin.last 81) }))))))))))))))))))))))))))))))

def bytes_l10f150 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x88, 0x02, 0x00,
    0x00, 0x48, 0x89, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xF4, 0x48,
    0x89, 0x7C, 0x24, 0x28, 0x4C, 0x8D, 0x6C, 0x24, 0x38, 0x4C, 0x89, 0xEF, 0x48, 0xC7, 0xC2, 0x00,
    0x22, 0x20, 0x00, 0xE8, 0x68, 0xC7, 0x00, 0x00]

theorem code_l10f150 : ∀ x ∈ codeRange 0x10f150 bytes_l10f150, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf150 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f188 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f188 (leaR64Effect 0x10f188 5 (.sib 4 none 0 (.d32 0x268))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x10f188 (fun s => s.RIP = 0x10f188) (leaR64Effect 0x10f188 5 (.sib 4 none 0 (.d32 0x268))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10f190 (movR64R64Effect 0x10f190 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10f190 (fun s => s.RIP = 0x10f190) (movR64R64Effect 0x10f190 7 5) (Reg.operands [.gpr 5] [])) #v[53]
    (.letOp (n := 57) (.out 0x10f193 (movR64R64Effect 0x10f193 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 58) (.exec 0x10f193 (fun s => s.RIP = 0x10f193) (movR64R64Effect 0x10f193 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x10f196 (movR64Imm32Effect 0x10f196 2 0x202220) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x10f196 (fun s => s.RIP = 0x10f196) (movR64Imm32Effect 0x10f196 2 0x202220) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10f19d (callEffect (fun _ => 0x1099c0) 0x10f1a2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x10f19d (PushPre 0x10f19d 5) (callEffect (fun _ => 0x1099c0) 0x10f1a2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10f1a2⟩) #v[]
    (.terminate (.call ⟨.l1099c0, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 53), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10f1a2, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10f188 : List UInt8 :=
  [0x48, 0x8D, 0xAC, 0x24, 0x68, 0x02, 0x00, 0x00, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xEE, 0x48, 0xC7,
    0xC2, 0x20, 0x22, 0x20, 0x00, 0xE8, 0x1E, 0xA8, 0xFF, 0xFF]

theorem code_l10f188 : ∀ x ∈ codeRange 0x10f188 bytes_l10f188, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf188 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f1a2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f1a2 (leaR64Effect 0x10f1a2 13 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 54) (.exec 0x10f1a2 (fun s => s.RIP = 0x10f1a2) (leaR64Effect 0x10f1a2 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10f1a7 (movR64R64Effect 0x10f1a7 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10f1a7 (fun s => s.RIP = 0x10f1a7) (movR64R64Effect 0x10f1a7 7 13) (Reg.operands [.gpr 13] [])) #v[53]
    (.letOp (n := 57) (.out 0x10f1aa (movR64R64Effect 0x10f1aa 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x10f1aa (fun s => s.RIP = 0x10f1aa) (movR64R64Effect 0x10f1aa 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x10f1ad (movR64Imm32Effect 0x10f1ad 2 0x202240) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x10f1ad (fun s => s.RIP = 0x10f1ad) (movR64Imm32Effect 0x10f1ad 2 0x202240) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10f1b4 (callEffect (fun _ => 0x11b8f0) 0x10f1b9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x10f1b4 (PushPre 0x10f1b4 5) (callEffect (fun _ => 0x11b8f0) 0x10f1b9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10f1b9⟩) #v[]
    (.terminate (.call ⟨.l11b8f0, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10f1b9, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10f1a2 : List UInt8 :=
  [0x4C, 0x8D, 0x6C, 0x24, 0x38, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xE6, 0x48, 0xC7, 0xC2, 0x40, 0x22,
    0x20, 0x00, 0xE8, 0x37, 0xC7, 0x00, 0x00]

theorem code_l10f1a2 : ∀ x ∈ codeRange 0x10f1a2 bytes_l10f1a2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf1a2 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f1b9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f1b9 (leaR64Effect 0x10f1b9 15 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x10f1b9 (fun s => s.RIP = 0x10f1b9) (leaR64Effect 0x10f1b9 15 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10f1c1 (movR64R64Effect 0x10f1c1 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10f1c1 (fun s => s.RIP = 0x10f1c1) (movR64R64Effect 0x10f1c1 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 57) (.out 0x10f1c4 (movR64R64Effect 0x10f1c4 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 58) (.exec 0x10f1c4 (fun s => s.RIP = 0x10f1c4) (movR64R64Effect 0x10f1c4 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x10f1c7 (movR64Imm32Effect 0x10f1c7 2 0x202260) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x10f1c7 (fun s => s.RIP = 0x10f1c7) (movR64Imm32Effect 0x10f1c7 2 0x202260) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10f1ce (callEffect (fun _ => 0x1099c0) 0x10f1d3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x10f1ce (PushPre 0x10f1ce 5) (callEffect (fun _ => 0x1099c0) 0x10f1d3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10f1d3⟩) #v[]
    (.terminate (.call ⟨.l1099c0, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10f1d3, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10f1b9 : List UInt8 :=
  [0x4C, 0x8D, 0xBC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xEE, 0x48, 0xC7,
    0xC2, 0x60, 0x22, 0x20, 0x00, 0xE8, 0xED, 0xA7, 0xFF, 0xFF]

theorem code_l10f1b9 : ∀ x ∈ codeRange 0x10f1b9 bytes_l10f1b9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf1b9 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f1d3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f1d3 (leaR64Effect 0x10f1d3 13 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 54) (.exec 0x10f1d3 (fun s => s.RIP = 0x10f1d3) (leaR64Effect 0x10f1d3 13 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10f1db (movR64R64Effect 0x10f1db 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10f1db (fun s => s.RIP = 0x10f1db) (movR64R64Effect 0x10f1db 7 13) (Reg.operands [.gpr 13] [])) #v[53]
    (.letOp (n := 57) (.out 0x10f1de (movR64R64Effect 0x10f1de 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 58) (.exec 0x10f1de (fun s => s.RIP = 0x10f1de) (movR64R64Effect 0x10f1de 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x10f1e1 (movR64R64Effect 0x10f1e1 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 60) (.exec 0x10f1e1 (fun s => s.RIP = 0x10f1e1) (movR64R64Effect 0x10f1e1 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.out 0x10f1e4 (movR64Imm32Effect 0x10f1e4 1 0x2021a0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 62) (.exec 0x10f1e4 (fun s => s.RIP = 0x10f1e4) (movR64Imm32Effect 0x10f1e4 1 0x2021a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x10f1eb (callEffect (fun _ => 0x1109b0) 0x10f1f0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x10f1eb (PushPre 0x10f1eb 5) (callEffect (fun _ => 0x1109b0) 0x10f1f0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x10f1f0⟩) #v[]
    (.terminate (.call ⟨.l1109b0, RegMap.args [(0, 0), (1, 61), (2, 59), (3, 3), (4, 63), (5, 5), (6, 57), (7, 55), (8, 8), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l10f1f0, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l10f1d3 : List UInt8 :=
  [0x4C, 0x8D, 0xAC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x48, 0x89, 0xEE, 0x4C, 0x89,
    0xFA, 0x48, 0xC7, 0xC1, 0xA0, 0x21, 0x20, 0x00, 0xE8, 0xC0, 0x17, 0x00, 0x00]

theorem code_l10f1d3 : ∀ x ∈ codeRange 0x10f1d3 bytes_l10f1d3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf1d3 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f1f0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f1f0 (leaR64Effect 0x10f1f0 15 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x10f1f0 (fun s => s.RIP = 0x10f1f0) (leaR64Effect 0x10f1f0 15 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10f1f8 (movR64R64Effect 0x10f1f8 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10f1f8 (fun s => s.RIP = 0x10f1f8) (movR64R64Effect 0x10f1f8 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 57) (.out 0x10f1fb (movR64R64Effect 0x10f1fb 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 58) (.exec 0x10f1fb (fun s => s.RIP = 0x10f1fb) (movR64R64Effect 0x10f1fb 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x10f1fe (movR64Imm32Effect 0x10f1fe 2 0x202280) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x10f1fe (fun s => s.RIP = 0x10f1fe) (movR64Imm32Effect 0x10f1fe 2 0x202280) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10f205 (callEffect (fun _ => 0x1099c0) 0x10f20a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x10f205 (PushPre 0x10f205 5) (callEffect (fun _ => 0x1099c0) 0x10f20a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10f20a⟩) #v[]
    (.terminate (.call ⟨.l1099c0, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10f20a, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10f1f0 : List UInt8 :=
  [0x4C, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xEE, 0x48, 0xC7,
    0xC2, 0x80, 0x22, 0x20, 0x00, 0xE8, 0xB6, 0xA7, 0xFF, 0xFF]

theorem code_l10f1f0 : ∀ x ∈ codeRange 0x10f1f0 bytes_l10f1f0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf1f0 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f20a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f20a (leaR64Effect 0x10f20a 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10f20a (fun s => s.RIP = 0x10f20a) (leaR64Effect 0x10f20a 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10f20f (movR64R64Effect 0x10f20f 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 56) (.exec 0x10f20f (fun s => s.RIP = 0x10f20f) (movR64R64Effect 0x10f20f 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x10f212 (movR64R64Effect 0x10f212 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 58) (.exec 0x10f212 (fun s => s.RIP = 0x10f212) (movR64R64Effect 0x10f212 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x10f215 (movR64Imm32Effect 0x10f215 1 0x2021a0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x10f215 (fun s => s.RIP = 0x10f215) (movR64Imm32Effect 0x10f215 1 0x2021a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10f21c (callEffect (fun _ => 0x1109b0) 0x10f221) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x10f21c (PushPre 0x10f21c 5) (callEffect (fun _ => 0x1109b0) 0x10f221) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10f221⟩) #v[]
    (.terminate (.call ⟨.l1109b0, RegMap.args [(0, 0), (1, 59), (2, 57), (3, 3), (4, 61), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10f221, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10f20a : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x38, 0x4C, 0x89, 0xE6, 0x4C, 0x89, 0xFA, 0x48, 0xC7, 0xC1, 0xA0, 0x21,
    0x20, 0x00, 0xE8, 0x8F, 0x17, 0x00, 0x00]

theorem code_l10f20a : ∀ x ∈ codeRange 0x10f20a bytes_l10f20a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf20a 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f221_2 : Block Op Label signature Reg.count 122 :=
  .letOp (n := 122) (.out 0x10f2e2 (shrR64Effect 0x10f2e2 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[120]
    (.letOp (n := 123) (.exec 0x10f2e2 (fun s => s.RIP = 0x10f2e2) (shrR64Effect 0x10f2e2 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[120]
    (.letOp (n := 124) (.exec 0x10f2e6 (StorePre 0x10f2e6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f2e6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f2e6 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[122, 4]
    (.letOp (n := 125) (.out 0x10f2eb (xorR32R32Effect 0x10f2eb 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[111, 111]
    (.letOp (n := 126) (.exec 0x10f2eb (fun s => s.RIP = 0x10f2eb) (xorR32R32Effect 0x10f2eb 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[111, 111]
    (.letOp (n := 127) (.out 0x10f2ed (subR64M64Effect 0x10f2ed 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[125, 4]
    (.letOp (n := 128) (.exec 0x10f2ed (LoadPre 0x10f2ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f2ed + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10f2ed 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[125, 4]
    (.letOp (n := 129) (.out 0x10f2f2 (sarR64Effect 0x10f2f2 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[127]
    (.letOp (n := 130) (.exec 0x10f2f2 (fun s => s.RIP = 0x10f2f2) (sarR64Effect 0x10f2f2 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127]
    (.letOp (n := 131) (.out 0x10f2f6 (subR64R64Effect 0x10f2f6 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[129, 72]
    (.letOp (n := 132) (.exec 0x10f2f6 (fun s => s.RIP = 0x10f2f6) (subR64R64Effect 0x10f2f6 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[129, 72]
    (.letOp (n := 133) (.out 0x10f2f9 (movR64Imm64Effect 0x10f2f9 2 0x7fffffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 134) (.exec 0x10f2f9 (fun s => s.RIP = 0x10f2f9) (movR64Imm64Effect 0x10f2f9 2 0x7fffffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 135) (.out 0x10f303 (addR64R64Effect 0x10f303 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[131, 133]
    (.letOp (n := 136) (.exec 0x10f303 (fun s => s.RIP = 0x10f303) (addR64R64Effect 0x10f303 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[131, 133]
    (.letOp (n := 137) (.exec 0x10f306 (StorePre 0x10f306 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10f306 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f306 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 138) (.out 0x10f30b (orR64R64Effect 0x10f30b 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[135, 72]
    (.letOp (n := 139) (.exec 0x10f30b (fun s => s.RIP = 0x10f30b) (orR64R64Effect 0x10f30b 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[135, 72]
    (.letOp (n := 140) (.out 0x10f30e (shrR64Effect 0x10f30e 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[138]
    (.letOp (n := 141) (.exec 0x10f30e (fun s => s.RIP = 0x10f30e) (shrR64Effect 0x10f30e 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[138]
    (.letOp (n := 142) (.exec 0x10f312 (StorePre 0x10f312 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f312 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f312 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[140, 4]
    (.letOp (n := 143) (.out 0x10f317 (movzxR32M8Effect 0x10f317 5 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 144) (.exec 0x10f317 (LoadPre 0x10f317 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f317 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10f317 5 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 145) (.out 0x10f31c (andAlImm8Effect 0x10f31c 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[143]
    (.letOp (n := 146) (.exec 0x10f31c (fun s => s.RIP = 0x10f31c) (andAlImm8Effect 0x10f31c 0x1) (Reg.operands [.gpr 0] [])) #v[143]
    (.letOp (n := 147) (.out 0x10f31e (movzxR32R8Effect 0x10f31e 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[145]
    (.letOp (n := 148) (.exec 0x10f31e (fun s => s.RIP = 0x10f31e) (movzxR32R8Effect 0x10f31e 3 7 0) (Reg.operands [.gpr 0] [])) #v[145]
    (.letOp (n := 149) (.out 0x10f321 (callEffect (fun _ => 0x127d50) 0x10f326) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 150) (.exec 0x10f321 (PushPre 0x10f321 5) (callEffect (fun _ => 0x127d50) 0x10f326) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 151) (.const ⟨64, 0x10f326⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 145), (1, 140), (2, 133), (3, 3), (4, 149), (5, 57), (6, 72), (7, 147), (8, 97), (9, 9), (10, 10), (11, 11), (12, 62), (13, 74), (14, 60), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)] 152⟩ { target := .l10f326, kept := #v[], arity := rfl, guard := some (Fin.last 151) })))))))))))))))))))))))))))))))

def bytes_l10f221_2 : List UInt8 :=
  [0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x38, 0x31, 0xC9, 0x48, 0x2B, 0x4C, 0x24, 0x38,
    0x48, 0xC1, 0xF9, 0x3F, 0x48, 0x29, 0xF1, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x7F, 0x48, 0x01, 0xD1, 0x48, 0x89, 0x74, 0x24, 0x20, 0x48, 0x09, 0xF1, 0x48, 0xC1, 0xE9, 0x3F,
    0x48, 0x89, 0x4C, 0x24, 0x38, 0x0F, 0xB6, 0x44, 0x24, 0x38, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8,
    0x2A, 0x8A, 0x01, 0x00]

theorem code_l10f221_2 : ∀ x ∈ codeRange 0x10f2e2 bytes_l10f221_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf2e2 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f221_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.exec 0x10f292 (fun s => s.RIP = 0x10f292) (leaR64Effect 0x10f292 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x10f297 (xorR32R32Effect 0x10f297 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[15, 15]
    (.letOp (n := 88) (.exec 0x10f297 (fun s => s.RIP = 0x10f297) (xorR32R32Effect 0x10f297 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 89) (.out 0x10f29a (xorR32R32Effect 0x10f29a 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[66, 66]
    (.letOp (n := 90) (.exec 0x10f29a (fun s => s.RIP = 0x10f29a) (xorR32R32Effect 0x10f29a 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[66, 66]
    (.letOp (n := 91) (.out 0x10f29c (subR64M64Effect 0x10f29c 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[89, 4]
    (.letOp (n := 92) (.exec 0x10f29c (LoadPre 0x10f29c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f29c + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10f29c 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 93) (.out 0x10f2a1 (sarR64Effect 0x10f2a1 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 94) (.exec 0x10f2a1 (fun s => s.RIP = 0x10f2a1) (sarR64Effect 0x10f2a1 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91]
    (.letOp (n := 95) (.out 0x10f2a5 (subR64R64Effect 0x10f2a5 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[93, 68]
    (.letOp (n := 96) (.exec 0x10f2a5 (fun s => s.RIP = 0x10f2a5) (subR64R64Effect 0x10f2a5 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[93, 68]
    (.letOp (n := 97) (.out 0x10f2a8 (movR64Imm64Effect 0x10f2a8 8 0x5d576e7357a4501d) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 98) (.exec 0x10f2a8 (fun s => s.RIP = 0x10f2a8) (movR64Imm64Effect 0x10f2a8 8 0x5d576e7357a4501d) (Reg.operands [] [])) #v[]
    (.letOp (n := 99) (.out 0x10f2b2 (addR64R64Effect 0x10f2b2 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[95, 97]
    (.letOp (n := 100) (.exec 0x10f2b2 (fun s => s.RIP = 0x10f2b2) (addR64R64Effect 0x10f2b2 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[95, 97]
    (.letOp (n := 101) (.exec 0x10f2b5 (StorePre 0x10f2b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10f2b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f2b5 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 102) (.out 0x10f2ba (orR64R64Effect 0x10f2ba 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[99, 68]
    (.letOp (n := 103) (.exec 0x10f2ba (fun s => s.RIP = 0x10f2ba) (orR64R64Effect 0x10f2ba 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[99, 68]
    (.letOp (n := 104) (.out 0x10f2bd (shrR64Effect 0x10f2bd 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[102]
    (.letOp (n := 105) (.exec 0x10f2bd (fun s => s.RIP = 0x10f2bd) (shrR64Effect 0x10f2bd 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[102]
    (.letOp (n := 106) (.exec 0x10f2c1 (StorePre 0x10f2c1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f2c1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f2c1 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[104, 4]
    (.letOp (n := 107) (.out 0x10f2c6 (xorR32R32Effect 0x10f2c6 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[104, 104]
    (.letOp (n := 108) (.exec 0x10f2c6 (fun s => s.RIP = 0x10f2c6) (xorR32R32Effect 0x10f2c6 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[104, 104]
    (.letOp (n := 109) (.out 0x10f2c8 (subR64M64Effect 0x10f2c8 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[107, 4]
    (.letOp (n := 110) (.exec 0x10f2c8 (LoadPre 0x10f2c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f2c8 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10f2c8 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[107, 4]
    (.letOp (n := 111) (.out 0x10f2cd (sarR64Effect 0x10f2cd 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[109]
    (.letOp (n := 112) (.exec 0x10f2cd (fun s => s.RIP = 0x10f2cd) (sarR64Effect 0x10f2cd 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[109]
    (.letOp (n := 113) (.out 0x10f2d1 (movR64R64Effect 0x10f2d1 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[70]
    (.letOp (n := 114) (.exec 0x10f2d1 (fun s => s.RIP = 0x10f2d1) (movR64R64Effect 0x10f2d1 2 7) (Reg.operands [.gpr 7] [])) #v[70]
    (.letOp (n := 115) (.out 0x10f2d4 (notR64Effect 0x10f2d4 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[113]
    (.letOp (n := 116) (.exec 0x10f2d4 (fun s => s.RIP = 0x10f2d4) (notR64Effect 0x10f2d4 2) (Reg.operands [.gpr 2] [])) #v[113]
    (.letOp (n := 117) (.out 0x10f2d7 (addR64R64Effect 0x10f2d7 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[115, 111]
    (.letOp (n := 118) (.exec 0x10f2d7 (fun s => s.RIP = 0x10f2d7) (addR64R64Effect 0x10f2d7 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[115, 111]
    (.letOp (n := 119) (.exec 0x10f2da (StorePre 0x10f2da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10f2da + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f2da 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 120) (.out 0x10f2df (andR64R64Effect 0x10f2df 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[117, 70]
    (.letOp (n := 121) (.exec 0x10f2df (fun s => s.RIP = 0x10f2df) (andR64R64Effect 0x10f2df 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[117, 70]
    (b_l10f221_2))))))))))))))))))))))))))))))))))))

def bytes_l10f221_1 : List UInt8 :=
  [0x48, 0x8D, 0x44, 0x24, 0x38, 0x45, 0x31, 0xFF, 0x31, 0xC9, 0x48, 0x2B, 0x4C, 0x24, 0x38, 0x48,
    0xC1, 0xF9, 0x3F, 0x48, 0x29, 0xD1, 0x49, 0xB8, 0x1D, 0x50, 0xA4, 0x57, 0x73, 0x6E, 0x57, 0x5D,
    0x4C, 0x01, 0xC1, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x09, 0xD1, 0x48, 0xC1, 0xE9, 0x3F, 0x48,
    0x89, 0x4C, 0x24, 0x38, 0x31, 0xC9, 0x48, 0x2B, 0x4C, 0x24, 0x38, 0x48, 0xC1, 0xF9, 0x3F, 0x48,
    0x89, 0xFA, 0x48, 0xF7, 0xD2, 0x48, 0x01, 0xCA, 0x48, 0x89, 0x7C, 0x24, 0x18, 0x48, 0x21, 0xFA] ++ bytes_l10f221_2

theorem code_l10f221_1 : ∀ x ∈ codeRange 0x10f292 bytes_l10f221_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xf292 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10f221_2

@[cfg_block] def b_l10f221 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f221 (movR64M64Effect 0x10f221 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10f221 (LoadPre 0x10f221 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10f221 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f221 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10f229 (StorePre 0x10f229 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10f229 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f229 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.exec 0x10f231 (StorePre 0x10f231 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10f231 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f231 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 57) (.out 0x10f236 (movR64M64Effect 0x10f236 5 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 58) (.exec 0x10f236 (LoadPre 0x10f236 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10f236 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f236 5 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x10f23e (StorePre 0x10f23e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10f23e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f23e 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x10f243 (movR64M64Effect 0x10f243 14 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 61) (.exec 0x10f243 (LoadPre 0x10f243 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10f243 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f243 14 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x10f24b (movR64M64Effect 0x10f24b 12 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 63) (.exec 0x10f24b (LoadPre 0x10f24b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10f24b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f24b 12 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x10f253 (StorePre 0x10f253 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10f253 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f253 12 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.exec 0x10f258 (StorePre 0x10f258 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10f258 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f258 14 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 66) (.out 0x10f25d (movR64M64Effect 0x10f25d 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 67) (.exec 0x10f25d (LoadPre 0x10f25d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f25d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f25d 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x10f262 (movR64M64Effect 0x10f262 2 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 69) (.exec 0x10f262 (LoadPre 0x10f262 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10f262 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f262 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x10f267 (movR64M64Effect 0x10f267 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 71) (.exec 0x10f267 (LoadPre 0x10f267 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10f267 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f267 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x10f26c (movR64M64Effect 0x10f26c 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 73) (.exec 0x10f26c (LoadPre 0x10f26c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10f26c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f26c 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x10f271 (movR64Imm64Effect 0x10f271 13 0xdfe92f46681b20a0) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 75) (.exec 0x10f271 (fun s => s.RIP = 0x10f271) (movR64Imm64Effect 0x10f271 13 0xdfe92f46681b20a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 76) (.out 0x10f27b (movR64R64Effect 0x10f27b 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 77) (.exec 0x10f27b (fun s => s.RIP = 0x10f27b) (movR64R64Effect 0x10f27b 0 13) (Reg.operands [.gpr 13] [])) #v[74]
    (.letOp (n := 78) (.out 0x10f27e (subR64R64Effect 0x10f27e 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[76, 66]
    (.letOp (n := 79) (.exec 0x10f27e (fun s => s.RIP = 0x10f27e) (subR64R64Effect 0x10f27e 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[76, 66]
    (.letOp (n := 80) (.exec 0x10f281 (StorePre 0x10f281 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10f281 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f281 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 81) (.out 0x10f286 (andR64R64Effect 0x10f286 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[78, 66]
    (.letOp (n := 82) (.exec 0x10f286 (fun s => s.RIP = 0x10f286) (andR64R64Effect 0x10f286 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[78, 66]
    (.letOp (n := 83) (.out 0x10f289 (shrR64Effect 0x10f289 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[81]
    (.letOp (n := 84) (.exec 0x10f289 (fun s => s.RIP = 0x10f289) (shrR64Effect 0x10f289 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.exec 0x10f28d (StorePre 0x10f28d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f28d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f28d 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 4]
    (b_l10f221_1)))))))))))))))))))))))))))))))))

def bytes_l10f221 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x44, 0x24, 0x70, 0x48, 0x8B, 0xAC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x6C,
    0x24, 0x68, 0x4C, 0x8B, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0xA4, 0x24, 0xB8, 0x00,
    0x00, 0x00, 0x4C, 0x89, 0x64, 0x24, 0x60, 0x4C, 0x89, 0x74, 0x24, 0x58, 0x48, 0x8B, 0x4C, 0x24,
    0x38, 0x48, 0x8B, 0x54, 0x24, 0x40, 0x48, 0x8B, 0x7C, 0x24, 0x48, 0x48, 0x8B, 0x74, 0x24, 0x50,
    0x49, 0xBD, 0xA0, 0x20, 0x1B, 0x68, 0x46, 0x2F, 0xE9, 0xDF, 0x4C, 0x89, 0xE8, 0x48, 0x29, 0xC8,
    0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x21, 0xC8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x44, 0x24,
    0x38] ++ bytes_l10f221_1

theorem code_l10f221 : ∀ x ∈ codeRange 0x10f221 bytes_l10f221, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xf221 113 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10f221_1

@[cfg_block] def b_l10f326_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.out 0x10f37c (movR64R64Effect 0x10f37c 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 91) (.exec 0x10f37c (fun s => s.RIP = 0x10f37c) (movR64R64Effect 0x10f37c 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 92) (.out 0x10f37f (notR64Effect 0x10f37f 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[90]
    (.letOp (n := 93) (.exec 0x10f37f (fun s => s.RIP = 0x10f37f) (notR64Effect 0x10f37f 0) (Reg.operands [.gpr 0] [])) #v[90]
    (.letOp (n := 94) (.out 0x10f382 (addR64R64Effect 0x10f382 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[92, 88]
    (.letOp (n := 95) (.exec 0x10f382 (fun s => s.RIP = 0x10f382) (addR64R64Effect 0x10f382 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[92, 88]
    (.letOp (n := 96) (.out 0x10f385 (andR64R64Effect 0x10f385 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[94, 5]
    (.letOp (n := 97) (.exec 0x10f385 (fun s => s.RIP = 0x10f385) (andR64R64Effect 0x10f385 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[94, 5]
    (.letOp (n := 98) (.out 0x10f388 (shrR64Effect 0x10f388 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[96]
    (.letOp (n := 99) (.exec 0x10f388 (fun s => s.RIP = 0x10f388) (shrR64Effect 0x10f388 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[96]
    (.letOp (n := 100) (.exec 0x10f38c (StorePre 0x10f38c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f38c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f38c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[98, 4]
    (.letOp (n := 101) (.out 0x10f391 (subR64M64Effect 0x10f391 15 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[15, 4]
    (.letOp (n := 102) (.exec 0x10f391 (LoadPre 0x10f391 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f391 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10f391 15 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 103) (.out 0x10f396 (sarR64Effect 0x10f396 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[101]
    (.letOp (n := 104) (.exec 0x10f396 (fun s => s.RIP = 0x10f396) (sarR64Effect 0x10f396 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[101]
    (.letOp (n := 105) (.out 0x10f39a (subR64R64Effect 0x10f39a 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[103, 61]
    (.letOp (n := 106) (.exec 0x10f39a (fun s => s.RIP = 0x10f39a) (subR64R64Effect 0x10f39a 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[103, 61]
    (.letOp (n := 107) (.out 0x10f39d (movR64Imm64Effect 0x10f39d 0 0x7fffffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 108) (.exec 0x10f39d (fun s => s.RIP = 0x10f39d) (movR64Imm64Effect 0x10f39d 0 0x7fffffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 109) (.out 0x10f3a7 (addR64R64Effect 0x10f3a7 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[105, 107]
    (.letOp (n := 110) (.exec 0x10f3a7 (fun s => s.RIP = 0x10f3a7) (addR64R64Effect 0x10f3a7 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[105, 107]
    (.letOp (n := 111) (.out 0x10f3aa (orR64R64Effect 0x10f3aa 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[109, 61]
    (.letOp (n := 112) (.exec 0x10f3aa (fun s => s.RIP = 0x10f3aa) (orR64R64Effect 0x10f3aa 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[109, 61]
    (.letOp (n := 113) (.out 0x10f3ad (shrR64Effect 0x10f3ad 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[111]
    (.letOp (n := 114) (.exec 0x10f3ad (fun s => s.RIP = 0x10f3ad) (shrR64Effect 0x10f3ad 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[111]
    (.letOp (n := 115) (.exec 0x10f3b1 (StorePre 0x10f3b1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f3b1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f3b1 15 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[113, 4]
    (.letOp (n := 116) (.out 0x10f3b6 (movzxR32M8Effect 0x10f3b6 5 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 117) (.exec 0x10f3b6 (LoadPre 0x10f3b6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f3b6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10f3b6 5 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 118) (.out 0x10f3bb (andAlImm8Effect 0x10f3bb 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[116]
    (.letOp (n := 119) (.exec 0x10f3bb (fun s => s.RIP = 0x10f3bb) (andAlImm8Effect 0x10f3bb 0x1) (Reg.operands [.gpr 0] [])) #v[116]
    (.letOp (n := 120) (.out 0x10f3bd (movzxR32R8Effect 0x10f3bd 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[118]
    (.letOp (n := 121) (.exec 0x10f3bd (fun s => s.RIP = 0x10f3bd) (movzxR32R8Effect 0x10f3bd 3 7 0) (Reg.operands [.gpr 0] [])) #v[118]
    (.letOp (n := 122) (.out 0x10f3c0 (callEffect (fun _ => 0x127d50) 0x10f3c5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 123) (.exec 0x10f3c0 (PushPre 0x10f3c0 5) (callEffect (fun _ => 0x127d50) 0x10f3c5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 124) (.const ⟨64, 0x10f3c5⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 118), (1, 63), (2, 88), (3, 3), (4, 122), (5, 5), (6, 73), (7, 120), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 86), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)] 125⟩ { target := .l10f3c5, kept := #v[], arity := rfl, guard := some (Fin.last 124) }))))))))))))))))))))))))))))))))))))

def bytes_l10f326_1 : List UInt8 :=
  [0x48, 0x89, 0xE8, 0x48, 0xF7, 0xD0, 0x48, 0x01, 0xD0, 0x48, 0x21, 0xE8, 0x48, 0xC1, 0xE8, 0x3F,
    0x48, 0x89, 0x44, 0x24, 0x38, 0x4C, 0x2B, 0x7C, 0x24, 0x38, 0x49, 0xC1, 0xFF, 0x3F, 0x4D, 0x29,
    0xEF, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x49, 0x01, 0xC7, 0x4D, 0x09,
    0xEF, 0x49, 0xC1, 0xEF, 0x3F, 0x4C, 0x89, 0x7C, 0x24, 0x38, 0x0F, 0xB6, 0x44, 0x24, 0x38, 0x24,
    0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x8B, 0x89, 0x01, 0x00]

theorem code_l10f326_1 : ∀ x ∈ codeRange 0x10f37c bytes_l10f326_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf37c 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f326 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f326 (subR64R64Effect 0x10f326 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[13, 14]
    (.letOp (n := 54) (.exec 0x10f326 (fun s => s.RIP = 0x10f326) (subR64R64Effect 0x10f326 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[13, 14]
    (.letOp (n := 55) (.exec 0x10f329 (StorePre 0x10f329 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10f329 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f329 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 56) (.out 0x10f32e (andR64R64Effect 0x10f32e 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[53, 14]
    (.letOp (n := 57) (.exec 0x10f32e (fun s => s.RIP = 0x10f32e) (andR64R64Effect 0x10f32e 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.out 0x10f331 (shrR64Effect 0x10f331 4 13 63) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[56]
    (.letOp (n := 59) (.exec 0x10f331 (fun s => s.RIP = 0x10f331) (shrR64Effect 0x10f331 4 13 63) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 60) (.exec 0x10f335 (StorePre 0x10f335 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f335 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f335 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x10f33a (movR64M64Effect 0x10f33a 13 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 62) (.exec 0x10f33a (LoadPre 0x10f33a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10f33a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f33a 13 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x10f342 (leaR64Effect 0x10f342 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 64) (.exec 0x10f342 (fun s => s.RIP = 0x10f342) (leaR64Effect 0x10f342 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x10f347 (xorR32R32Effect 0x10f347 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 66) (.exec 0x10f347 (fun s => s.RIP = 0x10f347) (xorR32R32Effect 0x10f347 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 67) (.out 0x10f349 (subR64M64Effect 0x10f349 2 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[65, 4]
    (.letOp (n := 68) (.exec 0x10f349 (LoadPre 0x10f349 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f349 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10f349 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 69) (.out 0x10f34e (sarR64Effect 0x10f34e 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[67]
    (.letOp (n := 70) (.exec 0x10f34e (fun s => s.RIP = 0x10f34e) (sarR64Effect 0x10f34e 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x10f352 (subR64R64Effect 0x10f352 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[69, 12]
    (.letOp (n := 72) (.exec 0x10f352 (fun s => s.RIP = 0x10f352) (subR64R64Effect 0x10f352 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[69, 12]
    (.letOp (n := 73) (.out 0x10f355 (movR64Imm64Effect 0x10f355 6 0x5d576e7357a4501d) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 74) (.exec 0x10f355 (fun s => s.RIP = 0x10f355) (movR64Imm64Effect 0x10f355 6 0x5d576e7357a4501d) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x10f35f (addR64R64Effect 0x10f35f 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[71, 73]
    (.letOp (n := 76) (.exec 0x10f35f (fun s => s.RIP = 0x10f35f) (addR64R64Effect 0x10f35f 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[71, 73]
    (.letOp (n := 77) (.out 0x10f362 (orR64R64Effect 0x10f362 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[75, 12]
    (.letOp (n := 78) (.exec 0x10f362 (fun s => s.RIP = 0x10f362) (orR64R64Effect 0x10f362 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[75, 12]
    (.letOp (n := 79) (.out 0x10f365 (shrR64Effect 0x10f365 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[77]
    (.letOp (n := 80) (.exec 0x10f365 (fun s => s.RIP = 0x10f365) (shrR64Effect 0x10f365 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.exec 0x10f369 (StorePre 0x10f369 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f369 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f369 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.out 0x10f36e (xorR32R32Effect 0x10f36e 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[79, 79]
    (.letOp (n := 83) (.exec 0x10f36e (fun s => s.RIP = 0x10f36e) (xorR32R32Effect 0x10f36e 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[79, 79]
    (.letOp (n := 84) (.out 0x10f370 (subR64M64Effect 0x10f370 2 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[82, 4]
    (.letOp (n := 85) (.exec 0x10f370 (LoadPre 0x10f370 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f370 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10f370 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[82, 4]
    (.letOp (n := 86) (.out 0x10f375 (movR32R32Effect 0x10f375 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[0]
    (.letOp (n := 87) (.exec 0x10f375 (fun s => s.RIP = 0x10f375) (movR32R32Effect 0x10f375 3 14 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 88) (.out 0x10f378 (sarR64Effect 0x10f378 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[84]
    (.letOp (n := 89) (.exec 0x10f378 (fun s => s.RIP = 0x10f378) (sarR64Effect 0x10f378 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[84]
    (b_l10f326_1)))))))))))))))))))))))))))))))))))))

def bytes_l10f326 : List UInt8 :=
  [0x4D, 0x29, 0xF5, 0x4C, 0x89, 0x74, 0x24, 0x30, 0x4D, 0x21, 0xF5, 0x49, 0xC1, 0xED, 0x3F, 0x4C,
    0x89, 0x6C, 0x24, 0x38, 0x4C, 0x8B, 0xAC, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x4C, 0x24,
    0x38, 0x31, 0xD2, 0x48, 0x2B, 0x54, 0x24, 0x38, 0x48, 0xC1, 0xFA, 0x3F, 0x4C, 0x29, 0xE2, 0x48,
    0xBE, 0x1D, 0x50, 0xA4, 0x57, 0x73, 0x6E, 0x57, 0x5D, 0x48, 0x01, 0xF2, 0x4C, 0x09, 0xE2, 0x48,
    0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x38, 0x31, 0xD2, 0x48, 0x2B, 0x54, 0x24, 0x38, 0x41,
    0x89, 0xC6, 0x48, 0xC1, 0xFA, 0x3F] ++ bytes_l10f326_1

theorem code_l10f326 : ∀ x ∈ codeRange 0x10f326 bytes_l10f326, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xf326 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10f326_1

@[cfg_block] def b_l10f3c5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f3c5 (movR32R32Effect 0x10f3c5 3 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[0]
    (.letOp (n := 54) (.exec 0x10f3c5 (fun s => s.RIP = 0x10f3c5) (movR32R32Effect 0x10f3c5 3 15 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x10f3c8 (testR8R8Effect 0x10f3c8 3 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 56) (.exec 0x10f3c8 (fun s => s.RIP = 0x10f3c8) (testR8R8Effect 0x10f3c8 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l10f44c, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l10f3cd, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l10f3c5 : List UInt8 :=
  [0x41, 0x89, 0xC7, 0x45, 0x84, 0xF6, 0x74, 0x7F]

theorem code_l10f3c5 : ∀ x ∈ codeRange 0x10f3c5 bytes_l10f3c5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf3c5 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f3cd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f3cd (movR64M64Effect 0x10f3cd 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10f3cd (LoadPre 0x10f3cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10f3cd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f3cd 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10f3d2 (StorePre 0x10f3d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f3d2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f3d2 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10f3d7 (movR64M64Effect 0x10f3d7 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x10f3d7 (LoadPre 0x10f3d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10f3d7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f3d7 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10f3dc (StorePre 0x10f3dc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10f3dc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f3dc 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x10f3e1 (movR64M64Effect 0x10f3e1 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x10f3e1 (LoadPre 0x10f3e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10f3e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f3e1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x10f3e6 (StorePre 0x10f3e6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10f3e6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f3e6 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x10f3eb (movR64M64Effect 0x10f3eb 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x10f3eb (LoadPre 0x10f3eb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10f3eb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f3eb 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x10f3f0 (StorePre 0x10f3f0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10f3f0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f3f0 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x10f3f5 (leaR64Effect 0x10f3f5 7 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x10f3f5 (fun s => s.RIP = 0x10f3f5) (leaR64Effect 0x10f3f5 7 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x10f3fd (leaR64Effect 0x10f3fd 6 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x10f3fd (fun s => s.RIP = 0x10f3fd) (leaR64Effect 0x10f3fd 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x10f402 (movR64Imm32Effect 0x10f402 2 0x2021a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 70) (.exec 0x10f402 (fun s => s.RIP = 0x10f402) (movR64Imm32Effect 0x10f402 2 0x2021a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x10f409 (callEffect (fun _ => 0x110b80) 0x10f40e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x10f409 (PushPre 0x10f409 5) (callEffect (fun _ => 0x110b80) 0x10f40e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x10f40e⟩) #v[]
    (.terminate (.call ⟨.l110b80, RegMap.args [(0, 62), (2, 69), (3, 3), (4, 71), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l10f40e, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l10f3cd : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48,
    0x89, 0x44, 0x24, 0x40, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0x8B,
    0x44, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0x8D, 0xBC, 0x24, 0xE0, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0x74, 0x24, 0x38, 0x48, 0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00, 0xE8, 0x72, 0x17, 0x00,
    0x00]

theorem code_l10f3cd : ∀ x ∈ codeRange 0x10f3cd bytes_l10f3cd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf3cd 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f40e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f40e (testR8R8Effect 0x10f40e 3 15 15) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 15] []) (.flag .ZF)) #v[15, 15]
    (.letOp (n := 54) (.exec 0x10f40e (fun s => s.RIP = 0x10f40e) (testR8R8Effect 0x10f40e 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 55) (.exec 0x10f411 (StorePre 0x10f411 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10f411 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10f411 5 15 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 56) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 56) ⟨.l10f48a, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l10f418, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l10f40e : List UInt8 :=
  [0x45, 0x84, 0xFF, 0x44, 0x88, 0x7C, 0x24, 0x07, 0x74, 0x72]

theorem code_l10f40e : ∀ x ∈ codeRange 0x10f40e bytes_l10f40e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf40e 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f418 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f418 (movR64M64Effect 0x10f418 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10f418 (LoadPre 0x10f418 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10f418 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f418 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10f41d (StorePre 0x10f41d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f41d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f41d 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.exec 0x10f422 (StorePre 0x10f422 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10f422 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f422 12 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 57) (.exec 0x10f427 (StorePre 0x10f427 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10f427 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f427 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 58) (.exec 0x10f42c (StorePre 0x10f42c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10f42c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10f42c 13 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 59) (.out 0x10f431 (leaR64Effect 0x10f431 7 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x10f431 (fun s => s.RIP = 0x10f431) (leaR64Effect 0x10f431 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10f439 (leaR64Effect 0x10f439 6 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x10f439 (fun s => s.RIP = 0x10f439) (leaR64Effect 0x10f439 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x10f43e (movR64Imm32Effect 0x10f43e 2 0x2021a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 64) (.exec 0x10f43e (fun s => s.RIP = 0x10f43e) (movR64Imm32Effect 0x10f43e 2 0x2021a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x10f445 (callEffect (fun _ => 0x110b80) 0x10f44a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x10f445 (PushPre 0x10f445 5) (callEffect (fun _ => 0x110b80) 0x10f44a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x10f44a⟩) #v[]
    (.terminate (.call ⟨.l110b80, RegMap.args [(0, 53), (2, 63), (3, 3), (4, 65), (5, 5), (6, 61), (7, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l10f44a, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l10f418 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x89, 0x44, 0x24, 0x38, 0x4C, 0x89, 0x64, 0x24, 0x40, 0x48,
    0x89, 0x6C, 0x24, 0x48, 0x4C, 0x89, 0x6C, 0x24, 0x50, 0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x00, 0x00,
    0x00, 0x48, 0x8D, 0x74, 0x24, 0x38, 0x48, 0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00, 0xE8, 0x36, 0x17,
    0x00, 0x00]

theorem code_l10f418 : ∀ x ∈ codeRange 0x10f418 bytes_l10f418, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf418 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f44a : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l10f4af, RegMap.args (entryMap (live .l10f44a)) 53⟩)

def bytes_l10f44a : List UInt8 :=
  [0xEB, 0x63]

theorem code_l10f44a : ∀ x ∈ codeRange 0x10f44a bytes_l10f44a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf44a 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f44c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f44c (movR64M64Effect 0x10f44c 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10f44c (LoadPre 0x10f44c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10f44c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f44c 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10f451 (StorePre 0x10f451 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10f451 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f451 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10f459 (movR64M64Effect 0x10f459 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x10f459 (LoadPre 0x10f459 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10f459 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f459 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10f45e (StorePre 0x10f45e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10f45e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f45e 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x10f466 (movR64M64Effect 0x10f466 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x10f466 (LoadPre 0x10f466 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10f466 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f466 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x10f46b (StorePre 0x10f46b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10f46b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f46b 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x10f473 (movR64M64Effect 0x10f473 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x10f473 (LoadPre 0x10f473 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10f473 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f473 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x10f478 (StorePre 0x10f478 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10f478 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f478 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x10f480 (testR8R8Effect 0x10f480 3 15 15) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 15] []) (.flag .ZF)) #v[15, 15]
    (.letOp (n := 66) (.exec 0x10f480 (fun s => s.RIP = 0x10f480) (testR8R8Effect 0x10f480 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 67) (.exec 0x10f483 (StorePre 0x10f483 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10f483 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10f483 5 15 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 68) (.pure (condOp 5)) #v[65]
    (.terminate (.condBr (Fin.last 68) ⟨.l10f418, RegMap.args [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ ⟨.l10f48a, RegMap.args [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l10f44c : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44,
    0x24, 0x10, 0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48,
    0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24,
    0xF8, 0x00, 0x00, 0x00, 0x45, 0x84, 0xFF, 0x44, 0x88, 0x7C, 0x24, 0x07, 0x75, 0x8E]

theorem code_l10f44c : ∀ x ∈ codeRange 0x10f44c bytes_l10f44c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf44c 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f48a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f48a (movR64M64Effect 0x10f48a 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10f48a (LoadPre 0x10f48a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10f48a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f48a 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10f48f (StorePre 0x10f48f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10f48f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f48f 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.exec 0x10f497 (StorePre 0x10f497 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10f497 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f497 12 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 57) (.exec 0x10f49f (StorePre 0x10f49f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10f49f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f49f 5 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 58) (.exec 0x10f4a7 (StorePre 0x10f4a7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10f4a7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f4a7 13 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.terminate (.br ⟨.l10f4af, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l10f48a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xA4,
    0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xAC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xAC,
    0x24, 0xC8, 0x00, 0x00, 0x00]

theorem code_l10f48a : ∀ x ∈ codeRange 0x10f48a bytes_l10f48a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf48a 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f4af : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f4af (leaR64Effect 0x10f4af 15 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x10f4af (fun s => s.RIP = 0x10f4af) (leaR64Effect 0x10f4af 15 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10f4b4 (leaR64Effect 0x10f4b4 6 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x10f4b4 (fun s => s.RIP = 0x10f4b4) (leaR64Effect 0x10f4b4 6 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10f4bc (movR64R64Effect 0x10f4bc 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x10f4bc (fun s => s.RIP = 0x10f4bc) (movR64R64Effect 0x10f4bc 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 59) (.out 0x10f4bf (callEffect (fun _ => 0x10a2f0) 0x10f4c4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10f4bf (PushPre 0x10f4bf 5) (callEffect (fun _ => 0x10a2f0) 0x10f4c4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10f4c4⟩) #v[]
    (.terminate (.call ⟨.l10a2f0, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 55), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10f4c4, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10f4af : List UInt8 :=
  [0x4C, 0x8D, 0x7C, 0x24, 0x38, 0x48, 0x8D, 0xB4, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF,
    0xE8, 0x2C, 0xAE, 0xFF, 0xFF]

theorem code_l10f4af : ∀ x ∈ codeRange 0x10f4af bytes_l10f4af, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf4af 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f4c4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f4c4 (movR64M64Effect 0x10f4c4 5 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x10f4c4 (LoadPre 0x10f4c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10f4c4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f4c4 5 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10f4cc (leaR64Effect 0x10f4cc 7 (.base 5 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10f4cc (fun s => s.RIP = 0x10f4cc) (leaR64Effect 0x10f4cc 7 (.base 5 (.d8 0x8))) (Reg.operands [.gpr 5] [])) #v[53]
    (.letOp (n := 57) (.out 0x10f4d0 (movR32Imm32Effect 0x10f4d0 5 6 0x101) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x10f4d0 (fun s => s.RIP = 0x10f4d0) (movR32Imm32Effect 0x10f4d0 5 6 0x101) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10f4d5 (movR32Imm32Effect 0x10f4d5 5 1 0x10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x10f4d5 (fun s => s.RIP = 0x10f4d5) (movR32Imm32Effect 0x10f4d5 5 1 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10f4da (movR32Imm32Effect 0x10f4da 6 8 0x80) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 62) (.exec 0x10f4da (fun s => s.RIP = 0x10f4da) (movR32Imm32Effect 0x10f4da 6 8 0x80) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x10f4e0 (movR32Imm32Effect 0x10f4e0 6 9 0x5) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 64) (.exec 0x10f4e0 (fun s => s.RIP = 0x10f4e0) (movR32Imm32Effect 0x10f4e0 6 9 0x5) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x10f4e6 (movR64R64Effect 0x10f4e6 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 66) (.exec 0x10f4e6 (fun s => s.RIP = 0x10f4e6) (movR64R64Effect 0x10f4e6 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 67) (.out 0x10f4e9 (callEffect (fun _ => 0x1107b0) 0x10f4ee) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x10f4e9 (PushPre 0x10f4e9 5) (callEffect (fun _ => 0x1107b0) 0x10f4ee) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x10f4ee⟩) #v[]
    (.terminate (.call ⟨.l1107b0, RegMap.args [(1, 59), (2, 65), (3, 3), (4, 67), (5, 53), (6, 57), (7, 55), (8, 61), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l10f4ee, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l10f4c4 : List UInt8 :=
  [0x48, 0x8B, 0xAC, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7D, 0x08, 0xBE, 0x01, 0x01, 0x00,
    0x00, 0xB9, 0x10, 0x00, 0x00, 0x00, 0x41, 0xB8, 0x80, 0x00, 0x00, 0x00, 0x41, 0xB9, 0x05, 0x00,
    0x00, 0x00, 0x4C, 0x89, 0xFA, 0xE8, 0xC2, 0x12, 0x00, 0x00]

theorem code_l10f4c4 : ∀ x ∈ codeRange 0x10f4c4 bytes_l10f4c4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf4c4 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f4ee : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10f4ee (StorePre 0x10f4ee 4 (fun s => AddrMode.addr (.base 5 (.d8 0x0)) s (0x10f4ee + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10f4ee 0 (.base 5 (.d8 0x0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[0, 5]
    (.letOp (n := 54) (.out 0x10f4f2 (leaR64Effect 0x10f4f2 15 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 55) (.exec 0x10f4f2 (fun s => s.RIP = 0x10f4f2) (leaR64Effect 0x10f4f2 15 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x10f4f7 (leaR64Effect 0x10f4f7 6 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 57) (.exec 0x10f4f7 (fun s => s.RIP = 0x10f4f7) (leaR64Effect 0x10f4f7 6 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x10f4ff (movR64R64Effect 0x10f4ff 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[54]
    (.letOp (n := 59) (.exec 0x10f4ff (fun s => s.RIP = 0x10f4ff) (movR64R64Effect 0x10f4ff 7 15) (Reg.operands [.gpr 15] [])) #v[54]
    (.letOp (n := 60) (.out 0x10f502 (callEffect (fun _ => 0x10a2f0) 0x10f507) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x10f502 (PushPre 0x10f502 5) (callEffect (fun _ => 0x10a2f0) 0x10f507) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x10f507⟩) #v[]
    (.terminate (.call ⟨.l10a2f0, RegMap.args [(0, 0), (3, 3), (4, 60), (5, 5), (6, 56), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ { target := .l10f507, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l10f4ee : List UInt8 :=
  [0x48, 0x89, 0x45, 0x00, 0x4C, 0x8D, 0x7C, 0x24, 0x38, 0x48, 0x8D, 0xB4, 0x24, 0xB0, 0x00, 0x00,
    0x00, 0x4C, 0x89, 0xFF, 0xE8, 0xE9, 0xAD, 0xFF, 0xFF]

theorem code_l10f4ee : ∀ x ∈ codeRange 0x10f4ee bytes_l10f4ee, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf4ee 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f507 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f507 (leaR64Effect 0x10f507 7 (.base 5 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 54) (.exec 0x10f507 (fun s => s.RIP = 0x10f507) (leaR64Effect 0x10f507 7 (.base 5 (.d32 0x118))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x10f50e (movR32Imm32Effect 0x10f50e 5 6 0x101) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x10f50e (fun s => s.RIP = 0x10f50e) (movR32Imm32Effect 0x10f50e 5 6 0x101) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f513 (movR32Imm32Effect 0x10f513 5 1 0x10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x10f513 (fun s => s.RIP = 0x10f513) (movR32Imm32Effect 0x10f513 5 1 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10f518 (movR32Imm32Effect 0x10f518 6 8 0x80) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 60) (.exec 0x10f518 (fun s => s.RIP = 0x10f518) (movR32Imm32Effect 0x10f518 6 8 0x80) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10f51e (movR32Imm32Effect 0x10f51e 6 9 0x5) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 62) (.exec 0x10f51e (fun s => s.RIP = 0x10f51e) (movR32Imm32Effect 0x10f51e 6 9 0x5) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x10f524 (movR64R64Effect 0x10f524 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 64) (.exec 0x10f524 (fun s => s.RIP = 0x10f524) (movR64R64Effect 0x10f524 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 65) (.out 0x10f527 (callEffect (fun _ => 0x1107b0) 0x10f52c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x10f527 (PushPre 0x10f527 5) (callEffect (fun _ => 0x1107b0) 0x10f52c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x10f52c⟩) #v[]
    (.terminate (.call ⟨.l1107b0, RegMap.args [(1, 57), (2, 63), (3, 3), (4, 65), (5, 5), (6, 55), (7, 53), (8, 59), (9, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l10f52c, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l10f507 : List UInt8 :=
  [0x48, 0x8D, 0xBD, 0x18, 0x01, 0x00, 0x00, 0xBE, 0x01, 0x01, 0x00, 0x00, 0xB9, 0x10, 0x00, 0x00,
    0x00, 0x41, 0xB8, 0x80, 0x00, 0x00, 0x00, 0x41, 0xB9, 0x05, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFA,
    0xE8, 0x84, 0x12, 0x00, 0x00]

theorem code_l10f507 : ∀ x ∈ codeRange 0x10f507 bytes_l10f507, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf507 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f52c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f52c (movR64Imm64Effect 0x10f52c 13 0x3ffffffffffffc) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 54) (.exec 0x10f52c (fun s => s.RIP = 0x10f52c) (movR64Imm64Effect 0x10f52c 13 0x3ffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10f536 (movR64Imm64Effect 0x10f536 1 0x3ffffbfffff0bc) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f536 (fun s => s.RIP = 0x10f536) (movR64Imm64Effect 0x10f536 1 0x3ffffbfffff0bc) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f540 (movR64Imm64Effect 0x10f540 15 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 58) (.exec 0x10f540 (fun s => s.RIP = 0x10f540) (movR64Imm64Effect 0x10f540 15 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10f54a (movR64Imm64Effect 0x10f54a 12 0x3fffffffffffc) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 60) (.exec 0x10f54a (fun s => s.RIP = 0x10f54a) (movR64Imm64Effect 0x10f54a 12 0x3fffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10f554 (movR64Imm64Effect 0x10f554 11 0xffffffffffff) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 62) (.exec 0x10f554 (fun s => s.RIP = 0x10f554) (movR64Imm64Effect 0x10f554 11 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.exec 0x10f55e (StorePre 0x10f55e 7 (fun s => AddrMode.addr (.base 5 (.d32 0x110)) s (0x10f55e + BitVec.ofNat 64 7)) 8) (movM64R64Effect 0x10f55e 0 (.base 5 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[0, 5]
    (.letOp (n := 64) (.out 0x10f565 (movR64Imm64Effect 0x10f565 6 0x1000003d1) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 65) (.exec 0x10f565 (fun s => s.RIP = 0x10f565) (movR64Imm64Effect 0x10f565 6 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.out 0x10f56f (testR8R8Effect 0x10f56f 3 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 67) (.exec 0x10f56f (fun s => s.RIP = 0x10f56f) (testR8R8Effect 0x10f56f 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 68) (.pure (condOp 4)) #v[66]
    (.terminate (.condBr (Fin.last 68) ⟨.l10f680, RegMap.args [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (6, 64), (11, 61), (12, 59), (13, 53), (14, 14), (15, 57), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ ⟨.l10f578, RegMap.args [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (6, 64), (11, 61), (12, 59), (13, 53), (14, 14), (15, 57), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l10f52c : List UInt8 :=
  [0x49, 0xBD, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00, 0x48, 0xB9, 0xBC, 0xF0, 0xFF, 0xFF,
    0xFB, 0xFF, 0x3F, 0x00, 0x49, 0xBF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0xBC,
    0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00, 0x49, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x00, 0x00, 0x48, 0x89, 0x85, 0x10, 0x01, 0x00, 0x00, 0x48, 0xBE, 0xD1, 0x03, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x45, 0x84, 0xF6, 0x0F, 0x84, 0x08, 0x01, 0x00, 0x00]

theorem code_l10f52c : ∀ x ∈ codeRange 0x10f52c bytes_l10f52c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf52c 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f578_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x10f61b (movR64M64Effect 0x10f61b 2 (.base 10 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 129) (.exec 0x10f61b (LoadPre 0x10f61b (fun s => AddrMode.addr (.base 10 .none) s (0x10f61b + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10f61b 2 (.base 10 .none)) (Reg.operands [.gpr 10] [])) #v[55]
    (.letOp (n := 130) (.out 0x10f61e (movR64M64Effect 0x10f61e 9 (.base 10 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 131) (.exec 0x10f61e (LoadPre 0x10f61e (fun s => AddrMode.addr (.base 10 (.d8 0x8)) s (0x10f61e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f61e 9 (.base 10 (.d8 0x8))) (Reg.operands [.gpr 10] [])) #v[55]
    (.letOp (n := 132) (.exec 0x10f622 (StorePre 0x10f622 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x10f622 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f622 2 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[128, 4]
    (.letOp (n := 133) (.exec 0x10f62a (StorePre 0x10f62a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x10f62a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f62a 9 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[130, 4]
    (.letOp (n := 134) (.out 0x10f632 (movR64M64Effect 0x10f632 2 (.base 10 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 135) (.exec 0x10f632 (LoadPre 0x10f632 (fun s => AddrMode.addr (.base 10 (.d8 0x10)) s (0x10f632 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f632 2 (.base 10 (.d8 0x10))) (Reg.operands [.gpr 10] [])) #v[55]
    (.letOp (n := 136) (.exec 0x10f636 (StorePre 0x10f636 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x10f636 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f636 2 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[134, 4]
    (.letOp (n := 137) (.out 0x10f63e (movR64M64Effect 0x10f63e 2 (.base 10 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 138) (.exec 0x10f63e (LoadPre 0x10f63e (fun s => AddrMode.addr (.base 10 (.d8 0x18)) s (0x10f63e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f63e 2 (.base 10 (.d8 0x18))) (Reg.operands [.gpr 10] [])) #v[55]
    (.letOp (n := 139) (.exec 0x10f642 (StorePre 0x10f642 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x10f642 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f642 2 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[137, 4]
    (.letOp (n := 140) (.out 0x10f64a (movR64M64Effect 0x10f64a 2 (.base 10 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 141) (.exec 0x10f64a (LoadPre 0x10f64a (fun s => AddrMode.addr (.base 10 (.d8 0x20)) s (0x10f64a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f64a 2 (.base 10 (.d8 0x20))) (Reg.operands [.gpr 10] [])) #v[55]
    (.letOp (n := 142) (.exec 0x10f64e (StorePre 0x10f64e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x10f64e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f64e 2 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[140, 4]
    (.letOp (n := 143) (.exec 0x10f656 (StorePre 0x10f656 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x10f656 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f656 0 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[112, 4]
    (.letOp (n := 144) (.exec 0x10f65e (StorePre 0x10f65e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x10f65e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f65e 1 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[114, 4]
    (.letOp (n := 145) (.exec 0x10f666 (StorePre 0x10f666 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x10f666 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f666 6 (.sib 4 none 0 (.d32 0x1b0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[118, 4]
    (.letOp (n := 146) (.exec 0x10f66e (StorePre 0x10f66e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b8)) s (0x10f66e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f66e 7 (.sib 4 none 0 (.d32 0x1b8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[126, 4]
    (.letOp (n := 147) (.exec 0x10f676 (StorePre 0x10f676 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x10f676 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f676 8 (.sib 4 none 0 (.d32 0x1c0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[124, 4]
    (.terminate (.br ⟨.l10f69e, RegMap.args [(0, 112), (1, 114), (2, 140), (3, 3), (4, 4), (5, 63), (6, 118), (7, 126), (8, 124), (9, 130), (10, 55), (11, 11), (12, 12), (13, 13), (14, 108), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 148⟩)))))))))))))))))))))

def bytes_l10f578_2 : List UInt8 :=
  [0x49, 0x8B, 0x12, 0x4D, 0x8B, 0x4A, 0x08, 0x48, 0x89, 0x94, 0x24, 0x78, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0x8C, 0x24, 0x80, 0x01, 0x00, 0x00, 0x49, 0x8B, 0x52, 0x10, 0x48, 0x89, 0x94, 0x24, 0x88,
    0x01, 0x00, 0x00, 0x49, 0x8B, 0x52, 0x18, 0x48, 0x89, 0x94, 0x24, 0x90, 0x01, 0x00, 0x00, 0x49,
    0x8B, 0x52, 0x20, 0x48, 0x89, 0x94, 0x24, 0x98, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xA0,
    0x01, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xA8, 0x01, 0x00, 0x00, 0x48, 0x89, 0xB4, 0x24, 0xB0,
    0x01, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24, 0xB8, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0xC0,
    0x01, 0x00, 0x00, 0xEB, 0x1E]

theorem code_l10f578_2 : ∀ x ∈ codeRange 0x10f61b bytes_l10f578_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf61b 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f578_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x10f5c0 (subR64M64Effect 0x10f5c0 7 (.base 10 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[91, 55]
    (.letOp (n := 94) (.exec 0x10f5c0 (LoadPre 0x10f5c0 (fun s => AddrMode.addr (.base 10 (.d8 0x40)) s (0x10f5c0 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10f5c0 7 (.base 10 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 10] [])) #v[91, 55]
    (.letOp (n := 95) (.exec 0x10f5c4 (StorePre 0x10f5c4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x10f5c4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f5c4 8 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[77, 4]
    (.letOp (n := 96) (.out 0x10f5cc (movR64M64Effect 0x10f5cc 8 (.base 10 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 97) (.exec 0x10f5cc (LoadPre 0x10f5cc (fun s => AddrMode.addr (.base 10 (.d8 0x68)) s (0x10f5cc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f5cc 8 (.base 10 (.d8 0x68))) (Reg.operands [.gpr 10] [])) #v[55]
    (.letOp (n := 98) (.exec 0x10f5d0 (StorePre 0x10f5d0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x10f5d0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f5d0 8 (.sib 4 none 0 (.d32 0x1e0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[96, 4]
    (.letOp (n := 99) (.out 0x10f5d8 (movR64M64Effect 0x10f5d8 8 (.base 10 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 100) (.exec 0x10f5d8 (LoadPre 0x10f5d8 (fun s => AddrMode.addr (.base 10 (.d8 0x60)) s (0x10f5d8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f5d8 8 (.base 10 (.d8 0x60))) (Reg.operands [.gpr 10] [])) #v[55]
    (.letOp (n := 101) (.exec 0x10f5dc (StorePre 0x10f5dc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x10f5dc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f5dc 8 (.sib 4 none 0 (.d32 0x1d8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[99, 4]
    (.letOp (n := 102) (.out 0x10f5e4 (movR64M64Effect 0x10f5e4 8 (.base 10 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 103) (.exec 0x10f5e4 (LoadPre 0x10f5e4 (fun s => AddrMode.addr (.base 10 (.d8 0x50)) s (0x10f5e4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f5e4 8 (.base 10 (.d8 0x50))) (Reg.operands [.gpr 10] [])) #v[55]
    (.letOp (n := 104) (.out 0x10f5e8 (movR64M64Effect 0x10f5e8 9 (.base 10 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 105) (.exec 0x10f5e8 (LoadPre 0x10f5e8 (fun s => AddrMode.addr (.base 10 (.d8 0x58)) s (0x10f5e8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f5e8 9 (.base 10 (.d8 0x58))) (Reg.operands [.gpr 10] [])) #v[55]
    (.letOp (n := 106) (.exec 0x10f5ec (StorePre 0x10f5ec 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x10f5ec + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f5ec 9 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[104, 4]
    (.letOp (n := 107) (.exec 0x10f5f4 (StorePre 0x10f5f4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x10f5f4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f5f4 8 (.sib 4 none 0 (.d32 0x1c8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[102, 4]
    (.letOp (n := 108) (.out 0x10f5fc (movR64R64Effect 0x10f5fc 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 11] []) (.reg (.gpr 14))) #v[11]
    (.letOp (n := 109) (.exec 0x10f5fc (fun s => s.RIP = 0x10f5fc) (movR64R64Effect 0x10f5fc 14 11) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 110) (.out 0x10f5ff (andR64R64Effect 0x10f5ff 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[57, 11]
    (.letOp (n := 111) (.exec 0x10f5ff (fun s => s.RIP = 0x10f5ff) (andR64R64Effect 0x10f5ff 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[57, 11]
    (.letOp (n := 112) (.out 0x10f602 (andR64R64Effect 0x10f602 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[69, 15]
    (.letOp (n := 113) (.exec 0x10f602 (fun s => s.RIP = 0x10f602) (andR64R64Effect 0x10f602 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[69, 15]
    (.letOp (n := 114) (.out 0x10f605 (andR64R64Effect 0x10f605 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[79, 15]
    (.letOp (n := 115) (.exec 0x10f605 (fun s => s.RIP = 0x10f605) (andR64R64Effect 0x10f605 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[79, 15]
    (.letOp (n := 116) (.out 0x10f608 (addR64R64Effect 0x10f608 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[93, 13]
    (.letOp (n := 117) (.exec 0x10f608 (fun s => s.RIP = 0x10f608) (addR64R64Effect 0x10f608 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[93, 13]
    (.letOp (n := 118) (.out 0x10f60b (andR64R64Effect 0x10f60b 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[87, 15]
    (.letOp (n := 119) (.exec 0x10f60b (fun s => s.RIP = 0x10f60b) (andR64R64Effect 0x10f60b 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[87, 15]
    (.letOp (n := 120) (.out 0x10f60e (movR64R64Effect 0x10f60e 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[116]
    (.letOp (n := 121) (.exec 0x10f60e (fun s => s.RIP = 0x10f60e) (movR64R64Effect 0x10f60e 8 7) (Reg.operands [.gpr 7] [])) #v[116]
    (.letOp (n := 122) (.out 0x10f611 (shrR64Effect 0x10f611 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[120]
    (.letOp (n := 123) (.exec 0x10f611 (fun s => s.RIP = 0x10f611) (shrR64Effect 0x10f611 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[120]
    (.letOp (n := 124) (.out 0x10f615 (addR64R64Effect 0x10f615 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[122, 110]
    (.letOp (n := 125) (.exec 0x10f615 (fun s => s.RIP = 0x10f615) (addR64R64Effect 0x10f615 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[122, 110]
    (.letOp (n := 126) (.out 0x10f618 (andR64R64Effect 0x10f618 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[116, 15]
    (.letOp (n := 127) (.exec 0x10f618 (fun s => s.RIP = 0x10f618) (andR64R64Effect 0x10f618 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[116, 15]
    (b_l10f578_2)))))))))))))))))))))))))))))))))))

def bytes_l10f578_1 : List UInt8 :=
  [0x49, 0x2B, 0x7A, 0x40, 0x4C, 0x89, 0x84, 0x24, 0xE8, 0x01, 0x00, 0x00, 0x4D, 0x8B, 0x42, 0x68,
    0x4C, 0x89, 0x84, 0x24, 0xE0, 0x01, 0x00, 0x00, 0x4D, 0x8B, 0x42, 0x60, 0x4C, 0x89, 0x84, 0x24,
    0xD8, 0x01, 0x00, 0x00, 0x4D, 0x8B, 0x42, 0x50, 0x4D, 0x8B, 0x4A, 0x58, 0x4C, 0x89, 0x8C, 0x24,
    0xD0, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0xC8, 0x01, 0x00, 0x00, 0x4D, 0x89, 0xDE, 0x4C,
    0x21, 0xDA, 0x4C, 0x21, 0xF8, 0x4C, 0x21, 0xF9, 0x4C, 0x01, 0xEF, 0x4C, 0x21, 0xFE, 0x49, 0x89,
    0xF8, 0x49, 0xC1, 0xE8, 0x34, 0x49, 0x01, 0xD0, 0x4C, 0x21, 0xFF] ++ bytes_l10f578_2

theorem code_l10f578_1 : ∀ x ∈ codeRange 0x10f5c0 bytes_l10f578_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xf5c0 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10f578_2

@[cfg_block] def b_l10f578 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f578 (movR64R64Effect 0x10f578 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 54) (.exec 0x10f578 (fun s => s.RIP = 0x10f578) (movR64R64Effect 0x10f578 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x10f57b (movR64M64Effect 0x10f57b 10 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 56) (.exec 0x10f57b (LoadPre 0x10f57b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10f57b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f57b 10 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10f580 (subR64M64Effect 0x10f580 2 (.base 10 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x10f580 (LoadPre 0x10f580 (fun s => AddrMode.addr (.base 10 (.d8 0x48)) s (0x10f580 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10f580 2 (.base 10 (.d8 0x48))) (Reg.operands [.gpr 2, .gpr 10] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x10f584 (movR64R64Effect 0x10f584 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x10f584 (fun s => s.RIP = 0x10f584) (movR64R64Effect 0x10f584 0 2) (Reg.operands [.gpr 2] [])) #v[57]
    (.letOp (n := 61) (.out 0x10f587 (shrR64Effect 0x10f587 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 62) (.exec 0x10f587 (fun s => s.RIP = 0x10f587) (shrR64Effect 0x10f587 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.out 0x10f58b (movR64R64Effect 0x10f58b 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 64) (.exec 0x10f58b (fun s => s.RIP = 0x10f58b) (movR64R64Effect 0x10f58b 5 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x10f58e (imulR64R64Effect 0x10f58e 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[61, 6]
    (.letOp (n := 66) (.exec 0x10f58e (fun s => s.RIP = 0x10f58e) (imulR64R64Effect 0x10f58e 4 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[61, 6]
    (.letOp (n := 67) (.out 0x10f592 (subR64M64Effect 0x10f592 0 (.base 10 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[65, 55]
    (.letOp (n := 68) (.exec 0x10f592 (LoadPre 0x10f592 (fun s => AddrMode.addr (.base 10 (.d8 0x28)) s (0x10f592 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10f592 0 (.base 10 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 10] [])) #v[65, 55]
    (.letOp (n := 69) (.out 0x10f596 (addR64R64Effect 0x10f596 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[67, 1]
    (.letOp (n := 70) (.exec 0x10f596 (fun s => s.RIP = 0x10f596) (addR64R64Effect 0x10f596 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[67, 1]
    (.letOp (n := 71) (.out 0x10f599 (movR64R64Effect 0x10f599 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[69]
    (.letOp (n := 72) (.exec 0x10f599 (fun s => s.RIP = 0x10f599) (movR64R64Effect 0x10f599 1 0) (Reg.operands [.gpr 0] [])) #v[69]
    (.letOp (n := 73) (.out 0x10f59c (shrR64Effect 0x10f59c 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[71]
    (.letOp (n := 74) (.exec 0x10f59c (fun s => s.RIP = 0x10f59c) (shrR64Effect 0x10f59c 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 75) (.out 0x10f5a0 (subR64M64Effect 0x10f5a0 1 (.base 10 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[73, 55]
    (.letOp (n := 76) (.exec 0x10f5a0 (LoadPre 0x10f5a0 (fun s => AddrMode.addr (.base 10 (.d8 0x30)) s (0x10f5a0 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10f5a0 1 (.base 10 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 10] [])) #v[73, 55]
    (.letOp (n := 77) (.out 0x10f5a4 (movR64M64Effect 0x10f5a4 8 (.base 10 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 78) (.exec 0x10f5a4 (LoadPre 0x10f5a4 (fun s => AddrMode.addr (.base 10 (.d8 0x70)) s (0x10f5a4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10f5a4 8 (.base 10 (.d8 0x70))) (Reg.operands [.gpr 10] [])) #v[55]
    (.letOp (n := 79) (.out 0x10f5a8 (addR64R64Effect 0x10f5a8 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[75, 13]
    (.letOp (n := 80) (.exec 0x10f5a8 (fun s => s.RIP = 0x10f5a8) (addR64R64Effect 0x10f5a8 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[75, 13]
    (.letOp (n := 81) (.out 0x10f5ab (movR64R64Effect 0x10f5ab 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[79]
    (.letOp (n := 82) (.exec 0x10f5ab (fun s => s.RIP = 0x10f5ab) (movR64R64Effect 0x10f5ab 6 1) (Reg.operands [.gpr 1] [])) #v[79]
    (.letOp (n := 83) (.out 0x10f5ae (shrR64Effect 0x10f5ae 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[81]
    (.letOp (n := 84) (.exec 0x10f5ae (fun s => s.RIP = 0x10f5ae) (shrR64Effect 0x10f5ae 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.out 0x10f5b2 (subR64M64Effect 0x10f5b2 6 (.base 10 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[83, 55]
    (.letOp (n := 86) (.exec 0x10f5b2 (LoadPre 0x10f5b2 (fun s => AddrMode.addr (.base 10 (.d8 0x38)) s (0x10f5b2 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10f5b2 6 (.base 10 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 10] [])) #v[83, 55]
    (.letOp (n := 87) (.out 0x10f5b6 (addR64R64Effect 0x10f5b6 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[85, 13]
    (.letOp (n := 88) (.exec 0x10f5b6 (fun s => s.RIP = 0x10f5b6) (addR64R64Effect 0x10f5b6 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[85, 13]
    (.letOp (n := 89) (.out 0x10f5b9 (movR64R64Effect 0x10f5b9 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[87]
    (.letOp (n := 90) (.exec 0x10f5b9 (fun s => s.RIP = 0x10f5b9) (movR64R64Effect 0x10f5b9 7 6) (Reg.operands [.gpr 6] [])) #v[87]
    (.letOp (n := 91) (.out 0x10f5bc (shrR64Effect 0x10f5bc 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[89]
    (.letOp (n := 92) (.exec 0x10f5bc (fun s => s.RIP = 0x10f5bc) (shrR64Effect 0x10f5bc 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[89]
    (b_l10f578_1))))))))))))))))))))))))))))))))))))))))

def bytes_l10f578 : List UInt8 :=
  [0x4C, 0x89, 0xE2, 0x4C, 0x8B, 0x54, 0x24, 0x28, 0x49, 0x2B, 0x52, 0x48, 0x48, 0x89, 0xD0, 0x48,
    0xC1, 0xE8, 0x30, 0x48, 0x89, 0xF5, 0x48, 0x0F, 0xAF, 0xC6, 0x49, 0x2B, 0x42, 0x28, 0x48, 0x01,
    0xC8, 0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x34, 0x49, 0x2B, 0x4A, 0x30, 0x4D, 0x8B, 0x42, 0x70,
    0x4C, 0x01, 0xE9, 0x48, 0x89, 0xCE, 0x48, 0xC1, 0xEE, 0x34, 0x49, 0x2B, 0x72, 0x38, 0x4C, 0x01,
    0xEE, 0x48, 0x89, 0xF7, 0x48, 0xC1, 0xEF, 0x34] ++ bytes_l10f578_1

theorem code_l10f578 : ∀ x ∈ codeRange 0x10f578 bytes_l10f578, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xf578 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10f578_1

@[cfg_block] def b_l10f680 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f680 (movR64R64Effect 0x10f680 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 54) (.exec 0x10f680 (fun s => s.RIP = 0x10f680) (movR64R64Effect 0x10f680 5 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x10f683 (movR64R64Effect 0x10f683 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 11] []) (.reg (.gpr 14))) #v[11]
    (.letOp (n := 56) (.exec 0x10f683 (fun s => s.RIP = 0x10f683) (movR64R64Effect 0x10f683 14 11) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 57) (.out 0x10f686 (leaR64Effect 0x10f686 7 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x10f686 (fun s => s.RIP = 0x10f686) (leaR64Effect 0x10f686 7 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10f68e (movR32Imm32Effect 0x10f68e 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x10f68e (fun s => s.RIP = 0x10f68e) (movR32Imm32Effect 0x10f68e 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10f693 (movR64M64Effect 0x10f693 10 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 62) (.exec 0x10f693 (LoadPre 0x10f693 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10f693 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10f693 10 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x10f698 (movR64R64Effect 0x10f698 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 64) (.exec 0x10f698 (fun s => s.RIP = 0x10f698) (movR64R64Effect 0x10f698 6 10) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 65) (.exec 0x10f69b (RepPre 0x10f69b (RepMovsqPre 0x10f69b)) (repMovsqEffect 0x10f69b) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[63, 57, 59, 22]
    (.terminate (.br ⟨.l10f69e, RegMap.args [(3, 3), (4, 4), (5, 53), (10, 61), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l10f680 : List UInt8 :=
  [0x48, 0x89, 0xF5, 0x4D, 0x89, 0xDE, 0x48, 0x8D, 0xBC, 0x24, 0x78, 0x01, 0x00, 0x00, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x4C, 0x8B, 0x54, 0x24, 0x28, 0x4C, 0x89, 0xD6, 0xF3, 0x48, 0xA5]

theorem code_l10f680 : ∀ x ∈ codeRange 0x10f680 bytes_l10f680, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf680 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f69e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f69e (leaR64Effect 0x10f69e 7 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10f69e (fun s => s.RIP = 0x10f69e) (leaR64Effect 0x10f69e 7 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10f6a6 (movR64R64Effect 0x10f6a6 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[10]
    (.letOp (n := 56) (.exec 0x10f6a6 (fun s => s.RIP = 0x10f6a6) (movR64R64Effect 0x10f6a6 6 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 57) (.out 0x10f6a9 (callEffect (fun _ => 0x10e010) 0x10f6ae) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10f6a9 (PushPre 0x10f6a9 5) (callEffect (fun _ => 0x10e010) 0x10f6ae) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x10f6ae⟩) #v[]
    (.terminate (.call ⟨.l10e010, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l10f6ae, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l10f69e : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xD6, 0xE8, 0x62, 0xE9, 0xFF, 0xFF]

theorem code_l10f69e : ∀ x ∈ codeRange 0x10f69e bytes_l10f69e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf69e 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f6ae : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f6ae (cmpM8Imm8Effect 0x10f6ae 5 (.sib 4 none 0 (.d8 0x7)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x10f6ae (LoadPre 0x10f6ae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10f6ae + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x10f6ae 5 (.sib 4 none 0 (.d8 0x7)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10f7fa, RegMap.args [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10f6b9, RegMap.args [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10f6ae : List UInt8 :=
  [0x80, 0x7C, 0x24, 0x07, 0x00, 0x0F, 0x84, 0x41, 0x01, 0x00, 0x00]

theorem code_l10f6ae : ∀ x ∈ codeRange 0x10f6ae bytes_l10f6ae, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf6ae 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f6b9_2 : Block Op Label signature Reg.count 123 :=
  .letOp (n := 123) (.out 0x10f7ba (andR64R64Effect 0x10f7ba 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[105, 15]
    (.letOp (n := 124) (.exec 0x10f7ba (fun s => s.RIP = 0x10f7ba) (andR64R64Effect 0x10f7ba 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[105, 15]
    (.letOp (n := 125) (.out 0x10f7bd (addR64R64Effect 0x10f7bd 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[121, 13]
    (.letOp (n := 126) (.exec 0x10f7bd (fun s => s.RIP = 0x10f7bd) (addR64R64Effect 0x10f7bd 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[121, 13]
    (.letOp (n := 127) (.out 0x10f7c0 (andR64R64Effect 0x10f7c0 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[115, 15]
    (.letOp (n := 128) (.exec 0x10f7c0 (fun s => s.RIP = 0x10f7c0) (andR64R64Effect 0x10f7c0 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[115, 15]
    (.letOp (n := 129) (.out 0x10f7c3 (movR64R64Effect 0x10f7c3 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[125]
    (.letOp (n := 130) (.exec 0x10f7c3 (fun s => s.RIP = 0x10f7c3) (movR64R64Effect 0x10f7c3 7 6) (Reg.operands [.gpr 6] [])) #v[125]
    (.letOp (n := 131) (.out 0x10f7c6 (shrR64Effect 0x10f7c6 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[129]
    (.letOp (n := 132) (.exec 0x10f7c6 (fun s => s.RIP = 0x10f7c6) (shrR64Effect 0x10f7c6 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[129]
    (.letOp (n := 133) (.out 0x10f7ca (addR64R64Effect 0x10f7ca 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[131, 103]
    (.letOp (n := 134) (.exec 0x10f7ca (fun s => s.RIP = 0x10f7ca) (addR64R64Effect 0x10f7ca 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[131, 103]
    (.letOp (n := 135) (.out 0x10f7cd (andR64R64Effect 0x10f7cd 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[125, 15]
    (.letOp (n := 136) (.exec 0x10f7cd (fun s => s.RIP = 0x10f7cd) (andR64R64Effect 0x10f7cd 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[125, 15]
    (.letOp (n := 137) (.exec 0x10f7d0 (StorePre 0x10f7d0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x218)) s (0x10f7d0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f7d0 0 (.sib 4 none 0 (.d32 0x218))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[107, 4]
    (.letOp (n := 138) (.exec 0x10f7d8 (StorePre 0x10f7d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x220)) s (0x10f7d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f7d8 1 (.sib 4 none 0 (.d32 0x220))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[123, 4]
    (.letOp (n := 139) (.exec 0x10f7e0 (StorePre 0x10f7e0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x10f7e0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f7e0 2 (.sib 4 none 0 (.d32 0x228))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[127, 4]
    (.letOp (n := 140) (.exec 0x10f7e8 (StorePre 0x10f7e8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x230)) s (0x10f7e8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f7e8 6 (.sib 4 none 0 (.d32 0x230))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[135, 4]
    (.letOp (n := 141) (.exec 0x10f7f0 (StorePre 0x10f7f0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x238)) s (0x10f7f0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f7f0 7 (.sib 4 none 0 (.d32 0x238))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[133, 4]
    (.terminate (.br ⟨.l10f812, RegMap.args [(0, 107), (1, 123), (2, 127), (3, 3), (4, 4), (5, 5), (6, 135), (7, 133), (12, 103), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 142⟩))))))))))))))))))))

def bytes_l10f6b9_2 : List UInt8 :=
  [0x4C, 0x21, 0xF9, 0x4C, 0x01, 0xEE, 0x4C, 0x21, 0xFA, 0x48, 0x89, 0xF7, 0x48, 0xC1, 0xEF, 0x34,
    0x4C, 0x01, 0xE7, 0x4C, 0x21, 0xFE, 0x48, 0x89, 0x84, 0x24, 0x18, 0x02, 0x00, 0x00, 0x48, 0x89,
    0x8C, 0x24, 0x20, 0x02, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0x28, 0x02, 0x00, 0x00, 0x48, 0x89,
    0xB4, 0x24, 0x30, 0x02, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24, 0x38, 0x02, 0x00, 0x00, 0xEB, 0x18]

theorem code_l10f6b9_2 : ∀ x ∈ codeRange 0x10f7ba bytes_l10f6b9_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf7ba 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f6b9_1 : Block Op Label signature Reg.count 83 :=
  .letOp (n := 83) (.out 0x10f759 (subR64M64Effect 0x10f759 12 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[12, 4]
    (.letOp (n := 84) (.exec 0x10f759 (LoadPre 0x10f759 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x10f759 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x10f759 12 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 85) (.out 0x10f761 (movR64R64Effect 0x10f761 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[83]
    (.letOp (n := 86) (.exec 0x10f761 (fun s => s.RIP = 0x10f761) (movR64R64Effect 0x10f761 0 12) (Reg.operands [.gpr 12] [])) #v[83]
    (.letOp (n := 87) (.out 0x10f764 (shrR64Effect 0x10f764 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[85]
    (.letOp (n := 88) (.exec 0x10f764 (fun s => s.RIP = 0x10f764) (shrR64Effect 0x10f764 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[85]
    (.letOp (n := 89) (.out 0x10f768 (imulR64R64Effect 0x10f768 4 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[87, 5]
    (.letOp (n := 90) (.exec 0x10f768 (fun s => s.RIP = 0x10f768) (imulR64R64Effect 0x10f768 4 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[87, 5]
    (.letOp (n := 91) (.out 0x10f76c (subR64M64Effect 0x10f76c 0 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[89, 4]
    (.letOp (n := 92) (.exec 0x10f76c (LoadPre 0x10f76c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10f76c + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x10f76c 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 93) (.out 0x10f774 (movR64Imm64Effect 0x10f774 1 0x3ffffbfffff0bc) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 94) (.exec 0x10f774 (fun s => s.RIP = 0x10f774) (movR64Imm64Effect 0x10f774 1 0x3ffffbfffff0bc) (Reg.operands [] [])) #v[]
    (.letOp (n := 95) (.out 0x10f77e (addR64R64Effect 0x10f77e 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[91, 93]
    (.letOp (n := 96) (.exec 0x10f77e (fun s => s.RIP = 0x10f77e) (addR64R64Effect 0x10f77e 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[91, 93]
    (.letOp (n := 97) (.out 0x10f781 (movR64R64Effect 0x10f781 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 98) (.exec 0x10f781 (fun s => s.RIP = 0x10f781) (movR64R64Effect 0x10f781 1 0) (Reg.operands [.gpr 0] [])) #v[95]
    (.letOp (n := 99) (.out 0x10f784 (shrR64Effect 0x10f784 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[97]
    (.letOp (n := 100) (.exec 0x10f784 (fun s => s.RIP = 0x10f784) (shrR64Effect 0x10f784 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[97]
    (.letOp (n := 101) (.out 0x10f788 (subR64M64Effect 0x10f788 1 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[99, 4]
    (.letOp (n := 102) (.exec 0x10f788 (LoadPre 0x10f788 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10f788 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x10f788 1 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[99, 4]
    (.letOp (n := 103) (.out 0x10f790 (andR64R64Effect 0x10f790 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 14] []) (.reg (.gpr 12))) #v[83, 14]
    (.letOp (n := 104) (.exec 0x10f790 (fun s => s.RIP = 0x10f790) (andR64R64Effect 0x10f790 12 14) (Reg.operands [.gpr 12, .gpr 14] [])) #v[83, 14]
    (.letOp (n := 105) (.out 0x10f793 (addR64R64Effect 0x10f793 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[101, 13]
    (.letOp (n := 106) (.exec 0x10f793 (fun s => s.RIP = 0x10f793) (addR64R64Effect 0x10f793 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[101, 13]
    (.letOp (n := 107) (.out 0x10f796 (andR64R64Effect 0x10f796 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[95, 15]
    (.letOp (n := 108) (.exec 0x10f796 (fun s => s.RIP = 0x10f796) (andR64R64Effect 0x10f796 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[95, 15]
    (.letOp (n := 109) (.out 0x10f799 (movR64R64Effect 0x10f799 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[105]
    (.letOp (n := 110) (.exec 0x10f799 (fun s => s.RIP = 0x10f799) (movR64R64Effect 0x10f799 2 1) (Reg.operands [.gpr 1] [])) #v[105]
    (.letOp (n := 111) (.out 0x10f79c (shrR64Effect 0x10f79c 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[109]
    (.letOp (n := 112) (.exec 0x10f79c (fun s => s.RIP = 0x10f79c) (shrR64Effect 0x10f79c 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[109]
    (.letOp (n := 113) (.out 0x10f7a0 (subR64M64Effect 0x10f7a0 2 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[111, 4]
    (.letOp (n := 114) (.exec 0x10f7a0 (LoadPre 0x10f7a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10f7a0 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x10f7a0 2 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[111, 4]
    (.letOp (n := 115) (.out 0x10f7a8 (addR64R64Effect 0x10f7a8 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[113, 13]
    (.letOp (n := 116) (.exec 0x10f7a8 (fun s => s.RIP = 0x10f7a8) (addR64R64Effect 0x10f7a8 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[113, 13]
    (.letOp (n := 117) (.out 0x10f7ab (movR64R64Effect 0x10f7ab 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[115]
    (.letOp (n := 118) (.exec 0x10f7ab (fun s => s.RIP = 0x10f7ab) (movR64R64Effect 0x10f7ab 6 2) (Reg.operands [.gpr 2] [])) #v[115]
    (.letOp (n := 119) (.out 0x10f7ae (shrR64Effect 0x10f7ae 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[117]
    (.letOp (n := 120) (.exec 0x10f7ae (fun s => s.RIP = 0x10f7ae) (shrR64Effect 0x10f7ae 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[117]
    (.letOp (n := 121) (.out 0x10f7b2 (subR64M64Effect 0x10f7b2 6 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[119, 4]
    (.letOp (n := 122) (.exec 0x10f7b2 (LoadPre 0x10f7b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10f7b2 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x10f7b2 6 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[119, 4]
    (b_l10f6b9_2))))))))))))))))))))))))))))))))))))))))

def bytes_l10f6b9_1 : List UInt8 :=
  [0x4C, 0x2B, 0xA4, 0x24, 0x48, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x48, 0xC1, 0xE8, 0x30, 0x48,
    0x0F, 0xAF, 0xC5, 0x48, 0x2B, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0xB9, 0xBC, 0xF0, 0xFF,
    0xFF, 0xFB, 0xFF, 0x3F, 0x00, 0x48, 0x01, 0xC8, 0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x34, 0x48,
    0x2B, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00, 0x4D, 0x21, 0xF4, 0x4C, 0x01, 0xE9, 0x4C, 0x21, 0xF8,
    0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x34, 0x48, 0x2B, 0x94, 0x24, 0x38, 0x01, 0x00, 0x00, 0x4C,
    0x01, 0xEA, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xEE, 0x34, 0x48, 0x2B, 0xB4, 0x24, 0x40, 0x01, 0x00,
    0x00] ++ bytes_l10f6b9_2

theorem code_l10f6b9_1 : ∀ x ∈ codeRange 0x10f759 bytes_l10f6b9_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xf759 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10f6b9_2

@[cfg_block] def b_l10f6b9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f6b9 (movR64M64Effect 0x10f6b9 0 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10f6b9 (LoadPre 0x10f6b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10f6b9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f6b9 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10f6c1 (StorePre 0x10f6c1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x210)) s (0x10f6c1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f6c1 0 (.sib 4 none 0 (.d32 0x210))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10f6c9 (movR64M64Effect 0x10f6c9 0 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x10f6c9 (LoadPre 0x10f6c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10f6c9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f6c9 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10f6d1 (StorePre 0x10f6d1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x208)) s (0x10f6d1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f6d1 0 (.sib 4 none 0 (.d32 0x208))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x10f6d9 (movR64M64Effect 0x10f6d9 0 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x10f6d9 (LoadPre 0x10f6d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10f6d9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f6d9 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x10f6e1 (StorePre 0x10f6e1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x200)) s (0x10f6e1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f6e1 0 (.sib 4 none 0 (.d32 0x200))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x10f6e9 (movR64M64Effect 0x10f6e9 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x10f6e9 (LoadPre 0x10f6e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10f6e9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f6e9 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x10f6f1 (movR64M64Effect 0x10f6f1 1 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x10f6f1 (LoadPre 0x10f6f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10f6f1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f6f1 1 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x10f6f9 (StorePre 0x10f6f9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f8)) s (0x10f6f9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f6f9 1 (.sib 4 none 0 (.d32 0x1f8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x10f701 (StorePre 0x10f701 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f0)) s (0x10f701 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f701 0 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x10f709 (movR64M64Effect 0x10f709 0 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x10f709 (LoadPre 0x10f709 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10f709 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f709 0 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x10f711 (StorePre 0x10f711 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x240)) s (0x10f711 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f711 0 (.sib 4 none 0 (.d32 0x240))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x10f719 (movR64M64Effect 0x10f719 0 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x10f719 (LoadPre 0x10f719 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10f719 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f719 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x10f721 (StorePre 0x10f721 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x248)) s (0x10f721 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f721 0 (.sib 4 none 0 (.d32 0x248))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x10f729 (movR64M64Effect 0x10f729 0 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 75) (.exec 0x10f729 (LoadPre 0x10f729 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x10f729 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f729 0 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x10f731 (StorePre 0x10f731 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x250)) s (0x10f731 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f731 0 (.sib 4 none 0 (.d32 0x250))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x10f739 (movR64M64Effect 0x10f739 0 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 78) (.exec 0x10f739 (LoadPre 0x10f739 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10f739 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f739 0 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x10f741 (StorePre 0x10f741 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x258)) s (0x10f741 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f741 0 (.sib 4 none 0 (.d32 0x258))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[77, 4]
    (.letOp (n := 80) (.out 0x10f749 (movR64M64Effect 0x10f749 0 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 81) (.exec 0x10f749 (LoadPre 0x10f749 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x10f749 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10f749 0 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x10f751 (StorePre 0x10f751 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x260)) s (0x10f751 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10f751 0 (.sib 4 none 0 (.d32 0x260))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 4]
    (b_l10f6b9_1))))))))))))))))))))))))))))))

def bytes_l10f6b9 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x10, 0x02, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x08, 0x02, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x00, 0x02, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x8C, 0x24, 0xF8, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xF0, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x40, 0x02, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x48, 0x02, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x50, 0x02, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x58, 0x02, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x60, 0x02, 0x00, 0x00] ++ bytes_l10f6b9_1

theorem code_l10f6b9 : ∀ x ∈ codeRange 0x10f6b9 bytes_l10f6b9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xf6b9 160 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10f6b9_1

@[cfg_block] def b_l10f7fa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f7fa (leaR64Effect 0x10f7fa 7 (.sib 4 none 0 (.d32 0x1f0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10f7fa (fun s => s.RIP = 0x10f7fa) (leaR64Effect 0x10f7fa 7 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10f802 (leaR64Effect 0x10f802 6 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x10f802 (fun s => s.RIP = 0x10f802) (leaR64Effect 0x10f802 6 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10f80a (movR32Imm32Effect 0x10f80a 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x10f80a (fun s => s.RIP = 0x10f80a) (movR32Imm32Effect 0x10f80a 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x10f80f (RepPre 0x10f80f (RepMovsqPre 0x10f80f)) (repMovsqEffect 0x10f80f) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[55, 53, 57, 22]
    (.terminate (.br ⟨.l10f812, RegMap.args [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l10f7fa : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xF0, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x00, 0x01, 0x00, 0x00,
    0xB9, 0x0F, 0x00, 0x00, 0x00, 0xF3, 0x48, 0xA5]

theorem code_l10f7fa : ∀ x ∈ codeRange 0x10f7fa bytes_l10f7fa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf7fa 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f812 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f812 (leaR64Effect 0x10f812 15 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x10f812 (fun s => s.RIP = 0x10f812) (leaR64Effect 0x10f812 15 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10f817 (leaR64Effect 0x10f817 14 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 56) (.exec 0x10f817 (fun s => s.RIP = 0x10f817) (leaR64Effect 0x10f817 14 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10f81f (movR64R64Effect 0x10f81f 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x10f81f (fun s => s.RIP = 0x10f81f) (movR64R64Effect 0x10f81f 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 59) (.out 0x10f822 (movR64R64Effect 0x10f822 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 60) (.exec 0x10f822 (fun s => s.RIP = 0x10f822) (movR64R64Effect 0x10f822 6 14) (Reg.operands [.gpr 14] [])) #v[55]
    (.letOp (n := 61) (.out 0x10f825 (callEffect (fun _ => 0x110cd0) 0x10f82a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x10f825 (PushPre 0x10f825 5) (callEffect (fun _ => 0x110cd0) 0x10f82a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10f82a⟩) #v[]
    (.terminate (.call ⟨.l110cd0, RegMap.args [(3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 55), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10f82a, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10f812 : List UInt8 :=
  [0x4C, 0x8D, 0x7C, 0x24, 0x38, 0x4C, 0x8D, 0xB4, 0x24, 0x78, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xFF,
    0x4C, 0x89, 0xF6, 0xE8, 0xA6, 0x14, 0x00, 0x00]

theorem code_l10f812 : ∀ x ∈ codeRange 0x10f812 bytes_l10f812, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf812 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f82a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f82a (movR32Imm32Effect 0x10f82a 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x10f82a (fun s => s.RIP = 0x10f82a) (movR32Imm32Effect 0x10f82a 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10f82f (movR64R64Effect 0x10f82f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 56) (.exec 0x10f82f (fun s => s.RIP = 0x10f82f) (movR64R64Effect 0x10f82f 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x10f832 (movR64R64Effect 0x10f832 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f832 (fun s => s.RIP = 0x10f832) (movR64R64Effect 0x10f832 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f835 (RepPre 0x10f835 (RepMovsqPre 0x10f835)) (repMovsqEffect 0x10f835) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x10f838 (movR64R64Effect 0x10f838 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f838 (fun s => s.RIP = 0x10f838) (movR64R64Effect 0x10f838 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f83b (movR64R64Effect 0x10f83b 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f83b (fun s => s.RIP = 0x10f83b) (movR64R64Effect 0x10f83b 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f83e (callEffect (fun _ => 0x10a410) 0x10f843) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f83e (PushPre 0x10f83e 5) (callEffect (fun _ => 0x10a410) 0x10f843) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f843⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f843, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f82a : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xF3, 0x48, 0xA5, 0x4C, 0x89,
    0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0xCD, 0xAB, 0xFF, 0xFF]

theorem code_l10f82a : ∀ x ∈ codeRange 0x10f82a bytes_l10f82a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf82a 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f843 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f843 (leaR64Effect 0x10f843 7 (.base 3 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f843 (fun s => s.RIP = 0x10f843) (leaR64Effect 0x10f843 7 (.base 3 (.d8 0x78))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f847 (movR32Imm32Effect 0x10f847 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f847 (fun s => s.RIP = 0x10f847) (movR32Imm32Effect 0x10f847 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f84c (movR64R64Effect 0x10f84c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f84c (fun s => s.RIP = 0x10f84c) (movR64R64Effect 0x10f84c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f84f (RepPre 0x10f84f (RepMovsqPre 0x10f84f)) (repMovsqEffect 0x10f84f) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f852 (movR64R64Effect 0x10f852 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f852 (fun s => s.RIP = 0x10f852) (movR64R64Effect 0x10f852 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f855 (movR64R64Effect 0x10f855 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f855 (fun s => s.RIP = 0x10f855) (movR64R64Effect 0x10f855 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f858 (callEffect (fun _ => 0x10a410) 0x10f85d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f858 (PushPre 0x10f858 5) (callEffect (fun _ => 0x10a410) 0x10f85d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f85d⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f85d, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f843 : List UInt8 :=
  [0x48, 0x8D, 0x7B, 0x78, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3, 0x48, 0xA5, 0x4C,
    0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0xB3, 0xAB, 0xFF, 0xFF]

theorem code_l10f843 : ∀ x ∈ codeRange 0x10f843 bytes_l10f843, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf843 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f85d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f85d (leaR64Effect 0x10f85d 7 (.base 3 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f85d (fun s => s.RIP = 0x10f85d) (leaR64Effect 0x10f85d 7 (.base 3 (.d32 0xf0))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f864 (movR32Imm32Effect 0x10f864 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f864 (fun s => s.RIP = 0x10f864) (movR32Imm32Effect 0x10f864 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f869 (movR64R64Effect 0x10f869 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f869 (fun s => s.RIP = 0x10f869) (movR64R64Effect 0x10f869 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f86c (RepPre 0x10f86c (RepMovsqPre 0x10f86c)) (repMovsqEffect 0x10f86c) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f86f (movR64R64Effect 0x10f86f 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f86f (fun s => s.RIP = 0x10f86f) (movR64R64Effect 0x10f86f 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f872 (movR64R64Effect 0x10f872 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f872 (fun s => s.RIP = 0x10f872) (movR64R64Effect 0x10f872 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f875 (callEffect (fun _ => 0x10a410) 0x10f87a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f875 (PushPre 0x10f875 5) (callEffect (fun _ => 0x10a410) 0x10f87a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f87a⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f87a, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f85d : List UInt8 :=
  [0x48, 0x8D, 0xBB, 0xF0, 0x00, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3,
    0x48, 0xA5, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0x96, 0xAB, 0xFF, 0xFF]

theorem code_l10f85d : ∀ x ∈ codeRange 0x10f85d bytes_l10f85d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf85d 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f87a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f87a (leaR64Effect 0x10f87a 7 (.base 3 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f87a (fun s => s.RIP = 0x10f87a) (leaR64Effect 0x10f87a 7 (.base 3 (.d32 0x168))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f881 (movR32Imm32Effect 0x10f881 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f881 (fun s => s.RIP = 0x10f881) (movR32Imm32Effect 0x10f881 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f886 (movR64R64Effect 0x10f886 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f886 (fun s => s.RIP = 0x10f886) (movR64R64Effect 0x10f886 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f889 (RepPre 0x10f889 (RepMovsqPre 0x10f889)) (repMovsqEffect 0x10f889) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f88c (movR64R64Effect 0x10f88c 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f88c (fun s => s.RIP = 0x10f88c) (movR64R64Effect 0x10f88c 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f88f (movR64R64Effect 0x10f88f 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f88f (fun s => s.RIP = 0x10f88f) (movR64R64Effect 0x10f88f 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f892 (callEffect (fun _ => 0x10a410) 0x10f897) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f892 (PushPre 0x10f892 5) (callEffect (fun _ => 0x10a410) 0x10f897) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f897⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f897, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f87a : List UInt8 :=
  [0x48, 0x8D, 0xBB, 0x68, 0x01, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3,
    0x48, 0xA5, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0x79, 0xAB, 0xFF, 0xFF]

theorem code_l10f87a : ∀ x ∈ codeRange 0x10f87a bytes_l10f87a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf87a 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f897 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f897 (leaR64Effect 0x10f897 7 (.base 3 (.d32 0x1e0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f897 (fun s => s.RIP = 0x10f897) (leaR64Effect 0x10f897 7 (.base 3 (.d32 0x1e0))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f89e (movR32Imm32Effect 0x10f89e 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f89e (fun s => s.RIP = 0x10f89e) (movR32Imm32Effect 0x10f89e 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f8a3 (movR64R64Effect 0x10f8a3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f8a3 (fun s => s.RIP = 0x10f8a3) (movR64R64Effect 0x10f8a3 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f8a6 (RepPre 0x10f8a6 (RepMovsqPre 0x10f8a6)) (repMovsqEffect 0x10f8a6) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f8a9 (movR64R64Effect 0x10f8a9 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f8a9 (fun s => s.RIP = 0x10f8a9) (movR64R64Effect 0x10f8a9 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f8ac (movR64R64Effect 0x10f8ac 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f8ac (fun s => s.RIP = 0x10f8ac) (movR64R64Effect 0x10f8ac 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f8af (callEffect (fun _ => 0x10a410) 0x10f8b4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f8af (PushPre 0x10f8af 5) (callEffect (fun _ => 0x10a410) 0x10f8b4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f8b4⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f8b4, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f897 : List UInt8 :=
  [0x48, 0x8D, 0xBB, 0xE0, 0x01, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3,
    0x48, 0xA5, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0x5C, 0xAB, 0xFF, 0xFF]

theorem code_l10f897 : ∀ x ∈ codeRange 0x10f897 bytes_l10f897, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf897 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f8b4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f8b4 (leaR64Effect 0x10f8b4 7 (.base 3 (.d32 0x258))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f8b4 (fun s => s.RIP = 0x10f8b4) (leaR64Effect 0x10f8b4 7 (.base 3 (.d32 0x258))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f8bb (movR32Imm32Effect 0x10f8bb 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f8bb (fun s => s.RIP = 0x10f8bb) (movR32Imm32Effect 0x10f8bb 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f8c0 (movR64R64Effect 0x10f8c0 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f8c0 (fun s => s.RIP = 0x10f8c0) (movR64R64Effect 0x10f8c0 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f8c3 (RepPre 0x10f8c3 (RepMovsqPre 0x10f8c3)) (repMovsqEffect 0x10f8c3) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f8c6 (movR64R64Effect 0x10f8c6 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f8c6 (fun s => s.RIP = 0x10f8c6) (movR64R64Effect 0x10f8c6 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f8c9 (movR64R64Effect 0x10f8c9 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f8c9 (fun s => s.RIP = 0x10f8c9) (movR64R64Effect 0x10f8c9 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f8cc (callEffect (fun _ => 0x10a410) 0x10f8d1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f8cc (PushPre 0x10f8cc 5) (callEffect (fun _ => 0x10a410) 0x10f8d1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f8d1⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f8d1, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f8b4 : List UInt8 :=
  [0x48, 0x8D, 0xBB, 0x58, 0x02, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3,
    0x48, 0xA5, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0x3F, 0xAB, 0xFF, 0xFF]

theorem code_l10f8b4 : ∀ x ∈ codeRange 0x10f8b4 bytes_l10f8b4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf8b4 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f8d1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f8d1 (leaR64Effect 0x10f8d1 7 (.base 3 (.d32 0x2d0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f8d1 (fun s => s.RIP = 0x10f8d1) (leaR64Effect 0x10f8d1 7 (.base 3 (.d32 0x2d0))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f8d8 (movR32Imm32Effect 0x10f8d8 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f8d8 (fun s => s.RIP = 0x10f8d8) (movR32Imm32Effect 0x10f8d8 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f8dd (movR64R64Effect 0x10f8dd 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f8dd (fun s => s.RIP = 0x10f8dd) (movR64R64Effect 0x10f8dd 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f8e0 (RepPre 0x10f8e0 (RepMovsqPre 0x10f8e0)) (repMovsqEffect 0x10f8e0) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f8e3 (movR64R64Effect 0x10f8e3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f8e3 (fun s => s.RIP = 0x10f8e3) (movR64R64Effect 0x10f8e3 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f8e6 (movR64R64Effect 0x10f8e6 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f8e6 (fun s => s.RIP = 0x10f8e6) (movR64R64Effect 0x10f8e6 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f8e9 (callEffect (fun _ => 0x10a410) 0x10f8ee) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f8e9 (PushPre 0x10f8e9 5) (callEffect (fun _ => 0x10a410) 0x10f8ee) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f8ee⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f8ee, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f8d1 : List UInt8 :=
  [0x48, 0x8D, 0xBB, 0xD0, 0x02, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3,
    0x48, 0xA5, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0x22, 0xAB, 0xFF, 0xFF]

theorem code_l10f8d1 : ∀ x ∈ codeRange 0x10f8d1 bytes_l10f8d1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf8d1 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f8ee : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f8ee (leaR64Effect 0x10f8ee 7 (.base 3 (.d32 0x348))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f8ee (fun s => s.RIP = 0x10f8ee) (leaR64Effect 0x10f8ee 7 (.base 3 (.d32 0x348))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f8f5 (movR32Imm32Effect 0x10f8f5 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f8f5 (fun s => s.RIP = 0x10f8f5) (movR32Imm32Effect 0x10f8f5 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f8fa (movR64R64Effect 0x10f8fa 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f8fa (fun s => s.RIP = 0x10f8fa) (movR64R64Effect 0x10f8fa 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f8fd (RepPre 0x10f8fd (RepMovsqPre 0x10f8fd)) (repMovsqEffect 0x10f8fd) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f900 (leaR64Effect 0x10f900 15 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 61) (.exec 0x10f900 (fun s => s.RIP = 0x10f900) (leaR64Effect 0x10f900 15 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x10f905 (leaR64Effect 0x10f905 14 (.sib 4 none 0 (.d32 0x1f0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 63) (.exec 0x10f905 (fun s => s.RIP = 0x10f905) (leaR64Effect 0x10f905 14 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x10f90d (movR64R64Effect 0x10f90d 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[60]
    (.letOp (n := 65) (.exec 0x10f90d (fun s => s.RIP = 0x10f90d) (movR64R64Effect 0x10f90d 7 15) (Reg.operands [.gpr 15] [])) #v[60]
    (.letOp (n := 66) (.out 0x10f910 (movR64R64Effect 0x10f910 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[62]
    (.letOp (n := 67) (.exec 0x10f910 (fun s => s.RIP = 0x10f910) (movR64R64Effect 0x10f910 6 14) (Reg.operands [.gpr 14] [])) #v[62]
    (.letOp (n := 68) (.out 0x10f913 (callEffect (fun _ => 0x110cd0) 0x10f918) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 69) (.exec 0x10f913 (PushPre 0x10f913 5) (callEffect (fun _ => 0x110cd0) 0x10f918) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.const ⟨64, 0x10f918⟩) #v[]
    (.terminate (.call ⟨.l110cd0, RegMap.args [(3, 3), (4, 68), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 62), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l10f918, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l10f8ee : List UInt8 :=
  [0x48, 0x8D, 0xBB, 0x48, 0x03, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3,
    0x48, 0xA5, 0x4C, 0x8D, 0x7C, 0x24, 0x38, 0x4C, 0x8D, 0xB4, 0x24, 0xF0, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0xFF, 0x4C, 0x89, 0xF6, 0xE8, 0xB8, 0x13, 0x00, 0x00]

theorem code_l10f8ee : ∀ x ∈ codeRange 0x10f8ee bytes_l10f8ee, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf8ee 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f918 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f918 (leaR64Effect 0x10f918 7 (.base 3 (.d32 0x3c0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f918 (fun s => s.RIP = 0x10f918) (leaR64Effect 0x10f918 7 (.base 3 (.d32 0x3c0))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f91f (movR32Imm32Effect 0x10f91f 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f91f (fun s => s.RIP = 0x10f91f) (movR32Imm32Effect 0x10f91f 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f924 (movR64R64Effect 0x10f924 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f924 (fun s => s.RIP = 0x10f924) (movR64R64Effect 0x10f924 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f927 (RepPre 0x10f927 (RepMovsqPre 0x10f927)) (repMovsqEffect 0x10f927) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f92a (movR64R64Effect 0x10f92a 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f92a (fun s => s.RIP = 0x10f92a) (movR64R64Effect 0x10f92a 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f92d (movR64R64Effect 0x10f92d 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f92d (fun s => s.RIP = 0x10f92d) (movR64R64Effect 0x10f92d 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f930 (callEffect (fun _ => 0x10a410) 0x10f935) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f930 (PushPre 0x10f930 5) (callEffect (fun _ => 0x10a410) 0x10f935) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f935⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f935, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f918 : List UInt8 :=
  [0x48, 0x8D, 0xBB, 0xC0, 0x03, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3,
    0x48, 0xA5, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0xDB, 0xAA, 0xFF, 0xFF]

theorem code_l10f918 : ∀ x ∈ codeRange 0x10f918 bytes_l10f918, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf918 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f935 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f935 (leaR64Effect 0x10f935 7 (.base 3 (.d32 0x438))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f935 (fun s => s.RIP = 0x10f935) (leaR64Effect 0x10f935 7 (.base 3 (.d32 0x438))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f93c (movR32Imm32Effect 0x10f93c 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f93c (fun s => s.RIP = 0x10f93c) (movR32Imm32Effect 0x10f93c 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f941 (movR64R64Effect 0x10f941 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f941 (fun s => s.RIP = 0x10f941) (movR64R64Effect 0x10f941 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f944 (RepPre 0x10f944 (RepMovsqPre 0x10f944)) (repMovsqEffect 0x10f944) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f947 (movR64R64Effect 0x10f947 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f947 (fun s => s.RIP = 0x10f947) (movR64R64Effect 0x10f947 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f94a (movR64R64Effect 0x10f94a 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f94a (fun s => s.RIP = 0x10f94a) (movR64R64Effect 0x10f94a 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f94d (callEffect (fun _ => 0x10a410) 0x10f952) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f94d (PushPre 0x10f94d 5) (callEffect (fun _ => 0x10a410) 0x10f952) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f952⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f952, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f935 : List UInt8 :=
  [0x48, 0x8D, 0xBB, 0x38, 0x04, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3,
    0x48, 0xA5, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0xBE, 0xAA, 0xFF, 0xFF]

theorem code_l10f935 : ∀ x ∈ codeRange 0x10f935 bytes_l10f935, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf935 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f952 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f952 (leaR64Effect 0x10f952 7 (.base 3 (.d32 0x4b0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f952 (fun s => s.RIP = 0x10f952) (leaR64Effect 0x10f952 7 (.base 3 (.d32 0x4b0))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f959 (movR32Imm32Effect 0x10f959 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f959 (fun s => s.RIP = 0x10f959) (movR32Imm32Effect 0x10f959 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f95e (movR64R64Effect 0x10f95e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f95e (fun s => s.RIP = 0x10f95e) (movR64R64Effect 0x10f95e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f961 (RepPre 0x10f961 (RepMovsqPre 0x10f961)) (repMovsqEffect 0x10f961) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f964 (movR64R64Effect 0x10f964 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f964 (fun s => s.RIP = 0x10f964) (movR64R64Effect 0x10f964 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f967 (movR64R64Effect 0x10f967 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f967 (fun s => s.RIP = 0x10f967) (movR64R64Effect 0x10f967 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f96a (callEffect (fun _ => 0x10a410) 0x10f96f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f96a (PushPre 0x10f96a 5) (callEffect (fun _ => 0x10a410) 0x10f96f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f96f⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f96f, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f952 : List UInt8 :=
  [0x48, 0x8D, 0xBB, 0xB0, 0x04, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3,
    0x48, 0xA5, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0xA1, 0xAA, 0xFF, 0xFF]

theorem code_l10f952 : ∀ x ∈ codeRange 0x10f952 bytes_l10f952, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf952 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f96f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f96f (leaR64Effect 0x10f96f 7 (.base 3 (.d32 0x528))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f96f (fun s => s.RIP = 0x10f96f) (leaR64Effect 0x10f96f 7 (.base 3 (.d32 0x528))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f976 (movR32Imm32Effect 0x10f976 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f976 (fun s => s.RIP = 0x10f976) (movR32Imm32Effect 0x10f976 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f97b (movR64R64Effect 0x10f97b 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f97b (fun s => s.RIP = 0x10f97b) (movR64R64Effect 0x10f97b 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f97e (RepPre 0x10f97e (RepMovsqPre 0x10f97e)) (repMovsqEffect 0x10f97e) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f981 (movR64R64Effect 0x10f981 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f981 (fun s => s.RIP = 0x10f981) (movR64R64Effect 0x10f981 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f984 (movR64R64Effect 0x10f984 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f984 (fun s => s.RIP = 0x10f984) (movR64R64Effect 0x10f984 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f987 (callEffect (fun _ => 0x10a410) 0x10f98c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f987 (PushPre 0x10f987 5) (callEffect (fun _ => 0x10a410) 0x10f98c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f98c⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f98c, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f96f : List UInt8 :=
  [0x48, 0x8D, 0xBB, 0x28, 0x05, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3,
    0x48, 0xA5, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0x84, 0xAA, 0xFF, 0xFF]

theorem code_l10f96f : ∀ x ∈ codeRange 0x10f96f bytes_l10f96f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf96f 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f98c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f98c (leaR64Effect 0x10f98c 7 (.base 3 (.d32 0x5a0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f98c (fun s => s.RIP = 0x10f98c) (leaR64Effect 0x10f98c 7 (.base 3 (.d32 0x5a0))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f993 (movR32Imm32Effect 0x10f993 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f993 (fun s => s.RIP = 0x10f993) (movR32Imm32Effect 0x10f993 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f998 (movR64R64Effect 0x10f998 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f998 (fun s => s.RIP = 0x10f998) (movR64R64Effect 0x10f998 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f99b (RepPre 0x10f99b (RepMovsqPre 0x10f99b)) (repMovsqEffect 0x10f99b) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f99e (movR64R64Effect 0x10f99e 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f99e (fun s => s.RIP = 0x10f99e) (movR64R64Effect 0x10f99e 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f9a1 (movR64R64Effect 0x10f9a1 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f9a1 (fun s => s.RIP = 0x10f9a1) (movR64R64Effect 0x10f9a1 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f9a4 (callEffect (fun _ => 0x10a410) 0x10f9a9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f9a4 (PushPre 0x10f9a4 5) (callEffect (fun _ => 0x10a410) 0x10f9a9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f9a9⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f9a9, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f98c : List UInt8 :=
  [0x48, 0x8D, 0xBB, 0xA0, 0x05, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3,
    0x48, 0xA5, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0x67, 0xAA, 0xFF, 0xFF]

theorem code_l10f98c : ∀ x ∈ codeRange 0x10f98c bytes_l10f98c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf98c 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f9a9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f9a9 (leaR64Effect 0x10f9a9 7 (.base 3 (.d32 0x618))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f9a9 (fun s => s.RIP = 0x10f9a9) (leaR64Effect 0x10f9a9 7 (.base 3 (.d32 0x618))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f9b0 (movR32Imm32Effect 0x10f9b0 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f9b0 (fun s => s.RIP = 0x10f9b0) (movR32Imm32Effect 0x10f9b0 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f9b5 (movR64R64Effect 0x10f9b5 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f9b5 (fun s => s.RIP = 0x10f9b5) (movR64R64Effect 0x10f9b5 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f9b8 (RepPre 0x10f9b8 (RepMovsqPre 0x10f9b8)) (repMovsqEffect 0x10f9b8) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f9bb (movR64R64Effect 0x10f9bb 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f9bb (fun s => s.RIP = 0x10f9bb) (movR64R64Effect 0x10f9bb 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f9be (movR64R64Effect 0x10f9be 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f9be (fun s => s.RIP = 0x10f9be) (movR64R64Effect 0x10f9be 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f9c1 (callEffect (fun _ => 0x10a410) 0x10f9c6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f9c1 (PushPre 0x10f9c1 5) (callEffect (fun _ => 0x10a410) 0x10f9c6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f9c6⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f9c6, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f9a9 : List UInt8 :=
  [0x48, 0x8D, 0xBB, 0x18, 0x06, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3,
    0x48, 0xA5, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0x4A, 0xAA, 0xFF, 0xFF]

theorem code_l10f9a9 : ∀ x ∈ codeRange 0x10f9a9 bytes_l10f9a9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf9a9 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f9c6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f9c6 (leaR64Effect 0x10f9c6 7 (.base 3 (.d32 0x690))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10f9c6 (fun s => s.RIP = 0x10f9c6) (leaR64Effect 0x10f9c6 7 (.base 3 (.d32 0x690))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f9cd (movR32Imm32Effect 0x10f9cd 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f9cd (fun s => s.RIP = 0x10f9cd) (movR32Imm32Effect 0x10f9cd 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f9d2 (movR64R64Effect 0x10f9d2 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10f9d2 (fun s => s.RIP = 0x10f9d2) (movR64R64Effect 0x10f9d2 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x10f9d5 (RepPre 0x10f9d5 (RepMovsqPre 0x10f9d5)) (repMovsqEffect 0x10f9d5) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x10f9d8 (movR64R64Effect 0x10f9d8 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x10f9d8 (fun s => s.RIP = 0x10f9d8) (movR64R64Effect 0x10f9d8 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x10f9db (movR64R64Effect 0x10f9db 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 63) (.exec 0x10f9db (fun s => s.RIP = 0x10f9db) (movR64R64Effect 0x10f9db 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10f9de (callEffect (fun _ => 0x10a410) 0x10f9e3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10f9de (PushPre 0x10f9de 5) (callEffect (fun _ => 0x10a410) 0x10f9e3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10f9e3⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 64), (5, 5), (6, 62), (7, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l10f9e3, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10f9c6 : List UInt8 :=
  [0x48, 0x8D, 0xBB, 0x90, 0x06, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xF3,
    0x48, 0xA5, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0x2D, 0xAA, 0xFF, 0xFF]

theorem code_l10f9c6 : ∀ x ∈ codeRange 0x10f9c6 bytes_l10f9c6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf9c6 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f9e3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f9e3 (addR64Imm32Effect 0x10f9e3 3 0x708) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 54) (.exec 0x10f9e3 (fun s => s.RIP = 0x10f9e3) (addR64Imm32Effect 0x10f9e3 3 0x708) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f9ea (movR32Imm32Effect 0x10f9ea 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10f9ea (fun s => s.RIP = 0x10f9ea) (movR32Imm32Effect 0x10f9ea 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f9ef (movR64R64Effect 0x10f9ef 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x10f9ef (fun s => s.RIP = 0x10f9ef) (movR64R64Effect 0x10f9ef 7 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 59) (.out 0x10f9f2 (movR64R64Effect 0x10f9f2 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x10f9f2 (fun s => s.RIP = 0x10f9f2) (movR64R64Effect 0x10f9f2 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x10f9f5 (repMovsqEffect 0x10f9f5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[59, 57, 55, 22]
    (.letOp (n := 62) (.out 0x10f9f5 (repMovsqEffect 0x10f9f5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[59, 57, 55, 22]
    (.letOp (n := 63) (.out 0x10f9f5 (repMovsqEffect 0x10f9f5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[59, 57, 55, 22]
    (.letOp (n := 64) (.exec 0x10f9f5 (RepPre 0x10f9f5 (RepMovsqPre 0x10f9f5)) (repMovsqEffect 0x10f9f5) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[59, 57, 55, 22]
    (.letOp (n := 65) (.out 0x10f9f8 (addR64Imm32Effect 0x10f9f8 4 0x288) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x10f9f8 (fun s => s.RIP = 0x10f9f8) (addR64Imm32Effect 0x10f9f8 4 0x288) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x10f9ff (popR64Effect 0x10f9ff 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 68) (.out 0x10f9ff (popR64Effect 0x10f9ff 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x10f9ff (PopPre 0x10f9ff) (popR64Effect 0x10f9ff 1 3) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x10fa00 (popR64Effect 0x10fa00 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[68]
    (.letOp (n := 71) (.out 0x10fa00 (popR64Effect 0x10fa00 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x10fa00 (PopPre 0x10fa00) (popR64Effect 0x10fa00 2 12) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x10fa02 (popR64Effect 0x10fa02 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 74) (.out 0x10fa02 (popR64Effect 0x10fa02 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x10fa02 (PopPre 0x10fa02) (popR64Effect 0x10fa02 2 13) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x10fa04 (popR64Effect 0x10fa04 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[74]
    (.letOp (n := 77) (.out 0x10fa04 (popR64Effect 0x10fa04 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x10fa04 (PopPre 0x10fa04) (popR64Effect 0x10fa04 2 14) (Reg.operands [.gpr 4] [])) #v[74]
    (.letOp (n := 79) (.out 0x10fa06 (popR64Effect 0x10fa06 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[77]
    (.letOp (n := 80) (.out 0x10fa06 (popR64Effect 0x10fa06 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[77]
    (.letOp (n := 81) (.exec 0x10fa06 (PopPre 0x10fa06) (popR64Effect 0x10fa06 2 15) (Reg.operands [.gpr 4] [])) #v[77]
    (.letOp (n := 82) (.out 0x10fa08 (popR64Effect 0x10fa08 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[80]
    (.letOp (n := 83) (.out 0x10fa08 (popR64Effect 0x10fa08 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[80]
    (.letOp (n := 84) (.exec 0x10fa08 (PopPre 0x10fa08) (popR64Effect 0x10fa08 1 5) (Reg.operands [.gpr 4] [])) #v[80]
    (.letOp (n := 85) (.out 0x10fa09 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[83]
    (.letOp (n := 86) (.out 0x10fa09 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x10fa09 (RetPre 0x10fa09) (retEffect) (Reg.operands [.gpr 4] [])) #v[83]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 63), (2, 2), (3, 67), (4, 86), (5, 82), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (15, 79), (22, 22), (39, 39), (50, 50), (51, 51)] 88) (some ⟨85, by decide⟩)))))))))))))))))))))))))))))))))))))

def bytes_l10f9e3 : List UInt8 :=
  [0x48, 0x81, 0xC3, 0x08, 0x07, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0x4C,
    0x89, 0xF6, 0xF3, 0x48, 0xA5, 0x48, 0x81, 0xC4, 0x88, 0x02, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41,
    0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10f9e3 : ∀ x ∈ codeRange 0x10f9e3 bytes_l10f9e3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf9e3 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fa10_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.out 0x10fa54 (movR64M64Effect 0x10fa54 14 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 89) (.exec 0x10fa54 (LoadPre 0x10fa54 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10fa54 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa54 14 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 90) (.out 0x10fa58 (movR64M64Effect 0x10fa58 15 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 91) (.exec 0x10fa58 (LoadPre 0x10fa58 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10fa58 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa58 15 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 92) (.out 0x10fa5c (movR64M64Effect 0x10fa5c 12 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 93) (.exec 0x10fa5c (LoadPre 0x10fa5c (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x10fa5c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa5c 12 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 94) (.out 0x10fa60 (movR32M32LowEffect 0x10fa60 7 (.base 6 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 95) (.exec 0x10fa60 (LoadPre 0x10fa60 (fun s => AddrMode.addr (.base 6 (.d8 0x50)) s (0x10fa60 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x10fa60 7 (.base 6 (.d8 0x50))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 96) (.out 0x10fa63 (callEffect (fun _ => 0x127d50) 0x10fa68) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 97) (.exec 0x10fa63 (PushPre 0x10fa63 5) (callEffect (fun _ => 0x127d50) 0x10fa68) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 98) (.const ⟨64, 0x10fa68⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 81), (1, 1), (2, 2), (3, 67), (4, 96), (5, 86), (6, 6), (7, 94), (8, 8), (9, 9), (10, 10), (11, 11), (12, 92), (13, 84), (14, 88), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)] 99⟩ { target := .l10fa68, kept := #v[], arity := rfl, guard := some (Fin.last 98) }))))))))))))

def bytes_l10fa10_1 : List UInt8 :=
  [0x4C, 0x8B, 0x76, 0x10, 0x4C, 0x8B, 0x7E, 0x18, 0x4C, 0x8B, 0x66, 0x20, 0x8B, 0x7E, 0x50, 0xE8,
    0xE8, 0x82, 0x01, 0x00]

theorem code_l10fa10_1 : ∀ x ∈ codeRange 0x10fa54 bytes_l10fa10_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfa54 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fa10 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fa10 (pushR64Effect 0x10fa10 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x10fa10 (PushPre 0x10fa10 1) (pushR64Effect 0x10fa10 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x10fa11 (pushR64Effect 0x10fa11 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x10fa11 (PushPre 0x10fa11 2) (pushR64Effect 0x10fa11 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x10fa13 (pushR64Effect 0x10fa13 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x10fa13 (PushPre 0x10fa13 2) (pushR64Effect 0x10fa13 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x10fa15 (pushR64Effect 0x10fa15 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x10fa15 (PushPre 0x10fa15 2) (pushR64Effect 0x10fa15 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x10fa17 (pushR64Effect 0x10fa17 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x10fa17 (PushPre 0x10fa17 2) (pushR64Effect 0x10fa17 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x10fa19 (pushR64Effect 0x10fa19 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x10fa19 (PushPre 0x10fa19 1) (pushR64Effect 0x10fa19 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10fa1a (subR64Imm8Effect 0x10fa1a 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10fa1a (fun s => s.RIP = 0x10fa1a) (subR64Imm8Effect 0x10fa1a 4 0x28) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10fa1e (movR64R64Effect 0x10fa1e 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x10fa1e (fun s => s.RIP = 0x10fa1e) (movR64R64Effect 0x10fa1e 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x10fa21 (movR64M64Effect 0x10fa21 0 (.base 6 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 70) (.exec 0x10fa21 (LoadPre 0x10fa21 (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x10fa21 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa21 0 (.base 6 (.d8 0x28))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.exec 0x10fa25 (StorePre 0x10fa25 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fa25 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fa25 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 65]
    (.letOp (n := 72) (.out 0x10fa29 (movR64M64Effect 0x10fa29 0 (.base 6 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 73) (.exec 0x10fa29 (LoadPre 0x10fa29 (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x10fa29 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa29 0 (.base 6 (.d8 0x30))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 74) (.exec 0x10fa2d (StorePre 0x10fa2d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10fa2d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fa2d 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 65]
    (.letOp (n := 75) (.out 0x10fa32 (movR64M64Effect 0x10fa32 0 (.base 6 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 76) (.exec 0x10fa32 (LoadPre 0x10fa32 (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x10fa32 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa32 0 (.base 6 (.d8 0x38))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.exec 0x10fa36 (StorePre 0x10fa36 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10fa36 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fa36 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 65]
    (.letOp (n := 78) (.out 0x10fa3b (movR64M64Effect 0x10fa3b 0 (.base 6 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 79) (.exec 0x10fa3b (LoadPre 0x10fa3b (fun s => AddrMode.addr (.base 6 (.d8 0x40)) s (0x10fa3b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa3b 0 (.base 6 (.d8 0x40))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 80) (.exec 0x10fa3f (StorePre 0x10fa3f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10fa3f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fa3f 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 65]
    (.letOp (n := 81) (.out 0x10fa44 (movR64M64Effect 0x10fa44 0 (.base 6 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 82) (.exec 0x10fa44 (LoadPre 0x10fa44 (fun s => AddrMode.addr (.base 6 (.d8 0x48)) s (0x10fa44 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa44 0 (.base 6 (.d8 0x48))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 83) (.exec 0x10fa48 (StorePre 0x10fa48 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10fa48 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fa48 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 65]
    (.letOp (n := 84) (.out 0x10fa4d (movR64M64Effect 0x10fa4d 13 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 85) (.exec 0x10fa4d (LoadPre 0x10fa4d (fun s => AddrMode.addr (.base 6 .none) s (0x10fa4d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10fa4d 13 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 86) (.out 0x10fa50 (movR64M64Effect 0x10fa50 5 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 87) (.exec 0x10fa50 (LoadPre 0x10fa50 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10fa50 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa50 5 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (b_l10fa10_1)))))))))))))))))))))))))))))))))))

def bytes_l10fa10 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x28, 0x48, 0x89,
    0xFB, 0x48, 0x8B, 0x46, 0x28, 0x48, 0x89, 0x04, 0x24, 0x48, 0x8B, 0x46, 0x30, 0x48, 0x89, 0x44,
    0x24, 0x08, 0x48, 0x8B, 0x46, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x46, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x46, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x4C, 0x8B, 0x2E,
    0x48, 0x8B, 0x6E, 0x08] ++ bytes_l10fa10_1

theorem code_l10fa10 : ∀ x ∈ codeRange 0x10fa10 bytes_l10fa10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xfa10 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10fa10_1

@[cfg_block] def b_l10fa68_2 : Block Op Label signature Reg.count 118 :=
  .letOp (n := 118) (.out 0x10fb08 (popR64Effect 0x10fb08 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[116]
    (.letOp (n := 119) (.out 0x10fb08 (popR64Effect 0x10fb08 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[116]
    (.letOp (n := 120) (.exec 0x10fb08 (PopPre 0x10fb08) (popR64Effect 0x10fb08 1 3) (Reg.operands [.gpr 4] [])) #v[116]
    (.letOp (n := 121) (.out 0x10fb09 (popR64Effect 0x10fb09 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[119]
    (.letOp (n := 122) (.out 0x10fb09 (popR64Effect 0x10fb09 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[119]
    (.letOp (n := 123) (.exec 0x10fb09 (PopPre 0x10fb09) (popR64Effect 0x10fb09 2 12) (Reg.operands [.gpr 4] [])) #v[119]
    (.letOp (n := 124) (.out 0x10fb0b (popR64Effect 0x10fb0b 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[122]
    (.letOp (n := 125) (.out 0x10fb0b (popR64Effect 0x10fb0b 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[122]
    (.letOp (n := 126) (.exec 0x10fb0b (PopPre 0x10fb0b) (popR64Effect 0x10fb0b 2 13) (Reg.operands [.gpr 4] [])) #v[122]
    (.letOp (n := 127) (.out 0x10fb0d (popR64Effect 0x10fb0d 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[125]
    (.letOp (n := 128) (.out 0x10fb0d (popR64Effect 0x10fb0d 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[125]
    (.letOp (n := 129) (.exec 0x10fb0d (PopPre 0x10fb0d) (popR64Effect 0x10fb0d 2 14) (Reg.operands [.gpr 4] [])) #v[125]
    (.letOp (n := 130) (.out 0x10fb0f (popR64Effect 0x10fb0f 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[128]
    (.letOp (n := 131) (.out 0x10fb0f (popR64Effect 0x10fb0f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[128]
    (.letOp (n := 132) (.exec 0x10fb0f (PopPre 0x10fb0f) (popR64Effect 0x10fb0f 2 15) (Reg.operands [.gpr 4] [])) #v[128]
    (.letOp (n := 133) (.out 0x10fb11 (popR64Effect 0x10fb11 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[131]
    (.letOp (n := 134) (.out 0x10fb11 (popR64Effect 0x10fb11 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[131]
    (.letOp (n := 135) (.exec 0x10fb11 (PopPre 0x10fb11) (popR64Effect 0x10fb11 1 5) (Reg.operands [.gpr 4] [])) #v[131]
    (.letOp (n := 136) (.out 0x10fb12 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[134]
    (.letOp (n := 137) (.out 0x10fb12 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[134]
    (.letOp (n := 138) (.exec 0x10fb12 (RetPre 0x10fb12) (retEffect) (Reg.operands [.gpr 4] [])) #v[134]
    (.terminate (.ret (RegMap.args [(0, 114), (1, 97), (2, 81), (3, 118), (4, 137), (5, 133), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 121), (13, 124), (14, 127), (15, 130), (22, 22), (39, 39), (50, 50), (51, 51)] 139) (some ⟨136, by decide⟩)))))))))))))))))))))))

def bytes_l10fa68_2 : List UInt8 :=
  [0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10fa68_2 : ∀ x ∈ codeRange 0x10fb08 bytes_l10fa68_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfb08 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fa68_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x10faab (andR64R64Effect 0x10faab 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[91, 69]
    (.letOp (n := 94) (.exec 0x10faab (fun s => s.RIP = 0x10faab) (andR64R64Effect 0x10faab 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[91, 69]
    (.letOp (n := 95) (.out 0x10faae (andR64M64Effect 0x10faae 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[69, 4]
    (.letOp (n := 96) (.exec 0x10faae (LoadPre 0x10faae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10faae + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x10faae 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 97) (.out 0x10fab3 (andR32Imm8Effect 0x10fab3 3 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 98) (.exec 0x10fab3 (fun s => s.RIP = 0x10fab3) (andR32Imm8Effect 0x10fab3 3 1 0x1) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 99) (.exec 0x10fab6 (StorePre 0x10fab6 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10fab6 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10fab6 13 (.base 3 .none)) (Reg.operands [.gpr 13, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 100) (.exec 0x10fab9 (StorePre 0x10fab9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10fab9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fab9 5 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[73, 3]
    (.letOp (n := 101) (.exec 0x10fabd (StorePre 0x10fabd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10fabd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fabd 14 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 102) (.exec 0x10fac1 (StorePre 0x10fac1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10fac1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fac1 15 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[77, 3]
    (.letOp (n := 103) (.exec 0x10fac5 (StorePre 0x10fac5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10fac5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fac5 12 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 104) (.exec 0x10fac9 (StorePre 0x10fac9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x10fac9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fac9 2 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[81, 3]
    (.letOp (n := 105) (.exec 0x10facd (StorePre 0x10facd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x10facd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10facd 6 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[85, 3]
    (.letOp (n := 106) (.exec 0x10fad1 (StorePre 0x10fad1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x10fad1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fad1 7 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[89, 3]
    (.letOp (n := 107) (.exec 0x10fad5 (StorePre 0x10fad5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x10fad5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fad5 8 (.base 3 (.d8 0x40))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[93, 3]
    (.letOp (n := 108) (.exec 0x10fad9 (StorePre 0x10fad9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x10fad9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fad9 0 (.base 3 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[95, 3]
    (.letOp (n := 109) (.exec 0x10fadd (StorePre 0x10fadd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x10fadd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fadd 1 (.base 3 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[97, 3]
    (.letOp (n := 110) (.exec 0x10fae1 (StorePre 0x10fae1 8 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x10fae1 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10fae1 (.base 3 (.d8 0x58)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 111) (.exec 0x10fae9 (StorePre 0x10fae9 8 (fun s => AddrMode.addr (.base 3 (.d8 0x60)) s (0x10fae9 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10fae9 (.base 3 (.d8 0x60)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 112) (.exec 0x10faf1 (StorePre 0x10faf1 8 (fun s => AddrMode.addr (.base 3 (.d8 0x68)) s (0x10faf1 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10faf1 (.base 3 (.d8 0x68)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 113) (.exec 0x10faf9 (StorePre 0x10faf9 8 (fun s => AddrMode.addr (.base 3 (.d8 0x70)) s (0x10faf9 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10faf9 (.base 3 (.d8 0x70)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 114) (.out 0x10fb01 (movR64R64Effect 0x10fb01 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 115) (.exec 0x10fb01 (fun s => s.RIP = 0x10fb01) (movR64R64Effect 0x10fb01 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 116) (.out 0x10fb04 (addR64Imm8Effect 0x10fb04 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 117) (.exec 0x10fb04 (fun s => s.RIP = 0x10fb04) (addR64Imm8Effect 0x10fb04 4 0x28) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l10fa68_2)))))))))))))))))))))))))

def bytes_l10fa68_1 : List UInt8 :=
  [0x49, 0x21, 0xC0, 0x48, 0x23, 0x44, 0x24, 0x20, 0x83, 0xE1, 0x01, 0x4C, 0x89, 0x2B, 0x48, 0x89,
    0x6B, 0x08, 0x4C, 0x89, 0x73, 0x10, 0x4C, 0x89, 0x7B, 0x18, 0x4C, 0x89, 0x63, 0x20, 0x48, 0x89,
    0x53, 0x28, 0x48, 0x89, 0x73, 0x30, 0x48, 0x89, 0x7B, 0x38, 0x4C, 0x89, 0x43, 0x40, 0x48, 0x89,
    0x43, 0x48, 0x48, 0x89, 0x4B, 0x50, 0x48, 0xC7, 0x43, 0x58, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0x43, 0x60, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x43, 0x68, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0x43, 0x70, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x28] ++ bytes_l10fa68_2

theorem code_l10fa68_1 : ∀ x ∈ codeRange 0x10faab bytes_l10fa68_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xfaab 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10fa68_2

@[cfg_block] def b_l10fa68 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fa68 (movzxR32R8Effect 0x10fa68 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x10fa68 (fun s => s.RIP = 0x10fa68) (movzxR32R8Effect 0x10fa68 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x10fa6b (movR64R64Effect 0x10fa6b 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x10fa6b (fun s => s.RIP = 0x10fa6b) (movR64R64Effect 0x10fa6b 1 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x10fa6e (negR64Effect 0x10fa6e 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x10fa6e (fun s => s.RIP = 0x10fa6e) (negR64Effect 0x10fa6e 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 59) (.out 0x10fa71 (movR64M64Effect 0x10fa71 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x10fa71 (LoadPre 0x10fa71 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fa71 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa71 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10fa75 (movR64R64Effect 0x10fa75 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 62) (.exec 0x10fa75 (fun s => s.RIP = 0x10fa75) (movR64R64Effect 0x10fa75 2 6) (Reg.operands [.gpr 6] [])) #v[59]
    (.letOp (n := 63) (.out 0x10fa78 (xorR64Imm8Effect 0x10fa78 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 64) (.exec 0x10fa78 (fun s => s.RIP = 0x10fa78) (xorR64Imm8Effect 0x10fa78 2 0x1) (Reg.operands [.gpr 2] [])) #v[61]
    (.letOp (n := 65) (.out 0x10fa7c (andR64R64Effect 0x10fa7c 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[63, 57]
    (.letOp (n := 66) (.exec 0x10fa7c (fun s => s.RIP = 0x10fa7c) (andR64R64Effect 0x10fa7c 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[63, 57]
    (.letOp (n := 67) (.out 0x10fa7f (notR32Effect 0x10fa7f 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 68) (.exec 0x10fa7f (fun s => s.RIP = 0x10fa7f) (notR32Effect 0x10fa7f 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 69) (.out 0x10fa81 (decR64Effect 0x10fa81 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 70) (.exec 0x10fa81 (fun s => s.RIP = 0x10fa81) (decR64Effect 0x10fa81 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 71) (.out 0x10fa84 (andR64R64Effect 0x10fa84 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[13, 69]
    (.letOp (n := 72) (.exec 0x10fa84 (fun s => s.RIP = 0x10fa84) (andR64R64Effect 0x10fa84 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[13, 69]
    (.letOp (n := 73) (.out 0x10fa87 (andR64R64Effect 0x10fa87 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[5, 69]
    (.letOp (n := 74) (.exec 0x10fa87 (fun s => s.RIP = 0x10fa87) (andR64R64Effect 0x10fa87 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[5, 69]
    (.letOp (n := 75) (.out 0x10fa8a (andR64R64Effect 0x10fa8a 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[14, 69]
    (.letOp (n := 76) (.exec 0x10fa8a (fun s => s.RIP = 0x10fa8a) (andR64R64Effect 0x10fa8a 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[14, 69]
    (.letOp (n := 77) (.out 0x10fa8d (andR64R64Effect 0x10fa8d 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[15, 69]
    (.letOp (n := 78) (.exec 0x10fa8d (fun s => s.RIP = 0x10fa8d) (andR64R64Effect 0x10fa8d 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[15, 69]
    (.letOp (n := 79) (.out 0x10fa90 (andR64R64Effect 0x10fa90 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[12, 69]
    (.letOp (n := 80) (.exec 0x10fa90 (fun s => s.RIP = 0x10fa90) (andR64R64Effect 0x10fa90 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[12, 69]
    (.letOp (n := 81) (.out 0x10fa93 (xorR64R64Effect 0x10fa93 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[65, 59]
    (.letOp (n := 82) (.exec 0x10fa93 (fun s => s.RIP = 0x10fa93) (xorR64R64Effect 0x10fa93 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[65, 59]
    (.letOp (n := 83) (.out 0x10fa96 (movR64M64Effect 0x10fa96 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 84) (.exec 0x10fa96 (LoadPre 0x10fa96 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10fa96 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fa96 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x10fa9b (andR64R64Effect 0x10fa9b 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[83, 69]
    (.letOp (n := 86) (.exec 0x10fa9b (fun s => s.RIP = 0x10fa9b) (andR64R64Effect 0x10fa9b 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[83, 69]
    (.letOp (n := 87) (.out 0x10fa9e (movR64M64Effect 0x10fa9e 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 88) (.exec 0x10fa9e (LoadPre 0x10fa9e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10fa9e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fa9e 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.out 0x10faa3 (andR64R64Effect 0x10faa3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[87, 69]
    (.letOp (n := 90) (.exec 0x10faa3 (fun s => s.RIP = 0x10faa3) (andR64R64Effect 0x10faa3 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[87, 69]
    (.letOp (n := 91) (.out 0x10faa6 (movR64M64Effect 0x10faa6 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 92) (.exec 0x10faa6 (LoadPre 0x10faa6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10faa6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10faa6 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l10fa68_1))))))))))))))))))))))))))))))))))))))))

def bytes_l10fa68 : List UInt8 :=
  [0x0F, 0xB6, 0xC0, 0x48, 0x89, 0xC1, 0x48, 0xF7, 0xD9, 0x48, 0x8B, 0x34, 0x24, 0x48, 0x89, 0xF2,
    0x48, 0x83, 0xF2, 0x01, 0x48, 0x21, 0xCA, 0xF7, 0xD1, 0x48, 0xFF, 0xC8, 0x49, 0x21, 0xC5, 0x48,
    0x21, 0xC5, 0x49, 0x21, 0xC6, 0x49, 0x21, 0xC7, 0x49, 0x21, 0xC4, 0x48, 0x31, 0xF2, 0x48, 0x8B,
    0x74, 0x24, 0x08, 0x48, 0x21, 0xC6, 0x48, 0x8B, 0x7C, 0x24, 0x10, 0x48, 0x21, 0xC7, 0x4C, 0x8B,
    0x44, 0x24, 0x18] ++ bytes_l10fa68_1

theorem code_l10fa68 : ∀ x ∈ codeRange 0x10fa68 bytes_l10fa68, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xfa68 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10fa68_1

@[cfg_block] def b_l10fb20_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.out 0x10fb7b (xorR32R32Effect 0x10fb7b 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 91) (.exec 0x10fb7b (fun s => s.RIP = 0x10fb7b) (xorR32R32Effect 0x10fb7b 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 92) (.out 0x10fb7d (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fb7f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[71, 84]
    (.letOp (n := 93) (.exec 0x10fb7d (GoesTo (CallPre 0x10fb7d 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fb7f) 0x12a700) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fb7f) (Reg.operands [.gpr 4, .gpr 3] [])) #v[71, 84]
    (.letOp (n := 94) (.const ⟨64, 0x10fb7f⟩) #v[]
    (.terminate (.call ⟨.l12a700, RegMap.args [(1, 1), (2, 86), (3, 84), (4, 92), (5, 80), (6, 90), (7, 88), (9, 9), (10, 10), (11, 11), (12, 77), (13, 82), (14, 75), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)] 95⟩ { target := .l10fb7f, kept := #v[], arity := rfl, guard := some (Fin.last 94) }))))))

def bytes_l10fb20_1 : List UInt8 :=
  [0x31, 0xF6, 0xFF, 0xD3]

theorem code_l10fb20_1 : ∀ x ∈ codeRange 0x10fb7b bytes_l10fb20_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfb7b 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fb20 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fb20 (pushR64Effect 0x10fb20 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x10fb20 (PushPre 0x10fb20 1) (pushR64Effect 0x10fb20 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x10fb21 (pushR64Effect 0x10fb21 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x10fb21 (PushPre 0x10fb21 2) (pushR64Effect 0x10fb21 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x10fb23 (pushR64Effect 0x10fb23 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x10fb23 (PushPre 0x10fb23 2) (pushR64Effect 0x10fb23 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x10fb25 (pushR64Effect 0x10fb25 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x10fb25 (PushPre 0x10fb25 2) (pushR64Effect 0x10fb25 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x10fb27 (pushR64Effect 0x10fb27 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x10fb27 (PushPre 0x10fb27 2) (pushR64Effect 0x10fb27 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x10fb29 (pushR64Effect 0x10fb29 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x10fb29 (PushPre 0x10fb29 1) (pushR64Effect 0x10fb29 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10fb2a (subR64Imm32Effect 0x10fb2a 4 0x1000) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10fb2a (fun s => s.RIP = 0x10fb2a) (subR64Imm32Effect 0x10fb2a 4 0x1000) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x10fb31 (StorePre 0x10fb31 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fb31 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10fb31 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 68) (.out 0x10fb39 (subR64Imm32Effect 0x10fb39 4 0x1000) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x10fb39 (fun s => s.RIP = 0x10fb39) (subR64Imm32Effect 0x10fb39 4 0x1000) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.exec 0x10fb40 (StorePre 0x10fb40 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fb40 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10fb40 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 71) (.out 0x10fb48 (subR64Imm32Effect 0x10fb48 4 0x8a8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x10fb48 (fun s => s.RIP = 0x10fb48) (subR64Imm32Effect 0x10fb48 4 0x8a8) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x10fb4f (movR64R64Effect 0x10fb4f 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 1] []) (.reg (.gpr 15))) #v[1]
    (.letOp (n := 74) (.exec 0x10fb4f (fun s => s.RIP = 0x10fb4f) (movR64R64Effect 0x10fb4f 15 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 75) (.out 0x10fb52 (movR64R64Effect 0x10fb52 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 76) (.exec 0x10fb52 (fun s => s.RIP = 0x10fb52) (movR64R64Effect 0x10fb52 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 77) (.out 0x10fb55 (movR64R64Effect 0x10fb55 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 78) (.exec 0x10fb55 (fun s => s.RIP = 0x10fb55) (movR64R64Effect 0x10fb55 12 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 79) (.exec 0x10fb58 (StorePre 0x10fb58 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fb58 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fb58 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 71]
    (.letOp (n := 80) (.out 0x10fb5c (leaR64Effect 0x10fb5c 5 (.sib 4 none 0 (.d32 0x338))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[71]
    (.letOp (n := 81) (.exec 0x10fb5c (fun s => s.RIP = 0x10fb5c) (leaR64Effect 0x10fb5c 5 (.sib 4 none 0 (.d32 0x338))) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 82) (.out 0x10fb64 (leaR64Effect 0x10fb64 13 (.sib 4 none 0 (.d32 0x228))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 83) (.exec 0x10fb64 (fun s => s.RIP = 0x10fb64) (leaR64Effect 0x10fb64 13 (.sib 4 none 0 (.d32 0x228))) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 84) (.out 0x10fb6c (leaR64Effect 0x10fb6c 3 (.rip 0x1ab8d)) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 85) (.exec 0x10fb6c (fun s => s.RIP = 0x10fb6c) (leaR64Effect 0x10fb6c 3 (.rip 0x1ab8d)) (Reg.operands [] [])) #v[]
    (.letOp (n := 86) (.out 0x10fb73 (movR32Imm32Effect 0x10fb73 5 2 0x109) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 87) (.exec 0x10fb73 (fun s => s.RIP = 0x10fb73) (movR32Imm32Effect 0x10fb73 5 2 0x109) (Reg.operands [] [])) #v[]
    (.letOp (n := 88) (.out 0x10fb78 (movR64R64Effect 0x10fb78 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[82]
    (.letOp (n := 89) (.exec 0x10fb78 (fun s => s.RIP = 0x10fb78) (movR64R64Effect 0x10fb78 7 13) (Reg.operands [.gpr 13] [])) #v[82]
    (b_l10fb20_1)))))))))))))))))))))))))))))))))))))

def bytes_l10fb20 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x00, 0x10, 0x00,
    0x00, 0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48, 0x81, 0xEC, 0x00, 0x10, 0x00, 0x00,
    0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48, 0x81, 0xEC, 0xA8, 0x08, 0x00, 0x00, 0x49,
    0x89, 0xCF, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xF4, 0x48, 0x89, 0x3C, 0x24, 0x48, 0x8D, 0xAC, 0x24,
    0x38, 0x03, 0x00, 0x00, 0x4C, 0x8D, 0xAC, 0x24, 0x28, 0x02, 0x00, 0x00, 0x48, 0x8D, 0x1D, 0x8D,
    0xAB, 0x01, 0x00, 0xBA, 0x09, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xEF] ++ bytes_l10fb20_1

theorem code_l10fb20 : ∀ x ∈ codeRange 0x10fb20 bytes_l10fb20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xfb20 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10fb20_1

@[cfg_block] def b_l10fb7f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fb7f (movR32Imm32Effect 0x10fb7f 5 2 0x109) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x10fb7f (fun s => s.RIP = 0x10fb7f) (movR32Imm32Effect 0x10fb7f 5 2 0x109) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10fb84 (movR64R64Effect 0x10fb84 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 56) (.exec 0x10fb84 (fun s => s.RIP = 0x10fb84) (movR64R64Effect 0x10fb84 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x10fb87 (xorR32R32Effect 0x10fb87 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 58) (.exec 0x10fb87 (fun s => s.RIP = 0x10fb87) (xorR32R32Effect 0x10fb87 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 59) (.out 0x10fb89 (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fb8b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 60) (.exec 0x10fb89 (GoesTo (CallPre 0x10fb89 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fb8b) 0x12a700) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fb8b) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 61) (.const ⟨64, 0x10fb8b⟩) #v[]
    (.terminate (.call ⟨.l12a700, RegMap.args [(2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10fb8b, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10fb7f : List UInt8 :=
  [0xBA, 0x09, 0x01, 0x00, 0x00, 0x48, 0x89, 0xEF, 0x31, 0xF6, 0xFF, 0xD3]

theorem code_l10fb7f : ∀ x ∈ codeRange 0x10fb7f bytes_l10fb7f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfb7f 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fb8b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fb8b (leaR64Effect 0x10fb8b 5 (.sib 4 none 0 (.d32 0x1568))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x10fb8b (fun s => s.RIP = 0x10fb8b) (leaR64Effect 0x10fb8b 5 (.sib 4 none 0 (.d32 0x1568))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10fb93 (movR64Imm32Effect 0x10fb93 7 0x202bc8) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x10fb93 (fun s => s.RIP = 0x10fb93) (movR64Imm32Effect 0x10fb93 7 0x202bc8) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10fb9a (movR64R64Effect 0x10fb9a 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x10fb9a (fun s => s.RIP = 0x10fb9a) (movR64R64Effect 0x10fb9a 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x10fb9d (movR64R64Effect 0x10fb9d 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 60) (.exec 0x10fb9d (fun s => s.RIP = 0x10fb9d) (movR64R64Effect 0x10fb9d 2 5) (Reg.operands [.gpr 5] [])) #v[53]
    (.letOp (n := 61) (.out 0x10fba0 (movR64R64Effect 0x10fba0 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 62) (.exec 0x10fba0 (fun s => s.RIP = 0x10fba0) (movR64R64Effect 0x10fba0 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 63) (.out 0x10fba3 (callEffect (fun _ => 0x10f150) 0x10fba8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x10fba3 (PushPre 0x10fba3 5) (callEffect (fun _ => 0x10f150) 0x10fba8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x10fba8⟩) #v[]
    (.terminate (.call ⟨.l10f150, RegMap.args [(1, 61), (2, 59), (3, 3), (4, 63), (5, 53), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l10fba8, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l10fb8b : List UInt8 :=
  [0x48, 0x8D, 0xAC, 0x24, 0x68, 0x15, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0xC8, 0x2B, 0x20, 0x00, 0x4C,
    0x89, 0xE6, 0x48, 0x89, 0xEA, 0x4C, 0x89, 0xE9, 0xE8, 0xA8, 0xF5, 0xFF, 0xFF]

theorem code_l10fb8b : ∀ x ∈ codeRange 0x10fb8b bytes_l10fb8b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfb8b 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fba8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fba8 (leaR64Effect 0x10fba8 7 (.sib 4 none 0 (.d32 0xbc8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10fba8 (fun s => s.RIP = 0x10fba8) (leaR64Effect 0x10fba8 7 (.sib 4 none 0 (.d32 0xbc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10fbb0 (leaR64Effect 0x10fbb0 12 (.rip 0x1ac69)) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 56) (.exec 0x10fbb0 (fun s => s.RIP = 0x10fbb0) (leaR64Effect 0x10fbb0 12 (.rip 0x1ac69)) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10fbb7 (movR32Imm32Effect 0x10fbb7 5 2 0x780) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10fbb7 (fun s => s.RIP = 0x10fbb7) (movR32Imm32Effect 0x10fbb7 5 2 0x780) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10fbbc (movR64R64Effect 0x10fbbc 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 60) (.exec 0x10fbbc (fun s => s.RIP = 0x10fbbc) (movR64R64Effect 0x10fbbc 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 61) (.out 0x10fbbf (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fbc2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 55]
    (.letOp (n := 62) (.exec 0x10fbbf (GoesTo (CallPre 0x10fbbf 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fbc2) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fbc2) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 55]
    (.letOp (n := 63) (.const ⟨64, 0x10fbc2⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 3), (4, 61), (5, 5), (6, 59), (7, 53), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10fbc2, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10fba8 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xC8, 0x0B, 0x00, 0x00, 0x4C, 0x8D, 0x25, 0x69, 0xAC, 0x01, 0x00, 0xBA,
    0x80, 0x07, 0x00, 0x00, 0x48, 0x89, 0xEE, 0x41, 0xFF, 0xD4]

theorem code_l10fba8 : ∀ x ∈ codeRange 0x10fba8 bytes_l10fba8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfba8 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fbc2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fbc2 (leaR64Effect 0x10fbc2 7 (.sib 4 none 0 (.d32 0x1348))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10fbc2 (fun s => s.RIP = 0x10fbc2) (leaR64Effect 0x10fbc2 7 (.sib 4 none 0 (.d32 0x1348))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10fbca (movR32Imm32Effect 0x10fbca 5 2 0x220) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x10fbca (fun s => s.RIP = 0x10fbca) (movR32Imm32Effect 0x10fbca 5 2 0x220) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10fbcf (movR64R64Effect 0x10fbcf 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 58) (.exec 0x10fbcf (fun s => s.RIP = 0x10fbcf) (movR64R64Effect 0x10fbcf 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x10fbd2 (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fbd5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 12]
    (.letOp (n := 60) (.exec 0x10fbd2 (GoesTo (CallPre 0x10fbd2 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fbd5) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fbd5) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 61) (.const ⟨64, 0x10fbd5⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10fbd5, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10fbc2 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x48, 0x13, 0x00, 0x00, 0xBA, 0x20, 0x02, 0x00, 0x00, 0x4C, 0x89, 0xEE,
    0x41, 0xFF, 0xD4]

theorem code_l10fbc2 : ∀ x ∈ codeRange 0x10fbc2 bytes_l10fbc2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfbc2 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fbd5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fbd5 (leaR64Effect 0x10fbd5 13 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 54) (.exec 0x10fbd5 (fun s => s.RIP = 0x10fbd5) (leaR64Effect 0x10fbd5 13 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10fbdd (leaR64Effect 0x10fbdd 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 56) (.exec 0x10fbdd (fun s => s.RIP = 0x10fbdd) (leaR64Effect 0x10fbdd 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10fbe2 (movR32Imm32Effect 0x10fbe2 5 2 0x109) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10fbe2 (fun s => s.RIP = 0x10fbe2) (movR32Imm32Effect 0x10fbe2 5 2 0x109) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10fbe7 (movR64R64Effect 0x10fbe7 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 60) (.exec 0x10fbe7 (fun s => s.RIP = 0x10fbe7) (movR64R64Effect 0x10fbe7 7 5) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 61) (.out 0x10fbea (xorR32R32Effect 0x10fbea 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 62) (.exec 0x10fbea (fun s => s.RIP = 0x10fbea) (xorR32R32Effect 0x10fbea 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 63) (.out 0x10fbec (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fbee) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 64) (.exec 0x10fbec (GoesTo (CallPre 0x10fbec 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fbee) 0x12a700) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fbee) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 65) (.const ⟨64, 0x10fbee⟩) #v[]
    (.terminate (.call ⟨.l12a700, RegMap.args [(2, 57), (3, 3), (4, 63), (5, 55), (6, 61), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l10fbee, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l10fbd5 : List UInt8 :=
  [0x4C, 0x8D, 0xAC, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x6C, 0x24, 0x08, 0xBA, 0x09, 0x01,
    0x00, 0x00, 0x48, 0x89, 0xEF, 0x31, 0xF6, 0xFF, 0xD3]

theorem code_l10fbd5 : ∀ x ∈ codeRange 0x10fbd5 bytes_l10fbd5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfbd5 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fbee : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fbee (movR32Imm32Effect 0x10fbee 5 2 0x109) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x10fbee (fun s => s.RIP = 0x10fbee) (movR32Imm32Effect 0x10fbee 5 2 0x109) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10fbf3 (movR64R64Effect 0x10fbf3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 56) (.exec 0x10fbf3 (fun s => s.RIP = 0x10fbf3) (movR64R64Effect 0x10fbf3 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x10fbf6 (xorR32R32Effect 0x10fbf6 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 58) (.exec 0x10fbf6 (fun s => s.RIP = 0x10fbf6) (xorR32R32Effect 0x10fbf6 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 59) (.out 0x10fbf8 (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fbfa) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 60) (.exec 0x10fbf8 (GoesTo (CallPre 0x10fbf8 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fbfa) 0x12a700) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fbfa) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 61) (.const ⟨64, 0x10fbfa⟩) #v[]
    (.terminate (.call ⟨.l12a700, RegMap.args [(2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10fbfa, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10fbee : List UInt8 :=
  [0xBA, 0x09, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x31, 0xF6, 0xFF, 0xD3]

theorem code_l10fbee : ∀ x ∈ codeRange 0x10fbee bytes_l10fbee, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfbee 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fbfa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fbfa (leaR64Effect 0x10fbfa 13 (.sib 4 none 0 (.d32 0x1568))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 54) (.exec 0x10fbfa (fun s => s.RIP = 0x10fbfa) (leaR64Effect 0x10fbfa 13 (.sib 4 none 0 (.d32 0x1568))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10fc02 (movR64R64Effect 0x10fc02 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 56) (.exec 0x10fc02 (fun s => s.RIP = 0x10fc02) (movR64R64Effect 0x10fc02 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x10fc05 (movR64R64Effect 0x10fc05 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10fc05 (fun s => s.RIP = 0x10fc05) (movR64R64Effect 0x10fc05 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x10fc08 (movR64R64Effect 0x10fc08 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 60) (.exec 0x10fc08 (fun s => s.RIP = 0x10fc08) (movR64R64Effect 0x10fc08 2 13) (Reg.operands [.gpr 13] [])) #v[53]
    (.letOp (n := 61) (.out 0x10fc0b (movR64R64Effect 0x10fc0b 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 62) (.exec 0x10fc0b (fun s => s.RIP = 0x10fc0b) (movR64R64Effect 0x10fc0b 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 63) (.out 0x10fc0e (callEffect (fun _ => 0x10f150) 0x10fc13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x10fc0e (PushPre 0x10fc0e 5) (callEffect (fun _ => 0x10f150) 0x10fc13) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x10fc13⟩) #v[]
    (.terminate (.call ⟨.l10f150, RegMap.args [(1, 61), (2, 59), (3, 3), (4, 63), (5, 5), (6, 57), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l10fc13, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l10fbfa : List UInt8 :=
  [0x4C, 0x8D, 0xAC, 0x24, 0x68, 0x15, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xF6, 0x4C, 0x89,
    0xEA, 0x48, 0x89, 0xE9, 0xE8, 0x3D, 0xF5, 0xFF, 0xFF]

theorem code_l10fbfa : ∀ x ∈ codeRange 0x10fbfa bytes_l10fbfa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfbfa 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fc13 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fc13 (leaR64Effect 0x10fc13 14 (.sib 4 none 0 (.d32 0x228))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x10fc13 (fun s => s.RIP = 0x10fc13) (leaR64Effect 0x10fc13 14 (.sib 4 none 0 (.d32 0x228))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10fc1b (movR32Imm32Effect 0x10fc1b 5 2 0x780) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x10fc1b (fun s => s.RIP = 0x10fc1b) (movR32Imm32Effect 0x10fc1b 5 2 0x780) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10fc20 (movR64R64Effect 0x10fc20 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x10fc20 (fun s => s.RIP = 0x10fc20) (movR64R64Effect 0x10fc20 7 14) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 59) (.out 0x10fc23 (movR64R64Effect 0x10fc23 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 60) (.exec 0x10fc23 (fun s => s.RIP = 0x10fc23) (movR64R64Effect 0x10fc23 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x10fc26 (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc29) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 12]
    (.letOp (n := 62) (.exec 0x10fc26 (GoesTo (CallPre 0x10fc26 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc29) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc29) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 63) (.const ⟨64, 0x10fc29⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10fc29, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10fc13 : List UInt8 :=
  [0x4C, 0x8D, 0xB4, 0x24, 0x28, 0x02, 0x00, 0x00, 0xBA, 0x80, 0x07, 0x00, 0x00, 0x4C, 0x89, 0xF7,
    0x4C, 0x89, 0xEE, 0x41, 0xFF, 0xD4]

theorem code_l10fc13 : ∀ x ∈ codeRange 0x10fc13 bytes_l10fc13, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfc13 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fc29 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fc29 (leaR64Effect 0x10fc29 7 (.sib 4 none 0 (.d32 0x9a8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10fc29 (fun s => s.RIP = 0x10fc29) (leaR64Effect 0x10fc29 7 (.sib 4 none 0 (.d32 0x9a8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10fc31 (movR32Imm32Effect 0x10fc31 5 2 0x220) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x10fc31 (fun s => s.RIP = 0x10fc31) (movR32Imm32Effect 0x10fc31 5 2 0x220) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10fc36 (movR64R64Effect 0x10fc36 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 58) (.exec 0x10fc36 (fun s => s.RIP = 0x10fc36) (movR64R64Effect 0x10fc36 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x10fc39 (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc3c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 12]
    (.letOp (n := 60) (.exec 0x10fc39 (GoesTo (CallPre 0x10fc39 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc3c) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc3c) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 61) (.const ⟨64, 0x10fc3c⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10fc3c, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10fc29 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xA8, 0x09, 0x00, 0x00, 0xBA, 0x20, 0x02, 0x00, 0x00, 0x48, 0x89, 0xEE,
    0x41, 0xFF, 0xD4]

theorem code_l10fc29 : ∀ x ∈ codeRange 0x10fc29 bytes_l10fc29, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfc29 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fc3c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fc3c (movR32Imm32Effect 0x10fc3c 5 2 0x9a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x10fc3c (fun s => s.RIP = 0x10fc3c) (movR32Imm32Effect 0x10fc3c 5 2 0x9a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10fc41 (movR64R64Effect 0x10fc41 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 56) (.exec 0x10fc41 (fun s => s.RIP = 0x10fc41) (movR64R64Effect 0x10fc41 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x10fc44 (leaR64Effect 0x10fc44 6 (.sib 4 none 0 (.d32 0xbc8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x10fc44 (fun s => s.RIP = 0x10fc44) (leaR64Effect 0x10fc44 6 (.sib 4 none 0 (.d32 0xbc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10fc4c (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc4f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 12]
    (.letOp (n := 60) (.exec 0x10fc4c (GoesTo (CallPre 0x10fc4c 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc4f) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc4f) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 61) (.const ⟨64, 0x10fc4f⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10fc4f, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10fc3c : List UInt8 :=
  [0xBA, 0xA0, 0x09, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x48, 0x8D, 0xB4, 0x24, 0xC8, 0x0B, 0x00, 0x00,
    0x41, 0xFF, 0xD4]

theorem code_l10fc3c : ∀ x ∈ codeRange 0x10fc3c bytes_l10fc3c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfc3c 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fc4f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fc4f (leaR64Effect 0x10fc4f 7 (.sib 4 none 0 (.d32 0x1f08))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10fc4f (fun s => s.RIP = 0x10fc4f) (leaR64Effect 0x10fc4f 7 (.sib 4 none 0 (.d32 0x1f08))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10fc57 (movR32Imm32Effect 0x10fc57 5 2 0x9a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x10fc57 (fun s => s.RIP = 0x10fc57) (movR32Imm32Effect 0x10fc57 5 2 0x9a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10fc5c (movR64R64Effect 0x10fc5c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10fc5c (fun s => s.RIP = 0x10fc5c) (movR64R64Effect 0x10fc5c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x10fc5f (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc62) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 12]
    (.letOp (n := 60) (.exec 0x10fc5f (GoesTo (CallPre 0x10fc5f 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc62) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc62) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 61) (.const ⟨64, 0x10fc62⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10fc62, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10fc4f : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x08, 0x1F, 0x00, 0x00, 0xBA, 0xA0, 0x09, 0x00, 0x00, 0x4C, 0x89, 0xF6,
    0x41, 0xFF, 0xD4]

theorem code_l10fc4f : ∀ x ∈ codeRange 0x10fc4f bytes_l10fc4f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfc4f 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fc62 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fc62 (leaR64Effect 0x10fc62 0 (.sib 4 none 0 (.d32 0x28a8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10fc62 (fun s => s.RIP = 0x10fc62) (leaR64Effect 0x10fc62 0 (.sib 4 none 0 (.d32 0x28a8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10fc6a (StorePre 0x10fc6a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x10fc6a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10fc6a 13 (.sib 4 none 0 (.d32 0x228))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 56) (.exec 0x10fc72 (StorePre 0x10fc72 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x230)) s (0x10fc72 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10fc72 0 (.sib 4 none 0 (.d32 0x230))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 57) (.exec 0x10fc7a (StorePre 0x10fc7a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x238)) s (0x10fc7a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10fc7a (.sib 4 none 0 (.d32 0x238)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10fc86 (StorePre 0x10fc86 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x268)) s (0x10fc86 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10fc86 (.sib 4 none 0 (.d32 0x268)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10fc92 (leaR64Effect 0x10fc92 6 (.sib 4 none 0 (.d32 0x228))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x10fc92 (fun s => s.RIP = 0x10fc92) (leaR64Effect 0x10fc92 6 (.sib 4 none 0 (.d32 0x228))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10fc9a (movR64M64Effect 0x10fc9a 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 62) (.exec 0x10fc9a (LoadPre 0x10fc9a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fc9a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fc9a 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x10fc9e (movR64R64Effect 0x10fc9e 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 64) (.exec 0x10fc9e (fun s => s.RIP = 0x10fc9e) (movR64R64Effect 0x10fc9e 7 3) (Reg.operands [.gpr 3] [])) #v[61]
    (.letOp (n := 65) (.out 0x10fca1 (callEffect (fun _ => 0x1100a0) 0x10fca6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x10fca1 (PushPre 0x10fca1 5) (callEffect (fun _ => 0x1100a0) 0x10fca6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x10fca6⟩) #v[]
    (.terminate (.call ⟨.l1100a0, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 61), (4, 65), (5, 5), (6, 59), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l10fca6, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l10fc62 : List UInt8 :=
  [0x48, 0x8D, 0x84, 0x24, 0xA8, 0x28, 0x00, 0x00, 0x4C, 0x89, 0xAC, 0x24, 0x28, 0x02, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0x30, 0x02, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x38, 0x02, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x68, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0xB4, 0x24, 0x28, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x1C, 0x24, 0x48, 0x89, 0xDF, 0xE8,
    0xFA, 0x03, 0x00, 0x00]

theorem code_l10fc62 : ∀ x ∈ codeRange 0x10fc62 bytes_l10fc62, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfc62 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fca6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fca6 (movR64R64Effect 0x10fca6 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x10fca6 (fun s => s.RIP = 0x10fca6) (movR64R64Effect 0x10fca6 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10fca9 (addR64Imm32Effect 0x10fca9 4 0x28a8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x10fca9 (fun s => s.RIP = 0x10fca9) (addR64Imm32Effect 0x10fca9 4 0x28a8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10fcb0 (popR64Effect 0x10fcb0 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x10fcb0 (popR64Effect 0x10fcb0 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x10fcb0 (PopPre 0x10fcb0) (popR64Effect 0x10fcb0 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x10fcb1 (popR64Effect 0x10fcb1 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x10fcb1 (popR64Effect 0x10fcb1 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x10fcb1 (PopPre 0x10fcb1) (popR64Effect 0x10fcb1 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x10fcb3 (popR64Effect 0x10fcb3 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x10fcb3 (popR64Effect 0x10fcb3 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x10fcb3 (PopPre 0x10fcb3) (popR64Effect 0x10fcb3 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x10fcb5 (popR64Effect 0x10fcb5 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x10fcb5 (popR64Effect 0x10fcb5 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x10fcb5 (PopPre 0x10fcb5) (popR64Effect 0x10fcb5 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x10fcb7 (popR64Effect 0x10fcb7 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x10fcb7 (popR64Effect 0x10fcb7 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x10fcb7 (PopPre 0x10fcb7) (popR64Effect 0x10fcb7 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x10fcb9 (popR64Effect 0x10fcb9 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x10fcb9 (popR64Effect 0x10fcb9 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x10fcb9 (PopPre 0x10fcb9) (popR64Effect 0x10fcb9 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x10fcba (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x10fcba (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x10fcba (RetPre 0x10fcba) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l10fca6 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xA8, 0x28, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10fca6 : ∀ x ∈ codeRange 0x10fca6 bytes_l10fca6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfca6 21 (by decide +kernel)
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

@[cfg_block] def b_l10ff00 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10ff00 (pushR64Effect 0x10ff00 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x10ff00 (PushPre 0x10ff00 1) (pushR64Effect 0x10ff00 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x10ff01 (pushR64Effect 0x10ff01 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x10ff01 (PushPre 0x10ff01 2) (pushR64Effect 0x10ff01 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x10ff03 (pushR64Effect 0x10ff03 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x10ff03 (PushPre 0x10ff03 2) (pushR64Effect 0x10ff03 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x10ff05 (pushR64Effect 0x10ff05 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x10ff05 (PushPre 0x10ff05 2) (pushR64Effect 0x10ff05 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x10ff07 (pushR64Effect 0x10ff07 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x10ff07 (PushPre 0x10ff07 2) (pushR64Effect 0x10ff07 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x10ff09 (pushR64Effect 0x10ff09 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x10ff09 (PushPre 0x10ff09 1) (pushR64Effect 0x10ff09 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10ff0a (subR64Imm32Effect 0x10ff0a 4 0x148) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10ff0a (fun s => s.RIP = 0x10ff0a) (subR64Imm32Effect 0x10ff0a 4 0x148) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10ff11 (movR64R64Effect 0x10ff11 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x10ff11 (fun s => s.RIP = 0x10ff11) (movR64R64Effect 0x10ff11 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x10ff14 (leaR64Effect 0x10ff14 14 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 70) (.exec 0x10ff14 (fun s => s.RIP = 0x10ff14) (leaR64Effect 0x10ff14 14 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 71) (.out 0x10ff1c (movR64R64Effect 0x10ff1c 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[69]
    (.letOp (n := 72) (.exec 0x10ff1c (fun s => s.RIP = 0x10ff1c) (movR64R64Effect 0x10ff1c 7 14) (Reg.operands [.gpr 14] [])) #v[69]
    (.letOp (n := 73) (.out 0x10ff1f (callEffect (fun _ => 0x120f30) 0x10ff24) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 74) (.exec 0x10ff1f (PushPre 0x10ff1f 5) (callEffect (fun _ => 0x120f30) 0x10ff24) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.const ⟨64, 0x10ff24⟩) #v[]
    (.terminate (.call ⟨.l120f30, RegMap.args [(1, 1), (3, 67), (4, 73), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ { target := .l10ff24, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l10ff00 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x48, 0x01, 0x00,
    0x00, 0x48, 0x89, 0xFB, 0x4C, 0x8D, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0xE8,
    0x0C, 0x10, 0x01, 0x00]

theorem code_l10ff00 : ∀ x ∈ codeRange 0x10ff00 bytes_l10ff00, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xff00 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10ff24 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10ff24 (leaR64Effect 0x10ff24 0 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10ff24 (fun s => s.RIP = 0x10ff24) (leaR64Effect 0x10ff24 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10ff2c (movR32Imm32Effect 0x10ff2c 5 1 0xb) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10ff2c (fun s => s.RIP = 0x10ff2c) (movR32Imm32Effect 0x10ff2c 5 1 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10ff31 (movR64R64Effect 0x10ff31 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x10ff31 (fun s => s.RIP = 0x10ff31) (movR64R64Effect 0x10ff31 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x10ff34 (movR64Imm32Effect 0x10ff34 6 0x202b70) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 60) (.exec 0x10ff34 (fun s => s.RIP = 0x10ff34) (movR64Imm32Effect 0x10ff34 6 0x202b70) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.exec 0x10ff3b (RepPre 0x10ff3b (RepMovsqPre 0x10ff3b)) (repMovsqEffect 0x10ff3b) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[59, 57, 55, 22]
    (.letOp (n := 62) (.out 0x10ff3e (movR32M32LowEffect 0x10ff3e 1 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x10ff3e (LoadPre 0x10ff3e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10ff3e + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10ff3e 1 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x10ff45 (StorePre 0x10ff45 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10ff45 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10ff45 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x10ff49 (leaR64Effect 0x10ff49 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x10ff49 (fun s => s.RIP = 0x10ff49) (leaR64Effect 0x10ff49 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x10ff4e (movR64R64Effect 0x10ff4e 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 68) (.exec 0x10ff4e (fun s => s.RIP = 0x10ff4e) (movR64R64Effect 0x10ff4e 6 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 69) (.out 0x10ff51 (movR64R64Effect 0x10ff51 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 70) (.exec 0x10ff51 (fun s => s.RIP = 0x10ff51) (movR64R64Effect 0x10ff51 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 71) (.out 0x10ff54 (callEffect (fun _ => 0x120470) 0x10ff59) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x10ff54 (PushPre 0x10ff54 5) (callEffect (fun _ => 0x120470) 0x10ff59) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x10ff59⟩) #v[]
    (.terminate (.call ⟨.l120470, RegMap.args [(0, 53), (1, 62), (2, 69), (3, 3), (4, 71), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l10ff59, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l10ff24 : List UInt8 :=
  [0x48, 0x8D, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0xB9, 0x0B, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC7,
    0x48, 0xC7, 0xC6, 0x70, 0x2B, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x8B, 0x8C, 0x24, 0xE8, 0x00, 0x00,
    0x00, 0x89, 0x4C, 0x24, 0x0C, 0x48, 0x8D, 0x7C, 0x24, 0x38, 0x48, 0x89, 0xC6, 0x4C, 0x89, 0xF2,
    0xE8, 0x17, 0x05, 0x01, 0x00]

theorem code_l10ff24 : ∀ x ∈ codeRange 0x10ff24 bytes_l10ff24, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xff24 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10ff59 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10ff59 (movR64M64Effect 0x10ff59 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10ff59 (LoadPre 0x10ff59 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10ff59 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff59 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10ff5e (StorePre 0x10ff5e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10ff5e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff5e 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10ff63 (movR64M64Effect 0x10ff63 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x10ff63 (LoadPre 0x10ff63 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10ff63 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff63 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10ff68 (StorePre 0x10ff68 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ff68 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff68 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x10ff6d (movR64M64Effect 0x10ff6d 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x10ff6d (LoadPre 0x10ff6d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10ff6d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff6d 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x10ff72 (StorePre 0x10ff72 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ff72 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff72 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x10ff77 (movR64M64Effect 0x10ff77 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x10ff77 (LoadPre 0x10ff77 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10ff77 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff77 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x10ff7c (StorePre 0x10ff7c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10ff7c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff7c 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x10ff81 (movR64M64Effect 0x10ff81 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x10ff81 (LoadPre 0x10ff81 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10ff81 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ff81 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x10ff89 (StorePre 0x10ff89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10ff89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff89 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x10ff8e (movR64M64Effect 0x10ff8e 13 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 69) (.exec 0x10ff8e (LoadPre 0x10ff8e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10ff8e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff8e 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x10ff93 (movR64M64Effect 0x10ff93 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 71) (.exec 0x10ff93 (LoadPre 0x10ff93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10ff93 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff93 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x10ff98 (movR64M64Effect 0x10ff98 14 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 73) (.exec 0x10ff98 (LoadPre 0x10ff98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10ff98 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff98 14 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x10ff9d (movR64M64Effect 0x10ff9d 15 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 75) (.exec 0x10ff9d (LoadPre 0x10ff9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10ff9d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff9d 15 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x10ffa2 (movR64M64Effect 0x10ffa2 12 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 77) (.exec 0x10ffa2 (LoadPre 0x10ffa2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10ffa2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ffa2 12 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x10ffa7 (movR32M32LowEffect 0x10ffa7 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 79) (.exec 0x10ffa7 (LoadPre 0x10ffa7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10ffa7 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10ffa7 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x10ffae (callEffect (fun _ => 0x127d50) 0x10ffb3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 81) (.exec 0x10ffae (PushPre 0x10ffae 5) (callEffect (fun _ => 0x127d50) 0x10ffb3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.const ⟨64, 0x10ffb3⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 65), (1, 1), (2, 2), (3, 3), (4, 80), (5, 70), (6, 6), (7, 78), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 68), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩ { target := .l10ffb3, kept := #v[], arity := rfl, guard := some (Fin.last 82) })))))))))))))))))))))))))))))))

def bytes_l10ff59 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B,
    0x44, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x44, 0x24, 0x30, 0x4C, 0x8B, 0x6C, 0x24, 0x38, 0x48, 0x8B, 0x6C, 0x24, 0x40, 0x4C,
    0x8B, 0x74, 0x24, 0x48, 0x4C, 0x8B, 0x7C, 0x24, 0x50, 0x4C, 0x8B, 0x64, 0x24, 0x58, 0x8B, 0xBC,
    0x24, 0x88, 0x00, 0x00, 0x00, 0xE8, 0x9D, 0x7D, 0x01, 0x00]

theorem code_l10ff59 : ∀ x ∈ codeRange 0x10ff59 bytes_l10ff59, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xff59 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10ffb3_2 : Block Op Label signature Reg.count 117 :=
  .letOp (n := 117) (.out 0x110054 (movR64R64Effect 0x110054 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 118) (.exec 0x110054 (fun s => s.RIP = 0x110054) (movR64R64Effect 0x110054 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 119) (.out 0x110057 (addR64Imm32Effect 0x110057 4 0x148) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 120) (.exec 0x110057 (fun s => s.RIP = 0x110057) (addR64Imm32Effect 0x110057 4 0x148) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 121) (.out 0x11005e (popR64Effect 0x11005e 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[119]
    (.letOp (n := 122) (.out 0x11005e (popR64Effect 0x11005e 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[119]
    (.letOp (n := 123) (.exec 0x11005e (PopPre 0x11005e) (popR64Effect 0x11005e 1 3) (Reg.operands [.gpr 4] [])) #v[119]
    (.letOp (n := 124) (.out 0x11005f (popR64Effect 0x11005f 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[122]
    (.letOp (n := 125) (.out 0x11005f (popR64Effect 0x11005f 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[122]
    (.letOp (n := 126) (.exec 0x11005f (PopPre 0x11005f) (popR64Effect 0x11005f 2 12) (Reg.operands [.gpr 4] [])) #v[122]
    (.letOp (n := 127) (.out 0x110061 (popR64Effect 0x110061 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[125]
    (.letOp (n := 128) (.out 0x110061 (popR64Effect 0x110061 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[125]
    (.letOp (n := 129) (.exec 0x110061 (PopPre 0x110061) (popR64Effect 0x110061 2 13) (Reg.operands [.gpr 4] [])) #v[125]
    (.letOp (n := 130) (.out 0x110063 (popR64Effect 0x110063 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[128]
    (.letOp (n := 131) (.out 0x110063 (popR64Effect 0x110063 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[128]
    (.letOp (n := 132) (.exec 0x110063 (PopPre 0x110063) (popR64Effect 0x110063 2 14) (Reg.operands [.gpr 4] [])) #v[128]
    (.letOp (n := 133) (.out 0x110065 (popR64Effect 0x110065 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[131]
    (.letOp (n := 134) (.out 0x110065 (popR64Effect 0x110065 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[131]
    (.letOp (n := 135) (.exec 0x110065 (PopPre 0x110065) (popR64Effect 0x110065 2 15) (Reg.operands [.gpr 4] [])) #v[131]
    (.letOp (n := 136) (.out 0x110067 (popR64Effect 0x110067 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[134]
    (.letOp (n := 137) (.out 0x110067 (popR64Effect 0x110067 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[134]
    (.letOp (n := 138) (.exec 0x110067 (PopPre 0x110067) (popR64Effect 0x110067 1 5) (Reg.operands [.gpr 4] [])) #v[134]
    (.letOp (n := 139) (.out 0x110068 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[137]
    (.letOp (n := 140) (.out 0x110068 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[137]
    (.letOp (n := 141) (.exec 0x110068 (RetPre 0x110068) (retEffect) (Reg.operands [.gpr 4] [])) #v[137]
    (.terminate (.ret (RegMap.args [(0, 117), (1, 111), (2, 67), (3, 121), (4, 140), (5, 136), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 124), (13, 127), (14, 130), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)] 142) (some ⟨139, by decide⟩)))))))))))))))))))))))))))

def bytes_l10ffb3_2 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0x48, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10ffb3_2 : ∀ x ∈ codeRange 0x110054 bytes_l10ffb3_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10054 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10ffb3_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x10fff8 (andR64M64Effect 0x10fff8 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[69, 4]
    (.letOp (n := 94) (.exec 0x10fff8 (LoadPre 0x10fff8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10fff8 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x10fff8 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 95) (.exec 0x10fffd (StorePre 0x10fffd 8 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x10fffd + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10fffd (.base 3 (.d8 0x58)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 96) (.exec 0x110005 (StorePre 0x110005 8 (fun s => AddrMode.addr (.base 3 (.d8 0x60)) s (0x110005 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x110005 (.base 3 (.d8 0x60)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 97) (.exec 0x11000d (StorePre 0x11000d 8 (fun s => AddrMode.addr (.base 3 (.d8 0x68)) s (0x11000d + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x11000d (.base 3 (.d8 0x68)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 98) (.exec 0x110015 (StorePre 0x110015 8 (fun s => AddrMode.addr (.base 3 (.d8 0x70)) s (0x110015 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x110015 (.base 3 (.d8 0x70)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 99) (.exec 0x11001d (StorePre 0x11001d 3 (fun s => AddrMode.addr (.base 3 .none) s (0x11001d + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11001d 13 (.base 3 .none)) (Reg.operands [.gpr 13, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 100) (.exec 0x110020 (StorePre 0x110020 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x110020 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110020 5 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[73, 3]
    (.letOp (n := 101) (.exec 0x110024 (StorePre 0x110024 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x110024 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110024 14 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 102) (.exec 0x110028 (StorePre 0x110028 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x110028 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110028 15 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[77, 3]
    (.letOp (n := 103) (.exec 0x11002c (StorePre 0x11002c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x11002c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11002c 12 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 104) (.exec 0x110030 (StorePre 0x110030 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x110030 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110030 2 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 105) (.exec 0x110034 (StorePre 0x110034 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x110034 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110034 6 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[83, 3]
    (.letOp (n := 106) (.exec 0x110038 (StorePre 0x110038 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x110038 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110038 7 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[87, 3]
    (.letOp (n := 107) (.exec 0x11003c (StorePre 0x11003c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x11003c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11003c 8 (.base 3 (.d8 0x40))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[91, 3]
    (.letOp (n := 108) (.exec 0x110040 (StorePre 0x110040 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x110040 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110040 0 (.base 3 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[93, 3]
    (.letOp (n := 109) (.out 0x110044 (notR32Effect 0x110044 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 110) (.exec 0x110044 (fun s => s.RIP = 0x110044) (notR32Effect 0x110044 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 111) (.out 0x110046 (andR32Imm8Effect 0x110046 3 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[109]
    (.letOp (n := 112) (.exec 0x110046 (fun s => s.RIP = 0x110046) (andR32Imm8Effect 0x110046 3 1 0x1) (Reg.operands [.gpr 1] [])) #v[109]
    (.letOp (n := 113) (.exec 0x110049 (StorePre 0x110049 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x110049 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110049 1 (.base 3 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[111, 3]
    (.letOp (n := 114) (.out 0x11004d (movR32M32LowEffect 0x11004d 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 115) (.exec 0x11004d (LoadPre 0x11004d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x11004d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x11004d 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 116) (.exec 0x110051 (StorePre 0x110051 3 (fun s => AddrMode.addr (.base 3 (.d8 0x78)) s (0x110051 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110051 3 0 (.base 3 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[114, 3]
    (b_l10ffb3_2))))))))))))))))))))))))

def bytes_l10ffb3_1 : List UInt8 :=
  [0x48, 0x23, 0x44, 0x24, 0x30, 0x48, 0xC7, 0x43, 0x58, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x43,
    0x60, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x43, 0x68, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x43,
    0x70, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x2B, 0x48, 0x89, 0x6B, 0x08, 0x4C, 0x89, 0x73, 0x10,
    0x4C, 0x89, 0x7B, 0x18, 0x4C, 0x89, 0x63, 0x20, 0x48, 0x89, 0x53, 0x28, 0x48, 0x89, 0x73, 0x30,
    0x48, 0x89, 0x7B, 0x38, 0x4C, 0x89, 0x43, 0x40, 0x48, 0x89, 0x43, 0x48, 0xF7, 0xD1, 0x83, 0xE1,
    0x01, 0x48, 0x89, 0x4B, 0x50, 0x8B, 0x44, 0x24, 0x0C, 0x88, 0x43, 0x78] ++ bytes_l10ffb3_2

theorem code_l10ffb3_1 : ∀ x ∈ codeRange 0x10fff8 bytes_l10ffb3_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xfff8 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10ffb3_2

@[cfg_block] def b_l10ffb3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10ffb3 (movzxR32R8Effect 0x10ffb3 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x10ffb3 (fun s => s.RIP = 0x10ffb3) (movzxR32R8Effect 0x10ffb3 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x10ffb6 (movR64R64Effect 0x10ffb6 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x10ffb6 (fun s => s.RIP = 0x10ffb6) (movR64R64Effect 0x10ffb6 1 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x10ffb9 (negR64Effect 0x10ffb9 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x10ffb9 (fun s => s.RIP = 0x10ffb9) (negR64Effect 0x10ffb9 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 59) (.out 0x10ffbc (movR64M64Effect 0x10ffbc 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x10ffbc (LoadPre 0x10ffbc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10ffbc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ffbc 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10ffc1 (movR64R64Effect 0x10ffc1 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 62) (.exec 0x10ffc1 (fun s => s.RIP = 0x10ffc1) (movR64R64Effect 0x10ffc1 2 6) (Reg.operands [.gpr 6] [])) #v[59]
    (.letOp (n := 63) (.out 0x10ffc4 (xorR64Imm8Effect 0x10ffc4 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 64) (.exec 0x10ffc4 (fun s => s.RIP = 0x10ffc4) (xorR64Imm8Effect 0x10ffc4 2 0x1) (Reg.operands [.gpr 2] [])) #v[61]
    (.letOp (n := 65) (.out 0x10ffc8 (andR64R64Effect 0x10ffc8 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[63, 57]
    (.letOp (n := 66) (.exec 0x10ffc8 (fun s => s.RIP = 0x10ffc8) (andR64R64Effect 0x10ffc8 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[63, 57]
    (.letOp (n := 67) (.out 0x10ffcb (xorR64R64Effect 0x10ffcb 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[65, 59]
    (.letOp (n := 68) (.exec 0x10ffcb (fun s => s.RIP = 0x10ffcb) (xorR64R64Effect 0x10ffcb 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[65, 59]
    (.letOp (n := 69) (.out 0x10ffce (decR64Effect 0x10ffce 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 70) (.exec 0x10ffce (fun s => s.RIP = 0x10ffce) (decR64Effect 0x10ffce 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 71) (.out 0x10ffd1 (andR64R64Effect 0x10ffd1 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[13, 69]
    (.letOp (n := 72) (.exec 0x10ffd1 (fun s => s.RIP = 0x10ffd1) (andR64R64Effect 0x10ffd1 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[13, 69]
    (.letOp (n := 73) (.out 0x10ffd4 (andR64R64Effect 0x10ffd4 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[5, 69]
    (.letOp (n := 74) (.exec 0x10ffd4 (fun s => s.RIP = 0x10ffd4) (andR64R64Effect 0x10ffd4 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[5, 69]
    (.letOp (n := 75) (.out 0x10ffd7 (andR64R64Effect 0x10ffd7 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[14, 69]
    (.letOp (n := 76) (.exec 0x10ffd7 (fun s => s.RIP = 0x10ffd7) (andR64R64Effect 0x10ffd7 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[14, 69]
    (.letOp (n := 77) (.out 0x10ffda (andR64R64Effect 0x10ffda 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[15, 69]
    (.letOp (n := 78) (.exec 0x10ffda (fun s => s.RIP = 0x10ffda) (andR64R64Effect 0x10ffda 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[15, 69]
    (.letOp (n := 79) (.out 0x10ffdd (andR64R64Effect 0x10ffdd 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[12, 69]
    (.letOp (n := 80) (.exec 0x10ffdd (fun s => s.RIP = 0x10ffdd) (andR64R64Effect 0x10ffdd 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[12, 69]
    (.letOp (n := 81) (.out 0x10ffe0 (movR64M64Effect 0x10ffe0 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 82) (.exec 0x10ffe0 (LoadPre 0x10ffe0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ffe0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ffe0 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x10ffe5 (andR64R64Effect 0x10ffe5 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[81, 69]
    (.letOp (n := 84) (.exec 0x10ffe5 (fun s => s.RIP = 0x10ffe5) (andR64R64Effect 0x10ffe5 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[81, 69]
    (.letOp (n := 85) (.out 0x10ffe8 (movR64M64Effect 0x10ffe8 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 86) (.exec 0x10ffe8 (LoadPre 0x10ffe8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ffe8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ffe8 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x10ffed (andR64R64Effect 0x10ffed 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[85, 69]
    (.letOp (n := 88) (.exec 0x10ffed (fun s => s.RIP = 0x10ffed) (andR64R64Effect 0x10ffed 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[85, 69]
    (.letOp (n := 89) (.out 0x10fff0 (movR64M64Effect 0x10fff0 8 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 90) (.exec 0x10fff0 (LoadPre 0x10fff0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10fff0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fff0 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.out 0x10fff5 (andR64R64Effect 0x10fff5 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[89, 69]
    (.letOp (n := 92) (.exec 0x10fff5 (fun s => s.RIP = 0x10fff5) (andR64R64Effect 0x10fff5 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[89, 69]
    (b_l10ffb3_1))))))))))))))))))))))))))))))))))))))))

def bytes_l10ffb3 : List UInt8 :=
  [0x0F, 0xB6, 0xC0, 0x48, 0x89, 0xC1, 0x48, 0xF7, 0xD9, 0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x89,
    0xF2, 0x48, 0x83, 0xF2, 0x01, 0x48, 0x21, 0xCA, 0x48, 0x31, 0xF2, 0x48, 0xFF, 0xC8, 0x49, 0x21,
    0xC5, 0x48, 0x21, 0xC5, 0x49, 0x21, 0xC6, 0x49, 0x21, 0xC7, 0x49, 0x21, 0xC4, 0x48, 0x8B, 0x74,
    0x24, 0x18, 0x48, 0x21, 0xC6, 0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x21, 0xC7, 0x4C, 0x8B, 0x44,
    0x24, 0x28, 0x49, 0x21, 0xC0] ++ bytes_l10ffb3_1

theorem code_l10ffb3 : ∀ x ∈ codeRange 0x10ffb3 bytes_l10ffb3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xffb3 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10ffb3_1

@[cfg_block] def b_l110070 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110070 (pushR64Effect 0x110070 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 14]
    (.letOp (n := 54) (.exec 0x110070 (PushPre 0x110070 2) (pushR64Effect 0x110070 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 55) (.out 0x110072 (pushR64Effect 0x110072 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x110072 (PushPre 0x110072 1) (pushR64Effect 0x110072 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x110073 (subR64Imm8Effect 0x110073 4 0x58) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 58) (.exec 0x110073 (fun s => s.RIP = 0x110073) (subR64Imm8Effect 0x110073 4 0x58) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 59) (.out 0x110077 (movR64R64Effect 0x110077 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 60) (.exec 0x110077 (fun s => s.RIP = 0x110077) (movR64R64Effect 0x110077 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 61) (.out 0x11007a (movR64R64Effect 0x11007a 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[57]
    (.letOp (n := 62) (.exec 0x11007a (fun s => s.RIP = 0x11007a) (movR64R64Effect 0x11007a 14 4) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 63) (.out 0x11007d (movR64R64Effect 0x11007d 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 64) (.exec 0x11007d (fun s => s.RIP = 0x11007d) (movR64R64Effect 0x11007d 7 14) (Reg.operands [.gpr 14] [])) #v[61]
    (.letOp (n := 65) (.out 0x110080 (callEffect (fun _ => 0x10ece0) 0x110085) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 66) (.exec 0x110080 (PushPre 0x110080 5) (callEffect (fun _ => 0x10ece0) 0x110085) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 67) (.const ⟨64, 0x110085⟩) #v[]
    (.terminate (.call ⟨.l10ece0, RegMap.args [(3, 59), (4, 65), (5, 5), (6, 6), (7, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l110085, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l110070 : List UInt8 :=
  [0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x58, 0x48, 0x89, 0xFB, 0x49, 0x89, 0xE6, 0x4C, 0x89, 0xF7,
    0xE8, 0x5B, 0xEC, 0xFF, 0xFF]

theorem code_l110070 : ∀ x ∈ codeRange 0x110070 bytes_l110070, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10070 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110085 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110085 (movR64R64Effect 0x110085 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x110085 (fun s => s.RIP = 0x110085) (movR64R64Effect 0x110085 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x110088 (movR64R64Effect 0x110088 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x110088 (fun s => s.RIP = 0x110088) (movR64R64Effect 0x110088 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x11008b (callEffect (fun _ => 0x1211b0) 0x110090) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x11008b (PushPre 0x11008b 5) (callEffect (fun _ => 0x1211b0) 0x110090) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x110090⟩) #v[]
    (.terminate (.call ⟨.l1211b0, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l110090, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l110085 : List UInt8 :=
  [0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x20, 0x11, 0x01, 0x00]

theorem code_l110085 : ∀ x ∈ codeRange 0x110085 bytes_l110085, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10085 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110090 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110090 (movR64R64Effect 0x110090 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x110090 (fun s => s.RIP = 0x110090) (movR64R64Effect 0x110090 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x110093 (addR64Imm8Effect 0x110093 4 0x58) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x110093 (fun s => s.RIP = 0x110093) (addR64Imm8Effect 0x110093 4 0x58) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x110097 (popR64Effect 0x110097 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x110097 (popR64Effect 0x110097 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x110097 (PopPre 0x110097) (popR64Effect 0x110097 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x110098 (popR64Effect 0x110098 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.out 0x110098 (popR64Effect 0x110098 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x110098 (PopPre 0x110098) (popR64Effect 0x110098 2 14) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x11009a (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[61]
    (.letOp (n := 64) (.out 0x11009a (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x11009a (RetPre 0x11009a) (retEffect) (Reg.operands [.gpr 4] [])) #v[61]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66) (some ⟨63, by decide⟩)))))))))))))))

def bytes_l110090 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x58, 0x5B, 0x41, 0x5E, 0xC3]

theorem code_l110090 : ∀ x ∈ codeRange 0x110090 bytes_l110090, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10090 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1100a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1100a0 (pushR64Effect 0x1100a0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1100a0 (PushPre 0x1100a0 1) (pushR64Effect 0x1100a0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1100a1 (pushR64Effect 0x1100a1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1100a1 (PushPre 0x1100a1 2) (pushR64Effect 0x1100a1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1100a3 (pushR64Effect 0x1100a3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1100a3 (PushPre 0x1100a3 2) (pushR64Effect 0x1100a3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1100a5 (pushR64Effect 0x1100a5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1100a5 (PushPre 0x1100a5 2) (pushR64Effect 0x1100a5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1100a7 (pushR64Effect 0x1100a7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1100a7 (PushPre 0x1100a7 2) (pushR64Effect 0x1100a7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1100a9 (pushR64Effect 0x1100a9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1100a9 (PushPre 0x1100a9 1) (pushR64Effect 0x1100a9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1100aa (subR64Imm32Effect 0x1100aa 4 0x1a8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1100aa (fun s => s.RIP = 0x1100aa) (subR64Imm32Effect 0x1100aa 4 0x1a8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1100b1 (movR64R64Effect 0x1100b1 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 68) (.exec 0x1100b1 (fun s => s.RIP = 0x1100b1) (movR64R64Effect 0x1100b1 15 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.exec 0x1100b4 (StorePre 0x1100b4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1100b4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1100b4 7 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 70) (.out 0x1100bc (movR64M64Effect 0x1100bc 13 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 71) (.exec 0x1100bc (LoadPre 0x1100bc (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1100bc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100bc 13 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 72) (.out 0x1100c0 (testR64R64Effect 0x1100c0 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[70, 70]
    (.letOp (n := 73) (.exec 0x1100c0 (fun s => s.RIP = 0x1100c0) (testR64R64Effect 0x1100c0 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[70, 70]
    (.letOp (n := 74) (.pure (condOp 4)) #v[72]
    (.terminate (.condBr (Fin.last 74) ⟨.l1100db, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 70), (14, 14), (15, 67), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ ⟨.l1100c5, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 70), (14, 14), (15, 67), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l1100a0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xA8, 0x01, 0x00,
    0x00, 0x49, 0x89, 0xF7, 0x48, 0x89, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x6E, 0x10,
    0x4D, 0x85, 0xED, 0x74, 0x16]

theorem code_l1100a0 : ∀ x ∈ codeRange 0x1100a0 bytes_l1100a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x100a0 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1100c5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1100c5 (movR64M64Effect 0x1100c5 2 (.base 15 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 54) (.exec 0x1100c5 (LoadPre 0x1100c5 (fun s => AddrMode.addr (.base 15 (.d8 0x18)) s (0x1100c5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100c5 2 (.base 15 (.d8 0x18))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x1100c9 (movR64M64Effect 0x1100c9 1 (.base 15 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 56) (.exec 0x1100c9 (LoadPre 0x1100c9 (fun s => AddrMode.addr (.base 15 (.d8 0x20)) s (0x1100c9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100c9 1 (.base 15 (.d8 0x20))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x1100cd (movR64M64Effect 0x1100cd 7 (.base 15 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 58) (.exec 0x1100cd (LoadPre 0x1100cd (fun s => AddrMode.addr (.base 15 (.d8 0x28)) s (0x1100cd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100cd 7 (.base 15 (.d8 0x28))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x1100d1 (movR64M64Effect 0x1100d1 0 (.base 15 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 60) (.exec 0x1100d1 (LoadPre 0x1100d1 (fun s => AddrMode.addr (.base 15 (.d8 0x30)) s (0x1100d1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100d1 0 (.base 15 (.d8 0x30))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.out 0x1100d5 (movR64M64Effect 0x1100d5 6 (.base 15 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 62) (.exec 0x1100d5 (LoadPre 0x1100d5 (fun s => AddrMode.addr (.base 15 (.d8 0x38)) s (0x1100d5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100d5 6 (.base 15 (.d8 0x38))) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l1100db, RegMap.args [(0, 59), (1, 55), (2, 53), (3, 3), (4, 4), (6, 61), (7, 57), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l1100c5 : List UInt8 :=
  [0x49, 0x8B, 0x57, 0x18, 0x49, 0x8B, 0x4F, 0x20, 0x49, 0x8B, 0x7F, 0x28, 0x49, 0x8B, 0x47, 0x30,
    0x49, 0x8B, 0x77, 0x38, 0xEB, 0x00]

theorem code_l1100c5 : ∀ x ∈ codeRange 0x1100c5 bytes_l1100c5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x100c5 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1100db : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1100db (StorePre 0x1100db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1100db + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1100db 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 54) (.out 0x1100e0 (movR64M64Effect 0x1100e0 5 (.base 15 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 15] []) (.reg (.gpr 5))) #v[15]
    (.letOp (n := 55) (.exec 0x1100e0 (LoadPre 0x1100e0 (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x1100e0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100e0 5 (.base 15 (.d8 0x8))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 56) (.out 0x1100e4 (movR64M64Effect 0x1100e4 8 (.base 15 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[15]
    (.letOp (n := 57) (.exec 0x1100e4 (LoadPre 0x1100e4 (fun s => AddrMode.addr (.base 15 (.d8 0x40)) s (0x1100e4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100e4 8 (.base 15 (.d8 0x40))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 58) (.exec 0x1100e8 (StorePre 0x1100e8 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1100e8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1100e8 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 8, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1100ec (testR64R64Effect 0x1100ec 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[56, 56]
    (.letOp (n := 60) (.exec 0x1100ec (fun s => s.RIP = 0x1100ec) (testR64R64Effect 0x1100ec 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[56, 56]
    (.letOp (n := 61) (.pure (condOp 4)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l110107, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (7, 7), (8, 56), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l1100f1, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (7, 7), (8, 56), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l1100db : List UInt8 :=
  [0x48, 0x89, 0x7C, 0x24, 0x18, 0x49, 0x8B, 0x6F, 0x08, 0x4D, 0x8B, 0x47, 0x40, 0x4C, 0x89, 0x04,
    0x24, 0x4D, 0x85, 0xC0, 0x74, 0x16]

theorem code_l1100db : ∀ x ∈ codeRange 0x1100db bytes_l1100db, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x100db 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1100f1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1100f1 (movR64M64Effect 0x1100f1 11 (.base 15 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 15] []) (.reg (.gpr 11))) #v[15]
    (.letOp (n := 54) (.exec 0x1100f1 (LoadPre 0x1100f1 (fun s => AddrMode.addr (.base 15 (.d8 0x48)) s (0x1100f1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100f1 11 (.base 15 (.d8 0x48))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x1100f5 (movR64M64Effect 0x1100f5 8 (.base 15 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[15]
    (.letOp (n := 56) (.exec 0x1100f5 (LoadPre 0x1100f5 (fun s => AddrMode.addr (.base 15 (.d8 0x50)) s (0x1100f5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100f5 8 (.base 15 (.d8 0x50))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x1100f9 (movR64M64Effect 0x1100f9 3 (.base 15 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[15]
    (.letOp (n := 58) (.exec 0x1100f9 (LoadPre 0x1100f9 (fun s => AddrMode.addr (.base 15 (.d8 0x58)) s (0x1100f9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100f9 3 (.base 15 (.d8 0x58))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x1100fd (movR64M64Effect 0x1100fd 9 (.base 15 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 15] []) (.reg (.gpr 9))) #v[15]
    (.letOp (n := 60) (.exec 0x1100fd (LoadPre 0x1100fd (fun s => AddrMode.addr (.base 15 (.d8 0x60)) s (0x1100fd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1100fd 9 (.base 15 (.d8 0x60))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.out 0x110101 (movR64M64Effect 0x110101 10 (.base 15 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 15] []) (.reg (.gpr 10))) #v[15]
    (.letOp (n := 62) (.exec 0x110101 (LoadPre 0x110101 (fun s => AddrMode.addr (.base 15 (.d8 0x68)) s (0x110101 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110101 10 (.base 15 (.d8 0x68))) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l110107, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 59), (10, 61), (11, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l1100f1 : List UInt8 :=
  [0x4D, 0x8B, 0x5F, 0x48, 0x4D, 0x8B, 0x47, 0x50, 0x49, 0x8B, 0x5F, 0x58, 0x4D, 0x8B, 0x4F, 0x60,
    0x4D, 0x8B, 0x57, 0x68, 0xEB, 0x00]

theorem code_l1100f1 : ∀ x ∈ codeRange 0x1100f1 bytes_l1100f1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x100f1 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110107 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110107 (movR64M64Effect 0x110107 14 (.base 15 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 15] []) (.reg (.gpr 14))) #v[15]
    (.letOp (n := 54) (.exec 0x110107 (LoadPre 0x110107 (fun s => AddrMode.addr (.base 15 .none) s (0x110107 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110107 14 (.base 15 .none)) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x11010a (testR64R64Effect 0x11010a 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[13, 13]
    (.letOp (n := 56) (.exec 0x11010a (fun s => s.RIP = 0x11010a) (testR64R64Effect 0x11010a 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 57) (.out 0x11010d (atFlags (condHolds 5) (setccR8Effect 0x11010d 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[7, 55]
    (.letOp (n := 58) (.exec 0x11010d (fun s => s.RIP = 0x11010d) (atFlags (condHolds 5) (setccR8Effect 0x11010d 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[7, 55]
    (.letOp (n := 59) (.exec 0x110111 (StorePre 0x110111 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x110111 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110111 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 60) (.out 0x110116 (movR64M64Effect 0x110116 12 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 61) (.exec 0x110116 (LoadPre 0x110116 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110116 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110116 12 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x11011a (StorePre 0x11011a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11011a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11011a 12 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.exec 0x110122 (StorePre 0x110122 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x110122 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110122 11 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.letOp (n := 64) (.exec 0x11012a (StorePre 0x11012a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11012a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11012a 8 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 65) (.exec 0x110132 (StorePre 0x110132 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x110132 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110132 3 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 66) (.exec 0x11013a (StorePre 0x11013a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11013a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11013a 9 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 67) (.exec 0x110142 (StorePre 0x110142 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x110142 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110142 10 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 68) (.out 0x11014a (cmpR64R64Effect 0x11014a 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[0, 6]
    (.letOp (n := 69) (.exec 0x11014a (fun s => s.RIP = 0x11014a) (cmpR64R64Effect 0x11014a 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[0, 6]
    (.letOp (n := 70) (.out 0x11014d (atFlags (condHolds 2) (setccR8Effect 0x11014d 4 11)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[11, 68]
    (.letOp (n := 71) (.exec 0x11014d (fun s => s.RIP = 0x11014d) (atFlags (condHolds 2) (setccR8Effect 0x11014d 4 11)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[11, 68]
    (.letOp (n := 72) (.out 0x110151 (testR8R8Effect 0x110151 3 7 11) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 11] []) (.flag .ZF)) #v[57, 70]
    (.letOp (n := 73) (.exec 0x110151 (fun s => s.RIP = 0x110151) (testR8R8Effect 0x110151 3 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[57, 70]
    (.letOp (n := 74) (.pure (condOp 5)) #v[72]
    (.terminate (.condBr (Fin.last 74) ⟨.l110188, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 70), (12, 60), (13, 13), (14, 53), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ ⟨.l110156, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 70), (12, 60), (13, 13), (14, 53), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l110107 : List UInt8 :=
  [0x4D, 0x8B, 0x37, 0x4D, 0x85, 0xED, 0x40, 0x0F, 0x95, 0xC7, 0x48, 0x89, 0x6C, 0x24, 0x60, 0x4C,
    0x8B, 0x24, 0x24, 0x4C, 0x89, 0xA4, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x9C, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x9C, 0x24, 0xB0,
    0x00, 0x00, 0x00, 0x4C, 0x89, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x94, 0x24, 0xC0,
    0x00, 0x00, 0x00, 0x48, 0x39, 0xF0, 0x41, 0x0F, 0x92, 0xC3, 0x44, 0x84, 0xDF, 0x75, 0x32]

theorem code_l110107 : ∀ x ∈ codeRange 0x110107 bytes_l110107, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10107 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110156 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110156 (testR64R64Effect 0x110156 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 54) (.exec 0x110156 (fun s => s.RIP = 0x110156) (testR64R64Effect 0x110156 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1106e9, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11015f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l110156 : List UInt8 :=
  [0x4D, 0x85, 0xF6, 0x0F, 0x84, 0x8A, 0x05, 0x00, 0x00]

theorem code_l110156 : ∀ x ∈ codeRange 0x110156 bytes_l110156, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10156 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11015f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11015f (cmpR64R64Effect 0x11015f 14 5) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 5] []) (.flag .ZF)) #v[14, 5]
    (.letOp (n := 54) (.exec 0x11015f (fun s => s.RIP = 0x11015f) (cmpR64R64Effect 0x11015f 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[14, 5]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1106e9, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l110168, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11015f : List UInt8 :=
  [0x49, 0x39, 0xEE, 0x0F, 0x84, 0x81, 0x05, 0x00, 0x00]

theorem code_l11015f : ∀ x ∈ codeRange 0x11015f bytes_l11015f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1015f 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110168 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110168 (leaR64Effect 0x110168 7 (.base 14 (.d32 0x9a0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x110168 (fun s => s.RIP = 0x110168) (leaR64Effect 0x110168 7 (.base 14 (.d32 0x9a0))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x11016f (leaR64Effect 0x11016f 1 (.base 14 (.d32 0x780))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 56) (.exec 0x11016f (fun s => s.RIP = 0x11016f) (leaR64Effect 0x11016f 1 (.base 14 (.d32 0x780))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x110176 (movR32Imm32Effect 0x110176 5 6 0x2) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x110176 (fun s => s.RIP = 0x110176) (movR32Imm32Effect 0x110176 5 6 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x11017b (xorR32R32Effect 0x11017b 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 60) (.exec 0x11017b (fun s => s.RIP = 0x11017b) (xorR32R32Effect 0x11017b 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 61) (.out 0x11017d (movR64R64Effect 0x11017d 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 62) (.exec 0x11017d (fun s => s.RIP = 0x11017d) (movR64R64Effect 0x11017d 2 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 63) (.out 0x110180 (movR64R64Effect 0x110180 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[14]
    (.letOp (n := 64) (.exec 0x110180 (fun s => s.RIP = 0x110180) (movR64R64Effect 0x110180 8 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.out 0x110183 (movR64R64Effect 0x110183 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 66) (.exec 0x110183 (fun s => s.RIP = 0x110183) (movR64R64Effect 0x110183 9 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.terminate (.br ⟨.l110193, RegMap.args [(0, 59), (1, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 63), (9, 65), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l110168 : List UInt8 :=
  [0x49, 0x8D, 0xBE, 0xA0, 0x09, 0x00, 0x00, 0x49, 0x8D, 0x8E, 0x80, 0x07, 0x00, 0x00, 0xBE, 0x02,
    0x00, 0x00, 0x00, 0x31, 0xC0, 0x48, 0x89, 0xCA, 0x4D, 0x89, 0xF0, 0x49, 0x89, 0xF9, 0xEB, 0x0B]

theorem code_l110168 : ∀ x ∈ codeRange 0x110168 bytes_l110168, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10168 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110188 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110188 (movR64R64Effect 0x110188 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 13] []) (.reg (.gpr 8))) #v[13]
    (.letOp (n := 54) (.exec 0x110188 (fun s => s.RIP = 0x110188) (movR64R64Effect 0x110188 8 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x11018b (movR64R64Effect 0x11018b 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[14]
    (.letOp (n := 56) (.exec 0x11018b (fun s => s.RIP = 0x11018b) (movR64R64Effect 0x11018b 9 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x11018e (movR64M64Effect 0x11018e 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x11018e (LoadPre 0x11018e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11018e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11018e 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l110193, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 53), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l110188 : List UInt8 :=
  [0x4D, 0x89, 0xE8, 0x4D, 0x89, 0xF1, 0x48, 0x8B, 0x7C, 0x24, 0x18]

theorem code_l110188 : ∀ x ∈ codeRange 0x110188 bytes_l110188, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10188 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110193 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x110193 (StorePre 0x110193 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x110193 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110193 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 54) (.exec 0x110198 (StorePre 0x110198 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x110198 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110198 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 55) (.exec 0x11019d (StorePre 0x11019d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11019d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11019d 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 56) (.exec 0x1101a5 (StorePre 0x1101a5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1101a5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1101a5 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 57) (.exec 0x1101ad (StorePre 0x1101ad 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1101ad + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1101ad 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 58) (.exec 0x1101b2 (StorePre 0x1101b2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1101b2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1101b2 9 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 59) (.out 0x1101b7 (leaR64Effect 0x1101b7 2 (.base 0 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[0]
    (.letOp (n := 60) (.exec 0x1101b7 (fun s => s.RIP = 0x1101b7) (leaR64Effect 0x1101b7 2 (.base 0 (.d8 0x1))) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 61) (.exec 0x1101bb (StorePre 0x1101bb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1101bb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1101bb 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1101c3 (movR64R64Effect 0x1101c3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1]
    (.letOp (n := 63) (.exec 0x1101c3 (fun s => s.RIP = 0x1101c3) (movR64R64Effect 0x1101c3 8 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 64) (.out 0x1101c6 (movR64R64Effect 0x1101c6 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[0]
    (.letOp (n := 65) (.exec 0x1101c6 (fun s => s.RIP = 0x1101c6) (movR64R64Effect 0x1101c6 9 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l1101c9, RegMap.args [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 62), (9, 64), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l110193 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x70, 0x48, 0x89, 0x4C, 0x24, 0x78, 0x48, 0x89, 0xBC, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x48, 0x89, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x44, 0x24, 0x68, 0x4C,
    0x89, 0x4C, 0x24, 0x58, 0x48, 0x8D, 0x50, 0x01, 0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x49, 0x89, 0xC8, 0x49, 0x89, 0xC1]

theorem code_l110193 : ∀ x ∈ codeRange 0x110193 bytes_l110193, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10193 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1101c9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1101c9 (imulR64R64Imm32Effect 0x1101c9 7 0 9 0x110) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[9]
    (.letOp (n := 54) (.exec 0x1101c9 (fun s => s.RIP = 0x1101c9) (imulR64R64Imm32Effect 0x1101c9 7 0 9 0x110) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x1101d0 (movR64M64Effect 0x1101d0 6 (.sib 8 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8, .gpr 0] []) (.reg (.gpr 6))) #v[8, 53]
    (.letOp (n := 56) (.exec 0x1101d0 (LoadPre 0x1101d0 (fun s => AddrMode.addr (.sib 8 (some 0) 0 .none) s (0x1101d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1101d0 6 (.sib 8 (some 0) 0 .none)) (Reg.operands [.gpr 8, .gpr 0] [])) #v[8, 53]
    (.letOp (n := 57) (.out 0x1101d4 (leaR64Effect 0x1101d4 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x1101d4 (fun s => s.RIP = 0x1101d4) (leaR64Effect 0x1101d4 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1101d9 (callEffect (fun _ => 0x11c0b0) 0x1101de) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1101d9 (PushPre 0x1101d9 5) (callEffect (fun _ => 0x11c0b0) 0x1101de) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1101de⟩) #v[]
    (.terminate (.call ⟨.l11c0b0, RegMap.args [(0, 53), (3, 3), (4, 59), (5, 5), (6, 55), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1101de, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1101c9 : List UInt8 :=
  [0x49, 0x69, 0xC1, 0x10, 0x01, 0x00, 0x00, 0x49, 0x8B, 0x34, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x58,
    0xE8, 0xD2, 0xBE, 0x00, 0x00]

theorem code_l1101c9 : ∀ x ∈ codeRange 0x1101c9 bytes_l1101c9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x101c9 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1101de : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1101de (leaR64Effect 0x1101de 7 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1101de (fun s => s.RIP = 0x1101de) (leaR64Effect 0x1101de 7 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1101e6 (movR32Imm32Effect 0x1101e6 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x1101e6 (fun s => s.RIP = 0x1101e6) (movR32Imm32Effect 0x1101e6 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1101eb (movR64Imm32Effect 0x1101eb 6 0x202d48) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x1101eb (fun s => s.RIP = 0x1101eb) (movR64Imm32Effect 0x1101eb 6 0x202d48) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x1101f2 (RepPre 0x1101f2 (RepMovsqPre 0x1101f2)) (repMovsqEffect 0x1101f2) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x1101f5 (testR64R64Effect 0x1101f5 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 61) (.exec 0x1101f5 (fun s => s.RIP = 0x1101f5) (testR64R64Effect 0x1101f5 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 62) (.out 0x1101f8 (movR64M64Effect 0x1101f8 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 63) (.exec 0x1101f8 (LoadPre 0x1101f8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1101f8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1101f8 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.pure (condOp 4)) #v[60]
    (.terminate (.condBr (Fin.last 64) ⟨.l11075a, RegMap.args [(0, 0), (2, 2), (4, 4), (5, 5), (8, 62), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l110202, RegMap.args [(0, 0), (2, 2), (4, 4), (5, 5), (8, 62), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l1101de : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x30, 0x01, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6,
    0x48, 0x2D, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x85, 0xC0, 0x4C, 0x8B, 0x04, 0x24, 0x0F, 0x84,
    0x58, 0x05, 0x00, 0x00]

theorem code_l1101de : ∀ x ∈ codeRange 0x1101de bytes_l1101de, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x101de 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110202 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110202 (movR64R64Effect 0x110202 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[0]
    (.letOp (n := 54) (.exec 0x110202 (fun s => s.RIP = 0x110202) (movR64R64Effect 0x110202 9 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x110205 (movR64M64Effect 0x110205 0 (.base 15 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 56) (.exec 0x110205 (LoadPre 0x110205 (fun s => AddrMode.addr (.base 15 (.d8 0x20)) s (0x110205 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110205 0 (.base 15 (.d8 0x20))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.exec 0x110209 (StorePre 0x110209 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x110209 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110209 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x110211 (movR64M64Effect 0x110211 12 (.base 15 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15] []) (.reg (.gpr 12))) #v[15]
    (.letOp (n := 59) (.exec 0x110211 (LoadPre 0x110211 (fun s => AddrMode.addr (.base 15 (.d8 0x30)) s (0x110211 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110211 12 (.base 15 (.d8 0x30))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 60) (.out 0x110215 (movR64M64Effect 0x110215 0 (.base 15 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 61) (.exec 0x110215 (LoadPre 0x110215 (fun s => AddrMode.addr (.base 15 (.d8 0x38)) s (0x110215 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110215 0 (.base 15 (.d8 0x38))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 62) (.exec 0x110219 (StorePre 0x110219 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x110219 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110219 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x11021e (movR64M64Effect 0x11021e 10 (.base 15 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 15] []) (.reg (.gpr 10))) #v[15]
    (.letOp (n := 64) (.exec 0x11021e (LoadPre 0x11021e (fun s => AddrMode.addr (.base 15 (.d8 0x50)) s (0x11021e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11021e 10 (.base 15 (.d8 0x50))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 65) (.out 0x110222 (movR64M64Effect 0x110222 0 (.base 15 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 66) (.exec 0x110222 (LoadPre 0x110222 (fun s => AddrMode.addr (.base 15 (.d8 0x60)) s (0x110222 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110222 0 (.base 15 (.d8 0x60))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 67) (.exec 0x110226 (StorePre 0x110226 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x110226 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110226 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x11022b (movR64M64Effect 0x11022b 11 (.base 15 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 15] []) (.reg (.gpr 11))) #v[15]
    (.letOp (n := 69) (.exec 0x11022b (LoadPre 0x11022b (fun s => AddrMode.addr (.base 15 (.d8 0x68)) s (0x11022b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11022b 11 (.base 15 (.d8 0x68))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 70) (.exec 0x11022f (StorePre 0x11022f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11022f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11022f (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x110238 (StorePre 0x110238 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110238 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110238 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 72) (.exec 0x11023d (StorePre 0x11023d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11023d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11023d 13 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 73) (.exec 0x110242 (StorePre 0x110242 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x110242 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110242 14 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 74) (.exec 0x110247 (StorePre 0x110247 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x110247 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110247 12 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 75) (.exec 0x11024c (StorePre 0x11024c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11024c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11024c 11 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[68, 4]
    (.terminate (.br ⟨.l110278, RegMap.args [(0, 65), (2, 2), (4, 4), (5, 5), (8, 8), (9, 53), (10, 63), (11, 68), (12, 58), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l110202 : List UInt8 :=
  [0x49, 0x89, 0xC1, 0x49, 0x8B, 0x47, 0x20, 0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x4D,
    0x8B, 0x67, 0x30, 0x49, 0x8B, 0x47, 0x38, 0x48, 0x89, 0x44, 0x24, 0x50, 0x4D, 0x8B, 0x57, 0x50,
    0x49, 0x8B, 0x47, 0x60, 0x48, 0x89, 0x44, 0x24, 0x48, 0x4D, 0x8B, 0x5F, 0x68, 0x48, 0xC7, 0x44,
    0x24, 0x28, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x54, 0x24, 0x08, 0x4C, 0x89, 0x6C, 0x24, 0x40,
    0x4C, 0x89, 0x74, 0x24, 0x38, 0x4C, 0x89, 0x64, 0x24, 0x30, 0x4C, 0x89, 0x5C, 0x24, 0x20, 0xEB,
    0x25]

theorem code_l110202 : ∀ x ∈ codeRange 0x110202 bytes_l110202, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10202 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110260 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110260 (movR64M64Effect 0x110260 13 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 54) (.exec 0x110260 (LoadPre 0x110260 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x110260 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110260 13 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x110265 (movR64M64Effect 0x110265 14 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 56) (.exec 0x110265 (LoadPre 0x110265 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x110265 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110265 14 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11026a (movR64M64Effect 0x11026a 12 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 58) (.exec 0x11026a (LoadPre 0x11026a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11026a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11026a 12 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x11026f (testR64R64Effect 0x11026f 9 9) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 9] []) (.flag .ZF)) #v[9, 9]
    (.letOp (n := 60) (.exec 0x11026f (fun s => s.RIP = 0x11026f) (testR64R64Effect 0x11026f 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 61) (.pure (condOp 4)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l11075a, RegMap.args [(2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 53), (14, 55), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l110278, RegMap.args [(2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 53), (14, 55), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l110260 : List UInt8 :=
  [0x4C, 0x8B, 0x6C, 0x24, 0x40, 0x4C, 0x8B, 0x74, 0x24, 0x38, 0x4C, 0x8B, 0x64, 0x24, 0x30, 0x4D,
    0x85, 0xC9, 0x0F, 0x84, 0xE2, 0x04, 0x00, 0x00]

theorem code_l110260 : ∀ x ∈ codeRange 0x110260 bytes_l110260, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10260 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110278 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110278 (movR64R64Effect 0x110278 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[9]
    (.letOp (n := 54) (.exec 0x110278 (fun s => s.RIP = 0x110278) (movR64R64Effect 0x110278 3 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x11027b (testM8Imm8Effect 0x11027b 5 (.sib 4 none 0 (.d8 0x28)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 56) (.exec 0x11027b (LoadPre 0x11027b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11027b + BitVec.ofNat 64 5)) 1) (testM8Imm8Effect 0x11027b 5 (.sib 4 none 0 (.d8 0x28)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1102c2, RegMap.args [(2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l110282, RegMap.args [(2, 2), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l110278 : List UInt8 :=
  [0x4C, 0x89, 0xCB, 0xF6, 0x44, 0x24, 0x28, 0x01, 0x74, 0x40]

theorem code_l110278 : ∀ x ∈ codeRange 0x110278 bytes_l110278, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10278 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110282 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110282 (leaR64Effect 0x110282 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x110282 (fun s => s.RIP = 0x110282) (leaR64Effect 0x110282 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x110287 (movR64R64Effect 0x110287 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[12]
    (.letOp (n := 56) (.exec 0x110287 (fun s => s.RIP = 0x110287) (movR64R64Effect 0x110287 15 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x11028a (movR64R64Effect 0x11028a 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[14]
    (.letOp (n := 58) (.exec 0x11028a (fun s => s.RIP = 0x11028a) (movR64R64Effect 0x11028a 12 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x11028d (movR64R64Effect 0x11028d 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 13] []) (.reg (.gpr 14))) #v[13]
    (.letOp (n := 60) (.exec 0x11028d (fun s => s.RIP = 0x11028d) (movR64R64Effect 0x11028d 14 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x110290 (leaR64Effect 0x110290 13 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 62) (.exec 0x110290 (fun s => s.RIP = 0x110290) (leaR64Effect 0x110290 13 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x110298 (movR64R64Effect 0x110298 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 64) (.exec 0x110298 (fun s => s.RIP = 0x110298) (movR64R64Effect 0x110298 6 13) (Reg.operands [.gpr 13] [])) #v[61]
    (.letOp (n := 65) (.out 0x11029b (callEffect (fun _ => 0x110cd0) 0x1102a0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x11029b (PushPre 0x11029b 5) (callEffect (fun _ => 0x110cd0) 0x1102a0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x1102a0⟩) #v[]
    (.terminate (.call ⟨.l110cd0, RegMap.args [(3, 3), (4, 65), (5, 5), (6, 63), (7, 53), (12, 57), (13, 61), (14, 59), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l1102a0, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l110282 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x58, 0x4D, 0x89, 0xE7, 0x4D, 0x89, 0xF4, 0x4D, 0x89, 0xEE, 0x4C, 0x8D,
    0xAC, 0x24, 0x30, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xEE, 0xE8, 0x30, 0x0A, 0x00, 0x00]

theorem code_l110282 : ∀ x ∈ codeRange 0x110282 bytes_l110282, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10282 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1102a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1102a0 (movR64M64Effect 0x1102a0 10 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 54) (.exec 0x1102a0 (LoadPre 0x1102a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1102a0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1102a0 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1102a5 (movR64M64Effect 0x1102a5 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 56) (.exec 0x1102a5 (LoadPre 0x1102a5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1102a5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1102a5 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1102a9 (movR32Imm32Effect 0x1102a9 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x1102a9 (fun s => s.RIP = 0x1102a9) (movR32Imm32Effect 0x1102a9 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1102ae (movR64R64Effect 0x1102ae 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 60) (.exec 0x1102ae (fun s => s.RIP = 0x1102ae) (movR64R64Effect 0x1102ae 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x1102b1 (movR64R64Effect 0x1102b1 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[14]
    (.letOp (n := 62) (.exec 0x1102b1 (fun s => s.RIP = 0x1102b1) (movR64R64Effect 0x1102b1 13 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 63) (.out 0x1102b4 (movR64R64Effect 0x1102b4 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 12] []) (.reg (.gpr 14))) #v[12]
    (.letOp (n := 64) (.exec 0x1102b4 (fun s => s.RIP = 0x1102b4) (movR64R64Effect 0x1102b4 14 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 65) (.out 0x1102b7 (movR64R64Effect 0x1102b7 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15] []) (.reg (.gpr 12))) #v[15]
    (.letOp (n := 66) (.exec 0x1102b7 (fun s => s.RIP = 0x1102b7) (movR64R64Effect 0x1102b7 12 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 67) (.out 0x1102ba (leaR64Effect 0x1102ba 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x1102ba (fun s => s.RIP = 0x1102ba) (leaR64Effect 0x1102ba 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x1102bf (RepPre 0x1102bf (RepMovsqPre 0x1102bf)) (repMovsqEffect 0x1102bf) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[67, 59, 57, 22]
    (.terminate (.br ⟨.l1102c2, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (8, 55), (10, 53), (12, 65), (13, 61), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l1102a0 : List UInt8 :=
  [0x4C, 0x8B, 0x54, 0x24, 0x08, 0x4C, 0x8B, 0x04, 0x24, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xEF, 0x4D, 0x89, 0xF5, 0x4D, 0x89, 0xE6, 0x4D, 0x89, 0xFC, 0x48, 0x8D, 0x74, 0x24, 0x58, 0xF3,
    0x48, 0xA5]

theorem code_l1102a0 : ∀ x ∈ codeRange 0x1102a0 bytes_l1102a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x102a0 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1102c2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1102c2 (leaR64Effect 0x1102c2 9 (.base 3 (.d8 0xff))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[3]
    (.letOp (n := 54) (.exec 0x1102c2 (fun s => s.RIP = 0x1102c2) (leaR64Effect 0x1102c2 9 (.base 3 (.d8 0xff))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1102c6 (cmpR64Imm32Effect 0x1102c6 3 0x101) (EffectPart.reads (.flag .CF) [.gpr 3] []) (.flag .CF)) #v[3]
    (.letOp (n := 56) (.out 0x1102c6 (cmpR64Imm32Effect 0x1102c6 3 0x101) (EffectPart.reads (.flag .ZF) [.gpr 3] []) (.flag .ZF)) #v[3]
    (.letOp (n := 57) (.exec 0x1102c6 (fun s => s.RIP = 0x1102c6) (cmpR64Imm32Effect 0x1102c6 3 0x101) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 58) (.exec 0x1102cd (StorePre 0x1102cd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1102cd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1102cd 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.pure (condOp 7)) #v[55, 56]
    (.terminate (.condBr (Fin.last 59) ⟨.l110600, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 53), (10, 10), (12, 12), (13, 13), (14, 14), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1102d8, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 53), (10, 10), (12, 12), (13, 13), (14, 14), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1102c2 : List UInt8 :=
  [0x4C, 0x8D, 0x4B, 0xFF, 0x48, 0x81, 0xFB, 0x01, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x4C, 0x24, 0x10,
    0x0F, 0x87, 0x28, 0x03, 0x00, 0x00]

theorem code_l1102c2 : ∀ x ∈ codeRange 0x1102c2 bytes_l1102c2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x102c2 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1102d8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1102d8 (movR64M64Effect 0x1102d8 15 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x1102d8 (LoadPre 0x1102d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1102d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1102d8 15 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1102dd (movR64M64Effect 0x1102dd 0 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1102dd (LoadPre 0x1102dd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1102dd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1102dd 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1102e5 (StorePre 0x1102e5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1102e5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1102e5 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x1102ea (movR64M64Effect 0x1102ea 3 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 59) (.exec 0x1102ea (LoadPre 0x1102ea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1102ea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1102ea 3 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l11031a, RegMap.args [(0, 55), (2, 2), (3, 58), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1102d8 : List UInt8 :=
  [0x4C, 0x8B, 0x7C, 0x24, 0x48, 0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44,
    0x24, 0x18, 0x48, 0x8B, 0x5C, 0x24, 0x50, 0xEB, 0x29]

theorem code_l1102d8 : ∀ x ∈ codeRange 0x1102d8 bytes_l1102d8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x102d8 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110300 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110300 (callEffect (fun _ => 0x10a410) 0x110305) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x110300 (PushPre 0x110300 5) (callEffect (fun _ => 0x10a410) 0x110305) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.const ⟨64, 0x110305⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ { target := .l110305, kept := #v[], arity := rfl, guard := some (Fin.last 55) }))))

def bytes_l110300 : List UInt8 :=
  [0xE8, 0x0B, 0xA1, 0xFF, 0xFF]

theorem code_l110300 : ∀ x ∈ codeRange 0x110300 bytes_l110300, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10300 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110305 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110305 (movR8Imm8Effect 0x110305 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x110305 (fun s => s.RIP = 0x110305) (movR8Imm8Effect 0x110305 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.exec 0x110307 (StorePre 0x110307 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x110307 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110307 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11030c (movR64M64Effect 0x11030c 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 57) (.exec 0x11030c (LoadPre 0x11030c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11030c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11030c 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x110310 (movR64M64Effect 0x110310 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 59) (.exec 0x110310 (LoadPre 0x110310 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x110310 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110310 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x110315 (movR64M64Effect 0x110315 10 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 61) (.exec 0x110315 (LoadPre 0x110315 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110315 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110315 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l11031a, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 56), (9, 58), (10, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l110305 : List UInt8 :=
  [0xB0, 0x01, 0x48, 0x89, 0x44, 0x24, 0x28, 0x4C, 0x8B, 0x04, 0x24, 0x4C, 0x8B, 0x4C, 0x24, 0x10,
    0x4C, 0x8B, 0x54, 0x24, 0x08]

theorem code_l110305 : ∀ x ∈ codeRange 0x110305 bytes_l110305, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10305 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11031a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11031a (movR64M64Effect 0x11031a 11 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 54) (.exec 0x11031a (LoadPre 0x11031a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11031a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11031a 11 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11031f (movR64R64Effect 0x11031f 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 56) (.exec 0x11031f (fun s => s.RIP = 0x11031f) (movR64R64Effect 0x11031f 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l11037b, RegMap.args [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l11031a : List UInt8 :=
  [0x4C, 0x8B, 0x5C, 0x24, 0x20, 0x4C, 0x89, 0xF8, 0xEB, 0x57]

theorem code_l11031a : ∀ x ∈ codeRange 0x11031a bytes_l11031a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1031a 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110330 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110330 (leaR64Effect 0x110330 1 (.base 14 (.d32 0x780))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 54) (.exec 0x110330 (fun s => s.RIP = 0x110330) (leaR64Effect 0x110330 1 (.base 14 (.d32 0x780))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.exec 0x110337 (StorePre 0x110337 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x110337 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110337 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11033c (movR64R64Effect 0x11033c 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[14]
    (.letOp (n := 57) (.exec 0x11033c (fun s => s.RIP = 0x11033c) (movR64R64Effect 0x11033c 13 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x11033f (addR64Imm32Effect 0x11033f 14 0x9a0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 59) (.exec 0x11033f (fun s => s.RIP = 0x11033f) (addR64Imm32Effect 0x11033f 14 0x9a0) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 60) (.out 0x110346 (movR32Imm32Effect 0x110346 5 3 0x2) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 61) (.exec 0x110346 (fun s => s.RIP = 0x110346) (movR32Imm32Effect 0x110346 5 3 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11034b (xorR32R32Effect 0x11034b 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 63) (.exec 0x11034b (fun s => s.RIP = 0x11034b) (xorR32R32Effect 0x11034b 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.terminate (.br ⟨.l11034e, RegMap.args [(0, 0), (1, 53), (3, 60), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 62), (13, 56), (14, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l110330 : List UInt8 :=
  [0x49, 0x8D, 0x8E, 0x80, 0x07, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x4D, 0x89, 0xF5, 0x49,
    0x81, 0xC6, 0xA0, 0x09, 0x00, 0x00, 0xBB, 0x02, 0x00, 0x00, 0x00, 0x45, 0x31, 0xE4]

theorem code_l110330 : ∀ x ∈ codeRange 0x110330 bytes_l110330, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10330 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11034e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11034e (movR64R64Effect 0x11034e 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 54) (.exec 0x11034e (fun s => s.RIP = 0x11034e) (movR64R64Effect 0x11034e 1 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x110351 (incR64Effect 0x110351 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 56) (.exec 0x110351 (fun s => s.RIP = 0x110351) (incR64Effect 0x110351 12) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 57) (.out 0x110354 (imulR64R64Imm32Effect 0x110354 7 6 1 0x3c0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 58) (.exec 0x110354 (fun s => s.RIP = 0x110354) (imulR64R64Imm32Effect 0x110354 7 6 1 0x3c0) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.out 0x11035b (addR64R64Effect 0x11035b 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x11035b (fun s => s.RIP = 0x11035b) (addR64R64Effect 0x11035b 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x11035e (movR64R64Effect 0x11035e 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[0]
    (.letOp (n := 62) (.exec 0x11035e (fun s => s.RIP = 0x11035e) (movR64R64Effect 0x11035e 15 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 63) (.out 0x110361 (movR64M64Effect 0x110361 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x110361 (LoadPre 0x110361 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x110361 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110361 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l110366, RegMap.args [(0, 0), (1, 53), (2, 63), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l11034e : List UInt8 :=
  [0x4C, 0x89, 0xE1, 0x49, 0xFF, 0xC4, 0x48, 0x69, 0xF1, 0xC0, 0x03, 0x00, 0x00, 0x4C, 0x01, 0xEE,
    0x49, 0x89, 0xC7, 0x48, 0x8B, 0x54, 0x24, 0x18]

theorem code_l11034e : ∀ x ∈ codeRange 0x11034e bytes_l11034e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1034e 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110366 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110366 (imulR64R64Imm32Effect 0x110366 7 1 1 0x110) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.exec 0x110366 (fun s => s.RIP = 0x110366) (imulR64R64Imm32Effect 0x110366 7 1 1 0x110) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x11036d (addR64R64Effect 0x11036d 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[53, 2]
    (.letOp (n := 56) (.exec 0x11036d (fun s => s.RIP = 0x11036d) (addR64R64Effect 0x11036d 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[53, 2]
    (.letOp (n := 57) (.out 0x110370 (movzxR32M8Effect 0x110370 6 7 (.sib 9 (some 1) 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9, .gpr 1] []) (.reg (.gpr 7))) #v[9, 55]
    (.letOp (n := 58) (.exec 0x110370 (LoadPre 0x110370 (fun s => AddrMode.addr (.sib 9 (some 1) 0 (.d8 0x8)) s (0x110370 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x110370 6 7 (.sib 9 (some 1) 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 1] [])) #v[9, 55]
    (.letOp (n := 59) (.out 0x110376 (testR64R64Effect 0x110376 7 7) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 7] []) (.flag .ZF)) #v[57, 57]
    (.letOp (n := 60) (.exec 0x110376 (fun s => s.RIP = 0x110376) (testR64R64Effect 0x110376 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[57, 57]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l1103c0, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l11037b, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l110366 : List UInt8 :=
  [0x48, 0x69, 0xC9, 0x10, 0x01, 0x00, 0x00, 0x48, 0x01, 0xD1, 0x41, 0x0F, 0xB6, 0x7C, 0x09, 0x08,
    0x48, 0x85, 0xFF, 0x75, 0x45]

theorem code_l110366 : ∀ x ∈ codeRange 0x110366 bytes_l110366, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10366 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11037b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11037b (testR64R64Effect 0x11037b 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[13, 13]
    (.letOp (n := 54) (.exec 0x11037b (fun s => s.RIP = 0x11037b) (testR64R64Effect 0x11037b 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l110385, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l110380, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11037b : List UInt8 :=
  [0x4D, 0x85, 0xED, 0x74, 0x05]

theorem code_l11037b : ∀ x ∈ codeRange 0x11037b bytes_l11037b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1037b 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110380 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110380 (cmpR64R64Effect 0x110380 12 3) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 3] []) (.flag .CF)) #v[12, 3]
    (.letOp (n := 54) (.exec 0x110380 (fun s => s.RIP = 0x110380) (cmpR64R64Effect 0x110380 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 55) (.pure (condOp 2)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11034e, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l110385, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l110380 : List UInt8 :=
  [0x49, 0x39, 0xDC, 0x72, 0xC9]

theorem code_l110380 : ∀ x ∈ codeRange 0x110380 bytes_l110380, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10380 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110385 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110385 (testR64R64Effect 0x110385 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 54) (.exec 0x110385 (fun s => s.RIP = 0x110385) (testR64R64Effect 0x110385 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11038f, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11038a, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l110385 : List UInt8 :=
  [0x4D, 0x85, 0xF6, 0x74, 0x05]

theorem code_l110385 : ∀ x ∈ codeRange 0x110385 bytes_l110385, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10385 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11038a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11038a (cmpR64R64Effect 0x11038a 14 5) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 5] []) (.flag .ZF)) #v[14, 5]
    (.letOp (n := 54) (.exec 0x11038a (fun s => s.RIP = 0x11038a) (cmpR64R64Effect 0x11038a 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[14, 5]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l110330, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11038f, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11038a : List UInt8 :=
  [0x49, 0x39, 0xEE, 0x75, 0xA1]

theorem code_l11038a : ∀ x ∈ codeRange 0x11038a bytes_l11038a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1038a 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11038f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11038f (testR64R64Effect 0x11038f 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[8, 8]
    (.letOp (n := 54) (.exec 0x11038f (fun s => s.RIP = 0x11038f) (testR64R64Effect 0x11038f 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l110260, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l110398, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11038f : List UInt8 :=
  [0x4D, 0x85, 0xC0, 0x0F, 0x84, 0xC8, 0xFE, 0xFF, 0xFF]

theorem code_l11038f : ∀ x ∈ codeRange 0x11038f bytes_l11038f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1038f 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110398 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110398 (cmpR64R64Effect 0x110398 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[0, 11]
    (.letOp (n := 54) (.exec 0x110398 (fun s => s.RIP = 0x110398) (cmpR64R64Effect 0x110398 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[0, 11]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l110260, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1103a1, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l110398 : List UInt8 :=
  [0x4C, 0x39, 0xD8, 0x0F, 0x83, 0xBF, 0xFE, 0xFF, 0xFF]

theorem code_l110398 : ∀ x ∈ codeRange 0x110398 bytes_l110398, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10398 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1103a1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1103a1 (leaR64Effect 0x1103a1 15 (.base 0 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[0]
    (.letOp (n := 54) (.exec 0x1103a1 (fun s => s.RIP = 0x1103a1) (leaR64Effect 0x1103a1 15 (.base 0 (.d8 0x1))) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1103a5 (imulR64R64Imm32Effect 0x1103a5 7 6 0 0x3c0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[0]
    (.letOp (n := 56) (.exec 0x1103a5 (fun s => s.RIP = 0x1103a5) (imulR64R64Imm32Effect 0x1103a5 7 6 0 0x3c0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x1103ac (addR64R64Effect 0x1103ac 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[55, 8]
    (.letOp (n := 58) (.exec 0x1103ac (fun s => s.RIP = 0x1103ac) (addR64R64Effect 0x1103ac 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[55, 8]
    (.letOp (n := 59) (.out 0x1103af (xorR32R32Effect 0x1103af 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[13, 13]
    (.letOp (n := 60) (.exec 0x1103af (fun s => s.RIP = 0x1103af) (xorR32R32Effect 0x1103af 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 61) (.out 0x1103b2 (movR64R64Effect 0x1103b2 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[10]
    (.letOp (n := 62) (.exec 0x1103b2 (fun s => s.RIP = 0x1103b2) (movR64R64Effect 0x1103b2 2 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 63) (.out 0x1103b5 (movR64R64Effect 0x1103b5 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 64) (.exec 0x1103b5 (fun s => s.RIP = 0x1103b5) (movR64R64Effect 0x1103b5 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 65) (.out 0x1103b8 (movR64R64Effect 0x1103b8 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 66) (.exec 0x1103b8 (fun s => s.RIP = 0x1103b8) (movR64R64Effect 0x1103b8 0 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.terminate (.br ⟨.l110366, RegMap.args [(0, 65), (1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l1103a1 : List UInt8 :=
  [0x4C, 0x8D, 0x78, 0x01, 0x48, 0x69, 0xF0, 0xC0, 0x03, 0x00, 0x00, 0x4C, 0x01, 0xC6, 0x45, 0x31,
    0xED, 0x4C, 0x89, 0xD2, 0x48, 0x89, 0xC1, 0x4C, 0x89, 0xF8, 0xEB, 0xA9]

theorem code_l1103a1 : ∀ x ∈ codeRange 0x1103a1 bytes_l1103a1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x103a1 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1103c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1103c0 (movR32R32Effect 0x1103c0 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x1103c0 (fun s => s.RIP = 0x1103c0) (movR32R32Effect 0x1103c0 2 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1103c2 (testR8R8Effect 0x1103c2 3 7 7) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 7] []) (.flag .ZF)) #v[7, 7]
    (.letOp (n := 56) (.out 0x1103c2 (testR8R8Effect 0x1103c2 3 7 7) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 7] []) (.flag .SF)) #v[7, 7]
    (.letOp (n := 57) (.out 0x1103c2 (testR8R8Effect 0x1103c2 3 7 7) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 7] []) (.flag .OF)) #v[7, 7]
    (.letOp (n := 58) (.exec 0x1103c2 (fun s => s.RIP = 0x1103c2) (testR8R8Effect 0x1103c2 3 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 59) (.pure (condOp 14)) #v[55, 56, 57]
    (.terminate (.condBr (Fin.last 59) ⟨.l110400, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (20, 56), (21, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1103c7, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (20, 56), (21, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1103c0 : List UInt8 :=
  [0x89, 0xF8, 0x40, 0x84, 0xFF, 0x7E, 0x39]

theorem code_l1103c0 : ∀ x ∈ codeRange 0x1103c0 bytes_l1103c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x103c0 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1103c7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1103c7 (shrR32Effect 0x1103c7 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 54) (.exec 0x1103c7 (fun s => s.RIP = 0x1103c7) (shrR32Effect 0x1103c7 2 7 1) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7]
    (.letOp (n := 55) (.out 0x1103c9 (cmpAlImm8Effect 0x1103c9 0xf) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[0]
    (.letOp (n := 56) (.out 0x1103c9 (cmpAlImm8Effect 0x1103c9 0xf) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 57) (.exec 0x1103c9 (fun s => s.RIP = 0x1103c9) (cmpAlImm8Effect 0x1103c9 0xf) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 58) (.pure (condOp 7)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l110787, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l1103d1, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1103c7 : List UInt8 :=
  [0xD1, 0xEF, 0x3C, 0x0F, 0x0F, 0x87, 0xB6, 0x03, 0x00, 0x00]

theorem code_l1103c7 : ∀ x ∈ codeRange 0x1103c7 bytes_l1103c7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x103c7 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1103d1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1103d1 (imulR64R64Imm8Effect 0x1103d1 4 0 7 0x78) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x1103d1 (fun s => s.RIP = 0x1103d1) (imulR64R64Imm8Effect 0x1103d1 4 0 7 0x78) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1103d5 (addR64R64Effect 0x1103d5 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[6, 53]
    (.letOp (n := 56) (.exec 0x1103d5 (fun s => s.RIP = 0x1103d5) (addR64R64Effect 0x1103d5 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[6, 53]
    (.letOp (n := 57) (.out 0x1103d8 (movR32Imm32Effect 0x1103d8 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x1103d8 (fun s => s.RIP = 0x1103d8) (movR32Imm32Effect 0x1103d8 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1103dd (leaR64Effect 0x1103dd 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1103dd (fun s => s.RIP = 0x1103dd) (leaR64Effect 0x1103dd 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1103e2 (movR64R64Effect 0x1103e2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 62) (.exec 0x1103e2 (fun s => s.RIP = 0x1103e2) (movR64R64Effect 0x1103e2 7 0) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 63) (.exec 0x1103e5 (RepPre 0x1103e5 (RepMovsqPre 0x1103e5)) (repMovsqEffect 0x1103e5) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[55, 61, 57, 22]
    (.letOp (n := 64) (.out 0x1103e8 (leaR64Effect 0x1103e8 7 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 65) (.exec 0x1103e8 (fun s => s.RIP = 0x1103e8) (leaR64Effect 0x1103e8 7 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x1103f0 (movR64R64Effect 0x1103f0 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[59]
    (.letOp (n := 67) (.exec 0x1103f0 (fun s => s.RIP = 0x1103f0) (movR64R64Effect 0x1103f0 6 0) (Reg.operands [.gpr 0] [])) #v[59]
    (.terminate (.br ⟨.l110300, RegMap.args [(0, 59), (3, 3), (4, 4), (5, 5), (6, 66), (7, 64), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l1103d1 : List UInt8 :=
  [0x48, 0x6B, 0xC7, 0x78, 0x48, 0x01, 0xC6, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x44, 0x24,
    0x58, 0x48, 0x89, 0xC7, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x30, 0x01, 0x00, 0x00, 0x48,
    0x89, 0xC6, 0xE9, 0x08, 0xFF, 0xFF, 0xFF]

theorem code_l1103d1 : ∀ x ∈ codeRange 0x1103d1 bytes_l1103d1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x103d1 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110400 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110400 (negR8Effect 0x110400 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x110400 (fun s => s.RIP = 0x110400) (negR8Effect 0x110400 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x110402 (shrR8Effect 0x110402 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x110402 (fun s => s.RIP = 0x110402) (shrR8Effect 0x110402 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x110405 (subR8R8Effect 0x110405 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[55, 7]
    (.letOp (n := 58) (.exec 0x110405 (fun s => s.RIP = 0x110405) (subR8R8Effect 0x110405 3 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[55, 7]
    (.letOp (n := 59) (.out 0x110408 (sarR8Effect 0x110408 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x110408 (fun s => s.RIP = 0x110408) (sarR8Effect 0x110408 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x11040a (movsxR64R8Effect 0x11040a 4 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 62) (.exec 0x11040a (fun s => s.RIP = 0x11040a) (movsxR64R8Effect 0x11040a 4 7 0) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 63) (.out 0x11040e (cmpR8Imm8Effect 0x11040e 4 7 0x7) (EffectPart.reads (.flag .CF) [.gpr 7] []) (.flag .CF)) #v[61]
    (.letOp (n := 64) (.out 0x11040e (cmpR8Imm8Effect 0x11040e 4 7 0x7) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[61]
    (.letOp (n := 65) (.exec 0x11040e (fun s => s.RIP = 0x11040e) (cmpR8Imm8Effect 0x11040e 4 7 0x7) (Reg.operands [.gpr 7] [])) #v[61]
    (.letOp (n := 66) (.pure (condOp 7)) #v[63, 64]
    (.terminate (.condBr (Fin.last 66) ⟨.l110798, RegMap.args [(0, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 61), (12, 12), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l110418, RegMap.args [(0, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 61), (12, 12), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l110400 : List UInt8 :=
  [0xF6, 0xD8, 0xC0, 0xE8, 0x07, 0x40, 0x28, 0xF8, 0xD0, 0xF8, 0x48, 0x0F, 0xBE, 0xF8, 0x40, 0x80,
    0xFF, 0x07, 0x0F, 0x87, 0x80, 0x03, 0x00, 0x00]

theorem code_l110400 : ∀ x ∈ codeRange 0x110400 bytes_l110400, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10400 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110418_4 : Block Op Label signature Reg.count 188 :=
  .letOp (n := 188) (.out 0x1105eb (leaR64Effect 0x1105eb 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 189) (.exec 0x1105eb (fun s => s.RIP = 0x1105eb) (leaR64Effect 0x1105eb 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l110300, RegMap.args [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 188), (7, 186), (8, 178), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 190⟩)))

def bytes_l110418_4 : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x58, 0xE9, 0x0B, 0xFD, 0xFF, 0xFF]

theorem code_l110418_4 : ∀ x ∈ codeRange 0x1105eb bytes_l110418_4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x105eb 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110418_3 : Block Op Label signature Reg.count 160 :=
  .letOp (n := 160) (.out 0x110563 (movR64M64Effect 0x110563 8 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 161) (.exec 0x110563 (LoadPre 0x110563 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x110563 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110563 8 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 162) (.out 0x11056b (movR64M64Effect 0x11056b 9 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 163) (.exec 0x11056b (LoadPre 0x11056b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11056b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11056b 9 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 164) (.exec 0x110573 (StorePre 0x110573 4 (fun s => AddrMode.addr (.base 10 (.d8 0x8)) s (0x110573 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110573 9 (.base 10 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 10] [])) #v[162, 151]
    (.letOp (n := 165) (.exec 0x110577 (StorePre 0x110577 3 (fun s => AddrMode.addr (.base 10 .none) s (0x110577 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x110577 8 (.base 10 .none)) (Reg.operands [.gpr 8, .gpr 10] [])) #v[160, 151]
    (.letOp (n := 166) (.out 0x11057a (movR64M64Effect 0x11057a 8 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 167) (.exec 0x11057a (LoadPre 0x11057a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x11057a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11057a 8 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 168) (.out 0x110582 (movR64M64Effect 0x110582 9 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 169) (.exec 0x110582 (LoadPre 0x110582 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x110582 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110582 9 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 170) (.exec 0x11058a (StorePre 0x11058a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11058a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11058a 8 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[166, 4]
    (.letOp (n := 171) (.exec 0x11058f (StorePre 0x11058f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11058f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11058f 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[168, 4]
    (.letOp (n := 172) (.out 0x110594 (movR64M64Effect 0x110594 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 173) (.exec 0x110594 (LoadPre 0x110594 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x110594 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110594 8 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 174) (.exec 0x11059c (StorePre 0x11059c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11059c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11059c 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[172, 4]
    (.letOp (n := 175) (.out 0x1105a1 (movR64M64Effect 0x1105a1 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 176) (.exec 0x1105a1 (LoadPre 0x1105a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x1105a1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1105a1 8 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 177) (.exec 0x1105a9 (StorePre 0x1105a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1105a9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1105a9 8 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[175, 4]
    (.letOp (n := 178) (.out 0x1105ae (movR64M64Effect 0x1105ae 8 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 179) (.exec 0x1105ae (LoadPre 0x1105ae (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1105ae + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1105ae 8 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 180) (.exec 0x1105b6 (StorePre 0x1105b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1105b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1105b6 8 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[178, 4]
    (.letOp (n := 181) (.exec 0x1105bb (StorePre 0x1105bb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1105bb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105bb 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[133, 4]
    (.letOp (n := 182) (.exec 0x1105c3 (StorePre 0x1105c3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1105c3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105c3 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[135, 4]
    (.letOp (n := 183) (.exec 0x1105cb (StorePre 0x1105cb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1105cb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105cb 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[139, 4]
    (.letOp (n := 184) (.exec 0x1105d3 (StorePre 0x1105d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1105d3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105d3 7 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[147, 4]
    (.letOp (n := 185) (.exec 0x1105db (StorePre 0x1105db 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1105db + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105db 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[145, 4]
    (.letOp (n := 186) (.out 0x1105e3 (leaR64Effect 0x1105e3 7 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 187) (.exec 0x1105e3 (fun s => s.RIP = 0x1105e3) (leaR64Effect 0x1105e3 7 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l110418_4))))))))))))))))))))))))))))

def bytes_l110418_3 : List UInt8 :=
  [0x4C, 0x8B, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00,
    0x4D, 0x89, 0x4A, 0x08, 0x4D, 0x89, 0x02, 0x4C, 0x8B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x4C,
    0x8B, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x44, 0x24, 0x58, 0x4C, 0x89, 0x4C, 0x24,
    0x60, 0x4C, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x44, 0x24, 0x68, 0x4C, 0x8B,
    0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x44, 0x24, 0x70, 0x4C, 0x8B, 0x84, 0x24, 0x28,
    0x01, 0x00, 0x00, 0x4C, 0x89, 0x44, 0x24, 0x78, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xBC, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0xBC, 0x24, 0x30, 0x01, 0x00, 0x00] ++ bytes_l110418_4

theorem code_l110418_3 : ∀ x ∈ codeRange 0x110563 bytes_l110418_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10563 136 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110418_4

@[cfg_block] def b_l110418_2 : Block Op Label signature Reg.count 125 :=
  .letOp (n := 125) (.exec 0x1104f7 (StorePre 0x1104f7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1104f7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104f7 6 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[123, 4]
    (.letOp (n := 126) (.exec 0x1104ff (StorePre 0x1104ff 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1104ff + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104ff 10 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[121, 4]
    (.letOp (n := 127) (.out 0x110507 (movR64Imm64Effect 0x110507 6 0xffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 128) (.exec 0x110507 (fun s => s.RIP = 0x110507) (movR64Imm64Effect 0x110507 6 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 129) (.out 0x110511 (andR64R64Effect 0x110511 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[72, 127]
    (.letOp (n := 130) (.exec 0x110511 (fun s => s.RIP = 0x110511) (andR64R64Effect 0x110511 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[72, 127]
    (.letOp (n := 131) (.out 0x110514 (movR64Imm64Effect 0x110514 9 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 132) (.exec 0x110514 (fun s => s.RIP = 0x110514) (movR64Imm64Effect 0x110514 9 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 133) (.out 0x11051e (andR64R64Effect 0x11051e 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[86, 131]
    (.letOp (n := 134) (.exec 0x11051e (fun s => s.RIP = 0x11051e) (andR64R64Effect 0x11051e 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[86, 131]
    (.letOp (n := 135) (.out 0x110521 (andR64R64Effect 0x110521 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[96, 131]
    (.letOp (n := 136) (.exec 0x110521 (fun s => s.RIP = 0x110521) (andR64R64Effect 0x110521 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[96, 131]
    (.letOp (n := 137) (.out 0x110524 (addR64R64Effect 0x110524 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[110, 94]
    (.letOp (n := 138) (.exec 0x110524 (fun s => s.RIP = 0x110524) (addR64R64Effect 0x110524 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[110, 94]
    (.letOp (n := 139) (.out 0x110527 (andR64R64Effect 0x110527 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[104, 131]
    (.letOp (n := 140) (.exec 0x110527 (fun s => s.RIP = 0x110527) (andR64R64Effect 0x110527 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[104, 131]
    (.letOp (n := 141) (.out 0x11052a (movR64R64Effect 0x11052a 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[137]
    (.letOp (n := 142) (.exec 0x11052a (fun s => s.RIP = 0x11052a) (movR64R64Effect 0x11052a 6 7) (Reg.operands [.gpr 7] [])) #v[137]
    (.letOp (n := 143) (.out 0x11052d (shrR64Effect 0x11052d 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[141]
    (.letOp (n := 144) (.exec 0x11052d (fun s => s.RIP = 0x11052d) (shrR64Effect 0x11052d 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[141]
    (.letOp (n := 145) (.out 0x110531 (addR64R64Effect 0x110531 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[143, 129]
    (.letOp (n := 146) (.exec 0x110531 (fun s => s.RIP = 0x110531) (addR64R64Effect 0x110531 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[143, 129]
    (.letOp (n := 147) (.out 0x110534 (andR64R64Effect 0x110534 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[137, 131]
    (.letOp (n := 148) (.exec 0x110534 (fun s => s.RIP = 0x110534) (andR64R64Effect 0x110534 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[137, 131]
    (.letOp (n := 149) (.out 0x110537 (movR64M64Effect 0x110537 8 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 150) (.exec 0x110537 (LoadPre 0x110537 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x110537 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110537 8 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 151) (.out 0x11053f (leaR64Effect 0x11053f 10 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 152) (.exec 0x11053f (fun s => s.RIP = 0x11053f) (leaR64Effect 0x11053f 10 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 153) (.exec 0x110547 (StorePre 0x110547 4 (fun s => AddrMode.addr (.base 10 (.d8 0x20)) s (0x110547 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110547 8 (.base 10 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 10] [])) #v[149, 151]
    (.letOp (n := 154) (.out 0x11054b (movR64M64Effect 0x11054b 8 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 155) (.exec 0x11054b (LoadPre 0x11054b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11054b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11054b 8 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 156) (.exec 0x110553 (StorePre 0x110553 4 (fun s => AddrMode.addr (.base 10 (.d8 0x18)) s (0x110553 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110553 8 (.base 10 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 10] [])) #v[154, 151]
    (.letOp (n := 157) (.out 0x110557 (movR64M64Effect 0x110557 8 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 158) (.exec 0x110557 (LoadPre 0x110557 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x110557 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110557 8 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 159) (.exec 0x11055f (StorePre 0x11055f 4 (fun s => AddrMode.addr (.base 10 (.d8 0x10)) s (0x11055f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11055f 8 (.base 10 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 10] [])) #v[157, 151]
    (b_l110418_3)))))))))))))))))))))))))))))))))))

def bytes_l110418_2 : List UInt8 :=
  [0x48, 0x89, 0xB4, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x94, 0x24, 0xE0, 0x00, 0x00, 0x00,
    0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x49, 0x21, 0xF0, 0x49, 0xB9, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xC8, 0x4C, 0x21, 0xC9, 0x4C, 0x01, 0xDF,
    0x4C, 0x21, 0xCA, 0x48, 0x89, 0xFE, 0x48, 0xC1, 0xEE, 0x34, 0x4C, 0x01, 0xC6, 0x4C, 0x21, 0xCF,
    0x4C, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x8D, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0x4D, 0x89, 0x42, 0x20, 0x4C, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x4D, 0x89, 0x42, 0x18,
    0x4C, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x4D, 0x89, 0x42, 0x10] ++ bytes_l110418_3

theorem code_l110418_2 : ∀ x ∈ codeRange 0x1104f7 bytes_l110418_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x104f7 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110418_3

@[cfg_block] def b_l110418_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.out 0x110492 (movR64R64Effect 0x110492 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[86]
    (.letOp (n := 89) (.exec 0x110492 (fun s => s.RIP = 0x110492) (movR64R64Effect 0x110492 1 0) (Reg.operands [.gpr 0] [])) #v[86]
    (.letOp (n := 90) (.out 0x110495 (shrR64Effect 0x110495 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[88]
    (.letOp (n := 91) (.exec 0x110495 (fun s => s.RIP = 0x110495) (shrR64Effect 0x110495 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[88]
    (.letOp (n := 92) (.out 0x110499 (subR64M64Effect 0x110499 1 (.sib 6 (some 9) 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .gpr 9] []) (.reg (.gpr 1))) #v[90, 6, 53]
    (.letOp (n := 93) (.exec 0x110499 (LoadPre 0x110499 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x30)) s (0x110499 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110499 1 (.sib 6 (some 9) 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 6, .gpr 9] [])) #v[90, 6, 53]
    (.letOp (n := 94) (.out 0x11049e (movR64Imm64Effect 0x11049e 11 0x3ffffffffffffc) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 95) (.exec 0x11049e (fun s => s.RIP = 0x11049e) (movR64Imm64Effect 0x11049e 11 0x3ffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 96) (.out 0x1104a8 (addR64R64Effect 0x1104a8 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[92, 94]
    (.letOp (n := 97) (.exec 0x1104a8 (fun s => s.RIP = 0x1104a8) (addR64R64Effect 0x1104a8 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[92, 94]
    (.letOp (n := 98) (.out 0x1104ab (movR64R64Effect 0x1104ab 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[96]
    (.letOp (n := 99) (.exec 0x1104ab (fun s => s.RIP = 0x1104ab) (movR64R64Effect 0x1104ab 2 1) (Reg.operands [.gpr 1] [])) #v[96]
    (.letOp (n := 100) (.out 0x1104ae (shrR64Effect 0x1104ae 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[98]
    (.letOp (n := 101) (.exec 0x1104ae (fun s => s.RIP = 0x1104ae) (shrR64Effect 0x1104ae 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[98]
    (.letOp (n := 102) (.out 0x1104b2 (subR64M64Effect 0x1104b2 2 (.sib 6 (some 9) 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6, .gpr 9] []) (.reg (.gpr 2))) #v[100, 6, 53]
    (.letOp (n := 103) (.exec 0x1104b2 (LoadPre 0x1104b2 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x38)) s (0x1104b2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1104b2 2 (.sib 6 (some 9) 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 6, .gpr 9] [])) #v[100, 6, 53]
    (.letOp (n := 104) (.out 0x1104b7 (addR64R64Effect 0x1104b7 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[102, 94]
    (.letOp (n := 105) (.exec 0x1104b7 (fun s => s.RIP = 0x1104b7) (addR64R64Effect 0x1104b7 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[102, 94]
    (.letOp (n := 106) (.out 0x1104ba (movR64R64Effect 0x1104ba 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[104]
    (.letOp (n := 107) (.exec 0x1104ba (fun s => s.RIP = 0x1104ba) (movR64R64Effect 0x1104ba 7 2) (Reg.operands [.gpr 2] [])) #v[104]
    (.letOp (n := 108) (.out 0x1104bd (shrR64Effect 0x1104bd 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[106]
    (.letOp (n := 109) (.exec 0x1104bd (fun s => s.RIP = 0x1104bd) (shrR64Effect 0x1104bd 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[106]
    (.letOp (n := 110) (.out 0x1104c1 (subR64M64Effect 0x1104c1 7 (.sib 6 (some 9) 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .gpr 9] []) (.reg (.gpr 7))) #v[108, 6, 53]
    (.letOp (n := 111) (.exec 0x1104c1 (LoadPre 0x1104c1 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x40)) s (0x1104c1 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1104c1 7 (.sib 6 (some 9) 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 6, .gpr 9] [])) #v[108, 6, 53]
    (.letOp (n := 112) (.out 0x1104c6 (movR64M64Effect 0x1104c6 10 (.sib 6 (some 9) 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6, .gpr 9] []) (.reg (.gpr 10))) #v[6, 53]
    (.letOp (n := 113) (.exec 0x1104c6 (LoadPre 0x1104c6 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x70)) s (0x1104c6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104c6 10 (.sib 6 (some 9) 0 (.d8 0x70))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 114) (.exec 0x1104cb (StorePre 0x1104cb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1104cb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104cb 10 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[112, 4]
    (.letOp (n := 115) (.out 0x1104d3 (movR64M64Effect 0x1104d3 10 (.sib 6 (some 9) 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6, .gpr 9] []) (.reg (.gpr 10))) #v[6, 53]
    (.letOp (n := 116) (.exec 0x1104d3 (LoadPre 0x1104d3 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x68)) s (0x1104d3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104d3 10 (.sib 6 (some 9) 0 (.d8 0x68))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 117) (.exec 0x1104d8 (StorePre 0x1104d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1104d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104d8 10 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[115, 4]
    (.letOp (n := 118) (.out 0x1104e0 (movR64M64Effect 0x1104e0 10 (.sib 6 (some 9) 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6, .gpr 9] []) (.reg (.gpr 10))) #v[6, 53]
    (.letOp (n := 119) (.exec 0x1104e0 (LoadPre 0x1104e0 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x60)) s (0x1104e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104e0 10 (.sib 6 (some 9) 0 (.d8 0x60))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 120) (.exec 0x1104e5 (StorePre 0x1104e5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x1104e5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104e5 10 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[118, 4]
    (.letOp (n := 121) (.out 0x1104ed (movR64M64Effect 0x1104ed 10 (.sib 6 (some 9) 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6, .gpr 9] []) (.reg (.gpr 10))) #v[6, 53]
    (.letOp (n := 122) (.exec 0x1104ed (LoadPre 0x1104ed (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x50)) s (0x1104ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104ed 10 (.sib 6 (some 9) 0 (.d8 0x50))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 123) (.out 0x1104f2 (movR64M64Effect 0x1104f2 6 (.sib 6 (some 9) 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[6, 53]
    (.letOp (n := 124) (.exec 0x1104f2 (LoadPre 0x1104f2 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x58)) s (0x1104f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104f2 6 (.sib 6 (some 9) 0 (.d8 0x58))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (b_l110418_2)))))))))))))))))))))))))))))))))))))

def bytes_l110418_1 : List UInt8 :=
  [0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x34, 0x4A, 0x2B, 0x4C, 0x0E, 0x30, 0x49, 0xBB, 0xFC, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00, 0x4C, 0x01, 0xD9, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x34,
    0x4A, 0x2B, 0x54, 0x0E, 0x38, 0x4C, 0x01, 0xDA, 0x48, 0x89, 0xD7, 0x48, 0xC1, 0xEF, 0x34, 0x4A,
    0x2B, 0x7C, 0x0E, 0x40, 0x4E, 0x8B, 0x54, 0x0E, 0x70, 0x4C, 0x89, 0x94, 0x24, 0x00, 0x01, 0x00,
    0x00, 0x4E, 0x8B, 0x54, 0x0E, 0x68, 0x4C, 0x89, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x4E, 0x8B,
    0x54, 0x0E, 0x60, 0x4C, 0x89, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x4E, 0x8B, 0x54, 0x0E, 0x50,
    0x4A, 0x8B, 0x74, 0x0E, 0x58] ++ bytes_l110418_2

theorem code_l110418_1 : ∀ x ∈ codeRange 0x110492 bytes_l110418_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10492 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110418_2

@[cfg_block] def b_l110418 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110418 (imulR64R64Imm8Effect 0x110418 4 9 7 0x78) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[7]
    (.letOp (n := 54) (.exec 0x110418 (fun s => s.RIP = 0x110418) (imulR64R64Imm8Effect 0x110418 4 9 7 0x78) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x11041c (movR64M64Effect 0x11041c 0 (.sib 6 (some 9) 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 9] []) (.reg (.gpr 0))) #v[6, 53]
    (.letOp (n := 56) (.exec 0x11041c (LoadPre 0x11041c (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x20)) s (0x11041c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11041c 0 (.sib 6 (some 9) 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 57) (.exec 0x110421 (StorePre 0x110421 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x110421 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110421 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x110429 (movR64M64Effect 0x110429 0 (.sib 6 (some 9) 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 9] []) (.reg (.gpr 0))) #v[6, 53]
    (.letOp (n := 59) (.exec 0x110429 (LoadPre 0x110429 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x18)) s (0x110429 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110429 0 (.sib 6 (some 9) 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 60) (.exec 0x11042e (StorePre 0x11042e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x11042e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11042e 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x110436 (movR64M64Effect 0x110436 0 (.sib 6 (some 9) 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 9] []) (.reg (.gpr 0))) #v[6, 53]
    (.letOp (n := 62) (.exec 0x110436 (LoadPre 0x110436 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x10)) s (0x110436 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110436 0 (.sib 6 (some 9) 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 63) (.exec 0x11043b (StorePre 0x11043b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x11043b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11043b 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x110443 (movR64M64Effect 0x110443 0 (.sib 6 (some 9) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 9] []) (.reg (.gpr 0))) #v[6, 53]
    (.letOp (n := 65) (.exec 0x110443 (LoadPre 0x110443 (fun s => AddrMode.addr (.sib 6 (some 9) 0 .none) s (0x110443 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110443 0 (.sib 6 (some 9) 0 .none)) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 66) (.out 0x110447 (movR64M64Effect 0x110447 1 (.sib 6 (some 9) 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 9] []) (.reg (.gpr 1))) #v[6, 53]
    (.letOp (n := 67) (.exec 0x110447 (LoadPre 0x110447 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x8)) s (0x110447 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110447 1 (.sib 6 (some 9) 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 68) (.exec 0x11044c (StorePre 0x11044c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x11044c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11044c 1 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.exec 0x110454 (StorePre 0x110454 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x110454 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110454 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 70) (.out 0x11045c (movR64Imm64Effect 0x11045c 8 0x3fffffffffffc) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 71) (.exec 0x11045c (fun s => s.RIP = 0x11045c) (movR64Imm64Effect 0x11045c 8 0x3fffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 72) (.out 0x110466 (subR64M64Effect 0x110466 8 (.sib 6 (some 9) 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .gpr 9] []) (.reg (.gpr 8))) #v[70, 6, 53]
    (.letOp (n := 73) (.exec 0x110466 (LoadPre 0x110466 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x48)) s (0x110466 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110466 8 (.sib 6 (some 9) 0 (.d8 0x48))) (Reg.operands [.gpr 8, .gpr 6, .gpr 9] [])) #v[70, 6, 53]
    (.letOp (n := 74) (.out 0x11046b (movR64R64Effect 0x11046b 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[72]
    (.letOp (n := 75) (.exec 0x11046b (fun s => s.RIP = 0x11046b) (movR64R64Effect 0x11046b 0 8) (Reg.operands [.gpr 8] [])) #v[72]
    (.letOp (n := 76) (.out 0x11046e (shrR64Effect 0x11046e 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 77) (.exec 0x11046e (fun s => s.RIP = 0x11046e) (shrR64Effect 0x11046e 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[74]
    (.letOp (n := 78) (.out 0x110472 (movR64Imm64Effect 0x110472 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 79) (.exec 0x110472 (fun s => s.RIP = 0x110472) (movR64Imm64Effect 0x110472 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 80) (.out 0x11047c (imulR64R64Effect 0x11047c 4 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[76, 78]
    (.letOp (n := 81) (.exec 0x11047c (fun s => s.RIP = 0x11047c) (imulR64R64Effect 0x11047c 4 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[76, 78]
    (.letOp (n := 82) (.out 0x110480 (subR64M64Effect 0x110480 0 (.sib 6 (some 9) 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6, .gpr 9] []) (.reg (.gpr 0))) #v[80, 6, 53]
    (.letOp (n := 83) (.exec 0x110480 (LoadPre 0x110480 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x28)) s (0x110480 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110480 0 (.sib 6 (some 9) 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 6, .gpr 9] [])) #v[80, 6, 53]
    (.letOp (n := 84) (.out 0x110485 (movR64Imm64Effect 0x110485 1 0x3ffffbfffff0bc) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 85) (.exec 0x110485 (fun s => s.RIP = 0x110485) (movR64Imm64Effect 0x110485 1 0x3ffffbfffff0bc) (Reg.operands [] [])) #v[]
    (.letOp (n := 86) (.out 0x11048f (addR64R64Effect 0x11048f 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[82, 84]
    (.letOp (n := 87) (.exec 0x11048f (fun s => s.RIP = 0x11048f) (addR64R64Effect 0x11048f 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[82, 84]
    (b_l110418_1)))))))))))))))))))))))))))))))))))

def bytes_l110418 : List UInt8 :=
  [0x4C, 0x6B, 0xCF, 0x78, 0x4A, 0x8B, 0x44, 0x0E, 0x20, 0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00,
    0x00, 0x4A, 0x8B, 0x44, 0x0E, 0x18, 0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x4A, 0x8B,
    0x44, 0x0E, 0x10, 0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x4A, 0x8B, 0x04, 0x0E, 0x4A,
    0x8B, 0x4C, 0x0E, 0x08, 0x48, 0x89, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24,
    0x08, 0x01, 0x00, 0x00, 0x49, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00, 0x4E, 0x2B,
    0x44, 0x0E, 0x48, 0x4C, 0x89, 0xC0, 0x48, 0xC1, 0xE8, 0x30, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xC1, 0x4A, 0x2B, 0x44, 0x0E, 0x28, 0x48, 0xB9, 0xBC,
    0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00, 0x48, 0x01, 0xC8] ++ bytes_l110418_1

theorem code_l110418 : ∀ x ∈ codeRange 0x110418 bytes_l110418, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10418 122 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110418_1

end K256.Proofs.Verify.LIR
