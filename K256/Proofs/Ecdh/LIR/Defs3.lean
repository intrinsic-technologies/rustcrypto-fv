import K256.Proofs.Ecdh.LIR.Defs4
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

def b_l10a410_98 : Block Op Label signature Reg.count 4148 :=
  .letOp (n := 4148) (.out 0x10c68b (movR64Imm64Effect 0x10c68b 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 4149) (.exec 0x10c68b (fun s => s.RIP = 0x10c68b) (movR64Imm64Effect 0x10c68b 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 4150) (.out 0x10c695 (andR64R64Effect 0x10c695 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[4120, 4148]
    (.letOp (n := 4151) (.exec 0x10c695 (fun s => s.RIP = 0x10c695) (andR64R64Effect 0x10c695 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[4120, 4148]
    (.letOp (n := 4152) (.exec 0x10c698 (StorePre 0x10c698 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10c698 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c698 9 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[4150, 65]
    (.letOp (n := 4153) (.out 0x10c6a0 (movR64M64Effect 0x10c6a0 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4154) (.exec 0x10c6a0 (LoadPre 0x10c6a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10c6a0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c6a0 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4155) (.out 0x10c6a5 (mulR64Effect 0x10c6a5 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[4050, 4153]
    (.letOp (n := 4156) (.out 0x10c6a5 (mulR64Effect 0x10c6a5 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[4050, 4153]
    (.letOp (n := 4157) (.exec 0x10c6a5 (fun s => s.RIP = 0x10c6a5) (mulR64Effect 0x10c6a5 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[4050, 4153]
    (.letOp (n := 4158) (.out 0x10c6a8 (movR64R64Effect 0x10c6a8 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[4156]
    (.letOp (n := 4159) (.exec 0x10c6a8 (fun s => s.RIP = 0x10c6a8) (movR64R64Effect 0x10c6a8 9 2) (Reg.operands [.gpr 2] [])) #v[4156]
    (.letOp (n := 4160) (.out 0x10c6ab (movR64R64Effect 0x10c6ab 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[4155]
    (.letOp (n := 4161) (.exec 0x10c6ab (fun s => s.RIP = 0x10c6ab) (movR64R64Effect 0x10c6ab 15 0) (Reg.operands [.gpr 0] [])) #v[4155]
    (.letOp (n := 4162) (.out 0x10c6ae (movR64M64Effect 0x10c6ae 11 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 4163) (.exec 0x10c6ae (LoadPre 0x10c6ae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10c6ae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c6ae 11 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4164) (.out 0x10c6b3 (movR64R64Effect 0x10c6b3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[4162]
    (.letOp (n := 4165) (.exec 0x10c6b3 (fun s => s.RIP = 0x10c6b3) (movR64R64Effect 0x10c6b3 0 11) (Reg.operands [.gpr 11] [])) #v[4162]
    (.letOp (n := 4166) (.out 0x10c6b6 (mulR64Effect 0x10c6b6 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[4063, 4164]
    (.letOp (n := 4167) (.out 0x10c6b6 (mulR64Effect 0x10c6b6 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[4063, 4164]
    (.letOp (n := 4168) (.exec 0x10c6b6 (fun s => s.RIP = 0x10c6b6) (mulR64Effect 0x10c6b6 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[4063, 4164]
    (.letOp (n := 4169) (.out 0x10c6b9 (movR64R64Effect 0x10c6b9 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[4063]
    (.letOp (n := 4170) (.exec 0x10c6b9 (fun s => s.RIP = 0x10c6b9) (movR64R64Effect 0x10c6b9 3 8) (Reg.operands [.gpr 8] [])) #v[4063]
    (.letOp (n := 4171) (.out 0x10c6bc (movR64R64Effect 0x10c6bc 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[4166]
    (.letOp (n := 4172) (.exec 0x10c6bc (fun s => s.RIP = 0x10c6bc) (movR64R64Effect 0x10c6bc 8 0) (Reg.operands [.gpr 0] [])) #v[4166]
    (.letOp (n := 4173) (.out 0x10c6bf (addR64R64Effect 0x10c6bf 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[4171, 4160]
    (.letOp (n := 4174) (.out 0x10c6bf (addR64R64Effect 0x10c6bf 8 15) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 15] []) (.flag .CF)) #v[4171, 4160]
    (.letOp (n := 4175) (.exec 0x10c6bf (fun s => s.RIP = 0x10c6bf) (addR64R64Effect 0x10c6bf 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[4171, 4160]
    (.letOp (n := 4176) (.out 0x10c6c2 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c6c2 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[4158, 4167, 4174]
    (.letOp (n := 4177) (.exec 0x10c6c2 (fun s => s.RIP = 0x10c6c2) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c6c2 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4158, 4167, 4174]
    (.letOp (n := 4178) (.out 0x10c6c5 (addR64R64Effect 0x10c6c5 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[4173, 4144]
    (.letOp (n := 4179) (.out 0x10c6c5 (addR64R64Effect 0x10c6c5 8 7) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 7] []) (.flag .CF)) #v[4173, 4144]
    (.letOp (n := 4180) (.exec 0x10c6c5 (fun s => s.RIP = 0x10c6c5) (addR64R64Effect 0x10c6c5 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[4173, 4144]
    (.letOp (n := 4181) (.out 0x10c6c8 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c6c8 9 14)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[4176, 4146, 4179]
    (.letOp (n := 4182) (.exec 0x10c6c8 (fun s => s.RIP = 0x10c6c8) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c6c8 9 14)) (Reg.operands [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4176, 4146, 4179]
    (.letOp (n := 4183) (.out 0x10c6cb (addR64R64Effect 0x10c6cb 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[4178, 4090]
    (.letOp (n := 4184) (.out 0x10c6cb (addR64R64Effect 0x10c6cb 8 1) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 1] []) (.flag .CF)) #v[4178, 4090]
    (.letOp (n := 4185) (.exec 0x10c6cb (fun s => s.RIP = 0x10c6cb) (addR64R64Effect 0x10c6cb 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[4178, 4090]
    (.letOp (n := 4186) (.out 0x10c6ce (atFlags StatusFlags.CF (adcR64R64Effect 0x10c6ce 9 12)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[4181, 4100, 4184]
    (.letOp (n := 4187) (.exec 0x10c6ce (fun s => s.RIP = 0x10c6ce) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c6ce 9 12)) (Reg.operands [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4181, 4100, 4184]
    (.letOp (n := 4188) (.out 0x10c6d1 (movR64R64Effect 0x10c6d1 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[4183]
    (.letOp (n := 4189) (.exec 0x10c6d1 (fun s => s.RIP = 0x10c6d1) (movR64R64Effect 0x10c6d1 0 8) (Reg.operands [.gpr 8] [])) #v[4183]
    (.letOp (n := 4190) (.out 0x10c6d4 (movR64Imm64Effect 0x10c6d4 14 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 4191) (.exec 0x10c6d4 (fun s => s.RIP = 0x10c6d4) (movR64Imm64Effect 0x10c6d4 14 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l10a410_99))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_98 : List UInt8 :=
  [0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xC1, 0x4C, 0x89, 0x8C,
    0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD1,
    0x49, 0x89, 0xC7, 0x4C, 0x8B, 0x5C, 0x24, 0x30, 0x4C, 0x89, 0xD8, 0x49, 0xF7, 0xE0, 0x4C, 0x89,
    0xC3, 0x49, 0x89, 0xC0, 0x4D, 0x01, 0xF8, 0x49, 0x11, 0xD1, 0x49, 0x01, 0xF8, 0x4D, 0x11, 0xF1,
    0x49, 0x01, 0xC8, 0x4D, 0x11, 0xE1, 0x4C, 0x89, 0xC0, 0x49, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x0F, 0x00] ++ bytes_l10a410_99

theorem code_l10a410_98 : ∀ x ∈ codeRange 0x10c68b bytes_l10a410_98, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc68b 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_99

def b_l10a410_97 : Block Op Label signature Reg.count 4107 :=
  .letOp (n := 4107) (.out 0x10c625 (movR64R64Effect 0x10c625 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[4105]
    (.letOp (n := 4108) (.exec 0x10c625 (fun s => s.RIP = 0x10c625) (movR64R64Effect 0x10c625 10 2) (Reg.operands [.gpr 2] [])) #v[4105]
    (.letOp (n := 4109) (.out 0x10c628 (addR64M64Effect 0x10c628 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4104, 65]
    (.letOp (n := 4110) (.out 0x10c628 (addR64M64Effect 0x10c628 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[4104, 65]
    (.letOp (n := 4111) (.exec 0x10c628 (LoadPre 0x10c628 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10c628 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10c628 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4104, 65]
    (.letOp (n := 4112) (.out 0x10c630 (atFlags StatusFlags.CF (adcR64M64Effect 0x10c630 10 (.sib 4 none 0 (.d32 0x88)))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 10))) #v[4107, 65, 4110]
    (.letOp (n := 4113) (.exec 0x10c630 (LoadPre 0x10c630 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10c630 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10c630 10 (.sib 4 none 0 (.d32 0x88)))) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4107, 65, 4110]
    (.letOp (n := 4114) (.out 0x10c638 (movR64R64Effect 0x10c638 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 10] []) (.reg (.gpr 13))) #v[4112]
    (.letOp (n := 4115) (.exec 0x10c638 (fun s => s.RIP = 0x10c638) (movR64R64Effect 0x10c638 13 10) (Reg.operands [.gpr 10] [])) #v[4112]
    (.letOp (n := 4116) (.out 0x10c63b (shrR64Effect 0x10c63b 4 13 52) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[4114]
    (.letOp (n := 4117) (.exec 0x10c63b (fun s => s.RIP = 0x10c63b) (shrR64Effect 0x10c63b 4 13 52) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4114]
    (.letOp (n := 4118) (.out 0x10c63f (shldR64R64Effect 0x10c63f 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[4112, 4109]
    (.letOp (n := 4119) (.exec 0x10c63f (fun s => s.RIP = 0x10c63f) (shldR64R64Effect 0x10c63f 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4112, 4109]
    (.letOp (n := 4120) (.out 0x10c644 (movR64R64Effect 0x10c644 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[4109]
    (.letOp (n := 4121) (.exec 0x10c644 (fun s => s.RIP = 0x10c644) (movR64R64Effect 0x10c644 9 0) (Reg.operands [.gpr 0] [])) #v[4109]
    (.letOp (n := 4122) (.out 0x10c647 (movR64R64Effect 0x10c647 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[4059]
    (.letOp (n := 4123) (.exec 0x10c647 (fun s => s.RIP = 0x10c647) (movR64R64Effect 0x10c647 0 6) (Reg.operands [.gpr 6] [])) #v[4059]
    (.letOp (n := 4124) (.out 0x10c64a (mulR64Effect 0x10c64a 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[4021, 4122]
    (.letOp (n := 4125) (.out 0x10c64a (mulR64Effect 0x10c64a 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[4021, 4122]
    (.letOp (n := 4126) (.exec 0x10c64a (fun s => s.RIP = 0x10c64a) (mulR64Effect 0x10c64a 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[4021, 4122]
    (.letOp (n := 4127) (.exec 0x10c64d (StorePre 0x10c64d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10c64d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c64d 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[4125, 65]
    (.letOp (n := 4128) (.exec 0x10c655 (StorePre 0x10c655 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10c655 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c655 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4124, 65]
    (.letOp (n := 4129) (.out 0x10c65d (movR64M64Effect 0x10c65d 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4130) (.exec 0x10c65d (LoadPre 0x10c65d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10c65d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c65d 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4131) (.out 0x10c662 (mulM64Effect 0x10c662 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4129, 65]
    (.letOp (n := 4132) (.out 0x10c662 (mulM64Effect 0x10c662 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4129, 65]
    (.letOp (n := 4133) (.exec 0x10c662 (LoadPre 0x10c662 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10c662 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10c662 8 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4129, 65]
    (.letOp (n := 4134) (.out 0x10c66a (movR64R64Effect 0x10c66a 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[4132]
    (.letOp (n := 4135) (.exec 0x10c66a (fun s => s.RIP = 0x10c66a) (movR64R64Effect 0x10c66a 6 2) (Reg.operands [.gpr 2] [])) #v[4132]
    (.letOp (n := 4136) (.exec 0x10c66d (StorePre 0x10c66d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10c66d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c66d 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4131, 65]
    (.letOp (n := 4137) (.out 0x10c675 (movR64M64Effect 0x10c675 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4138) (.exec 0x10c675 (LoadPre 0x10c675 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10c675 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c675 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4139) (.out 0x10c67a (movR64M64Effect 0x10c67a 5 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 4140) (.exec 0x10c67a (LoadPre 0x10c67a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10c67a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c67a 5 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4141) (.out 0x10c682 (mulR64Effect 0x10c682 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[4139, 4137]
    (.letOp (n := 4142) (.out 0x10c682 (mulR64Effect 0x10c682 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[4139, 4137]
    (.letOp (n := 4143) (.exec 0x10c682 (fun s => s.RIP = 0x10c682) (mulR64Effect 0x10c682 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[4139, 4137]
    (.letOp (n := 4144) (.out 0x10c685 (movR64R64Effect 0x10c685 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[4141]
    (.letOp (n := 4145) (.exec 0x10c685 (fun s => s.RIP = 0x10c685) (movR64R64Effect 0x10c685 7 0) (Reg.operands [.gpr 0] [])) #v[4141]
    (.letOp (n := 4146) (.out 0x10c688 (movR64R64Effect 0x10c688 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[4142]
    (.letOp (n := 4147) (.exec 0x10c688 (fun s => s.RIP = 0x10c688) (movR64R64Effect 0x10c688 14 2) (Reg.operands [.gpr 2] [])) #v[4142]
    (b_l10a410_98)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_97 : List UInt8 :=
  [0x49, 0x89, 0xD2, 0x48, 0x03, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x94, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x4D, 0x89, 0xD5, 0x49, 0xC1, 0xED, 0x34, 0x49, 0x0F, 0xA4, 0xC2, 0x0C, 0x49,
    0x89, 0xC1, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0xF7, 0xA4,
    0x24, 0x20, 0x01, 0x00, 0x00, 0x48, 0x89, 0xD6, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x8B, 0xAC, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE5,
    0x48, 0x89, 0xC7, 0x49, 0x89, 0xD6] ++ bytes_l10a410_98

theorem code_l10a410_97 : ∀ x ∈ codeRange 0x10c625 bytes_l10a410_97, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc625 102 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_98

def b_l10a410_96 : Block Op Label signature Reg.count 4061 :=
  .letOp (n := 4061) (.out 0x10c5d2 (movR64R64Effect 0x10c5d2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[4059]
    (.letOp (n := 4062) (.exec 0x10c5d2 (fun s => s.RIP = 0x10c5d2) (movR64R64Effect 0x10c5d2 0 6) (Reg.operands [.gpr 6] [])) #v[4059]
    (.letOp (n := 4063) (.out 0x10c5d5 (movR64M64Effect 0x10c5d5 8 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 4064) (.exec 0x10c5d5 (LoadPre 0x10c5d5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10c5d5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c5d5 8 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4065) (.out 0x10c5dd (mulR64Effect 0x10c5dd 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[4063, 4061]
    (.letOp (n := 4066) (.out 0x10c5dd (mulR64Effect 0x10c5dd 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[4063, 4061]
    (.letOp (n := 4067) (.exec 0x10c5dd (fun s => s.RIP = 0x10c5dd) (mulR64Effect 0x10c5dd 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[4063, 4061]
    (.letOp (n := 4068) (.out 0x10c5e0 (addR64R64Effect 0x10c5e0 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[4065, 4057]
    (.letOp (n := 4069) (.out 0x10c5e0 (addR64R64Effect 0x10c5e0 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[4065, 4057]
    (.letOp (n := 4070) (.exec 0x10c5e0 (fun s => s.RIP = 0x10c5e0) (addR64R64Effect 0x10c5e0 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[4065, 4057]
    (.letOp (n := 4071) (.out 0x10c5e3 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c5e3 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4055, 4066, 4069]
    (.letOp (n := 4072) (.exec 0x10c5e3 (fun s => s.RIP = 0x10c5e3) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c5e3 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4055, 4066, 4069]
    (.letOp (n := 4073) (.out 0x10c5e6 (addR64R64Effect 0x10c5e6 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[4068, 4042]
    (.letOp (n := 4074) (.out 0x10c5e6 (addR64R64Effect 0x10c5e6 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[4068, 4042]
    (.letOp (n := 4075) (.exec 0x10c5e6 (fun s => s.RIP = 0x10c5e6) (addR64R64Effect 0x10c5e6 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[4068, 4042]
    (.letOp (n := 4076) (.out 0x10c5e9 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c5e9 1 11)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4071, 4044, 4074]
    (.letOp (n := 4077) (.exec 0x10c5e9 (fun s => s.RIP = 0x10c5e9) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c5e9 1 11)) (Reg.operands [.gpr 1, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4071, 4044, 4074]
    (.letOp (n := 4078) (.out 0x10c5ec (addR64R64Effect 0x10c5ec 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[4073, 4035]
    (.letOp (n := 4079) (.out 0x10c5ec (addR64R64Effect 0x10c5ec 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[4073, 4035]
    (.letOp (n := 4080) (.exec 0x10c5ec (fun s => s.RIP = 0x10c5ec) (addR64R64Effect 0x10c5ec 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[4073, 4035]
    (.letOp (n := 4081) (.out 0x10c5ef (atFlags StatusFlags.CF (adcR64R64Effect 0x10c5ef 1 13)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4076, 4033, 4079]
    (.letOp (n := 4082) (.exec 0x10c5ef (fun s => s.RIP = 0x10c5ef) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c5ef 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4076, 4033, 4079]
    (.letOp (n := 4083) (.out 0x10c5f2 (addR64R64Effect 0x10c5f2 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[4078, 4011]
    (.letOp (n := 4084) (.out 0x10c5f2 (addR64R64Effect 0x10c5f2 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[4078, 4011]
    (.letOp (n := 4085) (.exec 0x10c5f2 (fun s => s.RIP = 0x10c5f2) (addR64R64Effect 0x10c5f2 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[4078, 4011]
    (.letOp (n := 4086) (.out 0x10c5f5 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c5f5 1 12)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4081, 4013, 4084]
    (.letOp (n := 4087) (.exec 0x10c5f5 (fun s => s.RIP = 0x10c5f5) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c5f5 1 12)) (Reg.operands [.gpr 1, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4081, 4013, 4084]
    (.letOp (n := 4088) (.out 0x10c5f8 (movR64R64Effect 0x10c5f8 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[4086]
    (.letOp (n := 4089) (.exec 0x10c5f8 (fun s => s.RIP = 0x10c5f8) (movR64R64Effect 0x10c5f8 12 1) (Reg.operands [.gpr 1] [])) #v[4086]
    (.letOp (n := 4090) (.out 0x10c5fb (shldR64R64Effect 0x10c5fb 5 1 0 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4086, 4083]
    (.letOp (n := 4091) (.exec 0x10c5fb (fun s => s.RIP = 0x10c5fb) (shldR64R64Effect 0x10c5fb 5 1 0 12) (Reg.operands [.gpr 1, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4086, 4083]
    (.letOp (n := 4092) (.out 0x10c600 (shlR64Effect 0x10c600 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4083]
    (.letOp (n := 4093) (.exec 0x10c600 (fun s => s.RIP = 0x10c600) (shlR64Effect 0x10c600 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4083]
    (.letOp (n := 4094) (.out 0x10c604 (movR64Imm64Effect 0x10c604 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 4095) (.exec 0x10c604 (fun s => s.RIP = 0x10c604) (movR64Imm64Effect 0x10c604 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 4096) (.out 0x10c60e (andR64R64Effect 0x10c60e 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[4092, 4094]
    (.letOp (n := 4097) (.exec 0x10c60e (fun s => s.RIP = 0x10c60e) (andR64R64Effect 0x10c60e 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[4092, 4094]
    (.letOp (n := 4098) (.out 0x10c611 (orR64R64Effect 0x10c611 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[4096, 4046]
    (.letOp (n := 4099) (.exec 0x10c611 (fun s => s.RIP = 0x10c611) (orR64R64Effect 0x10c611 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[4096, 4046]
    (.letOp (n := 4100) (.out 0x10c614 (shrR64Effect 0x10c614 4 12 52) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[4088]
    (.letOp (n := 4101) (.exec 0x10c614 (fun s => s.RIP = 0x10c614) (shrR64Effect 0x10c614 4 12 52) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4088]
    (.letOp (n := 4102) (.out 0x10c618 (movR64Imm64Effect 0x10c618 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 4103) (.exec 0x10c618 (fun s => s.RIP = 0x10c618) (movR64Imm64Effect 0x10c618 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 4104) (.out 0x10c622 (mulR64Effect 0x10c622 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[4102, 4098]
    (.letOp (n := 4105) (.out 0x10c622 (mulR64Effect 0x10c622 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[4102, 4098]
    (.letOp (n := 4106) (.exec 0x10c622 (fun s => s.RIP = 0x10c622) (mulR64Effect 0x10c622 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[4102, 4098]
    (b_l10a410_97))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_96 : List UInt8 :=
  [0x48, 0x89, 0xF0, 0x4C, 0x8B, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE0, 0x4C, 0x01,
    0xF0, 0x48, 0x11, 0xD1, 0x48, 0x01, 0xF8, 0x4C, 0x11, 0xD9, 0x4C, 0x01, 0xD0, 0x4C, 0x11, 0xE9,
    0x4C, 0x01, 0xC8, 0x4C, 0x11, 0xE1, 0x49, 0x89, 0xCC, 0x48, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0xC1,
    0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x4C,
    0x09, 0xF8, 0x49, 0xC1, 0xEC, 0x34, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE2] ++ bytes_l10a410_97

theorem code_l10a410_96 : ∀ x ∈ codeRange 0x10c5d2 bytes_l10a410_96, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc5d2 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_97

def b_l10a410_95 : Block Op Label signature Reg.count 4019 :=
  .letOp (n := 4019) (.out 0x10c572 (movR64R64Effect 0x10c572 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[3946]
    (.letOp (n := 4020) (.exec 0x10c572 (fun s => s.RIP = 0x10c572) (movR64R64Effect 0x10c572 0 5) (Reg.operands [.gpr 5] [])) #v[3946]
    (.letOp (n := 4021) (.out 0x10c575 (movR64M64Effect 0x10c575 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 4022) (.exec 0x10c575 (LoadPre 0x10c575 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10c575 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c575 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4023) (.out 0x10c57a (mulR64Effect 0x10c57a 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[4021, 4019]
    (.letOp (n := 4024) (.out 0x10c57a (mulR64Effect 0x10c57a 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[4021, 4019]
    (.letOp (n := 4025) (.exec 0x10c57a (fun s => s.RIP = 0x10c57a) (mulR64Effect 0x10c57a 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[4021, 4019]
    (.letOp (n := 4026) (.exec 0x10c57d (StorePre 0x10c57d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10c57d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c57d 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[4024, 65]
    (.letOp (n := 4027) (.exec 0x10c585 (StorePre 0x10c585 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10c585 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c585 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4023, 65]
    (.letOp (n := 4028) (.out 0x10c58d (movR64M64Effect 0x10c58d 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4029) (.exec 0x10c58d (LoadPre 0x10c58d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10c58d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c58d 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4030) (.out 0x10c592 (mulM64Effect 0x10c592 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4028, 65]
    (.letOp (n := 4031) (.out 0x10c592 (mulM64Effect 0x10c592 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4028, 65]
    (.letOp (n := 4032) (.exec 0x10c592 (LoadPre 0x10c592 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10c592 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10c592 8 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4028, 65]
    (.letOp (n := 4033) (.out 0x10c59a (movR64R64Effect 0x10c59a 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[4031]
    (.letOp (n := 4034) (.exec 0x10c59a (fun s => s.RIP = 0x10c59a) (movR64R64Effect 0x10c59a 13 2) (Reg.operands [.gpr 2] [])) #v[4031]
    (.letOp (n := 4035) (.out 0x10c59d (movR64R64Effect 0x10c59d 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[4030]
    (.letOp (n := 4036) (.exec 0x10c59d (fun s => s.RIP = 0x10c59d) (movR64R64Effect 0x10c59d 10 0) (Reg.operands [.gpr 0] [])) #v[4030]
    (.letOp (n := 4037) (.out 0x10c5a0 (movR64M64Effect 0x10c5a0 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4038) (.exec 0x10c5a0 (LoadPre 0x10c5a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10c5a0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c5a0 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4039) (.out 0x10c5a5 (mulM64Effect 0x10c5a5 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4037, 65]
    (.letOp (n := 4040) (.out 0x10c5a5 (mulM64Effect 0x10c5a5 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4037, 65]
    (.letOp (n := 4041) (.exec 0x10c5a5 (LoadPre 0x10c5a5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10c5a5 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10c5a5 8 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4037, 65]
    (.letOp (n := 4042) (.out 0x10c5ad (movR64R64Effect 0x10c5ad 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[4039]
    (.letOp (n := 4043) (.exec 0x10c5ad (fun s => s.RIP = 0x10c5ad) (movR64R64Effect 0x10c5ad 7 0) (Reg.operands [.gpr 0] [])) #v[4039]
    (.letOp (n := 4044) (.out 0x10c5b0 (movR64R64Effect 0x10c5b0 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[4040]
    (.letOp (n := 4045) (.exec 0x10c5b0 (fun s => s.RIP = 0x10c5b0) (movR64R64Effect 0x10c5b0 11 2) (Reg.operands [.gpr 2] [])) #v[4040]
    (.letOp (n := 4046) (.out 0x10c5b3 (andR32Imm8Effect 0x10c5b3 4 15 0xf) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[4017]
    (.letOp (n := 4047) (.exec 0x10c5b3 (fun s => s.RIP = 0x10c5b3) (andR32Imm8Effect 0x10c5b3 4 15 0xf) (Reg.operands [.gpr 15] [])) #v[4017]
    (.letOp (n := 4048) (.out 0x10c5b7 (movR64M64Effect 0x10c5b7 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4049) (.exec 0x10c5b7 (LoadPre 0x10c5b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10c5b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c5b7 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4050) (.out 0x10c5bc (movR64M64Effect 0x10c5bc 3 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 4051) (.exec 0x10c5bc (LoadPre 0x10c5bc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10c5bc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c5bc 3 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4052) (.out 0x10c5c4 (mulR64Effect 0x10c5c4 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[4050, 4048]
    (.letOp (n := 4053) (.out 0x10c5c4 (mulR64Effect 0x10c5c4 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[4050, 4048]
    (.letOp (n := 4054) (.exec 0x10c5c4 (fun s => s.RIP = 0x10c5c4) (mulR64Effect 0x10c5c4 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[4050, 4048]
    (.letOp (n := 4055) (.out 0x10c5c7 (movR64R64Effect 0x10c5c7 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[4053]
    (.letOp (n := 4056) (.exec 0x10c5c7 (fun s => s.RIP = 0x10c5c7) (movR64R64Effect 0x10c5c7 1 2) (Reg.operands [.gpr 2] [])) #v[4053]
    (.letOp (n := 4057) (.out 0x10c5ca (movR64R64Effect 0x10c5ca 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[4052]
    (.letOp (n := 4058) (.exec 0x10c5ca (fun s => s.RIP = 0x10c5ca) (movR64R64Effect 0x10c5ca 14 0) (Reg.operands [.gpr 0] [])) #v[4052]
    (.letOp (n := 4059) (.out 0x10c5cd (movR64M64Effect 0x10c5cd 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 4060) (.exec 0x10c5cd (LoadPre 0x10c5cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10c5cd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c5cd 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_96))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_95 : List UInt8 :=
  [0x48, 0x89, 0xE8, 0x48, 0x8B, 0x6C, 0x24, 0x60, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0x94, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x48,
    0x48, 0xF7, 0xA4, 0x24, 0x20, 0x01, 0x00, 0x00, 0x49, 0x89, 0xD5, 0x49, 0x89, 0xC2, 0x48, 0x8B,
    0x44, 0x24, 0x58, 0x48, 0xF7, 0xA4, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x49, 0x89,
    0xD3, 0x41, 0x83, 0xE7, 0x0F, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x8B, 0x9C, 0x24, 0x08, 0x01,
    0x00, 0x00, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x74, 0x24, 0x28] ++ bytes_l10a410_96

theorem code_l10a410_95 : ∀ x ∈ codeRange 0x10c572 bytes_l10a410_95, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc572 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_96

def b_l10a410_94 : Block Op Label signature Reg.count 3974 :=
  .letOp (n := 3974) (.out 0x10c516 (shldR64R64Effect 0x10c516 5 1 8 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3910, 3972]
    (.letOp (n := 3975) (.exec 0x10c516 (fun s => s.RIP = 0x10c516) (shldR64R64Effect 0x10c516 5 1 8 12) (Reg.operands [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3910, 3972]
    (.letOp (n := 3976) (.out 0x10c51b (shrR64Effect 0x10c51b 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3970]
    (.letOp (n := 3977) (.exec 0x10c51b (fun s => s.RIP = 0x10c51b) (shrR64Effect 0x10c51b 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3970]
    (.letOp (n := 3978) (.out 0x10c51f (addR64R64Effect 0x10c51f 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[3953, 3944]
    (.letOp (n := 3979) (.out 0x10c51f (addR64R64Effect 0x10c51f 10 11) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 11] []) (.flag .CF)) #v[3953, 3944]
    (.letOp (n := 3980) (.exec 0x10c51f (fun s => s.RIP = 0x10c51f) (addR64R64Effect 0x10c51f 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[3953, 3944]
    (.letOp (n := 3981) (.out 0x10c522 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c522 9 13)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[3955, 3942, 3979]
    (.letOp (n := 3982) (.exec 0x10c522 (fun s => s.RIP = 0x10c522) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c522 9 13)) (Reg.operands [.gpr 9, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3955, 3942, 3979]
    (.letOp (n := 3983) (.out 0x10c525 (addR64R64Effect 0x10c525 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[3978, 3935]
    (.letOp (n := 3984) (.out 0x10c525 (addR64R64Effect 0x10c525 10 12) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 12] []) (.flag .CF)) #v[3978, 3935]
    (.letOp (n := 3985) (.exec 0x10c525 (fun s => s.RIP = 0x10c525) (addR64R64Effect 0x10c525 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[3978, 3935]
    (.letOp (n := 3986) (.out 0x10c528 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c528 9 7)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[3981, 3933, 3984]
    (.letOp (n := 3987) (.exec 0x10c528 (fun s => s.RIP = 0x10c528) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c528 9 7)) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3981, 3933, 3984]
    (.letOp (n := 3988) (.out 0x10c52b (addR64M64Effect 0x10c52b 10 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[3983, 65]
    (.letOp (n := 3989) (.out 0x10c52b (addR64M64Effect 0x10c52b 10 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[3983, 65]
    (.letOp (n := 3990) (.exec 0x10c52b (LoadPre 0x10c52b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10c52b + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10c52b 10 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[3983, 65]
    (.letOp (n := 3991) (.out 0x10c533 (atFlags StatusFlags.CF (adcR64M64Effect 0x10c533 9 (.sib 4 none 0 (.d32 0x110)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[3986, 65, 3989]
    (.letOp (n := 3992) (.exec 0x10c533 (LoadPre 0x10c533 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10c533 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10c533 9 (.sib 4 none 0 (.d32 0x110)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3986, 65, 3989]
    (.letOp (n := 3993) (.out 0x10c53b (addR64M64Effect 0x10c53b 10 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[3988, 65]
    (.letOp (n := 3994) (.out 0x10c53b (addR64M64Effect 0x10c53b 10 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[3988, 65]
    (.letOp (n := 3995) (.exec 0x10c53b (LoadPre 0x10c53b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10c53b + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10c53b 10 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[3988, 65]
    (.letOp (n := 3996) (.out 0x10c543 (atFlags StatusFlags.CF (adcR64M64Effect 0x10c543 9 (.sib 4 none 0 (.d32 0x88)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[3991, 65, 3994]
    (.letOp (n := 3997) (.exec 0x10c543 (LoadPre 0x10c543 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10c543 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10c543 9 (.sib 4 none 0 (.d32 0x88)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3991, 65, 3994]
    (.letOp (n := 3998) (.out 0x10c54b (addR64R64Effect 0x10c54b 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[3993, 3965]
    (.letOp (n := 3999) (.out 0x10c54b (addR64R64Effect 0x10c54b 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[3993, 3965]
    (.letOp (n := 4000) (.exec 0x10c54b (fun s => s.RIP = 0x10c54b) (addR64R64Effect 0x10c54b 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[3993, 3965]
    (.letOp (n := 4001) (.out 0x10c54e (atFlags StatusFlags.CF (adcR64R64Effect 0x10c54e 9 6)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[3996, 3968, 3999]
    (.letOp (n := 4002) (.exec 0x10c54e (fun s => s.RIP = 0x10c54e) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c54e 9 6)) (Reg.operands [.gpr 9, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3996, 3968, 3999]
    (.letOp (n := 4003) (.out 0x10c551 (addR64R64Effect 0x10c551 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[3998, 3974]
    (.letOp (n := 4004) (.out 0x10c551 (addR64R64Effect 0x10c551 10 1) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 1] []) (.flag .CF)) #v[3998, 3974]
    (.letOp (n := 4005) (.exec 0x10c551 (fun s => s.RIP = 0x10c551) (addR64R64Effect 0x10c551 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[3998, 3974]
    (.letOp (n := 4006) (.exec 0x10c554 (StorePre 0x10c554 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10c554 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c554 10 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[4003, 65]
    (.letOp (n := 4007) (.out 0x10c55c (atFlags StatusFlags.CF (adcR64R64Effect 0x10c55c 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[4001, 3976, 4004]
    (.letOp (n := 4008) (.exec 0x10c55c (fun s => s.RIP = 0x10c55c) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c55c 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4001, 3976, 4004]
    (.letOp (n := 4009) (.out 0x10c55f (movR64R64Effect 0x10c55f 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[4007]
    (.letOp (n := 4010) (.exec 0x10c55f (fun s => s.RIP = 0x10c55f) (movR64R64Effect 0x10c55f 12 9) (Reg.operands [.gpr 9] [])) #v[4007]
    (.letOp (n := 4011) (.out 0x10c562 (shldR64R64Effect 0x10c562 5 9 10 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4007, 4003]
    (.letOp (n := 4012) (.exec 0x10c562 (fun s => s.RIP = 0x10c562) (shldR64R64Effect 0x10c562 5 9 10 12) (Reg.operands [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4007, 4003]
    (.letOp (n := 4013) (.out 0x10c567 (shrR64Effect 0x10c567 4 12 52) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[4009]
    (.letOp (n := 4014) (.exec 0x10c567 (fun s => s.RIP = 0x10c567) (shrR64Effect 0x10c567 4 12 52) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4009]
    (.letOp (n := 4015) (.out 0x10c56b (movR64R64Effect 0x10c56b 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 10] []) (.reg (.gpr 15))) #v[4003]
    (.letOp (n := 4016) (.exec 0x10c56b (fun s => s.RIP = 0x10c56b) (movR64R64Effect 0x10c56b 15 10) (Reg.operands [.gpr 10] [])) #v[4003]
    (.letOp (n := 4017) (.out 0x10c56e (shrR64Effect 0x10c56e 4 15 48) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[4015]
    (.letOp (n := 4018) (.exec 0x10c56e (fun s => s.RIP = 0x10c56e) (shrR64Effect 0x10c56e 4 15 48) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4015]
    (b_l10a410_95)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_94 : List UInt8 :=
  [0x4C, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0xC1, 0xEA, 0x34, 0x4D, 0x01, 0xDA, 0x4D, 0x11, 0xE9, 0x4D,
    0x01, 0xE2, 0x49, 0x11, 0xF9, 0x4C, 0x03, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x8C,
    0x24, 0x10, 0x01, 0x00, 0x00, 0x4C, 0x03, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x8C,
    0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC2, 0x49, 0x11, 0xF1, 0x49, 0x01, 0xCA, 0x4C, 0x89,
    0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x49, 0x11, 0xD1, 0x4D, 0x89, 0xCC, 0x4D, 0x0F, 0xA4, 0xD1,
    0x0C, 0x49, 0xC1, 0xEC, 0x34, 0x4D, 0x89, 0xD7, 0x49, 0xC1, 0xEF, 0x30] ++ bytes_l10a410_95

theorem code_l10a410_94 : ∀ x ∈ codeRange 0x10c516 bytes_l10a410_94, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc516 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_95

def b_l10a410_93 : Block Op Label signature Reg.count 3930 :=
  .letOp (n := 3930) (.out 0x10c4ca (mulR64Effect 0x10c4ca 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[3843, 3928]
    (.letOp (n := 3931) (.out 0x10c4ca (mulR64Effect 0x10c4ca 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[3843, 3928]
    (.letOp (n := 3932) (.exec 0x10c4ca (fun s => s.RIP = 0x10c4ca) (mulR64Effect 0x10c4ca 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[3843, 3928]
    (.letOp (n := 3933) (.out 0x10c4cd (movR64R64Effect 0x10c4cd 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[3931]
    (.letOp (n := 3934) (.exec 0x10c4cd (fun s => s.RIP = 0x10c4cd) (movR64R64Effect 0x10c4cd 7 2) (Reg.operands [.gpr 2] [])) #v[3931]
    (.letOp (n := 3935) (.out 0x10c4d0 (movR64R64Effect 0x10c4d0 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[3930]
    (.letOp (n := 3936) (.exec 0x10c4d0 (fun s => s.RIP = 0x10c4d0) (movR64R64Effect 0x10c4d0 12 0) (Reg.operands [.gpr 0] [])) #v[3930]
    (.letOp (n := 3937) (.out 0x10c4d3 (movR64R64Effect 0x10c4d3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[3839]
    (.letOp (n := 3938) (.exec 0x10c4d3 (fun s => s.RIP = 0x10c4d3) (movR64R64Effect 0x10c4d3 0 15) (Reg.operands [.gpr 15] [])) #v[3839]
    (.letOp (n := 3939) (.out 0x10c4d6 (mulR64Effect 0x10c4d6 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[3852, 3937]
    (.letOp (n := 3940) (.out 0x10c4d6 (mulR64Effect 0x10c4d6 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[3852, 3937]
    (.letOp (n := 3941) (.exec 0x10c4d6 (fun s => s.RIP = 0x10c4d6) (mulR64Effect 0x10c4d6 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[3852, 3937]
    (.letOp (n := 3942) (.out 0x10c4d9 (movR64R64Effect 0x10c4d9 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[3940]
    (.letOp (n := 3943) (.exec 0x10c4d9 (fun s => s.RIP = 0x10c4d9) (movR64R64Effect 0x10c4d9 13 2) (Reg.operands [.gpr 2] [])) #v[3940]
    (.letOp (n := 3944) (.out 0x10c4dc (movR64R64Effect 0x10c4dc 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[3939]
    (.letOp (n := 3945) (.exec 0x10c4dc (fun s => s.RIP = 0x10c4dc) (movR64R64Effect 0x10c4dc 11 0) (Reg.operands [.gpr 0] [])) #v[3939]
    (.letOp (n := 3946) (.out 0x10c4df (movR64M64Effect 0x10c4df 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 3947) (.exec 0x10c4df (LoadPre 0x10c4df (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10c4df + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c4df 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3948) (.out 0x10c4e4 (movR64R64Effect 0x10c4e4 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[3946]
    (.letOp (n := 3949) (.exec 0x10c4e4 (fun s => s.RIP = 0x10c4e4) (movR64R64Effect 0x10c4e4 0 5) (Reg.operands [.gpr 5] [])) #v[3946]
    (.letOp (n := 3950) (.out 0x10c4e7 (mulR64Effect 0x10c4e7 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[3865, 3948]
    (.letOp (n := 3951) (.out 0x10c4e7 (mulR64Effect 0x10c4e7 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[3865, 3948]
    (.letOp (n := 3952) (.exec 0x10c4e7 (fun s => s.RIP = 0x10c4e7) (mulR64Effect 0x10c4e7 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[3865, 3948]
    (.letOp (n := 3953) (.out 0x10c4ea (movR64R64Effect 0x10c4ea 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[3950]
    (.letOp (n := 3954) (.exec 0x10c4ea (fun s => s.RIP = 0x10c4ea) (movR64R64Effect 0x10c4ea 10 0) (Reg.operands [.gpr 0] [])) #v[3950]
    (.letOp (n := 3955) (.out 0x10c4ed (movR64R64Effect 0x10c4ed 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[3951]
    (.letOp (n := 3956) (.exec 0x10c4ed (fun s => s.RIP = 0x10c4ed) (movR64R64Effect 0x10c4ed 9 2) (Reg.operands [.gpr 2] [])) #v[3951]
    (.letOp (n := 3957) (.out 0x10c4f0 (shrR64Effect 0x10c4f0 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3872]
    (.letOp (n := 3958) (.exec 0x10c4f0 (fun s => s.RIP = 0x10c4f0) (shrR64Effect 0x10c4f0 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3872]
    (.letOp (n := 3959) (.out 0x10c4f4 (movR64Imm64Effect 0x10c4f4 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 3960) (.exec 0x10c4f4 (fun s => s.RIP = 0x10c4f4) (movR64Imm64Effect 0x10c4f4 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 3961) (.out 0x10c4fe (imulR64R64Effect 0x10c4fe 4 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[3957, 3959]
    (.letOp (n := 3962) (.exec 0x10c4fe (fun s => s.RIP = 0x10c4fe) (imulR64R64Effect 0x10c4fe 4 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[3957, 3959]
    (.letOp (n := 3963) (.out 0x10c502 (movR64R64Effect 0x10c502 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3912]
    (.letOp (n := 3964) (.exec 0x10c502 (fun s => s.RIP = 0x10c502) (movR64R64Effect 0x10c502 0 3) (Reg.operands [.gpr 3] [])) #v[3912]
    (.letOp (n := 3965) (.out 0x10c505 (mulR64Effect 0x10c505 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[3959, 3963]
    (.letOp (n := 3966) (.out 0x10c505 (mulR64Effect 0x10c505 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3959, 3963]
    (.letOp (n := 3967) (.exec 0x10c505 (fun s => s.RIP = 0x10c505) (mulR64Effect 0x10c505 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3959, 3963]
    (.letOp (n := 3968) (.out 0x10c508 (addR64R64Effect 0x10c508 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[3961, 3966]
    (.letOp (n := 3969) (.exec 0x10c508 (fun s => s.RIP = 0x10c508) (addR64R64Effect 0x10c508 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[3961, 3966]
    (.letOp (n := 3970) (.out 0x10c50b (movR64R64Effect 0x10c50b 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[3910]
    (.letOp (n := 3971) (.exec 0x10c50b (fun s => s.RIP = 0x10c50b) (movR64R64Effect 0x10c50b 2 1) (Reg.operands [.gpr 1] [])) #v[3910]
    (.letOp (n := 3972) (.out 0x10c50e (movR64M64Effect 0x10c50e 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 3973) (.exec 0x10c50e (LoadPre 0x10c50e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10c50e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c50e 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_94))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_93 : List UInt8 :=
  [0x48, 0xF7, 0xE5, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC4, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE1, 0x49,
    0x89, 0xD5, 0x49, 0x89, 0xC3, 0x48, 0x8B, 0x6C, 0x24, 0x08, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE6,
    0x49, 0x89, 0xC2, 0x49, 0x89, 0xD1, 0x48, 0xC1, 0xEE, 0x34, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xF2, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0xE2, 0x48, 0x01,
    0xD6, 0x48, 0x89, 0xCA, 0x4C, 0x8B, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] ++ bytes_l10a410_94

theorem code_l10a410_93 : ∀ x ∈ codeRange 0x10c4ca bytes_l10a410_93, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc4ca 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_94

def b_l10a410_92 : Block Op Label signature Reg.count 3890 :=
  .letOp (n := 3890) (.exec 0x10c44c (StorePre 0x10c44c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10c44c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c44c 11 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[3888, 65]
    (.letOp (n := 3891) (.out 0x10c454 (addR64M64Effect 0x10c454 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[3859, 65]
    (.letOp (n := 3892) (.out 0x10c454 (addR64M64Effect 0x10c454 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[3859, 65]
    (.letOp (n := 3893) (.exec 0x10c454 (LoadPre 0x10c454 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10c454 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10c454 8 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[3859, 65]
    (.letOp (n := 3894) (.out 0x10c45c (atFlags StatusFlags.CF (adcR64M64Effect 0x10c45c 1 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[3857, 65, 3892]
    (.letOp (n := 3895) (.exec 0x10c45c (LoadPre 0x10c45c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10c45c + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10c45c 1 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3857, 65, 3892]
    (.letOp (n := 3896) (.out 0x10c464 (addR64M64Effect 0x10c464 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[3891, 65]
    (.letOp (n := 3897) (.out 0x10c464 (addR64M64Effect 0x10c464 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[3891, 65]
    (.letOp (n := 3898) (.exec 0x10c464 (LoadPre 0x10c464 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10c464 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10c464 8 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[3891, 65]
    (.letOp (n := 3899) (.out 0x10c46c (atFlags StatusFlags.CF (adcR64M64Effect 0x10c46c 1 (.sib 4 none 0 (.d32 0xa0)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[3894, 65, 3897]
    (.letOp (n := 3900) (.exec 0x10c46c (LoadPre 0x10c46c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10c46c + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10c46c 1 (.sib 4 none 0 (.d32 0xa0)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3894, 65, 3897]
    (.letOp (n := 3901) (.out 0x10c474 (addR64M64Effect 0x10c474 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[3896, 65]
    (.letOp (n := 3902) (.out 0x10c474 (addR64M64Effect 0x10c474 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[3896, 65]
    (.letOp (n := 3903) (.exec 0x10c474 (LoadPre 0x10c474 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10c474 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10c474 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[3896, 65]
    (.letOp (n := 3904) (.out 0x10c47c (atFlags StatusFlags.CF (adcR64M64Effect 0x10c47c 1 (.sib 4 none 0 (.d32 0xb8)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[3899, 65, 3902]
    (.letOp (n := 3905) (.exec 0x10c47c (LoadPre 0x10c47c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10c47c + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10c47c 1 (.sib 4 none 0 (.d32 0xb8)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3899, 65, 3902]
    (.letOp (n := 3906) (.out 0x10c484 (addR64R64Effect 0x10c484 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[3901, 3885]
    (.letOp (n := 3907) (.out 0x10c484 (addR64R64Effect 0x10c484 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[3901, 3885]
    (.letOp (n := 3908) (.exec 0x10c484 (fun s => s.RIP = 0x10c484) (addR64R64Effect 0x10c484 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3901, 3885]
    (.letOp (n := 3909) (.exec 0x10c487 (StorePre 0x10c487 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10c487 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c487 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[3906, 65]
    (.letOp (n := 3910) (.out 0x10c48f (atFlags StatusFlags.CF (adcR64R64Effect 0x10c48f 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[3904, 3886, 3907]
    (.letOp (n := 3911) (.exec 0x10c48f (fun s => s.RIP = 0x10c48f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c48f 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3904, 3886, 3907]
    (.letOp (n := 3912) (.out 0x10c492 (shrdR64R64Effect 0x10c492 5 3 6 52) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[3870, 3872]
    (.letOp (n := 3913) (.exec 0x10c492 (fun s => s.RIP = 0x10c492) (shrdR64R64Effect 0x10c492 5 3 6 52) (Reg.operands [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3870, 3872]
    (.letOp (n := 3914) (.out 0x10c497 (movR64R64Effect 0x10c497 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[3861]
    (.letOp (n := 3915) (.exec 0x10c497 (fun s => s.RIP = 0x10c497) (movR64R64Effect 0x10c497 0 7) (Reg.operands [.gpr 7] [])) #v[3861]
    (.letOp (n := 3916) (.out 0x10c49a (mulR64Effect 0x10c49a 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[3820, 3914]
    (.letOp (n := 3917) (.out 0x10c49a (mulR64Effect 0x10c49a 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[3820, 3914]
    (.letOp (n := 3918) (.exec 0x10c49a (fun s => s.RIP = 0x10c49a) (mulR64Effect 0x10c49a 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[3820, 3914]
    (.letOp (n := 3919) (.exec 0x10c49d (StorePre 0x10c49d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10c49d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c49d 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3917, 65]
    (.letOp (n := 3920) (.exec 0x10c4a5 (StorePre 0x10c4a5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10c4a5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c4a5 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3916, 65]
    (.letOp (n := 3921) (.out 0x10c4ad (movR64M64Effect 0x10c4ad 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3922) (.exec 0x10c4ad (LoadPre 0x10c4ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10c4ad + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c4ad 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3923) (.out 0x10c4b2 (mulR64Effect 0x10c4b2 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[3829, 3921]
    (.letOp (n := 3924) (.out 0x10c4b2 (mulR64Effect 0x10c4b2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[3829, 3921]
    (.letOp (n := 3925) (.exec 0x10c4b2 (fun s => s.RIP = 0x10c4b2) (mulR64Effect 0x10c4b2 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[3829, 3921]
    (.letOp (n := 3926) (.exec 0x10c4b5 (StorePre 0x10c4b5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10c4b5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c4b5 2 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3924, 65]
    (.letOp (n := 3927) (.exec 0x10c4bd (StorePre 0x10c4bd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10c4bd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c4bd 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3923, 65]
    (.letOp (n := 3928) (.out 0x10c4c5 (movR64M64Effect 0x10c4c5 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3929) (.exec 0x10c4c5 (LoadPre 0x10c4c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10c4c5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c4c5 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_93))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_92 : List UInt8 :=
  [0x4C, 0x89, 0x9C, 0x24, 0x38, 0x01, 0x00, 0x00, 0x4C, 0x03, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00,
    0x48, 0x13, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x03, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00,
    0x48, 0x13, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x03, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x48, 0x13, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC0, 0x4C, 0x89, 0x84, 0x24, 0xB8,
    0x00, 0x00, 0x00, 0x48, 0x11, 0xD1, 0x48, 0x0F, 0xAC, 0xF3, 0x34, 0x48, 0x89, 0xF8, 0x49, 0xF7,
    0xE4, 0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0x94, 0x24, 0x10, 0x01, 0x00,
    0x00, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x30] ++ bytes_l10a410_93

theorem code_l10a410_92 : ∀ x ∈ codeRange 0x10c44c bytes_l10a410_92, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc44c 126 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_93

def b_l10a410_91 : Block Op Label signature Reg.count 3849 :=
  .letOp (n := 3849) (.exec 0x10c3ea (StorePre 0x10c3ea 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10c3ea + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c3ea 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3845, 65]
    (.letOp (n := 3850) (.out 0x10c3f2 (movR64M64Effect 0x10c3f2 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3851) (.exec 0x10c3f2 (LoadPre 0x10c3f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10c3f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c3f2 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3852) (.out 0x10c3f7 (movR64M64Effect 0x10c3f7 9 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 3853) (.exec 0x10c3f7 (LoadPre 0x10c3f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10c3f7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c3f7 9 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3854) (.out 0x10c3ff (mulR64Effect 0x10c3ff 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[3852, 3850]
    (.letOp (n := 3855) (.out 0x10c3ff (mulR64Effect 0x10c3ff 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[3852, 3850]
    (.letOp (n := 3856) (.exec 0x10c3ff (fun s => s.RIP = 0x10c3ff) (mulR64Effect 0x10c3ff 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[3852, 3850]
    (.letOp (n := 3857) (.out 0x10c402 (movR64R64Effect 0x10c402 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[3855]
    (.letOp (n := 3858) (.exec 0x10c402 (fun s => s.RIP = 0x10c402) (movR64R64Effect 0x10c402 1 2) (Reg.operands [.gpr 2] [])) #v[3855]
    (.letOp (n := 3859) (.out 0x10c405 (movR64R64Effect 0x10c405 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[3854]
    (.letOp (n := 3860) (.exec 0x10c405 (fun s => s.RIP = 0x10c405) (movR64R64Effect 0x10c405 8 0) (Reg.operands [.gpr 0] [])) #v[3854]
    (.letOp (n := 3861) (.out 0x10c408 (movR64M64Effect 0x10c408 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 3862) (.exec 0x10c408 (LoadPre 0x10c408 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10c408 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c408 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3863) (.out 0x10c40d (movR64R64Effect 0x10c40d 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[3861]
    (.letOp (n := 3864) (.exec 0x10c40d (fun s => s.RIP = 0x10c40d) (movR64R64Effect 0x10c40d 0 7) (Reg.operands [.gpr 7] [])) #v[3861]
    (.letOp (n := 3865) (.out 0x10c410 (movR64M64Effect 0x10c410 14 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 3866) (.exec 0x10c410 (LoadPre 0x10c410 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10c410 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c410 14 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3867) (.out 0x10c418 (mulR64Effect 0x10c418 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[3865, 3863]
    (.letOp (n := 3868) (.out 0x10c418 (mulR64Effect 0x10c418 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[3865, 3863]
    (.letOp (n := 3869) (.exec 0x10c418 (fun s => s.RIP = 0x10c418) (mulR64Effect 0x10c418 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[3865, 3863]
    (.letOp (n := 3870) (.out 0x10c41b (movR64R64Effect 0x10c41b 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[3867]
    (.letOp (n := 3871) (.exec 0x10c41b (fun s => s.RIP = 0x10c41b) (movR64R64Effect 0x10c41b 3 0) (Reg.operands [.gpr 0] [])) #v[3867]
    (.letOp (n := 3872) (.out 0x10c41e (movR64R64Effect 0x10c41e 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[3868]
    (.letOp (n := 3873) (.exec 0x10c41e (fun s => s.RIP = 0x10c41e) (movR64R64Effect 0x10c41e 6 2) (Reg.operands [.gpr 2] [])) #v[3868]
    (.letOp (n := 3874) (.out 0x10c421 (movR64Imm64Effect 0x10c421 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 3875) (.exec 0x10c421 (fun s => s.RIP = 0x10c421) (movR64Imm64Effect 0x10c421 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 3876) (.out 0x10c42b (andR64R64Effect 0x10c42b 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[3778, 3874]
    (.letOp (n := 3877) (.exec 0x10c42b (fun s => s.RIP = 0x10c42b) (andR64R64Effect 0x10c42b 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[3778, 3874]
    (.letOp (n := 3878) (.exec 0x10c42e (StorePre 0x10c42e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10c42e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c42e 10 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[3876, 65]
    (.letOp (n := 3879) (.out 0x10c436 (andR64R64Effect 0x10c436 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3867, 3874]
    (.letOp (n := 3880) (.exec 0x10c436 (fun s => s.RIP = 0x10c436) (andR64R64Effect 0x10c436 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3867, 3874]
    (.letOp (n := 3881) (.out 0x10c439 (movR64R64Effect 0x10c439 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[3874]
    (.letOp (n := 3882) (.exec 0x10c439 (fun s => s.RIP = 0x10c439) (movR64R64Effect 0x10c439 10 2) (Reg.operands [.gpr 2] [])) #v[3874]
    (.letOp (n := 3883) (.out 0x10c43c (movR64Imm64Effect 0x10c43c 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 3884) (.exec 0x10c43c (fun s => s.RIP = 0x10c43c) (movR64Imm64Effect 0x10c43c 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 3885) (.out 0x10c446 (mulR64Effect 0x10c446 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[3883, 3879]
    (.letOp (n := 3886) (.out 0x10c446 (mulR64Effect 0x10c446 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3883, 3879]
    (.letOp (n := 3887) (.exec 0x10c446 (fun s => s.RIP = 0x10c446) (mulR64Effect 0x10c446 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3883, 3879]
    (.letOp (n := 3888) (.out 0x10c449 (andR64R64Effect 0x10c449 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[3794, 3881]
    (.letOp (n := 3889) (.exec 0x10c449 (fun s => s.RIP = 0x10c449) (andR64R64Effect 0x10c449 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[3794, 3881]
    (b_l10a410_92)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_91 : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x4C, 0x8B, 0x8C,
    0x24, 0x08, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC0, 0x48, 0x8B,
    0x7C, 0x24, 0x48, 0x48, 0x89, 0xF8, 0x4C, 0x8B, 0xB4, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x49, 0xF7,
    0xE6, 0x48, 0x89, 0xC3, 0x48, 0x89, 0xD6, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F,
    0x00, 0x49, 0x21, 0xD2, 0x4C, 0x89, 0x94, 0x24, 0x40, 0x01, 0x00, 0x00, 0x48, 0x21, 0xD0, 0x49,
    0x89, 0xD2, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4D,
    0x21, 0xD3] ++ bytes_l10a410_92

theorem code_l10a410_91 : ∀ x ∈ codeRange 0x10c3ea bytes_l10a410_91, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc3ea 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_92

def b_l10a410_90 : Block Op Label signature Reg.count 3813 :=
  .letOp (n := 3813) (.out 0x10c37b (andR64R64Effect 0x10c37b 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[3762, 3517]
    (.letOp (n := 3814) (.exec 0x10c37b (fun s => s.RIP = 0x10c37b) (andR64R64Effect 0x10c37b 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[3762, 3517]
    (.letOp (n := 3815) (.exec 0x10c37e (StorePre 0x10c37e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x10c37e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c37e 9 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[3813, 65]
    (.letOp (n := 3816) (.out 0x10c386 (movR64R64Effect 0x10c386 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[3517]
    (.letOp (n := 3817) (.exec 0x10c386 (fun s => s.RIP = 0x10c386) (movR64R64Effect 0x10c386 1 13) (Reg.operands [.gpr 13] [])) #v[3517]
    (.letOp (n := 3818) (.out 0x10c389 (movR64R64Effect 0x10c389 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[3551]
    (.letOp (n := 3819) (.exec 0x10c389 (fun s => s.RIP = 0x10c389) (movR64R64Effect 0x10c389 0 12) (Reg.operands [.gpr 12] [])) #v[3551]
    (.letOp (n := 3820) (.out 0x10c38c (movR64M64Effect 0x10c38c 12 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 3821) (.exec 0x10c38c (LoadPre 0x10c38c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10c38c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c38c 12 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3822) (.out 0x10c391 (mulR64Effect 0x10c391 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[3820, 3818]
    (.letOp (n := 3823) (.out 0x10c391 (mulR64Effect 0x10c391 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[3820, 3818]
    (.letOp (n := 3824) (.exec 0x10c391 (fun s => s.RIP = 0x10c391) (mulR64Effect 0x10c391 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[3820, 3818]
    (.letOp (n := 3825) (.exec 0x10c394 (StorePre 0x10c394 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10c394 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c394 2 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3823, 65]
    (.letOp (n := 3826) (.exec 0x10c39c (StorePre 0x10c39c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10c39c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c39c 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3822, 65]
    (.letOp (n := 3827) (.out 0x10c3a4 (movR64M64Effect 0x10c3a4 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3828) (.exec 0x10c3a4 (LoadPre 0x10c3a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10c3a4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c3a4 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3829) (.out 0x10c3a9 (movR64M64Effect 0x10c3a9 13 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 3830) (.exec 0x10c3a9 (LoadPre 0x10c3a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10c3a9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c3a9 13 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3831) (.out 0x10c3b1 (mulR64Effect 0x10c3b1 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[3829, 3827]
    (.letOp (n := 3832) (.out 0x10c3b1 (mulR64Effect 0x10c3b1 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[3829, 3827]
    (.letOp (n := 3833) (.exec 0x10c3b1 (fun s => s.RIP = 0x10c3b1) (mulR64Effect 0x10c3b1 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[3829, 3827]
    (.letOp (n := 3834) (.exec 0x10c3b4 (StorePre 0x10c3b4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10c3b4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c3b4 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3831, 65]
    (.letOp (n := 3835) (.exec 0x10c3bc (StorePre 0x10c3bc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10c3bc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c3bc 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3832, 65]
    (.letOp (n := 3836) (.out 0x10c3c4 (andR64R64Effect 0x10c3c4 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[3768, 3816]
    (.letOp (n := 3837) (.exec 0x10c3c4 (fun s => s.RIP = 0x10c3c4) (andR64R64Effect 0x10c3c4 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[3768, 3816]
    (.letOp (n := 3838) (.exec 0x10c3c7 (StorePre 0x10c3c7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10c3c7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c3c7 8 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[3836, 65]
    (.letOp (n := 3839) (.out 0x10c3cf (movR64M64Effect 0x10c3cf 15 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 3840) (.exec 0x10c3cf (LoadPre 0x10c3cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10c3cf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c3cf 15 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3841) (.out 0x10c3d4 (movR64R64Effect 0x10c3d4 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[3839]
    (.letOp (n := 3842) (.exec 0x10c3d4 (fun s => s.RIP = 0x10c3d4) (movR64R64Effect 0x10c3d4 0 15) (Reg.operands [.gpr 15] [])) #v[3839]
    (.letOp (n := 3843) (.out 0x10c3d7 (movR64M64Effect 0x10c3d7 5 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 3844) (.exec 0x10c3d7 (LoadPre 0x10c3d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10c3d7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c3d7 5 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3845) (.out 0x10c3df (mulR64Effect 0x10c3df 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[3843, 3841]
    (.letOp (n := 3846) (.out 0x10c3df (mulR64Effect 0x10c3df 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[3843, 3841]
    (.letOp (n := 3847) (.exec 0x10c3df (fun s => s.RIP = 0x10c3df) (mulR64Effect 0x10c3df 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[3843, 3841]
    (.letOp (n := 3848) (.exec 0x10c3e2 (StorePre 0x10c3e2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10c3e2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c3e2 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3846, 65]
    (b_l10a410_91))))))))))))))))))))))))))))))))))))

def bytes_l10a410_90 : List UInt8 :=
  [0x4D, 0x21, 0xE9, 0x4C, 0x89, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE9, 0x4C, 0x89,
    0xE0, 0x4C, 0x8B, 0x64, 0x24, 0x60, 0x49, 0xF7, 0xE4, 0x48, 0x89, 0x94, 0x24, 0xB8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x4C, 0x8B,
    0xAC, 0x24, 0x20, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00,
    0x00, 0x48, 0x89, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0x21, 0xC8, 0x4C, 0x89, 0x84, 0x24,
    0x58, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x7C, 0x24, 0x28, 0x4C, 0x89, 0xF8, 0x48, 0x8B, 0xAC, 0x24,
    0x18, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00] ++ bytes_l10a410_91

theorem code_l10a410_90 : ∀ x ∈ codeRange 0x10c37b bytes_l10a410_90, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc37b 111 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_91

def b_l10a410_89 : Block Op Label signature Reg.count 3778 :=
  .letOp (n := 3778) (.out 0x10c326 (subR64R64Effect 0x10c326 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[3776, 3770]
    (.letOp (n := 3779) (.exec 0x10c326 (fun s => s.RIP = 0x10c326) (subR64R64Effect 0x10c326 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[3776, 3770]
    (.letOp (n := 3780) (.out 0x10c329 (andR64R64Effect 0x10c329 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[3730, 3517]
    (.letOp (n := 3781) (.exec 0x10c329 (fun s => s.RIP = 0x10c329) (andR64R64Effect 0x10c329 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[3730, 3517]
    (.letOp (n := 3782) (.out 0x10c32c (movR64R64Effect 0x10c32c 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[3778]
    (.letOp (n := 3783) (.exec 0x10c32c (fun s => s.RIP = 0x10c32c) (movR64R64Effect 0x10c32c 0 10) (Reg.operands [.gpr 10] [])) #v[3778]
    (.letOp (n := 3784) (.out 0x10c32f (shrR64Effect 0x10c32f 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3782]
    (.letOp (n := 3785) (.exec 0x10c32f (fun s => s.RIP = 0x10c32f) (shrR64Effect 0x10c32f 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3782]
    (.letOp (n := 3786) (.out 0x10c333 (leaR64Effect 0x10c333 2 (.sib 0 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 1] []) (.reg (.gpr 2))) #v[3784, 3780]
    (.letOp (n := 3787) (.exec 0x10c333 (fun s => s.RIP = 0x10c333) (leaR64Effect 0x10c333 2 (.sib 0 (some 1) 3 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3784, 3780]
    (.letOp (n := 3788) (.out 0x10c337 (subR64R64Effect 0x10c337 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[3786, 3780]
    (.letOp (n := 3789) (.exec 0x10c337 (fun s => s.RIP = 0x10c337) (subR64R64Effect 0x10c337 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[3786, 3780]
    (.letOp (n := 3790) (.out 0x10c33a (andR64R64Effect 0x10c33a 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[3744, 3734]
    (.letOp (n := 3791) (.exec 0x10c33a (fun s => s.RIP = 0x10c33a) (andR64R64Effect 0x10c33a 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[3744, 3734]
    (.letOp (n := 3792) (.out 0x10c33d (movR64R64Effect 0x10c33d 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[3788]
    (.letOp (n := 3793) (.exec 0x10c33d (fun s => s.RIP = 0x10c33d) (movR64R64Effect 0x10c33d 0 2) (Reg.operands [.gpr 2] [])) #v[3788]
    (.letOp (n := 3794) (.out 0x10c340 (movR64R64Effect 0x10c340 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[3788]
    (.letOp (n := 3795) (.exec 0x10c340 (fun s => s.RIP = 0x10c340) (movR64R64Effect 0x10c340 11 2) (Reg.operands [.gpr 2] [])) #v[3788]
    (.letOp (n := 3796) (.out 0x10c343 (shrR64Effect 0x10c343 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3792]
    (.letOp (n := 3797) (.exec 0x10c343 (fun s => s.RIP = 0x10c343) (shrR64Effect 0x10c343 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3792]
    (.letOp (n := 3798) (.out 0x10c347 (addR64R64Effect 0x10c347 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[3796, 3790]
    (.letOp (n := 3799) (.exec 0x10c347 (fun s => s.RIP = 0x10c347) (addR64R64Effect 0x10c347 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[3796, 3790]
    (.letOp (n := 3800) (.exec 0x10c34a (StorePre 0x10c34a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10c34a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c34a 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3798, 65]
    (.letOp (n := 3801) (.out 0x10c352 (andR64R64Effect 0x10c352 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[3641, 3517]
    (.letOp (n := 3802) (.exec 0x10c352 (fun s => s.RIP = 0x10c352) (andR64R64Effect 0x10c352 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[3641, 3517]
    (.letOp (n := 3803) (.exec 0x10c355 (StorePre 0x10c355 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10c355 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10c355 14 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[3801, 65]
    (.letOp (n := 3804) (.out 0x10c35a (andR64R64Effect 0x10c35a 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[3651, 3517]
    (.letOp (n := 3805) (.exec 0x10c35a (fun s => s.RIP = 0x10c35a) (andR64R64Effect 0x10c35a 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[3651, 3517]
    (.letOp (n := 3806) (.exec 0x10c35d (StorePre 0x10c35d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10c35d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c35d 3 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3804, 65]
    (.letOp (n := 3807) (.out 0x10c365 (andR64R64Effect 0x10c365 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[3669, 3517]
    (.letOp (n := 3808) (.exec 0x10c365 (fun s => s.RIP = 0x10c365) (andR64R64Effect 0x10c365 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[3669, 3517]
    (.letOp (n := 3809) (.exec 0x10c368 (StorePre 0x10c368 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10c368 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c368 15 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[3807, 65]
    (.letOp (n := 3810) (.out 0x10c370 (andR64R64Effect 0x10c370 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[3679, 3517]
    (.letOp (n := 3811) (.exec 0x10c370 (fun s => s.RIP = 0x10c370) (andR64R64Effect 0x10c370 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[3679, 3517]
    (.letOp (n := 3812) (.exec 0x10c373 (StorePre 0x10c373 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10c373 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c373 5 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[3810, 65]
    (b_l10a410_90)))))))))))))))))))))))))))))))))))

def bytes_l10a410_89 : List UInt8 :=
  [0x49, 0x29, 0xD2, 0x4C, 0x21, 0xE9, 0x4C, 0x89, 0xD0, 0x48, 0xC1, 0xE8, 0x34, 0x48, 0x8D, 0x14,
    0xC8, 0x48, 0x29, 0xCA, 0x4C, 0x21, 0xDF, 0x48, 0x89, 0xD0, 0x49, 0x89, 0xD3, 0x48, 0xC1, 0xE8,
    0x34, 0x48, 0x01, 0xF8, 0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4D, 0x21, 0xEE, 0x4C,
    0x89, 0x74, 0x24, 0x68, 0x4C, 0x21, 0xEB, 0x48, 0x89, 0x9C, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x4D,
    0x21, 0xEF, 0x4C, 0x89, 0xBC, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x21, 0xED, 0x48, 0x89, 0xAC,
    0x24, 0xC8, 0x00, 0x00, 0x00] ++ bytes_l10a410_90

theorem code_l10a410_89 : ∀ x ∈ codeRange 0x10c326 bytes_l10a410_89, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc326 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_90

def b_l10a410_88 : Block Op Label signature Reg.count 3738 :=
  .letOp (n := 3738) (.out 0x10c2dd (shrR64Effect 0x10c2dd 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[3736]
    (.letOp (n := 3739) (.exec 0x10c2dd (fun s => s.RIP = 0x10c2dd) (shrR64Effect 0x10c2dd 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3736]
    (.letOp (n := 3740) (.out 0x10c2e1 (addR64R64Effect 0x10c2e1 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[3738, 3732]
    (.letOp (n := 3741) (.exec 0x10c2e1 (fun s => s.RIP = 0x10c2e1) (addR64R64Effect 0x10c2e1 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[3738, 3732]
    (.letOp (n := 3742) (.out 0x10c2e4 (leaR64Effect 0x10c2e4 7 (.abs (some 8) 3 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[3740]
    (.letOp (n := 3743) (.exec 0x10c2e4 (fun s => s.RIP = 0x10c2e4) (leaR64Effect 0x10c2e4 7 (.abs (some 8) 3 0x0)) (Reg.operands [.gpr 8] [])) #v[3740]
    (.letOp (n := 3744) (.out 0x10c2ec (subR64R64Effect 0x10c2ec 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[3742, 3740]
    (.letOp (n := 3745) (.exec 0x10c2ec (fun s => s.RIP = 0x10c2ec) (subR64R64Effect 0x10c2ec 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[3742, 3740]
    (.letOp (n := 3746) (.out 0x10c2ef (andR64R64Effect 0x10c2ef 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[3700, 3517]
    (.letOp (n := 3747) (.exec 0x10c2ef (fun s => s.RIP = 0x10c2ef) (andR64R64Effect 0x10c2ef 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[3700, 3517]
    (.letOp (n := 3748) (.out 0x10c2f2 (movR64R64Effect 0x10c2f2 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[3744]
    (.letOp (n := 3749) (.exec 0x10c2f2 (fun s => s.RIP = 0x10c2f2) (movR64R64Effect 0x10c2f2 8 7) (Reg.operands [.gpr 7] [])) #v[3744]
    (.letOp (n := 3750) (.out 0x10c2f5 (shrR64Effect 0x10c2f5 4 8 48) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[3748]
    (.letOp (n := 3751) (.exec 0x10c2f5 (fun s => s.RIP = 0x10c2f5) (shrR64Effect 0x10c2f5 4 8 48) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3748]
    (.letOp (n := 3752) (.out 0x10c2f9 (imulR64R64Effect 0x10c2f9 4 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[3750, 3694]
    (.letOp (n := 3753) (.exec 0x10c2f9 (fun s => s.RIP = 0x10c2f9) (imulR64R64Effect 0x10c2f9 4 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[3750, 3694]
    (.letOp (n := 3754) (.out 0x10c2fd (leaR64Effect 0x10c2fd 8 (.sib 8 (some 0) 3 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[3752, 3746]
    (.letOp (n := 3755) (.exec 0x10c2fd (fun s => s.RIP = 0x10c2fd) (leaR64Effect 0x10c2fd 8 (.sib 8 (some 0) 3 .none)) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3752, 3746]
    (.letOp (n := 3756) (.out 0x10c301 (subR64R64Effect 0x10c301 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[3754, 3746]
    (.letOp (n := 3757) (.exec 0x10c301 (fun s => s.RIP = 0x10c301) (subR64R64Effect 0x10c301 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3754, 3746]
    (.letOp (n := 3758) (.out 0x10c304 (andR64R64Effect 0x10c304 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[3710, 3517]
    (.letOp (n := 3759) (.exec 0x10c304 (fun s => s.RIP = 0x10c304) (andR64R64Effect 0x10c304 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[3710, 3517]
    (.letOp (n := 3760) (.out 0x10c307 (movR64R64Effect 0x10c307 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[3756]
    (.letOp (n := 3761) (.exec 0x10c307 (fun s => s.RIP = 0x10c307) (movR64R64Effect 0x10c307 0 8) (Reg.operands [.gpr 8] [])) #v[3756]
    (.letOp (n := 3762) (.out 0x10c30a (movR64R64Effect 0x10c30a 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[3756]
    (.letOp (n := 3763) (.exec 0x10c30a (fun s => s.RIP = 0x10c30a) (movR64R64Effect 0x10c30a 9 8) (Reg.operands [.gpr 8] [])) #v[3756]
    (.letOp (n := 3764) (.out 0x10c30d (shrR64Effect 0x10c30d 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3760]
    (.letOp (n := 3765) (.exec 0x10c30d (fun s => s.RIP = 0x10c30d) (shrR64Effect 0x10c30d 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3760]
    (.letOp (n := 3766) (.out 0x10c311 (leaR64Effect 0x10c311 8 (.sib 0 (some 6) 3 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0, .gpr 6] []) (.reg (.gpr 8))) #v[3764, 3758]
    (.letOp (n := 3767) (.exec 0x10c311 (fun s => s.RIP = 0x10c311) (leaR64Effect 0x10c311 8 (.sib 0 (some 6) 3 .none)) (Reg.operands [.gpr 0, .gpr 6] [])) #v[3764, 3758]
    (.letOp (n := 3768) (.out 0x10c315 (subR64R64Effect 0x10c315 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[3766, 3758]
    (.letOp (n := 3769) (.exec 0x10c315 (fun s => s.RIP = 0x10c315) (subR64R64Effect 0x10c315 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[3766, 3758]
    (.letOp (n := 3770) (.out 0x10c318 (andR64R64Effect 0x10c318 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[3720, 3517]
    (.letOp (n := 3771) (.exec 0x10c318 (fun s => s.RIP = 0x10c318) (andR64R64Effect 0x10c318 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[3720, 3517]
    (.letOp (n := 3772) (.out 0x10c31b (movR64R64Effect 0x10c31b 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[3768]
    (.letOp (n := 3773) (.exec 0x10c31b (fun s => s.RIP = 0x10c31b) (movR64R64Effect 0x10c31b 0 8) (Reg.operands [.gpr 8] [])) #v[3768]
    (.letOp (n := 3774) (.out 0x10c31e (shrR64Effect 0x10c31e 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3772]
    (.letOp (n := 3775) (.exec 0x10c31e (fun s => s.RIP = 0x10c31e) (shrR64Effect 0x10c31e 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3772]
    (.letOp (n := 3776) (.out 0x10c322 (leaR64Effect 0x10c322 10 (.sib 0 (some 2) 3 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0, .gpr 2] []) (.reg (.gpr 10))) #v[3774, 3770]
    (.letOp (n := 3777) (.exec 0x10c322 (fun s => s.RIP = 0x10c322) (leaR64Effect 0x10c322 10 (.sib 0 (some 2) 3 .none)) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3774, 3770]
    (b_l10a410_89))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_88 : List UInt8 :=
  [0x49, 0xC1, 0xE8, 0x34, 0x49, 0x01, 0xF8, 0x4A, 0x8D, 0x3C, 0xC5, 0x00, 0x00, 0x00, 0x00, 0x4C,
    0x29, 0xC7, 0x4C, 0x21, 0xE8, 0x49, 0x89, 0xF8, 0x49, 0xC1, 0xE8, 0x30, 0x4D, 0x0F, 0xAF, 0xC1,
    0x4D, 0x8D, 0x04, 0xC0, 0x49, 0x29, 0xC0, 0x4C, 0x21, 0xEE, 0x4C, 0x89, 0xC0, 0x4D, 0x89, 0xC1,
    0x48, 0xC1, 0xE8, 0x34, 0x4C, 0x8D, 0x04, 0xF0, 0x49, 0x29, 0xF0, 0x4C, 0x21, 0xEA, 0x4C, 0x89,
    0xC0, 0x48, 0xC1, 0xE8, 0x34, 0x4C, 0x8D, 0x14, 0xD0] ++ bytes_l10a410_89

theorem code_l10a410_88 : ∀ x ∈ codeRange 0x10c2dd bytes_l10a410_88, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc2dd 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_89

def b_l10a410_87 : Block Op Label signature Reg.count 3698 :=
  .letOp (n := 3698) (.out 0x10c28b (leaR64Effect 0x10c28b 1 (.sib 1 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[3696, 3696]
    (.letOp (n := 3699) (.exec 0x10c28b (fun s => s.RIP = 0x10c28b) (leaR64Effect 0x10c28b 1 (.sib 1 (some 1) 3 .none)) (Reg.operands [.gpr 1, .gpr 1] [])) #v[3696, 3696]
    (.letOp (n := 3700) (.out 0x10c28f (addR64R64Effect 0x10c28f 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3692, 3698]
    (.letOp (n := 3701) (.exec 0x10c28f (fun s => s.RIP = 0x10c28f) (addR64R64Effect 0x10c28f 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3692, 3698]
    (.letOp (n := 3702) (.out 0x10c292 (movR64R64Effect 0x10c292 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[3700]
    (.letOp (n := 3703) (.exec 0x10c292 (fun s => s.RIP = 0x10c292) (movR64R64Effect 0x10c292 6 0) (Reg.operands [.gpr 0] [])) #v[3700]
    (.letOp (n := 3704) (.out 0x10c295 (shrR64Effect 0x10c295 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3702]
    (.letOp (n := 3705) (.exec 0x10c295 (fun s => s.RIP = 0x10c295) (shrR64Effect 0x10c295 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3702]
    (.letOp (n := 3706) (.out 0x10c299 (movR64M64Effect 0x10c299 1 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 3707) (.exec 0x10c299 (LoadPre 0x10c299 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x10c299 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c299 1 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3708) (.out 0x10c2a1 (leaR64Effect 0x10c2a1 1 (.sib 1 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[3706, 3706]
    (.letOp (n := 3709) (.exec 0x10c2a1 (fun s => s.RIP = 0x10c2a1) (leaR64Effect 0x10c2a1 1 (.sib 1 (some 1) 3 .none)) (Reg.operands [.gpr 1, .gpr 1] [])) #v[3706, 3706]
    (.letOp (n := 3710) (.out 0x10c2a5 (addR64R64Effect 0x10c2a5 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[3704, 3708]
    (.letOp (n := 3711) (.exec 0x10c2a5 (fun s => s.RIP = 0x10c2a5) (addR64R64Effect 0x10c2a5 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[3704, 3708]
    (.letOp (n := 3712) (.out 0x10c2a8 (movR64R64Effect 0x10c2a8 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[3710]
    (.letOp (n := 3713) (.exec 0x10c2a8 (fun s => s.RIP = 0x10c2a8) (movR64R64Effect 0x10c2a8 2 6) (Reg.operands [.gpr 6] [])) #v[3710]
    (.letOp (n := 3714) (.out 0x10c2ab (shrR64Effect 0x10c2ab 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3712]
    (.letOp (n := 3715) (.exec 0x10c2ab (fun s => s.RIP = 0x10c2ab) (shrR64Effect 0x10c2ab 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3712]
    (.letOp (n := 3716) (.out 0x10c2af (movR64M64Effect 0x10c2af 1 (.sib 4 none 0 (.d32 0x1a0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 3717) (.exec 0x10c2af (LoadPre 0x10c2af (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x10c2af + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c2af 1 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3718) (.out 0x10c2b7 (leaR64Effect 0x10c2b7 1 (.sib 1 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[3716, 3716]
    (.letOp (n := 3719) (.exec 0x10c2b7 (fun s => s.RIP = 0x10c2b7) (leaR64Effect 0x10c2b7 1 (.sib 1 (some 1) 3 .none)) (Reg.operands [.gpr 1, .gpr 1] [])) #v[3716, 3716]
    (.letOp (n := 3720) (.out 0x10c2bb (addR64R64Effect 0x10c2bb 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[3714, 3718]
    (.letOp (n := 3721) (.exec 0x10c2bb (fun s => s.RIP = 0x10c2bb) (addR64R64Effect 0x10c2bb 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[3714, 3718]
    (.letOp (n := 3722) (.out 0x10c2be (movR64R64Effect 0x10c2be 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[3720]
    (.letOp (n := 3723) (.exec 0x10c2be (fun s => s.RIP = 0x10c2be) (movR64R64Effect 0x10c2be 1 2) (Reg.operands [.gpr 2] [])) #v[3720]
    (.letOp (n := 3724) (.out 0x10c2c1 (shrR64Effect 0x10c2c1 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3722]
    (.letOp (n := 3725) (.exec 0x10c2c1 (fun s => s.RIP = 0x10c2c1) (shrR64Effect 0x10c2c1 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3722]
    (.letOp (n := 3726) (.out 0x10c2c5 (movR64M64Effect 0x10c2c5 8 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 3727) (.exec 0x10c2c5 (LoadPre 0x10c2c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x10c2c5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c2c5 8 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3728) (.out 0x10c2cd (leaR64Effect 0x10c2cd 8 (.sib 8 (some 8) 3 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[3726, 3726]
    (.letOp (n := 3729) (.exec 0x10c2cd (fun s => s.RIP = 0x10c2cd) (leaR64Effect 0x10c2cd 8 (.sib 8 (some 8) 3 .none)) (Reg.operands [.gpr 8, .gpr 8] [])) #v[3726, 3726]
    (.letOp (n := 3730) (.out 0x10c2d1 (addR64R64Effect 0x10c2d1 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[3724, 3728]
    (.letOp (n := 3731) (.exec 0x10c2d1 (fun s => s.RIP = 0x10c2d1) (addR64R64Effect 0x10c2d1 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[3724, 3728]
    (.letOp (n := 3732) (.out 0x10c2d4 (andR64R64Effect 0x10c2d4 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[3686, 3581]
    (.letOp (n := 3733) (.exec 0x10c2d4 (fun s => s.RIP = 0x10c2d4) (andR64R64Effect 0x10c2d4 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[3686, 3581]
    (.letOp (n := 3734) (.out 0x10c2d7 (movR64R64Effect 0x10c2d7 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[3581]
    (.letOp (n := 3735) (.exec 0x10c2d7 (fun s => s.RIP = 0x10c2d7) (movR64R64Effect 0x10c2d7 11 10) (Reg.operands [.gpr 10] [])) #v[3581]
    (.letOp (n := 3736) (.out 0x10c2da (movR64R64Effect 0x10c2da 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[3730]
    (.letOp (n := 3737) (.exec 0x10c2da (fun s => s.RIP = 0x10c2da) (movR64R64Effect 0x10c2da 8 1) (Reg.operands [.gpr 1] [])) #v[3730]
    (b_l10a410_88))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_87 : List UInt8 :=
  [0x48, 0x8D, 0x0C, 0xC9, 0x48, 0x01, 0xC8, 0x48, 0x89, 0xC6, 0x48, 0xC1, 0xEE, 0x34, 0x48, 0x8B,
    0x8C, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x0C, 0xC9, 0x48, 0x01, 0xCE, 0x48, 0x89, 0xF2,
    0x48, 0xC1, 0xEA, 0x34, 0x48, 0x8B, 0x8C, 0x24, 0xA0, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x0C, 0xC9,
    0x48, 0x01, 0xCA, 0x48, 0x89, 0xD1, 0x48, 0xC1, 0xE9, 0x34, 0x4C, 0x8B, 0x84, 0x24, 0x78, 0x01,
    0x00, 0x00, 0x4F, 0x8D, 0x04, 0xC0, 0x4C, 0x01, 0xC1, 0x4C, 0x21, 0xD7, 0x4D, 0x89, 0xD3, 0x49,
    0x89, 0xC8] ++ bytes_l10a410_88

theorem code_l10a410_87 : ∀ x ∈ codeRange 0x10c28b bytes_l10a410_87, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc28b 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_88

def b_l10a410_86 : Block Op Label signature Reg.count 3659 :=
  .letOp (n := 3659) (.out 0x10c23e (shrR64Effect 0x10c23e 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3657]
    (.letOp (n := 3660) (.exec 0x10c23e (fun s => s.RIP = 0x10c23e) (shrR64Effect 0x10c23e 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3657]
    (.letOp (n := 3661) (.out 0x10c242 (addR64R64Effect 0x10c242 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3659, 3655]
    (.letOp (n := 3662) (.exec 0x10c242 (fun s => s.RIP = 0x10c242) (addR64R64Effect 0x10c242 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3659, 3655]
    (.letOp (n := 3663) (.out 0x10c245 (andR64R64Effect 0x10c245 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[3619, 3517]
    (.letOp (n := 3664) (.exec 0x10c245 (fun s => s.RIP = 0x10c245) (andR64R64Effect 0x10c245 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[3619, 3517]
    (.letOp (n := 3665) (.out 0x10c248 (leaR64Effect 0x10c248 0 (.sib 1 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 1] []) (.reg (.gpr 0))) #v[3663, 3663]
    (.letOp (n := 3666) (.exec 0x10c248 (fun s => s.RIP = 0x10c248) (leaR64Effect 0x10c248 0 (.sib 1 (some 1) 1 .none)) (Reg.operands [.gpr 1, .gpr 1] [])) #v[3663, 3663]
    (.letOp (n := 3667) (.out 0x10c24c (movR64R64Effect 0x10c24c 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[3661]
    (.letOp (n := 3668) (.exec 0x10c24c (fun s => s.RIP = 0x10c24c) (movR64R64Effect 0x10c24c 1 2) (Reg.operands [.gpr 2] [])) #v[3661]
    (.letOp (n := 3669) (.out 0x10c24f (movR64R64Effect 0x10c24f 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[3661]
    (.letOp (n := 3670) (.exec 0x10c24f (fun s => s.RIP = 0x10c24f) (movR64R64Effect 0x10c24f 15 2) (Reg.operands [.gpr 2] [])) #v[3661]
    (.letOp (n := 3671) (.out 0x10c252 (shrR64Effect 0x10c252 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3667]
    (.letOp (n := 3672) (.exec 0x10c252 (fun s => s.RIP = 0x10c252) (shrR64Effect 0x10c252 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3667]
    (.letOp (n := 3673) (.out 0x10c256 (addR64R64Effect 0x10c256 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[3671, 3665]
    (.letOp (n := 3674) (.exec 0x10c256 (fun s => s.RIP = 0x10c256) (addR64R64Effect 0x10c256 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3671, 3665]
    (.letOp (n := 3675) (.out 0x10c259 (andR64R64Effect 0x10c259 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[3631, 3581]
    (.letOp (n := 3676) (.exec 0x10c259 (fun s => s.RIP = 0x10c259) (andR64R64Effect 0x10c259 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[3631, 3581]
    (.letOp (n := 3677) (.out 0x10c25c (movR64R64Effect 0x10c25c 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[3673]
    (.letOp (n := 3678) (.exec 0x10c25c (fun s => s.RIP = 0x10c25c) (movR64R64Effect 0x10c25c 0 1) (Reg.operands [.gpr 1] [])) #v[3673]
    (.letOp (n := 3679) (.out 0x10c25f (movR64R64Effect 0x10c25f 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[3673]
    (.letOp (n := 3680) (.exec 0x10c25f (fun s => s.RIP = 0x10c25f) (movR64R64Effect 0x10c25f 5 1) (Reg.operands [.gpr 1] [])) #v[3673]
    (.letOp (n := 3681) (.out 0x10c262 (shrR64Effect 0x10c262 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3677]
    (.letOp (n := 3682) (.exec 0x10c262 (fun s => s.RIP = 0x10c262) (shrR64Effect 0x10c262 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3677]
    (.letOp (n := 3683) (.out 0x10c266 (addR64R64Effect 0x10c266 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[3681, 3675]
    (.letOp (n := 3684) (.exec 0x10c266 (fun s => s.RIP = 0x10c266) (addR64R64Effect 0x10c266 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[3681, 3675]
    (.letOp (n := 3685) (.exec 0x10c269 (StorePre 0x10c269 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10c269 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c269 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3683, 65]
    (.letOp (n := 3686) (.out 0x10c271 (leaR64Effect 0x10c271 7 (.sib 11 (some 11) 3 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 11, .gpr 11] []) (.reg (.gpr 7))) #v[3430, 3430]
    (.letOp (n := 3687) (.exec 0x10c271 (fun s => s.RIP = 0x10c271) (leaR64Effect 0x10c271 7 (.sib 11 (some 11) 3 .none)) (Reg.operands [.gpr 11, .gpr 11] [])) #v[3430, 3430]
    (.letOp (n := 3688) (.out 0x10c275 (movR64R64Effect 0x10c275 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[3686]
    (.letOp (n := 3689) (.exec 0x10c275 (fun s => s.RIP = 0x10c275) (movR64R64Effect 0x10c275 0 7) (Reg.operands [.gpr 7] [])) #v[3686]
    (.letOp (n := 3690) (.out 0x10c278 (shrR64Effect 0x10c278 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3688]
    (.letOp (n := 3691) (.exec 0x10c278 (fun s => s.RIP = 0x10c278) (shrR64Effect 0x10c278 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3688]
    (.letOp (n := 3692) (.out 0x10c27c (imulR64R64Effect 0x10c27c 4 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[3690, 3637]
    (.letOp (n := 3693) (.exec 0x10c27c (fun s => s.RIP = 0x10c27c) (imulR64R64Effect 0x10c27c 4 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[3690, 3637]
    (.letOp (n := 3694) (.out 0x10c280 (movR64R64Effect 0x10c280 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[3637]
    (.letOp (n := 3695) (.exec 0x10c280 (fun s => s.RIP = 0x10c280) (movR64R64Effect 0x10c280 9 8) (Reg.operands [.gpr 8] [])) #v[3637]
    (.letOp (n := 3696) (.out 0x10c283 (movR64M64Effect 0x10c283 1 (.sib 4 none 0 (.d32 0x1a8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 3697) (.exec 0x10c283 (LoadPre 0x10c283 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x10c283 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c283 1 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_87)))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_86 : List UInt8 :=
  [0x48, 0xC1, 0xEA, 0x34, 0x48, 0x01, 0xC2, 0x4C, 0x21, 0xE9, 0x48, 0x8D, 0x04, 0x49, 0x48, 0x89,
    0xD1, 0x49, 0x89, 0xD7, 0x48, 0xC1, 0xE9, 0x34, 0x48, 0x01, 0xC1, 0x4C, 0x21, 0xD6, 0x48, 0x89,
    0xC8, 0x48, 0x89, 0xCD, 0x48, 0xC1, 0xE8, 0x34, 0x48, 0x01, 0xF0, 0x48, 0x89, 0x84, 0x24, 0xE0,
    0x00, 0x00, 0x00, 0x4B, 0x8D, 0x3C, 0xDB, 0x48, 0x89, 0xF8, 0x48, 0xC1, 0xE8, 0x30, 0x49, 0x0F,
    0xAF, 0xC0, 0x4D, 0x89, 0xC1, 0x48, 0x8B, 0x8C, 0x24, 0xA8, 0x01, 0x00, 0x00] ++ bytes_l10a410_87

theorem code_l10a410_86 : ∀ x ∈ codeRange 0x10c23e bytes_l10a410_86, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc23e 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_87

def b_l10a410_85 : Block Op Label signature Reg.count 3619 :=
  .letOp (n := 3619) (.out 0x10c1fa (subR64R64Effect 0x10c1fa 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[3617, 3615]
    (.letOp (n := 3620) (.exec 0x10c1fa (fun s => s.RIP = 0x10c1fa) (subR64R64Effect 0x10c1fa 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[3617, 3615]
    (.letOp (n := 3621) (.out 0x10c1fd (movR64R64Effect 0x10c1fd 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[3619]
    (.letOp (n := 3622) (.exec 0x10c1fd (fun s => s.RIP = 0x10c1fd) (movR64R64Effect 0x10c1fd 8 1) (Reg.operands [.gpr 1] [])) #v[3619]
    (.letOp (n := 3623) (.out 0x10c200 (shrR64Effect 0x10c200 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[3621]
    (.letOp (n := 3624) (.exec 0x10c200 (fun s => s.RIP = 0x10c200) (shrR64Effect 0x10c200 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3621]
    (.letOp (n := 3625) (.out 0x10c204 (addR64R64Effect 0x10c204 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[3623, 3579]
    (.letOp (n := 3626) (.exec 0x10c204 (fun s => s.RIP = 0x10c204) (addR64R64Effect 0x10c204 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[3623, 3579]
    (.letOp (n := 3627) (.out 0x10c207 (andR64R64Effect 0x10c207 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[3589, 3517]
    (.letOp (n := 3628) (.exec 0x10c207 (fun s => s.RIP = 0x10c207) (andR64R64Effect 0x10c207 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[3589, 3517]
    (.letOp (n := 3629) (.out 0x10c20a (leaR64Effect 0x10c20a 7 (.sib 7 (some 7) 1 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[3627, 3627]
    (.letOp (n := 3630) (.exec 0x10c20a (fun s => s.RIP = 0x10c20a) (leaR64Effect 0x10c20a 7 (.sib 7 (some 7) 1 .none)) (Reg.operands [.gpr 7, .gpr 7] [])) #v[3627, 3627]
    (.letOp (n := 3631) (.out 0x10c20e (leaR64Effect 0x10c20e 6 (.sib 8 (some 8) 1 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8, .gpr 8] []) (.reg (.gpr 6))) #v[3625, 3625]
    (.letOp (n := 3632) (.exec 0x10c20e (fun s => s.RIP = 0x10c20e) (leaR64Effect 0x10c20e 6 (.sib 8 (some 8) 1 .none)) (Reg.operands [.gpr 8, .gpr 8] [])) #v[3625, 3625]
    (.letOp (n := 3633) (.out 0x10c212 (movR64R64Effect 0x10c212 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[3631]
    (.letOp (n := 3634) (.exec 0x10c212 (fun s => s.RIP = 0x10c212) (movR64R64Effect 0x10c212 14 6) (Reg.operands [.gpr 6] [])) #v[3631]
    (.letOp (n := 3635) (.out 0x10c215 (shrR64Effect 0x10c215 4 14 48) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[3633]
    (.letOp (n := 3636) (.exec 0x10c215 (fun s => s.RIP = 0x10c215) (shrR64Effect 0x10c215 4 14 48) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3633]
    (.letOp (n := 3637) (.out 0x10c219 (movR64R64Effect 0x10c219 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[3467]
    (.letOp (n := 3638) (.exec 0x10c219 (fun s => s.RIP = 0x10c219) (movR64R64Effect 0x10c219 8 15) (Reg.operands [.gpr 15] [])) #v[3467]
    (.letOp (n := 3639) (.out 0x10c21c (imulR64R64Effect 0x10c21c 4 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[3635, 3467]
    (.letOp (n := 3640) (.exec 0x10c21c (fun s => s.RIP = 0x10c21c) (imulR64R64Effect 0x10c21c 4 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[3635, 3467]
    (.letOp (n := 3641) (.out 0x10c220 (addR64R64Effect 0x10c220 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[3639, 3629]
    (.letOp (n := 3642) (.exec 0x10c220 (fun s => s.RIP = 0x10c220) (addR64R64Effect 0x10c220 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[3639, 3629]
    (.letOp (n := 3643) (.out 0x10c223 (andR64R64Effect 0x10c223 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[3599, 3517]
    (.letOp (n := 3644) (.exec 0x10c223 (fun s => s.RIP = 0x10c223) (andR64R64Effect 0x10c223 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[3599, 3517]
    (.letOp (n := 3645) (.out 0x10c226 (leaR64Effect 0x10c226 0 (.sib 0 (some 0) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[3643, 3643]
    (.letOp (n := 3646) (.exec 0x10c226 (fun s => s.RIP = 0x10c226) (leaR64Effect 0x10c226 0 (.sib 0 (some 0) 1 .none)) (Reg.operands [.gpr 0, .gpr 0] [])) #v[3643, 3643]
    (.letOp (n := 3647) (.out 0x10c22a (movR64R64Effect 0x10c22a 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 14] []) (.reg (.gpr 3))) #v[3641]
    (.letOp (n := 3648) (.exec 0x10c22a (fun s => s.RIP = 0x10c22a) (movR64R64Effect 0x10c22a 3 14) (Reg.operands [.gpr 14] [])) #v[3641]
    (.letOp (n := 3649) (.out 0x10c22d (shrR64Effect 0x10c22d 4 3 52) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[3647]
    (.letOp (n := 3650) (.exec 0x10c22d (fun s => s.RIP = 0x10c22d) (shrR64Effect 0x10c22d 4 3 52) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3647]
    (.letOp (n := 3651) (.out 0x10c231 (addR64R64Effect 0x10c231 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[3649, 3645]
    (.letOp (n := 3652) (.exec 0x10c231 (fun s => s.RIP = 0x10c231) (addR64R64Effect 0x10c231 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[3649, 3645]
    (.letOp (n := 3653) (.out 0x10c234 (andR64R64Effect 0x10c234 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[3609, 3517]
    (.letOp (n := 3654) (.exec 0x10c234 (fun s => s.RIP = 0x10c234) (andR64R64Effect 0x10c234 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[3609, 3517]
    (.letOp (n := 3655) (.out 0x10c237 (leaR64Effect 0x10c237 0 (.sib 2 (some 2) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 2] []) (.reg (.gpr 0))) #v[3653, 3653]
    (.letOp (n := 3656) (.exec 0x10c237 (fun s => s.RIP = 0x10c237) (leaR64Effect 0x10c237 0 (.sib 2 (some 2) 1 .none)) (Reg.operands [.gpr 2, .gpr 2] [])) #v[3653, 3653]
    (.letOp (n := 3657) (.out 0x10c23b (movR64R64Effect 0x10c23b 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3651]
    (.letOp (n := 3658) (.exec 0x10c23b (fun s => s.RIP = 0x10c23b) (movR64R64Effect 0x10c23b 2 3) (Reg.operands [.gpr 3] [])) #v[3651]
    (b_l10a410_86))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_85 : List UInt8 :=
  [0x4C, 0x29, 0xC1, 0x49, 0x89, 0xC8, 0x49, 0xC1, 0xE8, 0x34, 0x49, 0x01, 0xF0, 0x4C, 0x21, 0xEF,
    0x48, 0x8D, 0x3C, 0x7F, 0x4B, 0x8D, 0x34, 0x40, 0x49, 0x89, 0xF6, 0x49, 0xC1, 0xEE, 0x30, 0x4D,
    0x89, 0xF8, 0x4D, 0x0F, 0xAF, 0xF7, 0x49, 0x01, 0xFE, 0x4C, 0x21, 0xE8, 0x48, 0x8D, 0x04, 0x40,
    0x4C, 0x89, 0xF3, 0x48, 0xC1, 0xEB, 0x34, 0x48, 0x01, 0xC3, 0x4C, 0x21, 0xEA, 0x48, 0x8D, 0x04,
    0x52, 0x48, 0x89, 0xDA] ++ bytes_l10a410_86

theorem code_l10a410_85 : ∀ x ∈ codeRange 0x10c1fa bytes_l10a410_85, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc1fa 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_86

def b_l10a410_84 : Block Op Label signature Reg.count 3579 :=
  .letOp (n := 3579) (.out 0x10c1a8 (andR64R64Effect 0x10c1a8 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[3573, 3493]
    (.letOp (n := 3580) (.exec 0x10c1a8 (fun s => s.RIP = 0x10c1a8) (andR64R64Effect 0x10c1a8 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[3573, 3493]
    (.letOp (n := 3581) (.out 0x10c1ab (movR64R64Effect 0x10c1ab 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[3493]
    (.letOp (n := 3582) (.exec 0x10c1ab (fun s => s.RIP = 0x10c1ab) (movR64R64Effect 0x10c1ab 10 1) (Reg.operands [.gpr 1] [])) #v[3493]
    (.letOp (n := 3583) (.out 0x10c1ae (imulR64R64Effect 0x10c1ae 4 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[3577, 3467]
    (.letOp (n := 3584) (.exec 0x10c1ae (fun s => s.RIP = 0x10c1ae) (imulR64R64Effect 0x10c1ae 4 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[3577, 3467]
    (.letOp (n := 3585) (.out 0x10c1b2 (movR64M64Effect 0x10c1b2 1 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 3586) (.exec 0x10c1b2 (LoadPre 0x10c1b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10c1b2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c1b2 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3587) (.out 0x10c1ba (leaR64Effect 0x10c1ba 7 (.sib 0 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0, .gpr 1] []) (.reg (.gpr 7))) #v[3583, 3585]
    (.letOp (n := 3588) (.exec 0x10c1ba (fun s => s.RIP = 0x10c1ba) (leaR64Effect 0x10c1ba 7 (.sib 0 (some 1) 3 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3583, 3585]
    (.letOp (n := 3589) (.out 0x10c1be (subR64R64Effect 0x10c1be 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[3587, 3585]
    (.letOp (n := 3590) (.exec 0x10c1be (fun s => s.RIP = 0x10c1be) (subR64R64Effect 0x10c1be 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[3587, 3585]
    (.letOp (n := 3591) (.out 0x10c1c1 (movR64R64Effect 0x10c1c1 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[3589]
    (.letOp (n := 3592) (.exec 0x10c1c1 (fun s => s.RIP = 0x10c1c1) (movR64R64Effect 0x10c1c1 0 7) (Reg.operands [.gpr 7] [])) #v[3589]
    (.letOp (n := 3593) (.out 0x10c1c4 (shrR64Effect 0x10c1c4 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3591]
    (.letOp (n := 3594) (.exec 0x10c1c4 (fun s => s.RIP = 0x10c1c4) (shrR64Effect 0x10c1c4 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3591]
    (.letOp (n := 3595) (.out 0x10c1c8 (movR64M64Effect 0x10c1c8 1 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 3596) (.exec 0x10c1c8 (LoadPre 0x10c1c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10c1c8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c1c8 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3597) (.out 0x10c1cd (leaR64Effect 0x10c1cd 0 (.sib 0 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3593, 3595]
    (.letOp (n := 3598) (.exec 0x10c1cd (fun s => s.RIP = 0x10c1cd) (leaR64Effect 0x10c1cd 0 (.sib 0 (some 1) 3 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3593, 3595]
    (.letOp (n := 3599) (.out 0x10c1d1 (subR64R64Effect 0x10c1d1 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3597, 3595]
    (.letOp (n := 3600) (.exec 0x10c1d1 (fun s => s.RIP = 0x10c1d1) (subR64R64Effect 0x10c1d1 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3597, 3595]
    (.letOp (n := 3601) (.out 0x10c1d4 (movR64R64Effect 0x10c1d4 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[3599]
    (.letOp (n := 3602) (.exec 0x10c1d4 (fun s => s.RIP = 0x10c1d4) (movR64R64Effect 0x10c1d4 1 0) (Reg.operands [.gpr 0] [])) #v[3599]
    (.letOp (n := 3603) (.out 0x10c1d7 (shrR64Effect 0x10c1d7 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3601]
    (.letOp (n := 3604) (.exec 0x10c1d7 (fun s => s.RIP = 0x10c1d7) (shrR64Effect 0x10c1d7 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3601]
    (.letOp (n := 3605) (.out 0x10c1db (movR64M64Effect 0x10c1db 8 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 3606) (.exec 0x10c1db (LoadPre 0x10c1db (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10c1db + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c1db 8 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3607) (.out 0x10c1e3 (leaR64Effect 0x10c1e3 2 (.sib 1 (some 8) 3 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 8] []) (.reg (.gpr 2))) #v[3603, 3605]
    (.letOp (n := 3608) (.exec 0x10c1e3 (fun s => s.RIP = 0x10c1e3) (leaR64Effect 0x10c1e3 2 (.sib 1 (some 8) 3 .none)) (Reg.operands [.gpr 1, .gpr 8] [])) #v[3603, 3605]
    (.letOp (n := 3609) (.out 0x10c1e7 (subR64R64Effect 0x10c1e7 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[3607, 3605]
    (.letOp (n := 3610) (.exec 0x10c1e7 (fun s => s.RIP = 0x10c1e7) (subR64R64Effect 0x10c1e7 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[3607, 3605]
    (.letOp (n := 3611) (.out 0x10c1ea (movR64R64Effect 0x10c1ea 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[3609]
    (.letOp (n := 3612) (.exec 0x10c1ea (fun s => s.RIP = 0x10c1ea) (movR64R64Effect 0x10c1ea 1 2) (Reg.operands [.gpr 2] [])) #v[3609]
    (.letOp (n := 3613) (.out 0x10c1ed (shrR64Effect 0x10c1ed 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3611]
    (.letOp (n := 3614) (.exec 0x10c1ed (fun s => s.RIP = 0x10c1ed) (shrR64Effect 0x10c1ed 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3611]
    (.letOp (n := 3615) (.out 0x10c1f1 (movR64M64Effect 0x10c1f1 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 3616) (.exec 0x10c1f1 (LoadPre 0x10c1f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10c1f1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c1f1 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3617) (.out 0x10c1f6 (leaR64Effect 0x10c1f6 1 (.sib 1 (some 8) 3 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[3613, 3615]
    (.letOp (n := 3618) (.exec 0x10c1f6 (fun s => s.RIP = 0x10c1f6) (leaR64Effect 0x10c1f6 1 (.sib 1 (some 8) 3 .none)) (Reg.operands [.gpr 1, .gpr 8] [])) #v[3613, 3615]
    (b_l10a410_85))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_84 : List UInt8 :=
  [0x48, 0x21, 0xCE, 0x49, 0x89, 0xCA, 0x49, 0x0F, 0xAF, 0xC7, 0x48, 0x8B, 0x8C, 0x24, 0x90, 0x00,
    0x00, 0x00, 0x48, 0x8D, 0x3C, 0xC8, 0x48, 0x29, 0xCF, 0x48, 0x89, 0xF8, 0x48, 0xC1, 0xE8, 0x34,
    0x48, 0x8B, 0x4C, 0x24, 0x78, 0x48, 0x8D, 0x04, 0xC8, 0x48, 0x29, 0xC8, 0x48, 0x89, 0xC1, 0x48,
    0xC1, 0xE9, 0x34, 0x4C, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x4A, 0x8D, 0x14, 0xC1, 0x4C,
    0x29, 0xC2, 0x48, 0x89, 0xD1, 0x48, 0xC1, 0xE9, 0x34, 0x4C, 0x8B, 0x44, 0x24, 0x20, 0x4A, 0x8D,
    0x0C, 0xC1] ++ bytes_l10a410_85

theorem code_l10a410_84 : ∀ x ∈ codeRange 0x10c1a8 bytes_l10a410_84, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc1a8 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_85

def b_l10a410_83 : Block Op Label signature Reg.count 3544 :=
  .letOp (n := 3544) (.exec 0x10c145 (StorePre 0x10c145 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10c145 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10c145 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3542, 65]
    (.letOp (n := 3545) (.out 0x10c14a (andR64R64Effect 0x10c14a 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[3491, 3352]
    (.letOp (n := 3546) (.exec 0x10c14a (fun s => s.RIP = 0x10c14a) (andR64R64Effect 0x10c14a 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[3491, 3352]
    (.letOp (n := 3547) (.out 0x10c14d (movR64M64Effect 0x10c14d 0 (.sib 4 none 0 (.d32 0x1b8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3548) (.exec 0x10c14d (LoadPre 0x10c14d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b8)) s (0x10c14d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c14d 0 (.sib 4 none 0 (.d32 0x1b8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3549) (.out 0x10c155 (leaR64Effect 0x10c155 12 (.sib 0 (some 9) 0 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0, .gpr 9] []) (.reg (.gpr 12))) #v[3547, 3521]
    (.letOp (n := 3550) (.exec 0x10c155 (fun s => s.RIP = 0x10c155) (leaR64Effect 0x10c155 12 (.sib 0 (some 9) 0 .none)) (Reg.operands [.gpr 0, .gpr 9] [])) #v[3547, 3521]
    (.letOp (n := 3551) (.out 0x10c159 (subR64R64Effect 0x10c159 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[3549, 3545]
    (.letOp (n := 3552) (.exec 0x10c159 (fun s => s.RIP = 0x10c159) (subR64R64Effect 0x10c159 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[3549, 3545]
    (.letOp (n := 3553) (.exec 0x10c15c (StorePre 0x10c15c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10c15c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10c15c 12 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[3551, 65]
    (.letOp (n := 3554) (.out 0x10c161 (addR64R64Effect 0x10c161 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3545, 3547]
    (.letOp (n := 3555) (.exec 0x10c161 (fun s => s.RIP = 0x10c161) (addR64R64Effect 0x10c161 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3545, 3547]
    (.letOp (n := 3556) (.exec 0x10c164 (StorePre 0x10c164 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10c164 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c164 2 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3554, 65]
    (.letOp (n := 3557) (.out 0x10c16c (movR64Imm64Effect 0x10c16c 2 0x3fffffffffffc) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 3558) (.exec 0x10c16c (fun s => s.RIP = 0x10c16c) (movR64Imm64Effect 0x10c16c 2 0x3fffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 3559) (.out 0x10c176 (movR64M64Effect 0x10c176 0 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3560) (.exec 0x10c176 (LoadPre 0x10c176 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10c176 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c176 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3561) (.out 0x10c17e (addR64R64Effect 0x10c17e 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3557, 3559]
    (.letOp (n := 3562) (.exec 0x10c17e (fun s => s.RIP = 0x10c17e) (addR64R64Effect 0x10c17e 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3557, 3559]
    (.letOp (n := 3563) (.out 0x10c181 (subR64R64Effect 0x10c181 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[3561, 3501]
    (.letOp (n := 3564) (.exec 0x10c181 (fun s => s.RIP = 0x10c181) (subR64R64Effect 0x10c181 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[3561, 3501]
    (.letOp (n := 3565) (.exec 0x10c184 (StorePre 0x10c184 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10c184 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10c184 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3563, 65]
    (.letOp (n := 3566) (.out 0x10c189 (addR64R64Effect 0x10c189 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[3501, 3559]
    (.letOp (n := 3567) (.exec 0x10c189 (fun s => s.RIP = 0x10c189) (addR64R64Effect 0x10c189 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3501, 3559]
    (.letOp (n := 3568) (.exec 0x10c18c (StorePre 0x10c18c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10c18c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10c18c 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[3566, 65]
    (.letOp (n := 3569) (.out 0x10c191 (movR64M64Effect 0x10c191 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3570) (.exec 0x10c191 (LoadPre 0x10c191 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10c191 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c191 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3571) (.out 0x10c196 (leaR64Effect 0x10c196 6 (.abs (some 0) 3 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[3569]
    (.letOp (n := 3572) (.exec 0x10c196 (fun s => s.RIP = 0x10c196) (leaR64Effect 0x10c196 6 (.abs (some 0) 3 0x0)) (Reg.operands [.gpr 0] [])) #v[3569]
    (.letOp (n := 3573) (.out 0x10c19e (subR64R64Effect 0x10c19e 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[3571, 3569]
    (.letOp (n := 3574) (.exec 0x10c19e (fun s => s.RIP = 0x10c19e) (subR64R64Effect 0x10c19e 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3571, 3569]
    (.letOp (n := 3575) (.out 0x10c1a1 (movR64R64Effect 0x10c1a1 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[3573]
    (.letOp (n := 3576) (.exec 0x10c1a1 (fun s => s.RIP = 0x10c1a1) (movR64R64Effect 0x10c1a1 0 6) (Reg.operands [.gpr 6] [])) #v[3573]
    (.letOp (n := 3577) (.out 0x10c1a4 (shrR64Effect 0x10c1a4 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3575]
    (.letOp (n := 3578) (.exec 0x10c1a4 (fun s => s.RIP = 0x10c1a4) (shrR64Effect 0x10c1a4 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3575]
    (b_l10a410_84)))))))))))))))))))))))))))))))))))

def bytes_l10a410_83 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x70, 0x4C, 0x21, 0xD2, 0x48, 0x8B, 0x84, 0x24, 0xB8, 0x01, 0x00, 0x00,
    0x4E, 0x8D, 0x24, 0x08, 0x49, 0x29, 0xD4, 0x4C, 0x89, 0x64, 0x24, 0x58, 0x48, 0x01, 0xC2, 0x48,
    0x89, 0x94, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0xBA, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03,
    0x00, 0x48, 0x8B, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x01, 0xC2, 0x48, 0x29, 0xF2, 0x48,
    0x89, 0x54, 0x24, 0x48, 0x48, 0x01, 0xC6, 0x48, 0x89, 0x74, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24,
    0x40, 0x48, 0x8D, 0x34, 0xC5, 0x00, 0x00, 0x00, 0x00, 0x48, 0x29, 0xC6, 0x48, 0x89, 0xF0, 0x48,
    0xC1, 0xE8, 0x30] ++ bytes_l10a410_84

theorem code_l10a410_83 : ∀ x ∈ codeRange 0x10c145 bytes_l10a410_83, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc145 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_84

def b_l10a410_82 : Block Op Label signature Reg.count 3509 :=
  .letOp (n := 3509) (.out 0x10c0e6 (addR64R64Effect 0x10c0e6 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[3505, 3507]
    (.letOp (n := 3510) (.exec 0x10c0e6 (fun s => s.RIP = 0x10c0e6) (addR64R64Effect 0x10c0e6 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[3505, 3507]
    (.letOp (n := 3511) (.out 0x10c0e9 (subR64R64Effect 0x10c0e9 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[3509, 3503]
    (.letOp (n := 3512) (.exec 0x10c0e9 (fun s => s.RIP = 0x10c0e9) (subR64R64Effect 0x10c0e9 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[3509, 3503]
    (.letOp (n := 3513) (.exec 0x10c0ec (StorePre 0x10c0ec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10c0ec + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10c0ec 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[3511, 65]
    (.letOp (n := 3514) (.out 0x10c0f1 (addR64R64Effect 0x10c0f1 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[3503, 3507]
    (.letOp (n := 3515) (.exec 0x10c0f1 (fun s => s.RIP = 0x10c0f1) (addR64R64Effect 0x10c0f1 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[3503, 3507]
    (.letOp (n := 3516) (.exec 0x10c0f4 (StorePre 0x10c0f4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10c0f4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c0f4 8 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[3514, 65]
    (.letOp (n := 3517) (.out 0x10c0fc (movR64R64Effect 0x10c0fc 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 10] []) (.reg (.gpr 13))) #v[3352]
    (.letOp (n := 3518) (.exec 0x10c0fc (fun s => s.RIP = 0x10c0fc) (movR64R64Effect 0x10c0fc 13 10) (Reg.operands [.gpr 10] [])) #v[3352]
    (.letOp (n := 3519) (.out 0x10c0ff (andR64R64Effect 0x10c0ff 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[3481, 3352]
    (.letOp (n := 3520) (.exec 0x10c0ff (fun s => s.RIP = 0x10c0ff) (andR64R64Effect 0x10c0ff 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[3481, 3352]
    (.letOp (n := 3521) (.out 0x10c102 (movR64Imm64Effect 0x10c102 9 0x3ffffffffffffc) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 3522) (.exec 0x10c102 (fun s => s.RIP = 0x10c102) (movR64Imm64Effect 0x10c102 9 0x3ffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 3523) (.out 0x10c10c (movR64M64Effect 0x10c10c 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 3524) (.exec 0x10c10c (LoadPre 0x10c10c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10c10c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c10c 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3525) (.out 0x10c114 (leaR64Effect 0x10c114 8 (.sib 7 (some 9) 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7, .gpr 9] []) (.reg (.gpr 8))) #v[3523, 3521]
    (.letOp (n := 3526) (.exec 0x10c114 (fun s => s.RIP = 0x10c114) (leaR64Effect 0x10c114 8 (.sib 7 (some 9) 0 .none)) (Reg.operands [.gpr 7, .gpr 9] [])) #v[3523, 3521]
    (.letOp (n := 3527) (.out 0x10c118 (subR64R64Effect 0x10c118 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[3525, 3519]
    (.letOp (n := 3528) (.exec 0x10c118 (fun s => s.RIP = 0x10c118) (subR64R64Effect 0x10c118 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[3525, 3519]
    (.letOp (n := 3529) (.exec 0x10c11b (StorePre 0x10c11b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10c11b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10c11b 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[3527, 65]
    (.letOp (n := 3530) (.out 0x10c120 (addR64R64Effect 0x10c120 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[3519, 3523]
    (.letOp (n := 3531) (.exec 0x10c120 (fun s => s.RIP = 0x10c120) (addR64R64Effect 0x10c120 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[3519, 3523]
    (.letOp (n := 3532) (.exec 0x10c123 (StorePre 0x10c123 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10c123 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c123 12 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[3530, 65]
    (.letOp (n := 3533) (.out 0x10c12b (andR64R64Effect 0x10c12b 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[3485, 3352]
    (.letOp (n := 3534) (.exec 0x10c12b (fun s => s.RIP = 0x10c12b) (andR64R64Effect 0x10c12b 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[3485, 3352]
    (.letOp (n := 3535) (.out 0x10c12e (movR64M64Effect 0x10c12e 7 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 3536) (.exec 0x10c12e (LoadPre 0x10c12e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10c12e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c12e 7 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3537) (.out 0x10c136 (leaR64Effect 0x10c136 8 (.sib 7 (some 9) 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7, .gpr 9] []) (.reg (.gpr 8))) #v[3535, 3521]
    (.letOp (n := 3538) (.exec 0x10c136 (fun s => s.RIP = 0x10c136) (leaR64Effect 0x10c136 8 (.sib 7 (some 9) 0 .none)) (Reg.operands [.gpr 7, .gpr 9] [])) #v[3535, 3521]
    (.letOp (n := 3539) (.out 0x10c13a (subR64R64Effect 0x10c13a 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[3537, 3533]
    (.letOp (n := 3540) (.exec 0x10c13a (fun s => s.RIP = 0x10c13a) (subR64R64Effect 0x10c13a 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3537, 3533]
    (.letOp (n := 3541) (.exec 0x10c13d (StorePre 0x10c13d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10c13d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10c13d 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[3539, 65]
    (.letOp (n := 3542) (.out 0x10c142 (addR64R64Effect 0x10c142 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[3533, 3535]
    (.letOp (n := 3543) (.exec 0x10c142 (fun s => s.RIP = 0x10c142) (addR64R64Effect 0x10c142 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[3533, 3535]
    (b_l10a410_83)))))))))))))))))))))))))))))))))))

def bytes_l10a410_82 : List UInt8 :=
  [0x49, 0x01, 0xF9, 0x4D, 0x29, 0xC1, 0x4C, 0x89, 0x4C, 0x24, 0x08, 0x49, 0x01, 0xF8, 0x4C, 0x89,
    0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4D, 0x89, 0xD5, 0x4D, 0x21, 0xD4, 0x49, 0xB9, 0xFC, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00, 0x48, 0x8B, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00, 0x4E, 0x8D,
    0x04, 0x0F, 0x4D, 0x29, 0xE0, 0x4C, 0x89, 0x44, 0x24, 0x28, 0x49, 0x01, 0xFC, 0x4C, 0x89, 0xA4,
    0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x21, 0xD0, 0x48, 0x8B, 0xBC, 0x24, 0x68, 0x01, 0x00, 0x00,
    0x4E, 0x8D, 0x04, 0x0F, 0x49, 0x29, 0xC0, 0x4C, 0x89, 0x44, 0x24, 0x30, 0x48, 0x01, 0xF8] ++ bytes_l10a410_83

theorem code_l10a410_82 : ∀ x ∈ codeRange 0x10c0e6 bytes_l10a410_82, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc0e6 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_83

def b_l10a410_81 : Block Op Label signature Reg.count 3469 :=
  .letOp (n := 3469) (.out 0x10c099 (imulR64R64Effect 0x10c099 4 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[3465, 3467]
    (.letOp (n := 3470) (.exec 0x10c099 (fun s => s.RIP = 0x10c099) (imulR64R64Effect 0x10c099 4 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[3465, 3467]
    (.letOp (n := 3471) (.out 0x10c09d (addR64R64Effect 0x10c09d 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[3469, 3445]
    (.letOp (n := 3472) (.exec 0x10c09d (fun s => s.RIP = 0x10c09d) (addR64R64Effect 0x10c09d 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[3469, 3445]
    (.letOp (n := 3473) (.out 0x10c0a0 (movR64R64Effect 0x10c0a0 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[3471]
    (.letOp (n := 3474) (.exec 0x10c0a0 (fun s => s.RIP = 0x10c0a0) (movR64R64Effect 0x10c0a0 1 8) (Reg.operands [.gpr 8] [])) #v[3471]
    (.letOp (n := 3475) (.out 0x10c0a3 (shrR64Effect 0x10c0a3 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3473]
    (.letOp (n := 3476) (.exec 0x10c0a3 (fun s => s.RIP = 0x10c0a3) (shrR64Effect 0x10c0a3 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3473]
    (.letOp (n := 3477) (.out 0x10c0a7 (addR64R64Effect 0x10c0a7 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[3475, 3449]
    (.letOp (n := 3478) (.exec 0x10c0a7 (fun s => s.RIP = 0x10c0a7) (addR64R64Effect 0x10c0a7 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[3475, 3449]
    (.letOp (n := 3479) (.out 0x10c0aa (movR64R64Effect 0x10c0aa 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[3477]
    (.letOp (n := 3480) (.exec 0x10c0aa (fun s => s.RIP = 0x10c0aa) (movR64R64Effect 0x10c0aa 0 1) (Reg.operands [.gpr 1] [])) #v[3477]
    (.letOp (n := 3481) (.out 0x10c0ad (movR64R64Effect 0x10c0ad 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[3477]
    (.letOp (n := 3482) (.exec 0x10c0ad (fun s => s.RIP = 0x10c0ad) (movR64R64Effect 0x10c0ad 12 1) (Reg.operands [.gpr 1] [])) #v[3477]
    (.letOp (n := 3483) (.out 0x10c0b0 (shrR64Effect 0x10c0b0 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3479]
    (.letOp (n := 3484) (.exec 0x10c0b0 (fun s => s.RIP = 0x10c0b0) (shrR64Effect 0x10c0b0 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3479]
    (.letOp (n := 3485) (.out 0x10c0b4 (addR64R64Effect 0x10c0b4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[3483, 3453]
    (.letOp (n := 3486) (.exec 0x10c0b4 (fun s => s.RIP = 0x10c0b4) (addR64R64Effect 0x10c0b4 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[3483, 3453]
    (.letOp (n := 3487) (.out 0x10c0b7 (movR64R64Effect 0x10c0b7 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[3485]
    (.letOp (n := 3488) (.exec 0x10c0b7 (fun s => s.RIP = 0x10c0b7) (movR64R64Effect 0x10c0b7 2 0) (Reg.operands [.gpr 0] [])) #v[3485]
    (.letOp (n := 3489) (.out 0x10c0ba (shrR64Effect 0x10c0ba 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3487]
    (.letOp (n := 3490) (.exec 0x10c0ba (fun s => s.RIP = 0x10c0ba) (shrR64Effect 0x10c0ba 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3487]
    (.letOp (n := 3491) (.out 0x10c0be (addR64R64Effect 0x10c0be 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[3489, 3457]
    (.letOp (n := 3492) (.exec 0x10c0be (fun s => s.RIP = 0x10c0be) (addR64R64Effect 0x10c0be 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[3489, 3457]
    (.letOp (n := 3493) (.out 0x10c0c1 (movR64R64Effect 0x10c0c1 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[3370]
    (.letOp (n := 3494) (.exec 0x10c0c1 (fun s => s.RIP = 0x10c0c1) (movR64R64Effect 0x10c0c1 1 13) (Reg.operands [.gpr 13] [])) #v[3370]
    (.letOp (n := 3495) (.out 0x10c0c4 (andR64R64Effect 0x10c0c4 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[3461, 3370]
    (.letOp (n := 3496) (.exec 0x10c0c4 (fun s => s.RIP = 0x10c0c4) (andR64R64Effect 0x10c0c4 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[3461, 3370]
    (.letOp (n := 3497) (.out 0x10c0c7 (movR64R64Effect 0x10c0c7 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[3491]
    (.letOp (n := 3498) (.exec 0x10c0c7 (fun s => s.RIP = 0x10c0c7) (movR64R64Effect 0x10c0c7 6 2) (Reg.operands [.gpr 2] [])) #v[3491]
    (.letOp (n := 3499) (.out 0x10c0ca (shrR64Effect 0x10c0ca 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3497]
    (.letOp (n := 3500) (.exec 0x10c0ca (fun s => s.RIP = 0x10c0ca) (shrR64Effect 0x10c0ca 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3497]
    (.letOp (n := 3501) (.out 0x10c0ce (addR64R64Effect 0x10c0ce 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[3499, 3495]
    (.letOp (n := 3502) (.exec 0x10c0ce (fun s => s.RIP = 0x10c0ce) (addR64R64Effect 0x10c0ce 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[3499, 3495]
    (.letOp (n := 3503) (.out 0x10c0d1 (andR64R64Effect 0x10c0d1 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[3471, 3352]
    (.letOp (n := 3504) (.exec 0x10c0d1 (fun s => s.RIP = 0x10c0d1) (andR64R64Effect 0x10c0d1 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[3471, 3352]
    (.letOp (n := 3505) (.out 0x10c0d4 (movR64Imm64Effect 0x10c0d4 9 0x3ffffbfffff0bc) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 3506) (.exec 0x10c0d4 (fun s => s.RIP = 0x10c0d4) (movR64Imm64Effect 0x10c0d4 9 0x3ffffbfffff0bc) (Reg.operands [] [])) #v[]
    (.letOp (n := 3507) (.out 0x10c0de (movR64M64Effect 0x10c0de 7 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 3508) (.exec 0x10c0de (LoadPre 0x10c0de (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10c0de + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c0de 7 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_82))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_81 : List UInt8 :=
  [0x4D, 0x0F, 0xAF, 0xC7, 0x49, 0x01, 0xC8, 0x4C, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x34, 0x48, 0x01,
    0xD1, 0x48, 0x89, 0xC8, 0x49, 0x89, 0xCC, 0x48, 0xC1, 0xE8, 0x34, 0x48, 0x01, 0xF0, 0x48, 0x89,
    0xC2, 0x48, 0xC1, 0xEA, 0x34, 0x4C, 0x01, 0xCA, 0x4C, 0x89, 0xE9, 0x4C, 0x21, 0xEF, 0x48, 0x89,
    0xD6, 0x48, 0xC1, 0xEE, 0x34, 0x48, 0x01, 0xFE, 0x4D, 0x21, 0xD0, 0x49, 0xB9, 0xBC, 0xF0, 0xFF,
    0xFF, 0xFB, 0xFF, 0x3F, 0x00, 0x48, 0x8B, 0xBC, 0x24, 0x50, 0x01, 0x00, 0x00] ++ bytes_l10a410_82

theorem code_l10a410_81 : ∀ x ∈ codeRange 0x10c099 bytes_l10a410_81, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc099 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_82

def b_l10a410_80 : Block Op Label signature Reg.count 3430 :=
  .letOp (n := 3430) (.out 0x10c038 (movR64M64Effect 0x10c038 11 (.sib 4 none 0 (.d32 0x190))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 3431) (.exec 0x10c038 (LoadPre 0x10c038 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x10c038 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c038 11 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3432) (.out 0x10c040 (movR64M64Effect 0x10c040 8 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 3433) (.exec 0x10c040 (LoadPre 0x10c040 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10c040 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c040 8 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3434) (.out 0x10c048 (subR64R64Effect 0x10c048 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[3374, 3430]
    (.letOp (n := 3435) (.exec 0x10c048 (fun s => s.RIP = 0x10c048) (subR64R64Effect 0x10c048 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[3374, 3430]
    (.letOp (n := 3436) (.out 0x10c04b (subR64R64Effect 0x10c04b 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[3434, 3432]
    (.letOp (n := 3437) (.exec 0x10c04b (fun s => s.RIP = 0x10c04b) (subR64R64Effect 0x10c04b 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[3434, 3432]
    (.letOp (n := 3438) (.out 0x10c04e (movR64Imm64Effect 0x10c04e 0 0x5fffffffffffa) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 3439) (.exec 0x10c04e (fun s => s.RIP = 0x10c04e) (movR64Imm64Effect 0x10c04e 0 0x5fffffffffffa) (Reg.operands [] [])) #v[]
    (.letOp (n := 3440) (.out 0x10c058 (addR64R64Effect 0x10c058 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[3436, 3438]
    (.letOp (n := 3441) (.exec 0x10c058 (fun s => s.RIP = 0x10c058) (addR64R64Effect 0x10c058 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[3436, 3438]
    (.letOp (n := 3442) (.exec 0x10c05b (StorePre 0x10c05b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10c05b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10c05b 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[3440, 65]
    (.letOp (n := 3443) (.out 0x10c060 (leaR64Effect 0x10c060 0 (.sib 1 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 1] []) (.reg (.gpr 0))) #v[3376, 3376]
    (.letOp (n := 3444) (.exec 0x10c060 (fun s => s.RIP = 0x10c060) (leaR64Effect 0x10c060 0 (.sib 1 (some 1) 2 .none)) (Reg.operands [.gpr 1, .gpr 1] [])) #v[3376, 3376]
    (.letOp (n := 3445) (.out 0x10c064 (leaR64Effect 0x10c064 1 (.sib 1 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[3376, 3443]
    (.letOp (n := 3446) (.exec 0x10c064 (fun s => s.RIP = 0x10c064) (leaR64Effect 0x10c064 1 (.sib 1 (some 0) 2 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3376, 3443]
    (.letOp (n := 3447) (.out 0x10c068 (leaR64Effect 0x10c068 0 (.sib 9 (some 9) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 9] []) (.reg (.gpr 0))) #v[3391, 3391]
    (.letOp (n := 3448) (.exec 0x10c068 (fun s => s.RIP = 0x10c068) (leaR64Effect 0x10c068 0 (.sib 9 (some 9) 2 .none)) (Reg.operands [.gpr 9, .gpr 9] [])) #v[3391, 3391]
    (.letOp (n := 3449) (.out 0x10c06c (leaR64Effect 0x10c06c 2 (.sib 9 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[3391, 3447]
    (.letOp (n := 3450) (.exec 0x10c06c (fun s => s.RIP = 0x10c06c) (leaR64Effect 0x10c06c 2 (.sib 9 (some 0) 2 .none)) (Reg.operands [.gpr 9, .gpr 0] [])) #v[3391, 3447]
    (.letOp (n := 3451) (.out 0x10c070 (leaR64Effect 0x10c070 0 (.sib 15 (some 15) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 15] []) (.reg (.gpr 0))) #v[3401, 3401]
    (.letOp (n := 3452) (.exec 0x10c070 (fun s => s.RIP = 0x10c070) (leaR64Effect 0x10c070 0 (.sib 15 (some 15) 2 .none)) (Reg.operands [.gpr 15, .gpr 15] [])) #v[3401, 3401]
    (.letOp (n := 3453) (.out 0x10c074 (leaR64Effect 0x10c074 6 (.sib 15 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15, .gpr 0] []) (.reg (.gpr 6))) #v[3401, 3451]
    (.letOp (n := 3454) (.exec 0x10c074 (fun s => s.RIP = 0x10c074) (leaR64Effect 0x10c074 6 (.sib 15 (some 0) 2 .none)) (Reg.operands [.gpr 15, .gpr 0] [])) #v[3401, 3451]
    (.letOp (n := 3455) (.out 0x10c078 (leaR64Effect 0x10c078 0 (.sib 12 (some 12) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 12] []) (.reg (.gpr 0))) #v[3411, 3411]
    (.letOp (n := 3456) (.exec 0x10c078 (fun s => s.RIP = 0x10c078) (leaR64Effect 0x10c078 0 (.sib 12 (some 12) 2 .none)) (Reg.operands [.gpr 12, .gpr 12] [])) #v[3411, 3411]
    (.letOp (n := 3457) (.out 0x10c07c (leaR64Effect 0x10c07c 9 (.sib 12 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 12, .gpr 0] []) (.reg (.gpr 9))) #v[3411, 3455]
    (.letOp (n := 3458) (.exec 0x10c07c (fun s => s.RIP = 0x10c07c) (leaR64Effect 0x10c07c 9 (.sib 12 (some 0) 2 .none)) (Reg.operands [.gpr 12, .gpr 0] [])) #v[3411, 3455]
    (.letOp (n := 3459) (.out 0x10c080 (leaR64Effect 0x10c080 0 (.sib 8 (some 8) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 8] []) (.reg (.gpr 0))) #v[3432, 3432]
    (.letOp (n := 3460) (.exec 0x10c080 (fun s => s.RIP = 0x10c080) (leaR64Effect 0x10c080 0 (.sib 8 (some 8) 2 .none)) (Reg.operands [.gpr 8, .gpr 8] [])) #v[3432, 3432]
    (.letOp (n := 3461) (.out 0x10c084 (leaR64Effect 0x10c084 7 (.sib 8 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8, .gpr 0] []) (.reg (.gpr 7))) #v[3432, 3459]
    (.letOp (n := 3462) (.exec 0x10c084 (fun s => s.RIP = 0x10c084) (leaR64Effect 0x10c084 7 (.sib 8 (some 0) 2 .none)) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3432, 3459]
    (.letOp (n := 3463) (.out 0x10c088 (movR64R64Effect 0x10c088 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[3461]
    (.letOp (n := 3464) (.exec 0x10c088 (fun s => s.RIP = 0x10c088) (movR64R64Effect 0x10c088 8 7) (Reg.operands [.gpr 7] [])) #v[3461]
    (.letOp (n := 3465) (.out 0x10c08b (shrR64Effect 0x10c08b 4 8 48) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[3463]
    (.letOp (n := 3466) (.exec 0x10c08b (fun s => s.RIP = 0x10c08b) (shrR64Effect 0x10c08b 4 8 48) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3463]
    (.letOp (n := 3467) (.out 0x10c08f (movR64Imm64Effect 0x10c08f 15 0x1000003d1) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 3468) (.exec 0x10c08f (fun s => s.RIP = 0x10c08f) (movR64Imm64Effect 0x10c08f 15 0x1000003d1) (Reg.operands [] [])) #v[]
    (b_l10a410_81)))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_80 : List UInt8 :=
  [0x4C, 0x8B, 0x9C, 0x24, 0x90, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00,
    0x4C, 0x29, 0xDD, 0x4C, 0x29, 0xC5, 0x48, 0xB8, 0xFA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x05, 0x00,
    0x48, 0x01, 0xC5, 0x48, 0x89, 0x6C, 0x24, 0x10, 0x48, 0x8D, 0x04, 0x89, 0x48, 0x8D, 0x0C, 0x81,
    0x4B, 0x8D, 0x04, 0x89, 0x49, 0x8D, 0x14, 0x81, 0x4B, 0x8D, 0x04, 0xBF, 0x49, 0x8D, 0x34, 0x87,
    0x4B, 0x8D, 0x04, 0xA4, 0x4D, 0x8D, 0x0C, 0x84, 0x4B, 0x8D, 0x04, 0x80, 0x49, 0x8D, 0x3C, 0x80,
    0x49, 0x89, 0xF8, 0x49, 0xC1, 0xE8, 0x30, 0x49, 0xBF, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00,
    0x00] ++ bytes_l10a410_81

theorem code_l10a410_80 : ∀ x ∈ codeRange 0x10c038 bytes_l10a410_80, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc038 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_81

def b_l10a410_79 : Block Op Label signature Reg.count 3393 :=
  .letOp (n := 3393) (.out 0x10bfd4 (movR64M64Effect 0x10bfd4 0 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3394) (.exec 0x10bfd4 (LoadPre 0x10bfd4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x10bfd4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bfd4 0 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3395) (.out 0x10bfdc (addR64R64Effect 0x10bfdc 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[3393, 3391]
    (.letOp (n := 3396) (.exec 0x10bfdc (fun s => s.RIP = 0x10bfdc) (addR64R64Effect 0x10bfdc 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[3393, 3391]
    (.letOp (n := 3397) (.out 0x10bfdf (movR64R64Effect 0x10bfdf 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[3278]
    (.letOp (n := 3398) (.exec 0x10bfdf (fun s => s.RIP = 0x10bfdf) (movR64R64Effect 0x10bfdf 7 15) (Reg.operands [.gpr 15] [])) #v[3278]
    (.letOp (n := 3399) (.out 0x10bfe2 (subR64R64Effect 0x10bfe2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[3397, 3395]
    (.letOp (n := 3400) (.exec 0x10bfe2 (fun s => s.RIP = 0x10bfe2) (subR64R64Effect 0x10bfe2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[3397, 3395]
    (.letOp (n := 3401) (.out 0x10bfe5 (movR64M64Effect 0x10bfe5 15 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 3402) (.exec 0x10bfe5 (LoadPre 0x10bfe5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x10bfe5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bfe5 15 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3403) (.out 0x10bfed (movR64M64Effect 0x10bfed 0 (.sib 4 none 0 (.d32 0x1a0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3404) (.exec 0x10bfed (LoadPre 0x10bfed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x10bfed + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bfed 0 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3405) (.out 0x10bff5 (addR64R64Effect 0x10bff5 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[3403, 3401]
    (.letOp (n := 3406) (.exec 0x10bff5 (fun s => s.RIP = 0x10bff5) (addR64R64Effect 0x10bff5 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[3403, 3401]
    (.letOp (n := 3407) (.out 0x10bff8 (subR64R64Effect 0x10bff8 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[3341, 3405]
    (.letOp (n := 3408) (.exec 0x10bff8 (fun s => s.RIP = 0x10bff8) (subR64R64Effect 0x10bff8 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3341, 3405]
    (.letOp (n := 3409) (.out 0x10bffb (andR64R64Effect 0x10bffb 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[3366, 3352]
    (.letOp (n := 3410) (.exec 0x10bffb (fun s => s.RIP = 0x10bffb) (andR64R64Effect 0x10bffb 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[3366, 3352]
    (.letOp (n := 3411) (.out 0x10bffe (movR64M64Effect 0x10bffe 12 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 3412) (.exec 0x10bffe (LoadPre 0x10bffe (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10bffe + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bffe 12 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3413) (.out 0x10c006 (movR64M64Effect 0x10c006 0 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3414) (.exec 0x10c006 (LoadPre 0x10c006 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x10c006 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c006 0 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3415) (.out 0x10c00e (addR64R64Effect 0x10c00e 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[3413, 3411]
    (.letOp (n := 3416) (.exec 0x10c00e (fun s => s.RIP = 0x10c00e) (addR64R64Effect 0x10c00e 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[3413, 3411]
    (.letOp (n := 3417) (.out 0x10c011 (subR64R64Effect 0x10c011 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[3409, 3415]
    (.letOp (n := 3418) (.exec 0x10c011 (fun s => s.RIP = 0x10c011) (subR64R64Effect 0x10c011 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3409, 3415]
    (.letOp (n := 3419) (.out 0x10c014 (movR64Imm64Effect 0x10c014 0 0x5ffffffffffffa) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 3420) (.exec 0x10c014 (fun s => s.RIP = 0x10c014) (movR64Imm64Effect 0x10c014 0 0x5ffffffffffffa) (Reg.operands [] [])) #v[]
    (.letOp (n := 3421) (.out 0x10c01e (addR64R64Effect 0x10c01e 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[3399, 3419]
    (.letOp (n := 3422) (.exec 0x10c01e (fun s => s.RIP = 0x10c01e) (addR64R64Effect 0x10c01e 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[3399, 3419]
    (.letOp (n := 3423) (.exec 0x10c021 (StorePre 0x10c021 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10c021 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10c021 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[3421, 65]
    (.letOp (n := 3424) (.out 0x10c026 (addR64R64Effect 0x10c026 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[3407, 3419]
    (.letOp (n := 3425) (.exec 0x10c026 (fun s => s.RIP = 0x10c026) (addR64R64Effect 0x10c026 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3407, 3419]
    (.letOp (n := 3426) (.exec 0x10c029 (StorePre 0x10c029 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10c029 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c029 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[3424, 65]
    (.letOp (n := 3427) (.out 0x10c031 (addR64R64Effect 0x10c031 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[3417, 3419]
    (.letOp (n := 3428) (.exec 0x10c031 (fun s => s.RIP = 0x10c031) (addR64R64Effect 0x10c031 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3417, 3419]
    (.letOp (n := 3429) (.exec 0x10c034 (StorePre 0x10c034 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10c034 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10c034 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[3427, 65]
    (b_l10a410_80)))))))))))))))))))))))))))))))))))))

def bytes_l10a410_79 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00, 0x4C, 0x01, 0xC8, 0x4C, 0x89, 0xFF, 0x48, 0x29,
    0xC7, 0x4C, 0x8B, 0xBC, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xA0, 0x01, 0x00,
    0x00, 0x4C, 0x01, 0xF8, 0x49, 0x29, 0xC0, 0x4C, 0x21, 0xD6, 0x4C, 0x8B, 0xA4, 0x24, 0xD8, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x78, 0x01, 0x00, 0x00, 0x4C, 0x01, 0xE0, 0x48, 0x29, 0xC6,
    0x48, 0xB8, 0xFA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x5F, 0x00, 0x48, 0x01, 0xC7, 0x48, 0x89, 0x7C,
    0x24, 0x50, 0x49, 0x01, 0xC0, 0x4C, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x01, 0xC6,
    0x48, 0x89, 0x34, 0x24] ++ bytes_l10a410_80

theorem code_l10a410_79 : ∀ x ∈ codeRange 0x10bfd4 bytes_l10a410_79, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbfd4 100 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_80

def b_l10a410_78 : Block Op Label signature Reg.count 3352 :=
  .letOp (n := 3352) (.out 0x10bf74 (movR64R64Effect 0x10bf74 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[3276]
    (.letOp (n := 3353) (.exec 0x10bf74 (fun s => s.RIP = 0x10bf74) (movR64R64Effect 0x10bf74 10 1) (Reg.operands [.gpr 1] [])) #v[3276]
    (.letOp (n := 3354) (.out 0x10bf77 (addR64R64Effect 0x10bf77 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[3350, 3345]
    (.letOp (n := 3355) (.out 0x10bf77 (addR64R64Effect 0x10bf77 13 0) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 0] []) (.flag .CF)) #v[3350, 3345]
    (.letOp (n := 3356) (.exec 0x10bf77 (fun s => s.RIP = 0x10bf77) (addR64R64Effect 0x10bf77 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[3350, 3345]
    (.letOp (n := 3357) (.out 0x10bf7a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bf7a 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[3346, 3355]
    (.letOp (n := 3358) (.exec 0x10bf7a (fun s => s.RIP = 0x10bf7a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bf7a 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3346, 3355]
    (.letOp (n := 3359) (.out 0x10bf7e (addR64R64Effect 0x10bf7e 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[3354, 3337]
    (.letOp (n := 3360) (.out 0x10bf7e (addR64R64Effect 0x10bf7e 13 9) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 9] []) (.flag .CF)) #v[3354, 3337]
    (.letOp (n := 3361) (.exec 0x10bf7e (fun s => s.RIP = 0x10bf7e) (addR64R64Effect 0x10bf7e 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[3354, 3337]
    (.letOp (n := 3362) (.out 0x10bf81 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bf81 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[3357, 3360]
    (.letOp (n := 3363) (.exec 0x10bf81 (fun s => s.RIP = 0x10bf81) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bf81 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3357, 3360]
    (.letOp (n := 3364) (.out 0x10bf85 (shldR64R64Effect 0x10bf85 5 2 13 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3362, 3359]
    (.letOp (n := 3365) (.exec 0x10bf85 (fun s => s.RIP = 0x10bf85) (shldR64R64Effect 0x10bf85 5 2 13 12) (Reg.operands [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3362, 3359]
    (.letOp (n := 3366) (.out 0x10bf8a (movR64R64Effect 0x10bf8a 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[3359]
    (.letOp (n := 3367) (.exec 0x10bf8a (fun s => s.RIP = 0x10bf8a) (movR64R64Effect 0x10bf8a 6 13) (Reg.operands [.gpr 13] [])) #v[3359]
    (.letOp (n := 3368) (.out 0x10bf8d (movR64M64Effect 0x10bf8d 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 3369) (.exec 0x10bf8d (LoadPre 0x10bf8d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10bf8d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bf8d 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3370) (.out 0x10bf92 (movR64Imm64Effect 0x10bf92 13 0xffffffffffff) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 3371) (.exec 0x10bf92 (fun s => s.RIP = 0x10bf92) (movR64Imm64Effect 0x10bf92 13 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 3372) (.out 0x10bf9c (andR64R64Effect 0x10bf9c 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[3368, 3370]
    (.letOp (n := 3373) (.exec 0x10bf9c (fun s => s.RIP = 0x10bf9c) (andR64R64Effect 0x10bf9c 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[3368, 3370]
    (.letOp (n := 3374) (.out 0x10bf9f (addR64R64Effect 0x10bf9f 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[3372, 3364]
    (.letOp (n := 3375) (.exec 0x10bf9f (fun s => s.RIP = 0x10bf9f) (addR64R64Effect 0x10bf9f 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[3372, 3364]
    (.letOp (n := 3376) (.out 0x10bfa2 (movR64M64Effect 0x10bfa2 1 (.sib 4 none 0 (.d32 0x1d8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 3377) (.exec 0x10bfa2 (LoadPre 0x10bfa2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x10bfa2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bfa2 1 (.sib 4 none 0 (.d32 0x1d8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3378) (.out 0x10bfaa (movR64M64Effect 0x10bfaa 0 (.sib 4 none 0 (.d32 0x1a8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3379) (.exec 0x10bfaa (LoadPre 0x10bfaa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x10bfaa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bfaa 0 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3380) (.out 0x10bfb2 (addR64R64Effect 0x10bfb2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3378, 3376]
    (.letOp (n := 3381) (.exec 0x10bfb2 (fun s => s.RIP = 0x10bfb2) (addR64R64Effect 0x10bfb2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3378, 3376]
    (.letOp (n := 3382) (.out 0x10bfb5 (movR64M64Effect 0x10bfb5 14 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 3383) (.exec 0x10bfb5 (LoadPre 0x10bfb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10bfb5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bfb5 14 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3384) (.out 0x10bfba (subR64R64Effect 0x10bfba 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[3382, 3380]
    (.letOp (n := 3385) (.exec 0x10bfba (fun s => s.RIP = 0x10bfba) (subR64R64Effect 0x10bfba 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[3382, 3380]
    (.letOp (n := 3386) (.out 0x10bfbd (movR64Imm64Effect 0x10bfbd 0 0x5ffff9ffffe91a) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 3387) (.exec 0x10bfbd (fun s => s.RIP = 0x10bfbd) (movR64Imm64Effect 0x10bfbd 0 0x5ffff9ffffe91a) (Reg.operands [] [])) #v[]
    (.letOp (n := 3388) (.out 0x10bfc7 (addR64R64Effect 0x10bfc7 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[3384, 3386]
    (.letOp (n := 3389) (.exec 0x10bfc7 (fun s => s.RIP = 0x10bfc7) (addR64R64Effect 0x10bfc7 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[3384, 3386]
    (.letOp (n := 3390) (.exec 0x10bfca (StorePre 0x10bfca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10bfca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bfca 14 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[3388, 65]
    (.letOp (n := 3391) (.out 0x10bfcf (movR64M64Effect 0x10bfcf 9 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 3392) (.exec 0x10bfcf (LoadPre 0x10bfcf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10bfcf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bfcf 9 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_79)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_78 : List UInt8 :=
  [0x49, 0x89, 0xCA, 0x49, 0x01, 0xC5, 0x48, 0x83, 0xD2, 0x00, 0x4D, 0x01, 0xCD, 0x48, 0x83, 0xD2,
    0x00, 0x4C, 0x0F, 0xA4, 0xEA, 0x0C, 0x4C, 0x89, 0xEE, 0x48, 0x8B, 0x6C, 0x24, 0x10, 0x49, 0xBD,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x4C, 0x21, 0xED, 0x48, 0x01, 0xD5, 0x48, 0x8B,
    0x8C, 0x24, 0xD8, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x01, 0x00, 0x00, 0x48, 0x01,
    0xC8, 0x4C, 0x8B, 0x74, 0x24, 0x38, 0x49, 0x29, 0xC6, 0x48, 0xB8, 0x1A, 0xE9, 0xFF, 0xFF, 0xF9,
    0xFF, 0x5F, 0x00, 0x49, 0x01, 0xC6, 0x4C, 0x89, 0x74, 0x24, 0x38, 0x4C, 0x8B, 0x4C, 0x24, 0x68] ++ bytes_l10a410_79

theorem code_l10a410_78 : ∀ x ∈ codeRange 0x10bf74 bytes_l10a410_78, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbf74 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_79

def b_l10a410_77 : Block Op Label signature Reg.count 3306 :=
  .letOp (n := 3306) (.out 0x10bf29 (movR64R64Effect 0x10bf29 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[3301]
    (.letOp (n := 3307) (.exec 0x10bf29 (fun s => s.RIP = 0x10bf29) (movR64R64Effect 0x10bf29 0 10) (Reg.operands [.gpr 10] [])) #v[3301]
    (.letOp (n := 3308) (.out 0x10bf2c (andR64R64Effect 0x10bf2c 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3306, 3276]
    (.letOp (n := 3309) (.exec 0x10bf2c (fun s => s.RIP = 0x10bf2c) (andR64R64Effect 0x10bf2c 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3306, 3276]
    (.letOp (n := 3310) (.out 0x10bf2f (movR64Imm64Effect 0x10bf2f 6 0x1000003d10) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 3311) (.exec 0x10bf2f (fun s => s.RIP = 0x10bf2f) (movR64Imm64Effect 0x10bf2f 6 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 3312) (.out 0x10bf39 (mulR64Effect 0x10bf39 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[3310, 3308]
    (.letOp (n := 3313) (.out 0x10bf39 (mulR64Effect 0x10bf39 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[3310, 3308]
    (.letOp (n := 3314) (.exec 0x10bf39 (fun s => s.RIP = 0x10bf39) (mulR64Effect 0x10bf39 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3310, 3308]
    (.letOp (n := 3315) (.out 0x10bf3c (addR64R64Effect 0x10bf3c 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[3272, 3265]
    (.letOp (n := 3316) (.out 0x10bf3c (addR64R64Effect 0x10bf3c 7 12) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 12] []) (.flag .CF)) #v[3272, 3265]
    (.letOp (n := 3317) (.exec 0x10bf3c (fun s => s.RIP = 0x10bf3c) (addR64R64Effect 0x10bf3c 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[3272, 3265]
    (.letOp (n := 3318) (.out 0x10bf3f (atFlags StatusFlags.CF (adcR64R64Effect 0x10bf3f 9 14)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[3274, 3263, 3316]
    (.letOp (n := 3319) (.exec 0x10bf3f (fun s => s.RIP = 0x10bf3f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10bf3f 9 14)) (Reg.operands [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3274, 3263, 3316]
    (.letOp (n := 3320) (.out 0x10bf42 (addR64R64Effect 0x10bf42 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[3315, 3256]
    (.letOp (n := 3321) (.out 0x10bf42 (addR64R64Effect 0x10bf42 7 5) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 5] []) (.flag .CF)) #v[3315, 3256]
    (.letOp (n := 3322) (.exec 0x10bf42 (fun s => s.RIP = 0x10bf42) (addR64R64Effect 0x10bf42 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[3315, 3256]
    (.letOp (n := 3323) (.out 0x10bf45 (atFlags StatusFlags.CF (adcR64M64Effect 0x10bf45 9 (.sib 4 none 0 (.d8 0x30)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[3318, 65, 3321]
    (.letOp (n := 3324) (.exec 0x10bf45 (LoadPre 0x10bf45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10bf45 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10bf45 9 (.sib 4 none 0 (.d8 0x30)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3318, 65, 3321]
    (.letOp (n := 3325) (.out 0x10bf4a (addR64R64Effect 0x10bf4a 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[3320, 3312]
    (.letOp (n := 3326) (.out 0x10bf4a (addR64R64Effect 0x10bf4a 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[3320, 3312]
    (.letOp (n := 3327) (.exec 0x10bf4a (fun s => s.RIP = 0x10bf4a) (addR64R64Effect 0x10bf4a 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[3320, 3312]
    (.letOp (n := 3328) (.out 0x10bf4d (atFlags StatusFlags.CF (adcR64R64Effect 0x10bf4d 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[3323, 3313, 3326]
    (.letOp (n := 3329) (.exec 0x10bf4d (fun s => s.RIP = 0x10bf4d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10bf4d 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3323, 3313, 3326]
    (.letOp (n := 3330) (.out 0x10bf50 (addR64R64Effect 0x10bf50 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[3325, 3248]
    (.letOp (n := 3331) (.out 0x10bf50 (addR64R64Effect 0x10bf50 7 8) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 8] []) (.flag .CF)) #v[3325, 3248]
    (.letOp (n := 3332) (.exec 0x10bf50 (fun s => s.RIP = 0x10bf50) (addR64R64Effect 0x10bf50 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[3325, 3248]
    (.letOp (n := 3333) (.out 0x10bf53 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bf53 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[3328, 3331]
    (.letOp (n := 3334) (.exec 0x10bf53 (fun s => s.RIP = 0x10bf53) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bf53 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3328, 3331]
    (.letOp (n := 3335) (.out 0x10bf57 (shldR64R64Effect 0x10bf57 5 3 10 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[3304, 3301]
    (.letOp (n := 3336) (.exec 0x10bf57 (fun s => s.RIP = 0x10bf57) (shldR64R64Effect 0x10bf57 5 3 10 12) (Reg.operands [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3304, 3301]
    (.letOp (n := 3337) (.out 0x10bf5c (shldR64R64Effect 0x10bf5c 5 9 7 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[3333, 3330]
    (.letOp (n := 3338) (.exec 0x10bf5c (fun s => s.RIP = 0x10bf5c) (shldR64R64Effect 0x10bf5c 5 9 7 12) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3333, 3330]
    (.letOp (n := 3339) (.out 0x10bf61 (andR64R64Effect 0x10bf61 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[3330, 3276]
    (.letOp (n := 3340) (.exec 0x10bf61 (fun s => s.RIP = 0x10bf61) (andR64R64Effect 0x10bf61 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[3330, 3276]
    (.letOp (n := 3341) (.out 0x10bf64 (movR64R64Effect 0x10bf64 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[3339]
    (.letOp (n := 3342) (.exec 0x10bf64 (fun s => s.RIP = 0x10bf64) (movR64R64Effect 0x10bf64 8 7) (Reg.operands [.gpr 7] [])) #v[3339]
    (.letOp (n := 3343) (.out 0x10bf67 (movR64R64Effect 0x10bf67 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3335]
    (.letOp (n := 3344) (.exec 0x10bf67 (fun s => s.RIP = 0x10bf67) (movR64R64Effect 0x10bf67 0 3) (Reg.operands [.gpr 3] [])) #v[3335]
    (.letOp (n := 3345) (.out 0x10bf6a (mulR64Effect 0x10bf6a 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[3310, 3343]
    (.letOp (n := 3346) (.out 0x10bf6a (mulR64Effect 0x10bf6a 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[3310, 3343]
    (.letOp (n := 3347) (.exec 0x10bf6a (fun s => s.RIP = 0x10bf6a) (mulR64Effect 0x10bf6a 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3310, 3343]
    (.letOp (n := 3348) (.out 0x10bf6d (movR64M64Effect 0x10bf6d 13 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 3349) (.exec 0x10bf6d (LoadPre 0x10bf6d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10bf6d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10bf6d 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3350) (.out 0x10bf71 (andR64R64Effect 0x10bf71 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[3348, 3276]
    (.letOp (n := 3351) (.exec 0x10bf71 (fun s => s.RIP = 0x10bf71) (andR64R64Effect 0x10bf71 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[3348, 3276]
    (b_l10a410_78))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_77 : List UInt8 :=
  [0x4C, 0x89, 0xD0, 0x48, 0x21, 0xC8, 0x48, 0xBE, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE6, 0x4C, 0x01, 0xE7, 0x4D, 0x11, 0xF1, 0x48, 0x01, 0xEF, 0x4C, 0x13, 0x4C, 0x24,
    0x30, 0x48, 0x01, 0xC7, 0x49, 0x11, 0xD1, 0x4C, 0x01, 0xC7, 0x49, 0x83, 0xD1, 0x00, 0x4C, 0x0F,
    0xA4, 0xD3, 0x0C, 0x49, 0x0F, 0xA4, 0xF9, 0x0C, 0x48, 0x21, 0xCF, 0x49, 0x89, 0xF8, 0x48, 0x89,
    0xD8, 0x48, 0xF7, 0xE6, 0x4C, 0x8B, 0x2C, 0x24, 0x49, 0x21, 0xCD] ++ bytes_l10a410_78

theorem code_l10a410_77 : ∀ x ∈ codeRange 0x10bf29 bytes_l10a410_77, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbf29 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_78

def b_l10a410_76 : Block Op Label signature Reg.count 3260 :=
  .letOp (n := 3260) (.out 0x10bedc (mulM64Effect 0x10bedc 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3258, 65]
    (.letOp (n := 3261) (.out 0x10bedc (mulM64Effect 0x10bedc 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3258, 65]
    (.letOp (n := 3262) (.exec 0x10bedc (LoadPre 0x10bedc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10bedc + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10bedc 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3258, 65]
    (.letOp (n := 3263) (.out 0x10bee4 (movR64R64Effect 0x10bee4 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[3261]
    (.letOp (n := 3264) (.exec 0x10bee4 (fun s => s.RIP = 0x10bee4) (movR64R64Effect 0x10bee4 14 2) (Reg.operands [.gpr 2] [])) #v[3261]
    (.letOp (n := 3265) (.out 0x10bee7 (movR64R64Effect 0x10bee7 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[3260]
    (.letOp (n := 3266) (.exec 0x10bee7 (fun s => s.RIP = 0x10bee7) (movR64R64Effect 0x10bee7 12 0) (Reg.operands [.gpr 0] [])) #v[3260]
    (.letOp (n := 3267) (.out 0x10beea (movR64M64Effect 0x10beea 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3268) (.exec 0x10beea (LoadPre 0x10beea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10beea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10beea 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3269) (.out 0x10beef (mulR64Effect 0x10beef 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[3173, 3267]
    (.letOp (n := 3270) (.out 0x10beef (mulR64Effect 0x10beef 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[3173, 3267]
    (.letOp (n := 3271) (.exec 0x10beef (fun s => s.RIP = 0x10beef) (mulR64Effect 0x10beef 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3173, 3267]
    (.letOp (n := 3272) (.out 0x10bef2 (movR64R64Effect 0x10bef2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[3269]
    (.letOp (n := 3273) (.exec 0x10bef2 (fun s => s.RIP = 0x10bef2) (movR64R64Effect 0x10bef2 7 0) (Reg.operands [.gpr 0] [])) #v[3269]
    (.letOp (n := 3274) (.out 0x10bef5 (movR64R64Effect 0x10bef5 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[3270]
    (.letOp (n := 3275) (.exec 0x10bef5 (fun s => s.RIP = 0x10bef5) (movR64R64Effect 0x10bef5 9 2) (Reg.operands [.gpr 2] [])) #v[3270]
    (.letOp (n := 3276) (.out 0x10bef8 (movR64R64Effect 0x10bef8 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[3224]
    (.letOp (n := 3277) (.exec 0x10bef8 (fun s => s.RIP = 0x10bef8) (movR64R64Effect 0x10bef8 1 6) (Reg.operands [.gpr 6] [])) #v[3224]
    (.letOp (n := 3278) (.out 0x10befb (andR64R64Effect 0x10befb 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[3243, 3224]
    (.letOp (n := 3279) (.exec 0x10befb (fun s => s.RIP = 0x10befb) (andR64R64Effect 0x10befb 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[3243, 3224]
    (.letOp (n := 3280) (.out 0x10befe (movR64M64Effect 0x10befe 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3281) (.exec 0x10befe (LoadPre 0x10befe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10befe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10befe 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3282) (.out 0x10bf03 (mulM64Effect 0x10bf03 8 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3280, 65]
    (.letOp (n := 3283) (.out 0x10bf03 (mulM64Effect 0x10bf03 8 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3280, 65]
    (.letOp (n := 3284) (.exec 0x10bf03 (LoadPre 0x10bf03 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10bf03 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10bf03 8 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3280, 65]
    (.letOp (n := 3285) (.out 0x10bf0b (movR64R64Effect 0x10bf0b 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[3283]
    (.letOp (n := 3286) (.exec 0x10bf0b (fun s => s.RIP = 0x10bf0b) (movR64R64Effect 0x10bf0b 3 2) (Reg.operands [.gpr 2] [])) #v[3283]
    (.letOp (n := 3287) (.out 0x10bf0e (movR64R64Effect 0x10bf0e 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[3282]
    (.letOp (n := 3288) (.exec 0x10bf0e (fun s => s.RIP = 0x10bf0e) (movR64R64Effect 0x10bf0e 6 0) (Reg.operands [.gpr 0] [])) #v[3282]
    (.letOp (n := 3289) (.out 0x10bf11 (movR64M64Effect 0x10bf11 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3290) (.exec 0x10bf11 (LoadPre 0x10bf11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10bf11 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bf11 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3291) (.out 0x10bf16 (mulR64Effect 0x10bf16 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[3200, 3289]
    (.letOp (n := 3292) (.out 0x10bf16 (mulR64Effect 0x10bf16 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[3200, 3289]
    (.letOp (n := 3293) (.exec 0x10bf16 (fun s => s.RIP = 0x10bf16) (mulR64Effect 0x10bf16 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[3200, 3289]
    (.letOp (n := 3294) (.out 0x10bf19 (movR64R64Effect 0x10bf19 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[3291]
    (.letOp (n := 3295) (.exec 0x10bf19 (fun s => s.RIP = 0x10bf19) (movR64R64Effect 0x10bf19 10 0) (Reg.operands [.gpr 0] [])) #v[3291]
    (.letOp (n := 3296) (.out 0x10bf1c (addR64R64Effect 0x10bf1c 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[3294, 3287]
    (.letOp (n := 3297) (.out 0x10bf1c (addR64R64Effect 0x10bf1c 10 6) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 6] []) (.flag .CF)) #v[3294, 3287]
    (.letOp (n := 3298) (.exec 0x10bf1c (fun s => s.RIP = 0x10bf1c) (addR64R64Effect 0x10bf1c 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[3294, 3287]
    (.letOp (n := 3299) (.out 0x10bf1f (atFlags StatusFlags.CF (adcR64R64Effect 0x10bf1f 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[3285, 3292, 3297]
    (.letOp (n := 3300) (.exec 0x10bf1f (fun s => s.RIP = 0x10bf1f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10bf1f 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3285, 3292, 3297]
    (.letOp (n := 3301) (.out 0x10bf22 (addR64R64Effect 0x10bf22 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[3296, 3220]
    (.letOp (n := 3302) (.out 0x10bf22 (addR64R64Effect 0x10bf22 10 11) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 11] []) (.flag .CF)) #v[3296, 3220]
    (.letOp (n := 3303) (.exec 0x10bf22 (fun s => s.RIP = 0x10bf22) (addR64R64Effect 0x10bf22 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[3296, 3220]
    (.letOp (n := 3304) (.out 0x10bf25 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bf25 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[3299, 3302]
    (.letOp (n := 3305) (.exec 0x10bf25 (fun s => s.RIP = 0x10bf25) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bf25 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3299, 3302]
    (b_l10a410_77))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_76 : List UInt8 :=
  [0x48, 0xF7, 0xA4, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x48, 0x8B,
    0x44, 0x24, 0x18, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC7, 0x49, 0x89, 0xD1, 0x48, 0x89, 0xF1, 0x49,
    0x21, 0xF7, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0xF7, 0xA4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48,
    0x89, 0xD3, 0x48, 0x89, 0xC6, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xC2,
    0x49, 0x01, 0xF2, 0x48, 0x11, 0xD3, 0x4D, 0x01, 0xDA, 0x48, 0x83, 0xD3, 0x00] ++ bytes_l10a410_77

theorem code_l10a410_76 : ∀ x ∈ codeRange 0x10bedc bytes_l10a410_76, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbedc 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_77

def b_l10a410_75 : Block Op Label signature Reg.count 3215 :=
  .letOp (n := 3215) (.out 0x10be86 (addR64R64Effect 0x10be86 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[3210, 3129]
    (.letOp (n := 3216) (.out 0x10be86 (addR64R64Effect 0x10be86 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[3210, 3129]
    (.letOp (n := 3217) (.exec 0x10be86 (fun s => s.RIP = 0x10be86) (addR64R64Effect 0x10be86 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[3210, 3129]
    (.letOp (n := 3218) (.out 0x10be89 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10be89 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3213, 3216]
    (.letOp (n := 3219) (.exec 0x10be89 (fun s => s.RIP = 0x10be89) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10be89 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3213, 3216]
    (.letOp (n := 3220) (.out 0x10be8d (shldR64R64Effect 0x10be8d 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[3218, 3215]
    (.letOp (n := 3221) (.exec 0x10be8d (fun s => s.RIP = 0x10be8d) (shldR64R64Effect 0x10be8d 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3218, 3215]
    (.letOp (n := 3222) (.out 0x10be92 (andR64R64Effect 0x10be92 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[3215, 3182]
    (.letOp (n := 3223) (.exec 0x10be92 (fun s => s.RIP = 0x10be92) (andR64R64Effect 0x10be92 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[3215, 3182]
    (.letOp (n := 3224) (.out 0x10be95 (movR64R64Effect 0x10be95 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[3182]
    (.letOp (n := 3225) (.exec 0x10be95 (fun s => s.RIP = 0x10be95) (movR64R64Effect 0x10be95 6 5) (Reg.operands [.gpr 5] [])) #v[3182]
    (.letOp (n := 3226) (.out 0x10be98 (movR64Imm64Effect 0x10be98 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 3227) (.exec 0x10be98 (fun s => s.RIP = 0x10be98) (movR64Imm64Effect 0x10be98 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 3228) (.out 0x10bea2 (mulR64Effect 0x10bea2 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[3226, 3222]
    (.letOp (n := 3229) (.out 0x10bea2 (mulR64Effect 0x10bea2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3226, 3222]
    (.letOp (n := 3230) (.exec 0x10bea2 (fun s => s.RIP = 0x10bea2) (mulR64Effect 0x10bea2 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3226, 3222]
    (.letOp (n := 3231) (.out 0x10bea5 (movR64R64Effect 0x10bea5 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[3169]
    (.letOp (n := 3232) (.exec 0x10bea5 (fun s => s.RIP = 0x10bea5) (movR64R64Effect 0x10bea5 15 12) (Reg.operands [.gpr 12] [])) #v[3169]
    (.letOp (n := 3233) (.out 0x10bea8 (addR64M64Effect 0x10bea8 15 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[3231, 65]
    (.letOp (n := 3234) (.out 0x10bea8 (addR64M64Effect 0x10bea8 15 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[3231, 65]
    (.letOp (n := 3235) (.exec 0x10bea8 (LoadPre 0x10bea8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10bea8 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10bea8 15 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[3231, 65]
    (.letOp (n := 3236) (.out 0x10bead (atFlags StatusFlags.CF (adcR64M64Effect 0x10bead 8 (.sib 4 none 0 (.d8 0x50)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[3167, 65, 3234]
    (.letOp (n := 3237) (.exec 0x10bead (LoadPre 0x10bead (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10bead + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10bead 8 (.sib 4 none 0 (.d8 0x50)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3167, 65, 3234]
    (.letOp (n := 3238) (.out 0x10beb2 (addR64R64Effect 0x10beb2 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[3233, 3228]
    (.letOp (n := 3239) (.out 0x10beb2 (addR64R64Effect 0x10beb2 15 0) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 0] []) (.flag .CF)) #v[3233, 3228]
    (.letOp (n := 3240) (.exec 0x10beb2 (fun s => s.RIP = 0x10beb2) (addR64R64Effect 0x10beb2 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[3233, 3228]
    (.letOp (n := 3241) (.out 0x10beb5 (atFlags StatusFlags.CF (adcR64R64Effect 0x10beb5 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[3236, 3229, 3239]
    (.letOp (n := 3242) (.exec 0x10beb5 (fun s => s.RIP = 0x10beb5) (atFlags StatusFlags.CF (adcR64R64Effect 0x10beb5 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3236, 3229, 3239]
    (.letOp (n := 3243) (.out 0x10beb8 (addR64R64Effect 0x10beb8 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[3238, 3151]
    (.letOp (n := 3244) (.out 0x10beb8 (addR64R64Effect 0x10beb8 15 3) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 3] []) (.flag .CF)) #v[3238, 3151]
    (.letOp (n := 3245) (.exec 0x10beb8 (fun s => s.RIP = 0x10beb8) (addR64R64Effect 0x10beb8 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[3238, 3151]
    (.letOp (n := 3246) (.out 0x10bebb (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bebb 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[3241, 3244]
    (.letOp (n := 3247) (.exec 0x10bebb (fun s => s.RIP = 0x10bebb) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bebb 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3241, 3244]
    (.letOp (n := 3248) (.out 0x10bebf (shldR64R64Effect 0x10bebf 5 8 15 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[3246, 3243]
    (.letOp (n := 3249) (.exec 0x10bebf (fun s => s.RIP = 0x10bebf) (shldR64R64Effect 0x10bebf 5 8 15 12) (Reg.operands [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3246, 3243]
    (.letOp (n := 3250) (.out 0x10bec4 (movR64R64Effect 0x10bec4 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[3196]
    (.letOp (n := 3251) (.exec 0x10bec4 (fun s => s.RIP = 0x10bec4) (movR64R64Effect 0x10bec4 0 14) (Reg.operands [.gpr 14] [])) #v[3196]
    (.letOp (n := 3252) (.out 0x10bec7 (mulM64Effect 0x10bec7 8 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3250, 65]
    (.letOp (n := 3253) (.out 0x10bec7 (mulM64Effect 0x10bec7 8 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3250, 65]
    (.letOp (n := 3254) (.exec 0x10bec7 (LoadPre 0x10bec7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10bec7 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10bec7 8 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3250, 65]
    (.letOp (n := 3255) (.exec 0x10becf (StorePre 0x10becf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10becf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10becf 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3253, 65]
    (.letOp (n := 3256) (.out 0x10bed4 (movR64R64Effect 0x10bed4 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[3252]
    (.letOp (n := 3257) (.exec 0x10bed4 (fun s => s.RIP = 0x10bed4) (movR64R64Effect 0x10bed4 5 0) (Reg.operands [.gpr 0] [])) #v[3252]
    (.letOp (n := 3258) (.out 0x10bed7 (movR64M64Effect 0x10bed7 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3259) (.exec 0x10bed7 (LoadPre 0x10bed7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10bed7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bed7 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_76)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_75 : List UInt8 :=
  [0x4C, 0x01, 0xC8, 0x49, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0x21, 0xE8, 0x48,
    0x89, 0xEE, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4D,
    0x89, 0xE7, 0x4C, 0x03, 0x7C, 0x24, 0x28, 0x4C, 0x13, 0x44, 0x24, 0x50, 0x49, 0x01, 0xC7, 0x49,
    0x11, 0xD0, 0x49, 0x01, 0xDF, 0x49, 0x83, 0xD0, 0x00, 0x4D, 0x0F, 0xA4, 0xF8, 0x0C, 0x4C, 0x89,
    0xF0, 0x48, 0xF7, 0xA4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x30, 0x48, 0x89,
    0xC5, 0x48, 0x8B, 0x44, 0x24, 0x08] ++ bytes_l10a410_76

theorem code_l10a410_75 : ∀ x ∈ codeRange 0x10be86 bytes_l10a410_75, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbe86 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_76

def b_l10a410_74 : Block Op Label signature Reg.count 3171 :=
  .letOp (n := 3171) (.out 0x10be33 (movR64R64Effect 0x10be33 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[3068]
    (.letOp (n := 3172) (.exec 0x10be33 (fun s => s.RIP = 0x10be33) (movR64R64Effect 0x10be33 0 15) (Reg.operands [.gpr 15] [])) #v[3068]
    (.letOp (n := 3173) (.out 0x10be36 (movR64M64Effect 0x10be36 1 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 3174) (.exec 0x10be36 (LoadPre 0x10be36 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10be36 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10be36 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3175) (.out 0x10be3e (mulR64Effect 0x10be3e 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[3173, 3171]
    (.letOp (n := 3176) (.out 0x10be3e (mulR64Effect 0x10be3e 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[3173, 3171]
    (.letOp (n := 3177) (.exec 0x10be3e (fun s => s.RIP = 0x10be3e) (mulR64Effect 0x10be3e 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3173, 3171]
    (.letOp (n := 3178) (.out 0x10be41 (movR64R64Effect 0x10be41 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[3175]
    (.letOp (n := 3179) (.exec 0x10be41 (fun s => s.RIP = 0x10be41) (movR64R64Effect 0x10be41 6 0) (Reg.operands [.gpr 0] [])) #v[3175]
    (.letOp (n := 3180) (.out 0x10be44 (movR64R64Effect 0x10be44 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[3176]
    (.letOp (n := 3181) (.exec 0x10be44 (fun s => s.RIP = 0x10be44) (movR64R64Effect 0x10be44 7 2) (Reg.operands [.gpr 2] [])) #v[3176]
    (.letOp (n := 3182) (.out 0x10be47 (movR64Imm64Effect 0x10be47 5 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 3183) (.exec 0x10be47 (fun s => s.RIP = 0x10be47) (movR64Imm64Effect 0x10be47 5 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 3184) (.out 0x10be51 (andR64R64Effect 0x10be51 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[3153, 3182]
    (.letOp (n := 3185) (.exec 0x10be51 (fun s => s.RIP = 0x10be51) (andR64R64Effect 0x10be51 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[3153, 3182]
    (.letOp (n := 3186) (.exec 0x10be54 (StorePre 0x10be54 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10be54 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10be54 11 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[3184, 65]
    (.letOp (n := 3187) (.out 0x10be59 (movR64R64Effect 0x10be59 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[3080]
    (.letOp (n := 3188) (.exec 0x10be59 (fun s => s.RIP = 0x10be59) (movR64R64Effect 0x10be59 0 13) (Reg.operands [.gpr 13] [])) #v[3080]
    (.letOp (n := 3189) (.out 0x10be5c (mulM64Effect 0x10be5c 8 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3187, 65]
    (.letOp (n := 3190) (.out 0x10be5c (mulM64Effect 0x10be5c 8 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3187, 65]
    (.letOp (n := 3191) (.exec 0x10be5c (LoadPre 0x10be5c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10be5c + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10be5c 8 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3187, 65]
    (.letOp (n := 3192) (.out 0x10be64 (movR64R64Effect 0x10be64 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[3190]
    (.letOp (n := 3193) (.exec 0x10be64 (fun s => s.RIP = 0x10be64) (movR64R64Effect 0x10be64 11 2) (Reg.operands [.gpr 2] [])) #v[3190]
    (.letOp (n := 3194) (.out 0x10be67 (movR64R64Effect 0x10be67 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[3189]
    (.letOp (n := 3195) (.exec 0x10be67 (fun s => s.RIP = 0x10be67) (movR64R64Effect 0x10be67 10 0) (Reg.operands [.gpr 0] [])) #v[3189]
    (.letOp (n := 3196) (.out 0x10be6a (movR64M64Effect 0x10be6a 14 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 3197) (.exec 0x10be6a (LoadPre 0x10be6a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10be6a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10be6a 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3198) (.out 0x10be6f (movR64R64Effect 0x10be6f 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[3196]
    (.letOp (n := 3199) (.exec 0x10be6f (fun s => s.RIP = 0x10be6f) (movR64R64Effect 0x10be6f 0 14) (Reg.operands [.gpr 14] [])) #v[3196]
    (.letOp (n := 3200) (.out 0x10be72 (movR64M64Effect 0x10be72 13 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 3201) (.exec 0x10be72 (LoadPre 0x10be72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10be72 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10be72 13 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3202) (.out 0x10be77 (mulR64Effect 0x10be77 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[3200, 3198]
    (.letOp (n := 3203) (.out 0x10be77 (mulR64Effect 0x10be77 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[3200, 3198]
    (.letOp (n := 3204) (.exec 0x10be77 (fun s => s.RIP = 0x10be77) (mulR64Effect 0x10be77 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[3200, 3198]
    (.letOp (n := 3205) (.out 0x10be7a (addR64R64Effect 0x10be7a 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[3202, 3194]
    (.letOp (n := 3206) (.out 0x10be7a (addR64R64Effect 0x10be7a 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[3202, 3194]
    (.letOp (n := 3207) (.exec 0x10be7a (fun s => s.RIP = 0x10be7a) (addR64R64Effect 0x10be7a 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[3202, 3194]
    (.letOp (n := 3208) (.out 0x10be7d (atFlags StatusFlags.CF (adcR64R64Effect 0x10be7d 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3192, 3203, 3206]
    (.letOp (n := 3209) (.exec 0x10be7d (fun s => s.RIP = 0x10be7d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10be7d 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3192, 3203, 3206]
    (.letOp (n := 3210) (.out 0x10be80 (addR64R64Effect 0x10be80 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[3205, 3178]
    (.letOp (n := 3211) (.out 0x10be80 (addR64R64Effect 0x10be80 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[3205, 3178]
    (.letOp (n := 3212) (.exec 0x10be80 (fun s => s.RIP = 0x10be80) (addR64R64Effect 0x10be80 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[3205, 3178]
    (.letOp (n := 3213) (.out 0x10be83 (atFlags StatusFlags.CF (adcR64R64Effect 0x10be83 11 7)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3208, 3180, 3211]
    (.letOp (n := 3214) (.exec 0x10be83 (fun s => s.RIP = 0x10be83) (atFlags StatusFlags.CF (adcR64R64Effect 0x10be83 11 7)) (Reg.operands [.gpr 11, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3208, 3180, 3211]
    (b_l10a410_75))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_74 : List UInt8 :=
  [0x4C, 0x89, 0xF8, 0x48, 0x8B, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89,
    0xC6, 0x48, 0x89, 0xD7, 0x48, 0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21,
    0xEB, 0x4C, 0x89, 0x5C, 0x24, 0x38, 0x4C, 0x89, 0xE8, 0x48, 0xF7, 0xA4, 0x24, 0xC0, 0x00, 0x00,
    0x00, 0x49, 0x89, 0xD3, 0x49, 0x89, 0xC2, 0x4C, 0x8B, 0x74, 0x24, 0x30, 0x4C, 0x89, 0xF0, 0x4C,
    0x8B, 0x6C, 0x24, 0x70, 0x49, 0xF7, 0xE5, 0x4C, 0x01, 0xD0, 0x49, 0x11, 0xD3, 0x48, 0x01, 0xF0,
    0x49, 0x11, 0xFB] ++ bytes_l10a410_75

theorem code_l10a410_74 : ∀ x ∈ codeRange 0x10be33 bytes_l10a410_74, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbe33 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_75

def b_l10a410_73 : Block Op Label signature Reg.count 3129 :=
  .letOp (n := 3129) (.out 0x10bdda (shldR64R64Effect 0x10bdda 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[3127, 3124]
    (.letOp (n := 3130) (.exec 0x10bdda (fun s => s.RIP = 0x10bdda) (shldR64R64Effect 0x10bdda 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3127, 3124]
    (.letOp (n := 3131) (.out 0x10bddf (shlR64Effect 0x10bddf 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3124]
    (.letOp (n := 3132) (.exec 0x10bddf (fun s => s.RIP = 0x10bddf) (shlR64Effect 0x10bddf 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3124]
    (.letOp (n := 3133) (.out 0x10bde3 (movR64Imm64Effect 0x10bde3 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 3134) (.exec 0x10bde3 (fun s => s.RIP = 0x10bde3) (movR64Imm64Effect 0x10bde3 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 3135) (.out 0x10bded (andR64R64Effect 0x10bded 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3131, 3133]
    (.letOp (n := 3136) (.exec 0x10bded (fun s => s.RIP = 0x10bded) (andR64R64Effect 0x10bded 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3131, 3133]
    (.letOp (n := 3137) (.out 0x10bdf0 (orR64R64Effect 0x10bdf0 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[3135, 3091]
    (.letOp (n := 3138) (.exec 0x10bdf0 (fun s => s.RIP = 0x10bdf0) (orR64R64Effect 0x10bdf0 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[3135, 3091]
    (.letOp (n := 3139) (.out 0x10bdf3 (movR64Imm64Effect 0x10bdf3 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 3140) (.exec 0x10bdf3 (fun s => s.RIP = 0x10bdf3) (movR64Imm64Effect 0x10bdf3 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 3141) (.out 0x10bdfd (mulR64Effect 0x10bdfd 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[3139, 3137]
    (.letOp (n := 3142) (.out 0x10bdfd (mulR64Effect 0x10bdfd 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[3139, 3137]
    (.letOp (n := 3143) (.exec 0x10bdfd (fun s => s.RIP = 0x10bdfd) (mulR64Effect 0x10bdfd 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3139, 3137]
    (.letOp (n := 3144) (.out 0x10be00 (movR64R64Effect 0x10be00 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[3142]
    (.letOp (n := 3145) (.exec 0x10be00 (fun s => s.RIP = 0x10be00) (movR64R64Effect 0x10be00 3 2) (Reg.operands [.gpr 2] [])) #v[3142]
    (.letOp (n := 3146) (.out 0x10be03 (addR64M64Effect 0x10be03 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3141, 65]
    (.letOp (n := 3147) (.out 0x10be03 (addR64M64Effect 0x10be03 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[3141, 65]
    (.letOp (n := 3148) (.exec 0x10be03 (LoadPre 0x10be03 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10be03 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10be03 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3141, 65]
    (.letOp (n := 3149) (.out 0x10be08 (atFlags StatusFlags.CF (adcR64M64Effect 0x10be08 3 (.sib 4 none 0 (.d8 0x38)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[3144, 65, 3147]
    (.letOp (n := 3150) (.exec 0x10be08 (LoadPre 0x10be08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10be08 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10be08 3 (.sib 4 none 0 (.d8 0x38)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3144, 65, 3147]
    (.letOp (n := 3151) (.out 0x10be0d (shldR64R64Effect 0x10be0d 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[3149, 3146]
    (.letOp (n := 3152) (.exec 0x10be0d (fun s => s.RIP = 0x10be0d) (shldR64R64Effect 0x10be0d 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3149, 3146]
    (.letOp (n := 3153) (.out 0x10be12 (movR64R64Effect 0x10be12 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[3146]
    (.letOp (n := 3154) (.exec 0x10be12 (fun s => s.RIP = 0x10be12) (movR64R64Effect 0x10be12 11 0) (Reg.operands [.gpr 0] [])) #v[3146]
    (.letOp (n := 3155) (.out 0x10be15 (movR64R64Effect 0x10be15 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[3102]
    (.letOp (n := 3156) (.exec 0x10be15 (fun s => s.RIP = 0x10be15) (movR64R64Effect 0x10be15 0 10) (Reg.operands [.gpr 10] [])) #v[3102]
    (.letOp (n := 3157) (.out 0x10be18 (mulR64Effect 0x10be18 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[3061, 3155]
    (.letOp (n := 3158) (.out 0x10be18 (mulR64Effect 0x10be18 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[3061, 3155]
    (.letOp (n := 3159) (.exec 0x10be18 (fun s => s.RIP = 0x10be18) (mulR64Effect 0x10be18 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3061, 3155]
    (.letOp (n := 3160) (.exec 0x10be1b (StorePre 0x10be1b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10be1b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10be1b 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3158, 65]
    (.letOp (n := 3161) (.exec 0x10be20 (StorePre 0x10be20 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10be20 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10be20 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3157, 65]
    (.letOp (n := 3162) (.out 0x10be25 (movR64M64Effect 0x10be25 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3163) (.exec 0x10be25 (LoadPre 0x10be25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10be25 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10be25 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3164) (.out 0x10be2a (mulR64Effect 0x10be2a 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[3072, 3162]
    (.letOp (n := 3165) (.out 0x10be2a (mulR64Effect 0x10be2a 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[3072, 3162]
    (.letOp (n := 3166) (.exec 0x10be2a (fun s => s.RIP = 0x10be2a) (mulR64Effect 0x10be2a 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3072, 3162]
    (.letOp (n := 3167) (.out 0x10be2d (movR64R64Effect 0x10be2d 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[3165]
    (.letOp (n := 3168) (.exec 0x10be2d (fun s => s.RIP = 0x10be2d) (movR64R64Effect 0x10be2d 8 2) (Reg.operands [.gpr 2] [])) #v[3165]
    (.letOp (n := 3169) (.out 0x10be30 (movR64R64Effect 0x10be30 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[3164]
    (.letOp (n := 3170) (.exec 0x10be30 (fun s => s.RIP = 0x10be30) (movR64R64Effect 0x10be30 12 0) (Reg.operands [.gpr 0] [])) #v[3164]
    (b_l10a410_74))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_73 : List UInt8 :=
  [0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C, 0x09, 0xE0, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD3, 0x48, 0x03, 0x44, 0x24, 0x50, 0x48, 0x13,
    0x5C, 0x24, 0x38, 0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x49, 0x89, 0xC3, 0x4C, 0x89, 0xD0, 0x48, 0xF7,
    0xE6, 0x48, 0x89, 0x54, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x44, 0x24, 0x18,
    0x49, 0xF7, 0xE0, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC4] ++ bytes_l10a410_74

theorem code_l10a410_73 : ∀ x ∈ codeRange 0x10bdda bytes_l10a410_73, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbdda 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_74

def b_l10a410_72 : Block Op Label signature Reg.count 3082 :=
  .letOp (n := 3082) (.out 0x10bd96 (movR64R64Effect 0x10bd96 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[3080]
    (.letOp (n := 3083) (.exec 0x10bd96 (fun s => s.RIP = 0x10bd96) (movR64R64Effect 0x10bd96 0 13) (Reg.operands [.gpr 13] [])) #v[3080]
    (.letOp (n := 3084) (.out 0x10bd99 (mulR64Effect 0x10bd99 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[2982, 3082]
    (.letOp (n := 3085) (.out 0x10bd99 (mulR64Effect 0x10bd99 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[2982, 3082]
    (.letOp (n := 3086) (.exec 0x10bd99 (fun s => s.RIP = 0x10bd99) (mulR64Effect 0x10bd99 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[2982, 3082]
    (.letOp (n := 3087) (.out 0x10bd9c (movR64R64Effect 0x10bd9c 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[3084]
    (.letOp (n := 3088) (.exec 0x10bd9c (fun s => s.RIP = 0x10bd9c) (movR64R64Effect 0x10bd9c 7 0) (Reg.operands [.gpr 0] [])) #v[3084]
    (.letOp (n := 3089) (.out 0x10bd9f (movR64R64Effect 0x10bd9f 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[3085]
    (.letOp (n := 3090) (.exec 0x10bd9f (fun s => s.RIP = 0x10bd9f) (movR64R64Effect 0x10bd9f 1 2) (Reg.operands [.gpr 2] [])) #v[3085]
    (.letOp (n := 3091) (.out 0x10bda2 (andR32Imm8Effect 0x10bda2 4 12 0xf) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[3057]
    (.letOp (n := 3092) (.exec 0x10bda2 (fun s => s.RIP = 0x10bda2) (andR32Imm8Effect 0x10bda2 4 12 0xf) (Reg.operands [.gpr 12] [])) #v[3057]
    (.letOp (n := 3093) (.out 0x10bda6 (movR64M64Effect 0x10bda6 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 3094) (.exec 0x10bda6 (LoadPre 0x10bda6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10bda6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bda6 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3095) (.out 0x10bdab (mulR64Effect 0x10bdab 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[2993, 3093]
    (.letOp (n := 3096) (.out 0x10bdab (mulR64Effect 0x10bdab 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[2993, 3093]
    (.letOp (n := 3097) (.exec 0x10bdab (fun s => s.RIP = 0x10bdab) (mulR64Effect 0x10bdab 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2993, 3093]
    (.letOp (n := 3098) (.out 0x10bdae (movR64R64Effect 0x10bdae 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[3096]
    (.letOp (n := 3099) (.exec 0x10bdae (fun s => s.RIP = 0x10bdae) (movR64R64Effect 0x10bdae 9 2) (Reg.operands [.gpr 2] [])) #v[3096]
    (.letOp (n := 3100) (.out 0x10bdb1 (movR64R64Effect 0x10bdb1 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[3095]
    (.letOp (n := 3101) (.exec 0x10bdb1 (fun s => s.RIP = 0x10bdb1) (movR64R64Effect 0x10bdb1 3 0) (Reg.operands [.gpr 0] [])) #v[3095]
    (.letOp (n := 3102) (.out 0x10bdb4 (movR64M64Effect 0x10bdb4 10 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 3103) (.exec 0x10bdb4 (LoadPre 0x10bdb4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10bdb4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bdb4 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3104) (.out 0x10bdb9 (movR64R64Effect 0x10bdb9 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[3102]
    (.letOp (n := 3105) (.exec 0x10bdb9 (fun s => s.RIP = 0x10bdb9) (movR64R64Effect 0x10bdb9 0 10) (Reg.operands [.gpr 10] [])) #v[3102]
    (.letOp (n := 3106) (.out 0x10bdbc (mulR64Effect 0x10bdbc 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[3006, 3104]
    (.letOp (n := 3107) (.out 0x10bdbc (mulR64Effect 0x10bdbc 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[3006, 3104]
    (.letOp (n := 3108) (.exec 0x10bdbc (fun s => s.RIP = 0x10bdbc) (mulR64Effect 0x10bdbc 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[3006, 3104]
    (.letOp (n := 3109) (.out 0x10bdbf (addR64R64Effect 0x10bdbf 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[3106, 3100]
    (.letOp (n := 3110) (.out 0x10bdbf (addR64R64Effect 0x10bdbf 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[3106, 3100]
    (.letOp (n := 3111) (.exec 0x10bdbf (fun s => s.RIP = 0x10bdbf) (addR64R64Effect 0x10bdbf 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[3106, 3100]
    (.letOp (n := 3112) (.out 0x10bdc2 (atFlags StatusFlags.CF (adcR64R64Effect 0x10bdc2 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[3098, 3107, 3110]
    (.letOp (n := 3113) (.exec 0x10bdc2 (fun s => s.RIP = 0x10bdc2) (atFlags StatusFlags.CF (adcR64R64Effect 0x10bdc2 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3098, 3107, 3110]
    (.letOp (n := 3114) (.out 0x10bdc5 (addR64R64Effect 0x10bdc5 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[3109, 3087]
    (.letOp (n := 3115) (.out 0x10bdc5 (addR64R64Effect 0x10bdc5 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[3109, 3087]
    (.letOp (n := 3116) (.exec 0x10bdc5 (fun s => s.RIP = 0x10bdc5) (addR64R64Effect 0x10bdc5 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[3109, 3087]
    (.letOp (n := 3117) (.out 0x10bdc8 (atFlags StatusFlags.CF (adcR64R64Effect 0x10bdc8 9 1)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[3112, 3089, 3115]
    (.letOp (n := 3118) (.exec 0x10bdc8 (fun s => s.RIP = 0x10bdc8) (atFlags StatusFlags.CF (adcR64R64Effect 0x10bdc8 9 1)) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3112, 3089, 3115]
    (.letOp (n := 3119) (.out 0x10bdcb (addR64R64Effect 0x10bdcb 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[3114, 3078]
    (.letOp (n := 3120) (.out 0x10bdcb (addR64R64Effect 0x10bdcb 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[3114, 3078]
    (.letOp (n := 3121) (.exec 0x10bdcb (fun s => s.RIP = 0x10bdcb) (addR64R64Effect 0x10bdcb 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[3114, 3078]
    (.letOp (n := 3122) (.out 0x10bdce (atFlags StatusFlags.CF (adcR64M64Effect 0x10bdce 9 (.sib 4 none 0 (.d8 0x28)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[3117, 65, 3120]
    (.letOp (n := 3123) (.exec 0x10bdce (LoadPre 0x10bdce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10bdce + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10bdce 9 (.sib 4 none 0 (.d8 0x28)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3117, 65, 3120]
    (.letOp (n := 3124) (.out 0x10bdd3 (addR64R64Effect 0x10bdd3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[3119, 3053]
    (.letOp (n := 3125) (.out 0x10bdd3 (addR64R64Effect 0x10bdd3 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[3119, 3053]
    (.letOp (n := 3126) (.exec 0x10bdd3 (fun s => s.RIP = 0x10bdd3) (addR64R64Effect 0x10bdd3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[3119, 3053]
    (.letOp (n := 3127) (.out 0x10bdd6 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bdd6 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[3122, 3125]
    (.letOp (n := 3128) (.exec 0x10bdd6 (fun s => s.RIP = 0x10bdd6) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bdd6 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3122, 3125]
    (b_l10a410_73)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_72 : List UInt8 :=
  [0x4C, 0x89, 0xE8, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0xC7, 0x48, 0x89, 0xD1, 0x41, 0x83, 0xE4, 0x0F,
    0x48, 0x8B, 0x44, 0x24, 0x30, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD1, 0x48, 0x89, 0xC3, 0x4C, 0x8B,
    0x54, 0x24, 0x08, 0x4C, 0x89, 0xD0, 0x49, 0xF7, 0xE6, 0x48, 0x01, 0xD8, 0x49, 0x11, 0xD1, 0x48,
    0x01, 0xF8, 0x49, 0x11, 0xC9, 0x48, 0x01, 0xE8, 0x4C, 0x13, 0x4C, 0x24, 0x28, 0x4C, 0x01, 0xD8,
    0x49, 0x83, 0xD1, 0x00] ++ bytes_l10a410_73

theorem code_l10a410_72 : ∀ x ∈ codeRange 0x10bd96 bytes_l10a410_72, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbd96 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_73

def b_l10a410_71 : Block Op Label signature Reg.count 3042 :=
  .letOp (n := 3042) (.out 0x10bd40 (addR64R64Effect 0x10bd40 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[3037, 3019]
    (.letOp (n := 3043) (.out 0x10bd40 (addR64R64Effect 0x10bd40 15 0) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 0] []) (.flag .CF)) #v[3037, 3019]
    (.letOp (n := 3044) (.exec 0x10bd40 (fun s => s.RIP = 0x10bd40) (addR64R64Effect 0x10bd40 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[3037, 3019]
    (.letOp (n := 3045) (.out 0x10bd43 (atFlags StatusFlags.CF (adcR64R64Effect 0x10bd43 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3040, 3020, 3043]
    (.letOp (n := 3046) (.exec 0x10bd43 (fun s => s.RIP = 0x10bd43) (atFlags StatusFlags.CF (adcR64R64Effect 0x10bd43 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3040, 3020, 3043]
    (.letOp (n := 3047) (.out 0x10bd46 (addR64R64Effect 0x10bd46 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[3042, 2963]
    (.letOp (n := 3048) (.out 0x10bd46 (addR64R64Effect 0x10bd46 15 8) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 8] []) (.flag .CF)) #v[3042, 2963]
    (.letOp (n := 3049) (.exec 0x10bd46 (fun s => s.RIP = 0x10bd46) (addR64R64Effect 0x10bd46 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[3042, 2963]
    (.letOp (n := 3050) (.exec 0x10bd49 (StorePre 0x10bd49 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10bd49 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bd49 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[3047, 65]
    (.letOp (n := 3051) (.out 0x10bd4e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bd4e 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3045, 3048]
    (.letOp (n := 3052) (.exec 0x10bd4e (fun s => s.RIP = 0x10bd4e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10bd4e 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3045, 3048]
    (.letOp (n := 3053) (.out 0x10bd52 (shldR64R64Effect 0x10bd52 5 11 15 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[3051, 3047]
    (.letOp (n := 3054) (.exec 0x10bd52 (fun s => s.RIP = 0x10bd52) (shldR64R64Effect 0x10bd52 5 11 15 12) (Reg.operands [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3051, 3047]
    (.letOp (n := 3055) (.out 0x10bd57 (movR64R64Effect 0x10bd57 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15] []) (.reg (.gpr 12))) #v[3047]
    (.letOp (n := 3056) (.exec 0x10bd57 (fun s => s.RIP = 0x10bd57) (movR64R64Effect 0x10bd57 12 15) (Reg.operands [.gpr 15] [])) #v[3047]
    (.letOp (n := 3057) (.out 0x10bd5a (shrR64Effect 0x10bd5a 4 12 48) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[3055]
    (.letOp (n := 3058) (.exec 0x10bd5a (fun s => s.RIP = 0x10bd5a) (shrR64Effect 0x10bd5a 4 12 48) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3055]
    (.letOp (n := 3059) (.out 0x10bd5e (movR64R64Effect 0x10bd5e 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[3002]
    (.letOp (n := 3060) (.exec 0x10bd5e (fun s => s.RIP = 0x10bd5e) (movR64R64Effect 0x10bd5e 0 1) (Reg.operands [.gpr 1] [])) #v[3002]
    (.letOp (n := 3061) (.out 0x10bd61 (movR64M64Effect 0x10bd61 6 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 3062) (.exec 0x10bd61 (LoadPre 0x10bd61 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10bd61 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bd61 6 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3063) (.out 0x10bd69 (mulR64Effect 0x10bd69 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[3061, 3059]
    (.letOp (n := 3064) (.out 0x10bd69 (mulR64Effect 0x10bd69 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[3061, 3059]
    (.letOp (n := 3065) (.exec 0x10bd69 (fun s => s.RIP = 0x10bd69) (mulR64Effect 0x10bd69 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3061, 3059]
    (.letOp (n := 3066) (.exec 0x10bd6c (StorePre 0x10bd6c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10bd6c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bd6c 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3064, 65]
    (.letOp (n := 3067) (.exec 0x10bd71 (StorePre 0x10bd71 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10bd71 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bd71 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3063, 65]
    (.letOp (n := 3068) (.out 0x10bd76 (movR64M64Effect 0x10bd76 15 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 3069) (.exec 0x10bd76 (LoadPre 0x10bd76 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10bd76 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bd76 15 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3070) (.out 0x10bd7b (movR64R64Effect 0x10bd7b 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[3068]
    (.letOp (n := 3071) (.exec 0x10bd7b (fun s => s.RIP = 0x10bd7b) (movR64R64Effect 0x10bd7b 0 15) (Reg.operands [.gpr 15] [])) #v[3068]
    (.letOp (n := 3072) (.out 0x10bd7e (movR64M64Effect 0x10bd7e 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 3073) (.exec 0x10bd7e (LoadPre 0x10bd7e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10bd7e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bd7e 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3074) (.out 0x10bd86 (mulR64Effect 0x10bd86 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[3072, 3070]
    (.letOp (n := 3075) (.out 0x10bd86 (mulR64Effect 0x10bd86 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[3072, 3070]
    (.letOp (n := 3076) (.exec 0x10bd86 (fun s => s.RIP = 0x10bd86) (mulR64Effect 0x10bd86 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3072, 3070]
    (.letOp (n := 3077) (.exec 0x10bd89 (StorePre 0x10bd89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10bd89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bd89 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3075, 65]
    (.letOp (n := 3078) (.out 0x10bd8e (movR64R64Effect 0x10bd8e 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[3074]
    (.letOp (n := 3079) (.exec 0x10bd8e (fun s => s.RIP = 0x10bd8e) (movR64R64Effect 0x10bd8e 5 0) (Reg.operands [.gpr 0] [])) #v[3074]
    (.letOp (n := 3080) (.out 0x10bd91 (movR64M64Effect 0x10bd91 13 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 3081) (.exec 0x10bd91 (LoadPre 0x10bd91 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10bd91 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bd91 13 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_72))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_71 : List UInt8 :=
  [0x49, 0x01, 0xC7, 0x49, 0x11, 0xD3, 0x4D, 0x01, 0xC7, 0x4C, 0x89, 0x7C, 0x24, 0x10, 0x49, 0x83,
    0xD3, 0x00, 0x4D, 0x0F, 0xA4, 0xFB, 0x0C, 0x4D, 0x89, 0xFC, 0x49, 0xC1, 0xEC, 0x30, 0x48, 0x89,
    0xC8, 0x48, 0x8B, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE6, 0x48, 0x89, 0x54, 0x24,
    0x38, 0x48, 0x89, 0x44, 0x24, 0x50, 0x4C, 0x8B, 0x7C, 0x24, 0x48, 0x4C, 0x89, 0xF8, 0x4C, 0x8B,
    0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0x54, 0x24, 0x28, 0x48, 0x89,
    0xC5, 0x4C, 0x8B, 0x6C, 0x24, 0x58] ++ bytes_l10a410_72

theorem code_l10a410_71 : ∀ x ∈ codeRange 0x10bd40 bytes_l10a410_71, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbd40 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_72

def b_l10a410_70 : Block Op Label signature Reg.count 2995 :=
  .letOp (n := 2995) (.out 0x10bcf3 (mulR64Effect 0x10bcf3 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[2993, 2991]
    (.letOp (n := 2996) (.out 0x10bcf3 (mulR64Effect 0x10bcf3 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[2993, 2991]
    (.letOp (n := 2997) (.exec 0x10bcf3 (fun s => s.RIP = 0x10bcf3) (mulR64Effect 0x10bcf3 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2993, 2991]
    (.letOp (n := 2998) (.out 0x10bcf6 (movR64R64Effect 0x10bcf6 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2996]
    (.letOp (n := 2999) (.exec 0x10bcf6 (fun s => s.RIP = 0x10bcf6) (movR64R64Effect 0x10bcf6 6 2) (Reg.operands [.gpr 2] [])) #v[2996]
    (.letOp (n := 3000) (.out 0x10bcf9 (movR64R64Effect 0x10bcf9 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[2995]
    (.letOp (n := 3001) (.exec 0x10bcf9 (fun s => s.RIP = 0x10bcf9) (movR64R64Effect 0x10bcf9 12 0) (Reg.operands [.gpr 0] [])) #v[2995]
    (.letOp (n := 3002) (.out 0x10bcfc (movR64M64Effect 0x10bcfc 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 3003) (.exec 0x10bcfc (LoadPre 0x10bcfc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10bcfc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bcfc 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3004) (.out 0x10bd01 (movR64R64Effect 0x10bd01 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[3002]
    (.letOp (n := 3005) (.exec 0x10bd01 (fun s => s.RIP = 0x10bd01) (movR64R64Effect 0x10bd01 0 1) (Reg.operands [.gpr 1] [])) #v[3002]
    (.letOp (n := 3006) (.out 0x10bd04 (movR64M64Effect 0x10bd04 14 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 3007) (.exec 0x10bd04 (LoadPre 0x10bd04 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10bd04 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bd04 14 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 3008) (.out 0x10bd09 (mulR64Effect 0x10bd09 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[3006, 3004]
    (.letOp (n := 3009) (.out 0x10bd09 (mulR64Effect 0x10bd09 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[3006, 3004]
    (.letOp (n := 3010) (.exec 0x10bd09 (fun s => s.RIP = 0x10bd09) (mulR64Effect 0x10bd09 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[3006, 3004]
    (.letOp (n := 3011) (.out 0x10bd0c (movR64R64Effect 0x10bd0c 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[3009]
    (.letOp (n := 3012) (.exec 0x10bd0c (fun s => s.RIP = 0x10bd0c) (movR64R64Effect 0x10bd0c 11 2) (Reg.operands [.gpr 2] [])) #v[3009]
    (.letOp (n := 3013) (.out 0x10bd0f (movR64R64Effect 0x10bd0f 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[3008]
    (.letOp (n := 3014) (.exec 0x10bd0f (fun s => s.RIP = 0x10bd0f) (movR64R64Effect 0x10bd0f 15 0) (Reg.operands [.gpr 0] [])) #v[3008]
    (.letOp (n := 3015) (.out 0x10bd12 (movR64R64Effect 0x10bd12 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[2961]
    (.letOp (n := 3016) (.exec 0x10bd12 (fun s => s.RIP = 0x10bd12) (movR64R64Effect 0x10bd12 0 5) (Reg.operands [.gpr 5] [])) #v[2961]
    (.letOp (n := 3017) (.out 0x10bd15 (movR64Imm64Effect 0x10bd15 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 3018) (.exec 0x10bd15 (fun s => s.RIP = 0x10bd15) (movR64Imm64Effect 0x10bd15 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 3019) (.out 0x10bd1f (mulR64Effect 0x10bd1f 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[3017, 3015]
    (.letOp (n := 3020) (.out 0x10bd1f (mulR64Effect 0x10bd1f 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3017, 3015]
    (.letOp (n := 3021) (.exec 0x10bd1f (fun s => s.RIP = 0x10bd1f) (mulR64Effect 0x10bd1f 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3017, 3015]
    (.letOp (n := 3022) (.out 0x10bd22 (addR64R64Effect 0x10bd22 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[3013, 3000]
    (.letOp (n := 3023) (.out 0x10bd22 (addR64R64Effect 0x10bd22 15 12) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 12] []) (.flag .CF)) #v[3013, 3000]
    (.letOp (n := 3024) (.exec 0x10bd22 (fun s => s.RIP = 0x10bd22) (addR64R64Effect 0x10bd22 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[3013, 3000]
    (.letOp (n := 3025) (.out 0x10bd25 (atFlags StatusFlags.CF (adcR64R64Effect 0x10bd25 11 6)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3011, 2998, 3023]
    (.letOp (n := 3026) (.exec 0x10bd25 (fun s => s.RIP = 0x10bd25) (atFlags StatusFlags.CF (adcR64R64Effect 0x10bd25 11 6)) (Reg.operands [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3011, 2998, 3023]
    (.letOp (n := 3027) (.out 0x10bd28 (addR64R64Effect 0x10bd28 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[3022, 2989]
    (.letOp (n := 3028) (.out 0x10bd28 (addR64R64Effect 0x10bd28 15 7) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 7] []) (.flag .CF)) #v[3022, 2989]
    (.letOp (n := 3029) (.exec 0x10bd28 (fun s => s.RIP = 0x10bd28) (addR64R64Effect 0x10bd28 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[3022, 2989]
    (.letOp (n := 3030) (.out 0x10bd2b (atFlags StatusFlags.CF (adcR64R64Effect 0x10bd2b 11 9)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3025, 2987, 3028]
    (.letOp (n := 3031) (.exec 0x10bd2b (fun s => s.RIP = 0x10bd2b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10bd2b 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3025, 2987, 3028]
    (.letOp (n := 3032) (.out 0x10bd2e (addR64R64Effect 0x10bd2e 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[3027, 2978]
    (.letOp (n := 3033) (.out 0x10bd2e (addR64R64Effect 0x10bd2e 15 13) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 13] []) (.flag .CF)) #v[3027, 2978]
    (.letOp (n := 3034) (.exec 0x10bd2e (fun s => s.RIP = 0x10bd2e) (addR64R64Effect 0x10bd2e 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[3027, 2978]
    (.letOp (n := 3035) (.out 0x10bd31 (atFlags StatusFlags.CF (adcR64M64Effect 0x10bd31 11 (.sib 4 none 0 (.d8 0x50)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[3030, 65, 3033]
    (.letOp (n := 3036) (.exec 0x10bd31 (LoadPre 0x10bd31 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10bd31 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10bd31 11 (.sib 4 none 0 (.d8 0x50)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3030, 65, 3033]
    (.letOp (n := 3037) (.out 0x10bd36 (addR64M64Effect 0x10bd36 15 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[3032, 65]
    (.letOp (n := 3038) (.out 0x10bd36 (addR64M64Effect 0x10bd36 15 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[3032, 65]
    (.letOp (n := 3039) (.exec 0x10bd36 (LoadPre 0x10bd36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10bd36 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10bd36 15 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[3032, 65]
    (.letOp (n := 3040) (.out 0x10bd3b (atFlags StatusFlags.CF (adcR64M64Effect 0x10bd3b 11 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[3035, 65, 3038]
    (.letOp (n := 3041) (.exec 0x10bd3b (LoadPre 0x10bd3b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10bd3b + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10bd3b 11 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3035, 65, 3038]
    (b_l10a410_71)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_70 : List UInt8 :=
  [0x49, 0xF7, 0xE2, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x48, 0x89,
    0xC8, 0x4C, 0x8B, 0x74, 0x24, 0x70, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD3, 0x49, 0x89, 0xC7, 0x48,
    0x89, 0xE8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4D,
    0x01, 0xE7, 0x49, 0x11, 0xF3, 0x49, 0x01, 0xFF, 0x4D, 0x11, 0xCB, 0x4D, 0x01, 0xEF, 0x4C, 0x13,
    0x5C, 0x24, 0x50, 0x4C, 0x03, 0x7C, 0x24, 0x38, 0x4C, 0x13, 0x5C, 0x24, 0x10] ++ bytes_l10a410_71

theorem code_l10a410_70 : ∀ x ∈ codeRange 0x10bcf3 bytes_l10a410_70, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbcf3 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_71

def b_l10a410_69 : Block Op Label signature Reg.count 2955 :=
  .letOp (n := 2955) (.out 0x10bc9e (addR64R64Effect 0x10bc9e 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[2950, 2934]
    (.letOp (n := 2956) (.out 0x10bc9e (addR64R64Effect 0x10bc9e 13 0) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 0] []) (.flag .CF)) #v[2950, 2934]
    (.letOp (n := 2957) (.exec 0x10bc9e (fun s => s.RIP = 0x10bc9e) (addR64R64Effect 0x10bc9e 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2950, 2934]
    (.letOp (n := 2958) (.exec 0x10bca1 (StorePre 0x10bca1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10bca1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10bca1 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 13, .gpr 4] [])) #v[2955, 65]
    (.letOp (n := 2959) (.out 0x10bca5 (atFlags StatusFlags.CF (adcR64R64Effect 0x10bca5 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2953, 2935, 2956]
    (.letOp (n := 2960) (.exec 0x10bca5 (fun s => s.RIP = 0x10bca5) (atFlags StatusFlags.CF (adcR64R64Effect 0x10bca5 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2953, 2935, 2956]
    (.letOp (n := 2961) (.out 0x10bca8 (shldR64R64Effect 0x10bca8 5 5 14 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[2925, 2923]
    (.letOp (n := 2962) (.exec 0x10bca8 (fun s => s.RIP = 0x10bca8) (shldR64R64Effect 0x10bca8 5 5 14 12) (Reg.operands [.gpr 5, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2925, 2923]
    (.letOp (n := 2963) (.out 0x10bcad (shldR64R64Effect 0x10bcad 5 8 13 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2959, 2955]
    (.letOp (n := 2964) (.exec 0x10bcad (fun s => s.RIP = 0x10bcad) (shldR64R64Effect 0x10bcad 5 8 13 12) (Reg.operands [.gpr 8, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2959, 2955]
    (.letOp (n := 2965) (.out 0x10bcb2 (movR64R64Effect 0x10bcb2 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2863]
    (.letOp (n := 2966) (.exec 0x10bcb2 (fun s => s.RIP = 0x10bcb2) (movR64R64Effect 0x10bcb2 0 9) (Reg.operands [.gpr 9] [])) #v[2863]
    (.letOp (n := 2967) (.out 0x10bcb5 (mulR64Effect 0x10bcb5 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[2881, 2965]
    (.letOp (n := 2968) (.out 0x10bcb5 (mulR64Effect 0x10bcb5 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[2881, 2965]
    (.letOp (n := 2969) (.exec 0x10bcb5 (fun s => s.RIP = 0x10bcb5) (mulR64Effect 0x10bcb5 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[2881, 2965]
    (.letOp (n := 2970) (.exec 0x10bcb8 (StorePre 0x10bcb8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10bcb8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bcb8 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2968, 65]
    (.letOp (n := 2971) (.exec 0x10bcbd (StorePre 0x10bcbd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10bcbd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bcbd 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2967, 65]
    (.letOp (n := 2972) (.out 0x10bcc2 (movR64R64Effect 0x10bcc2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[2875]
    (.letOp (n := 2973) (.exec 0x10bcc2 (fun s => s.RIP = 0x10bcc2) (movR64R64Effect 0x10bcc2 0 3) (Reg.operands [.gpr 3] [])) #v[2875]
    (.letOp (n := 2974) (.out 0x10bcc5 (mulR64Effect 0x10bcc5 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[2825, 2972]
    (.letOp (n := 2975) (.out 0x10bcc5 (mulR64Effect 0x10bcc5 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[2825, 2972]
    (.letOp (n := 2976) (.exec 0x10bcc5 (fun s => s.RIP = 0x10bcc5) (mulR64Effect 0x10bcc5 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2825, 2972]
    (.letOp (n := 2977) (.exec 0x10bcc8 (StorePre 0x10bcc8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10bcc8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bcc8 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2975, 65]
    (.letOp (n := 2978) (.out 0x10bccd (movR64R64Effect 0x10bccd 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[2974]
    (.letOp (n := 2979) (.exec 0x10bccd (fun s => s.RIP = 0x10bccd) (movR64R64Effect 0x10bccd 13 0) (Reg.operands [.gpr 0] [])) #v[2974]
    (.letOp (n := 2980) (.out 0x10bcd0 (movR64M64Effect 0x10bcd0 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2981) (.exec 0x10bcd0 (LoadPre 0x10bcd0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10bcd0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bcd0 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2982) (.out 0x10bcd5 (movR64M64Effect 0x10bcd5 3 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 2983) (.exec 0x10bcd5 (LoadPre 0x10bcd5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10bcd5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bcd5 3 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2984) (.out 0x10bcdd (mulR64Effect 0x10bcdd 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[2982, 2980]
    (.letOp (n := 2985) (.out 0x10bcdd (mulR64Effect 0x10bcdd 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[2982, 2980]
    (.letOp (n := 2986) (.exec 0x10bcdd (fun s => s.RIP = 0x10bcdd) (mulR64Effect 0x10bcdd 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[2982, 2980]
    (.letOp (n := 2987) (.out 0x10bce0 (movR64R64Effect 0x10bce0 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2985]
    (.letOp (n := 2988) (.exec 0x10bce0 (fun s => s.RIP = 0x10bce0) (movR64R64Effect 0x10bce0 9 2) (Reg.operands [.gpr 2] [])) #v[2985]
    (.letOp (n := 2989) (.out 0x10bce3 (movR64R64Effect 0x10bce3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[2984]
    (.letOp (n := 2990) (.exec 0x10bce3 (fun s => s.RIP = 0x10bce3) (movR64R64Effect 0x10bce3 7 0) (Reg.operands [.gpr 0] [])) #v[2984]
    (.letOp (n := 2991) (.out 0x10bce6 (movR64M64Effect 0x10bce6 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2992) (.exec 0x10bce6 (LoadPre 0x10bce6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10bce6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bce6 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2993) (.out 0x10bceb (movR64M64Effect 0x10bceb 10 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 2994) (.exec 0x10bceb (LoadPre 0x10bceb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10bceb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bceb 10 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_70))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_69 : List UInt8 :=
  [0x49, 0x01, 0xC5, 0x4C, 0x89, 0x2C, 0x24, 0x49, 0x11, 0xD0, 0x4C, 0x0F, 0xA4, 0xF5, 0x0C, 0x4D,
    0x0F, 0xA4, 0xE8, 0x0C, 0x4C, 0x89, 0xC8, 0x49, 0xF7, 0xE3, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48,
    0x89, 0x44, 0x24, 0x38, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0x54, 0x24, 0x50, 0x49,
    0x89, 0xC5, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x8B, 0x9C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE3, 0x49, 0x89, 0xD1, 0x48, 0x89, 0xC7, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x4C, 0x8B, 0x94,
    0x24, 0xC0, 0x00, 0x00, 0x00] ++ bytes_l10a410_70

theorem code_l10a410_69 : ∀ x ∈ codeRange 0x10bc9e bytes_l10a410_69, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbc9e 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_70

def b_l10a410_68 : Block Op Label signature Reg.count 2913 :=
  .letOp (n := 2913) (.out 0x10bc40 (movR64R64Effect 0x10bc40 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2911]
    (.letOp (n := 2914) (.exec 0x10bc40 (fun s => s.RIP = 0x10bc40) (movR64R64Effect 0x10bc40 8 2) (Reg.operands [.gpr 2] [])) #v[2911]
    (.letOp (n := 2915) (.out 0x10bc43 (movR64R64Effect 0x10bc43 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[2910]
    (.letOp (n := 2916) (.exec 0x10bc43 (fun s => s.RIP = 0x10bc43) (movR64R64Effect 0x10bc43 13 0) (Reg.operands [.gpr 0] [])) #v[2910]
    (.letOp (n := 2917) (.out 0x10bc46 (movR64R64Effect 0x10bc46 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2863]
    (.letOp (n := 2918) (.exec 0x10bc46 (fun s => s.RIP = 0x10bc46) (movR64R64Effect 0x10bc46 0 9) (Reg.operands [.gpr 9] [])) #v[2863]
    (.letOp (n := 2919) (.exec 0x10bc49 (StorePre 0x10bc49 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10bc49 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bc49 9 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[2863, 65]
    (.letOp (n := 2920) (.out 0x10bc4e (mulR64Effect 0x10bc4e 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[2839, 2917]
    (.letOp (n := 2921) (.out 0x10bc4e (mulR64Effect 0x10bc4e 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[2839, 2917]
    (.letOp (n := 2922) (.exec 0x10bc4e (fun s => s.RIP = 0x10bc4e) (mulR64Effect 0x10bc4e 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[2839, 2917]
    (.letOp (n := 2923) (.out 0x10bc51 (movR64R64Effect 0x10bc51 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[2920]
    (.letOp (n := 2924) (.exec 0x10bc51 (fun s => s.RIP = 0x10bc51) (movR64R64Effect 0x10bc51 14 0) (Reg.operands [.gpr 0] [])) #v[2920]
    (.letOp (n := 2925) (.out 0x10bc54 (movR64R64Effect 0x10bc54 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2921]
    (.letOp (n := 2926) (.exec 0x10bc54 (fun s => s.RIP = 0x10bc54) (movR64R64Effect 0x10bc54 5 2) (Reg.operands [.gpr 2] [])) #v[2921]
    (.letOp (n := 2927) (.exec 0x10bc57 (StorePre 0x10bc57 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10bc57 + BitVec.ofNat 64 5)) 8) (addMREffect 0x10bc57 5 64 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2897, 65]
    (.letOp (n := 2928) (.out 0x10bc5c (movR64Imm64Effect 0x10bc5c 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2929) (.exec 0x10bc5c (fun s => s.RIP = 0x10bc5c) (movR64Imm64Effect 0x10bc5c 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2930) (.out 0x10bc66 (andR64R64Effect 0x10bc66 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2920, 2928]
    (.letOp (n := 2931) (.exec 0x10bc66 (fun s => s.RIP = 0x10bc66) (andR64R64Effect 0x10bc66 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2920, 2928]
    (.letOp (n := 2932) (.out 0x10bc69 (movR64Imm64Effect 0x10bc69 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2933) (.exec 0x10bc69 (fun s => s.RIP = 0x10bc69) (movR64Imm64Effect 0x10bc69 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2934) (.out 0x10bc73 (mulR64Effect 0x10bc73 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2932, 2930]
    (.letOp (n := 2935) (.out 0x10bc73 (mulR64Effect 0x10bc73 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2932, 2930]
    (.letOp (n := 2936) (.exec 0x10bc73 (fun s => s.RIP = 0x10bc73) (mulR64Effect 0x10bc73 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2932, 2930]
    (.letOp (n := 2937) (.out 0x10bc76 (movR64Imm64Effect 0x10bc76 15 0x5fffffffffffa) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 2938) (.exec 0x10bc76 (fun s => s.RIP = 0x10bc76) (movR64Imm64Effect 0x10bc76 15 0x5fffffffffffa) (Reg.operands [] [])) #v[]
    (.letOp (n := 2939) (.exec 0x10bc80 (StorePre 0x10bc80 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10bc80 + BitVec.ofNat 64 5)) 8) (addMREffect 0x10bc80 5 64 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[2937, 65]
    (.letOp (n := 2940) (.out 0x10bc85 (addR64R64Effect 0x10bc85 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 7] []) (.reg (.gpr 13))) #v[2915, 2906]
    (.letOp (n := 2941) (.out 0x10bc85 (addR64R64Effect 0x10bc85 13 7) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 7] []) (.flag .CF)) #v[2915, 2906]
    (.letOp (n := 2942) (.exec 0x10bc85 (fun s => s.RIP = 0x10bc85) (addR64R64Effect 0x10bc85 13 7) (Reg.operands [.gpr 13, .gpr 7] [])) #v[2915, 2906]
    (.letOp (n := 2943) (.out 0x10bc88 (atFlags StatusFlags.CF (adcR64R64Effect 0x10bc88 8 6)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2913, 2904, 2941]
    (.letOp (n := 2944) (.exec 0x10bc88 (fun s => s.RIP = 0x10bc88) (atFlags StatusFlags.CF (adcR64R64Effect 0x10bc88 8 6)) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2913, 2904, 2941]
    (.letOp (n := 2945) (.out 0x10bc8b (addR64M64Effect 0x10bc8b 13 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[2940, 65]
    (.letOp (n := 2946) (.out 0x10bc8b (addR64M64Effect 0x10bc8b 13 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[2940, 65]
    (.letOp (n := 2947) (.exec 0x10bc8b (LoadPre 0x10bc8b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10bc8b + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10bc8b 13 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[2940, 65]
    (.letOp (n := 2948) (.out 0x10bc90 (atFlags StatusFlags.CF (adcR64M64Effect 0x10bc90 8 (.sib 4 none 0 (.d8 0x38)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[2943, 65, 2946]
    (.letOp (n := 2949) (.exec 0x10bc90 (LoadPre 0x10bc90 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10bc90 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10bc90 8 (.sib 4 none 0 (.d8 0x38)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2943, 65, 2946]
    (.letOp (n := 2950) (.out 0x10bc95 (addR64M64Effect 0x10bc95 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[2945, 65]
    (.letOp (n := 2951) (.out 0x10bc95 (addR64M64Effect 0x10bc95 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[2945, 65]
    (.letOp (n := 2952) (.exec 0x10bc95 (LoadPre 0x10bc95 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10bc95 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10bc95 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[2945, 65]
    (.letOp (n := 2953) (.out 0x10bc9a (atFlags StatusFlags.CF (adcR64M64Effect 0x10bc9a 8 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[2948, 65, 2951]
    (.letOp (n := 2954) (.exec 0x10bc9a (LoadPre 0x10bc9a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10bc9a + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10bc9a 8 (.sib 4 none 0 .none))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2948, 65, 2951]
    (b_l10a410_69))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_68 : List UInt8 :=
  [0x49, 0x89, 0xD0, 0x49, 0x89, 0xC5, 0x4C, 0x89, 0xC8, 0x4C, 0x89, 0x4C, 0x24, 0x48, 0x49, 0xF7,
    0xE4, 0x49, 0x89, 0xC6, 0x48, 0x89, 0xD5, 0x48, 0x01, 0x4C, 0x24, 0x20, 0x48, 0xB9, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0xBF, 0xFA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x05, 0x00,
    0x4C, 0x01, 0x7C, 0x24, 0x40, 0x49, 0x01, 0xFD, 0x49, 0x11, 0xF0, 0x4C, 0x03, 0x6C, 0x24, 0x50,
    0x4C, 0x13, 0x44, 0x24, 0x38, 0x4C, 0x03, 0x6C, 0x24, 0x10, 0x4C, 0x13, 0x04, 0x24] ++ bytes_l10a410_69

theorem code_l10a410_68 : ∀ x ∈ codeRange 0x10bc40 bytes_l10a410_68, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbc40 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_69

def b_l10a410_67 : Block Op Label signature Reg.count 2877 :=
  .letOp (n := 2877) (.exec 0x10bbec (StorePre 0x10bbec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10bbec + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bbec 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2859, 65]
    (.letOp (n := 2878) (.out 0x10bbf1 (mulR64Effect 0x10bbf1 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2821, 2859]
    (.letOp (n := 2879) (.out 0x10bbf1 (mulR64Effect 0x10bbf1 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2821, 2859]
    (.letOp (n := 2880) (.exec 0x10bbf1 (fun s => s.RIP = 0x10bbf1) (mulR64Effect 0x10bbf1 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2821, 2859]
    (.letOp (n := 2881) (.out 0x10bbf4 (movR64R64Effect 0x10bbf4 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[2821]
    (.letOp (n := 2882) (.exec 0x10bbf4 (fun s => s.RIP = 0x10bbf4) (movR64R64Effect 0x10bbf4 11 1) (Reg.operands [.gpr 1] [])) #v[2821]
    (.letOp (n := 2883) (.exec 0x10bbf7 (StorePre 0x10bbf7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10bbf7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10bbf7 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2821, 65]
    (.letOp (n := 2884) (.exec 0x10bbff (StorePre 0x10bbff 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10bbff + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10bbff 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2879, 65]
    (.letOp (n := 2885) (.exec 0x10bc03 (StorePre 0x10bc03 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10bc03 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bc03 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2878, 65]
    (.letOp (n := 2886) (.out 0x10bc08 (movR64R64Effect 0x10bc08 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[2854]
    (.letOp (n := 2887) (.exec 0x10bc08 (fun s => s.RIP = 0x10bc08) (movR64R64Effect 0x10bc08 0 7) (Reg.operands [.gpr 7] [])) #v[2854]
    (.letOp (n := 2888) (.out 0x10bc0b (mulR64Effect 0x10bc0b 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[2825, 2886]
    (.letOp (n := 2889) (.out 0x10bc0b (mulR64Effect 0x10bc0b 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[2825, 2886]
    (.letOp (n := 2890) (.exec 0x10bc0b (fun s => s.RIP = 0x10bc0b) (mulR64Effect 0x10bc0b 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2825, 2886]
    (.letOp (n := 2891) (.exec 0x10bc0e (StorePre 0x10bc0e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10bc0e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10bc0e 10 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[2825, 65]
    (.letOp (n := 2892) (.exec 0x10bc16 (StorePre 0x10bc16 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10bc16 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bc16 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2888, 65]
    (.letOp (n := 2893) (.exec 0x10bc1b (StorePre 0x10bc1b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10bc1b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bc1b 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2889, 65]
    (.letOp (n := 2894) (.out 0x10bc20 (addR64R64Effect 0x10bc20 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[2797, 2870]
    (.letOp (n := 2895) (.exec 0x10bc20 (fun s => s.RIP = 0x10bc20) (addR64R64Effect 0x10bc20 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[2797, 2870]
    (.letOp (n := 2896) (.exec 0x10bc23 (StorePre 0x10bc23 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10bc23 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10bc23 5 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[2894, 65]
    (.letOp (n := 2897) (.out 0x10bc2b (movR64R64Effect 0x10bc2b 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[2870]
    (.letOp (n := 2898) (.exec 0x10bc2b (fun s => s.RIP = 0x10bc2b) (movR64R64Effect 0x10bc2b 1 13) (Reg.operands [.gpr 13] [])) #v[2870]
    (.letOp (n := 2899) (.out 0x10bc2e (movR64R64Effect 0x10bc2e 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2849]
    (.letOp (n := 2900) (.exec 0x10bc2e (fun s => s.RIP = 0x10bc2e) (movR64R64Effect 0x10bc2e 0 6) (Reg.operands [.gpr 6] [])) #v[2849]
    (.letOp (n := 2901) (.out 0x10bc31 (mulR64Effect 0x10bc31 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[2829, 2899]
    (.letOp (n := 2902) (.out 0x10bc31 (mulR64Effect 0x10bc31 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[2829, 2899]
    (.letOp (n := 2903) (.exec 0x10bc31 (fun s => s.RIP = 0x10bc31) (mulR64Effect 0x10bc31 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[2829, 2899]
    (.letOp (n := 2904) (.out 0x10bc34 (movR64R64Effect 0x10bc34 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2902]
    (.letOp (n := 2905) (.exec 0x10bc34 (fun s => s.RIP = 0x10bc34) (movR64R64Effect 0x10bc34 6 2) (Reg.operands [.gpr 2] [])) #v[2902]
    (.letOp (n := 2906) (.out 0x10bc37 (movR64R64Effect 0x10bc37 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[2901]
    (.letOp (n := 2907) (.exec 0x10bc37 (fun s => s.RIP = 0x10bc37) (movR64R64Effect 0x10bc37 7 0) (Reg.operands [.gpr 0] [])) #v[2901]
    (.letOp (n := 2908) (.out 0x10bc3a (movR64R64Effect 0x10bc3a 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2844]
    (.letOp (n := 2909) (.exec 0x10bc3a (fun s => s.RIP = 0x10bc3a) (movR64R64Effect 0x10bc3a 0 8) (Reg.operands [.gpr 8] [])) #v[2844]
    (.letOp (n := 2910) (.out 0x10bc3d (mulR64Effect 0x10bc3d 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[2834, 2908]
    (.letOp (n := 2911) (.out 0x10bc3d (mulR64Effect 0x10bc3d 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[2834, 2908]
    (.letOp (n := 2912) (.exec 0x10bc3d (fun s => s.RIP = 0x10bc3d) (mulR64Effect 0x10bc3d 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[2834, 2908]
    (b_l10a410_68))))))))))))))))))))))))))))))))))))

def bytes_l10a410_67 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x58, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xCB, 0x48, 0x89, 0x8C, 0x24, 0xD0,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x14, 0x24, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x89, 0xF8, 0x49,
    0xF7, 0xE2, 0x4C, 0x89, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x50, 0x48,
    0x89, 0x54, 0x24, 0x38, 0x4C, 0x01, 0xED, 0x48, 0x89, 0xAC, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x4C,
    0x89, 0xE9, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0xD6, 0x48, 0x89, 0xC7, 0x4C, 0x89,
    0xC0, 0x49, 0xF7, 0xE7] ++ bytes_l10a410_68

theorem code_l10a410_67 : ∀ x ∈ codeRange 0x10bbec bytes_l10a410_67, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbbec 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_68

def b_l10a410_66 : Block Op Label signature Reg.count 2842 :=
  .letOp (n := 2842) (.out 0x10bb72 (movR64M64Effect 0x10bb72 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 2843) (.exec 0x10bb72 (LoadPre 0x10bb72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10bb72 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bb72 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2844) (.out 0x10bb77 (addR64M64Effect 0x10bb77 8 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[2842, 65]
    (.letOp (n := 2845) (.exec 0x10bb77 (LoadPre 0x10bb77 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10bb77 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10bb77 8 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[2842, 65]
    (.letOp (n := 2846) (.exec 0x10bb7f (StorePre 0x10bb7f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10bb7f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bb7f 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[2844, 65]
    (.letOp (n := 2847) (.out 0x10bb84 (movR64M64Effect 0x10bb84 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 2848) (.exec 0x10bb84 (LoadPre 0x10bb84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10bb84 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bb84 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2849) (.out 0x10bb89 (addR64M64Effect 0x10bb89 6 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[2847, 65]
    (.letOp (n := 2850) (.exec 0x10bb89 (LoadPre 0x10bb89 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x10bb89 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10bb89 6 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[2847, 65]
    (.letOp (n := 2851) (.exec 0x10bb91 (StorePre 0x10bb91 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10bb91 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bb91 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[2849, 65]
    (.letOp (n := 2852) (.out 0x10bb96 (movR64M64Effect 0x10bb96 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 2853) (.exec 0x10bb96 (LoadPre 0x10bb96 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10bb96 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bb96 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2854) (.out 0x10bb9b (addR64M64Effect 0x10bb9b 7 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[2852, 65]
    (.letOp (n := 2855) (.exec 0x10bb9b (LoadPre 0x10bb9b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10bb9b + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10bb9b 7 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[2852, 65]
    (.letOp (n := 2856) (.exec 0x10bba3 (StorePre 0x10bba3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10bba3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bba3 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[2854, 65]
    (.letOp (n := 2857) (.out 0x10bba8 (movR64M64Effect 0x10bba8 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2858) (.exec 0x10bba8 (LoadPre 0x10bba8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10bba8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bba8 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2859) (.out 0x10bbad (addR64M64Effect 0x10bbad 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2857, 65]
    (.letOp (n := 2860) (.exec 0x10bbad (LoadPre 0x10bbad (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10bbad + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10bbad 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2857, 65]
    (.letOp (n := 2861) (.out 0x10bbb5 (movR64M64Effect 0x10bbb5 9 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 2862) (.exec 0x10bbb5 (LoadPre 0x10bbb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10bbb5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bbb5 9 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2863) (.out 0x10bbba (addR64M64Effect 0x10bbba 9 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[2861, 65]
    (.letOp (n := 2864) (.exec 0x10bbba (LoadPre 0x10bbba (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10bbba + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10bbba 9 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[2861, 65]
    (.letOp (n := 2865) (.out 0x10bbc2 (movR64Imm64Effect 0x10bbc2 2 0x5ffff9ffffe91a) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2866) (.exec 0x10bbc2 (fun s => s.RIP = 0x10bbc2) (movR64Imm64Effect 0x10bbc2 2 0x5ffff9ffffe91a) (Reg.operands [] [])) #v[]
    (.letOp (n := 2867) (.out 0x10bbcc (addR64R64Effect 0x10bbcc 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[2777, 2865]
    (.letOp (n := 2868) (.exec 0x10bbcc (fun s => s.RIP = 0x10bbcc) (addR64R64Effect 0x10bbcc 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[2777, 2865]
    (.letOp (n := 2869) (.exec 0x10bbcf (StorePre 0x10bbcf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10bbcf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10bbcf 11 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[2867, 65]
    (.letOp (n := 2870) (.out 0x10bbd7 (movR64Imm64Effect 0x10bbd7 13 0x5ffffffffffffa) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 2871) (.exec 0x10bbd7 (fun s => s.RIP = 0x10bbd7) (movR64Imm64Effect 0x10bbd7 13 0x5ffffffffffffa) (Reg.operands [] [])) #v[]
    (.letOp (n := 2872) (.out 0x10bbe1 (addR64R64Effect 0x10bbe1 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[2787, 2870]
    (.letOp (n := 2873) (.exec 0x10bbe1 (fun s => s.RIP = 0x10bbe1) (addR64R64Effect 0x10bbe1 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[2787, 2870]
    (.letOp (n := 2874) (.exec 0x10bbe4 (StorePre 0x10bbe4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10bbe4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bbe4 3 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[2872, 65]
    (.letOp (n := 2875) (.out 0x10bbe9 (movR64R64Effect 0x10bbe9 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[2859]
    (.letOp (n := 2876) (.exec 0x10bbe9 (fun s => s.RIP = 0x10bbe9) (movR64R64Effect 0x10bbe9 3 0) (Reg.operands [.gpr 0] [])) #v[2859]
    (b_l10a410_67)))))))))))))))))))))))))))))))))))

def bytes_l10a410_66 : List UInt8 :=
  [0x4C, 0x8B, 0x44, 0x24, 0x18, 0x4C, 0x03, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x44,
    0x24, 0x18, 0x48, 0x8B, 0x74, 0x24, 0x08, 0x48, 0x03, 0xB4, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48,
    0x89, 0x74, 0x24, 0x08, 0x48, 0x8B, 0x7C, 0x24, 0x30, 0x48, 0x03, 0xBC, 0x24, 0xA0, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x7C, 0x24, 0x30, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x03, 0x84, 0x24, 0xC8,
    0x00, 0x00, 0x00, 0x4C, 0x8B, 0x4C, 0x24, 0x48, 0x4C, 0x03, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00,
    0x48, 0xBA, 0x1A, 0xE9, 0xFF, 0xFF, 0xF9, 0xFF, 0x5F, 0x00, 0x49, 0x01, 0xD3, 0x4C, 0x89, 0x9C,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0xBD, 0xFA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x5F, 0x00, 0x4C,
    0x01, 0xEB, 0x48, 0x89, 0x5C, 0x24, 0x78, 0x48, 0x89, 0xC3] ++ bytes_l10a410_67

theorem code_l10a410_66 : ∀ x ∈ codeRange 0x10bb72 bytes_l10a410_66, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbb72 122 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_67

def b_l10a410_65 : Block Op Label signature Reg.count 2807 :=
  .letOp (n := 2807) (.out 0x10baed (subR64R64Effect 0x10baed 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[2799, 2805]
    (.letOp (n := 2808) (.exec 0x10baed (fun s => s.RIP = 0x10baed) (subR64R64Effect 0x10baed 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2799, 2805]
    (.letOp (n := 2809) (.exec 0x10baf0 (StorePre 0x10baf0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10baf0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10baf0 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[2807, 65]
    (.letOp (n := 2810) (.out 0x10baf5 (movR64M64Effect 0x10baf5 0 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2811) (.exec 0x10baf5 (LoadPre 0x10baf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10baf5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10baf5 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2812) (.out 0x10bafd (movR64M64Effect 0x10bafd 1 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 2813) (.exec 0x10bafd (LoadPre 0x10bafd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10bafd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bafd 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2814) (.out 0x10bb05 (addR64R64Effect 0x10bb05 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2810, 2812]
    (.letOp (n := 2815) (.exec 0x10bb05 (fun s => s.RIP = 0x10bb05) (addR64R64Effect 0x10bb05 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2810, 2812]
    (.letOp (n := 2816) (.out 0x10bb08 (subR64R64Effect 0x10bb08 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2767, 2814]
    (.letOp (n := 2817) (.exec 0x10bb08 (fun s => s.RIP = 0x10bb08) (subR64R64Effect 0x10bb08 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2767, 2814]
    (.letOp (n := 2818) (.exec 0x10bb0b (StorePre 0x10bb0b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10bb0b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bb0b 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2816, 65]
    (.letOp (n := 2819) (.out 0x10bb10 (movR64M64Effect 0x10bb10 1 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 2820) (.exec 0x10bb10 (LoadPre 0x10bb10 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10bb10 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bb10 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2821) (.out 0x10bb18 (addR64M64Effect 0x10bb18 1 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[2819, 65]
    (.letOp (n := 2822) (.exec 0x10bb18 (LoadPre 0x10bb18 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10bb18 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10bb18 1 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2819, 65]
    (.letOp (n := 2823) (.out 0x10bb20 (movR64M64Effect 0x10bb20 10 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 2824) (.exec 0x10bb20 (LoadPre 0x10bb20 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10bb20 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bb20 10 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2825) (.out 0x10bb28 (addR64M64Effect 0x10bb28 10 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[2823, 65]
    (.letOp (n := 2826) (.exec 0x10bb28 (LoadPre 0x10bb28 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10bb28 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10bb28 10 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[2823, 65]
    (.letOp (n := 2827) (.out 0x10bb30 (movR64M64Effect 0x10bb30 14 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 2828) (.exec 0x10bb30 (LoadPre 0x10bb30 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10bb30 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bb30 14 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2829) (.out 0x10bb38 (addR64M64Effect 0x10bb38 14 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[2827, 65]
    (.letOp (n := 2830) (.exec 0x10bb38 (LoadPre 0x10bb38 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10bb38 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10bb38 14 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[2827, 65]
    (.letOp (n := 2831) (.exec 0x10bb40 (StorePre 0x10bb40 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10bb40 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10bb40 14 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[2829, 65]
    (.letOp (n := 2832) (.out 0x10bb48 (movR64M64Effect 0x10bb48 15 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 2833) (.exec 0x10bb48 (LoadPre 0x10bb48 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10bb48 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bb48 15 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2834) (.out 0x10bb50 (addR64M64Effect 0x10bb50 15 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[2832, 65]
    (.letOp (n := 2835) (.exec 0x10bb50 (LoadPre 0x10bb50 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10bb50 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10bb50 15 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[2832, 65]
    (.letOp (n := 2836) (.exec 0x10bb58 (StorePre 0x10bb58 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10bb58 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10bb58 15 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[2834, 65]
    (.letOp (n := 2837) (.out 0x10bb60 (movR64M64Effect 0x10bb60 12 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 2838) (.exec 0x10bb60 (LoadPre 0x10bb60 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10bb60 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bb60 12 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2839) (.out 0x10bb65 (addR64M64Effect 0x10bb65 12 (.sib 4 none 0 (.d32 0x1c0))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[2837, 65]
    (.letOp (n := 2840) (.exec 0x10bb65 (LoadPre 0x10bb65 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x10bb65 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10bb65 12 (.sib 4 none 0 (.d32 0x1c0))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[2837, 65]
    (.letOp (n := 2841) (.exec 0x10bb6d (StorePre 0x10bb6d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10bb6d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10bb6d 12 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[2839, 65]
    (b_l10a410_66)))))))))))))))))))))))))))))))))))

def bytes_l10a410_65 : List UInt8 :=
  [0x49, 0x29, 0xC5, 0x4C, 0x89, 0x6C, 0x24, 0x20, 0x48, 0x8B, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x01, 0xC8, 0x48, 0x29, 0xC2, 0x48, 0x89,
    0x54, 0x24, 0x40, 0x48, 0x8B, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x03, 0x8C, 0x24, 0xA8,
    0x00, 0x00, 0x00, 0x4C, 0x8B, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x03, 0x94, 0x24, 0xF8,
    0x00, 0x00, 0x00, 0x4C, 0x8B, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x03, 0xB4, 0x24, 0x58,
    0x01, 0x00, 0x00, 0x4C, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0xBC, 0x24, 0xC0,
    0x00, 0x00, 0x00, 0x4C, 0x03, 0xBC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xBC, 0x24, 0xC0,
    0x00, 0x00, 0x00, 0x4C, 0x8B, 0x64, 0x24, 0x70, 0x4C, 0x03, 0xA4, 0x24, 0xC0, 0x01, 0x00, 0x00,
    0x4C, 0x89, 0x64, 0x24, 0x70] ++ bytes_l10a410_66

theorem code_l10a410_65 : ∀ x ∈ codeRange 0x10baed bytes_l10a410_65, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbaed 133 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_66

def b_l10a410_64 : Block Op Label signature Reg.count 2767 :=
  .letOp (n := 2767) (.out 0x10ba85 (movR64R64Effect 0x10ba85 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[2765]
    (.letOp (n := 2768) (.exec 0x10ba85 (fun s => s.RIP = 0x10ba85) (movR64R64Effect 0x10ba85 2 5) (Reg.operands [.gpr 5] [])) #v[2765]
    (.letOp (n := 2769) (.out 0x10ba88 (movR64M64Effect 0x10ba88 0 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2770) (.exec 0x10ba88 (LoadPre 0x10ba88 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10ba88 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ba88 0 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2771) (.out 0x10ba90 (movR64M64Effect 0x10ba90 1 (.sib 4 none 0 (.d32 0x1d8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 2772) (.exec 0x10ba90 (LoadPre 0x10ba90 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x10ba90 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ba90 1 (.sib 4 none 0 (.d32 0x1d8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2773) (.out 0x10ba98 (addR64R64Effect 0x10ba98 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2769, 2771]
    (.letOp (n := 2774) (.exec 0x10ba98 (fun s => s.RIP = 0x10ba98) (addR64R64Effect 0x10ba98 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2769, 2771]
    (.letOp (n := 2775) (.out 0x10ba9b (movR64M64Effect 0x10ba9b 11 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 2776) (.exec 0x10ba9b (LoadPre 0x10ba9b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10ba9b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ba9b 11 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2777) (.out 0x10baa3 (subR64R64Effect 0x10baa3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[2775, 2773]
    (.letOp (n := 2778) (.exec 0x10baa3 (fun s => s.RIP = 0x10baa3) (subR64R64Effect 0x10baa3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[2775, 2773]
    (.letOp (n := 2779) (.out 0x10baa6 (movR64M64Effect 0x10baa6 0 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2780) (.exec 0x10baa6 (LoadPre 0x10baa6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10baa6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10baa6 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2781) (.out 0x10baae (movR64M64Effect 0x10baae 1 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 2782) (.exec 0x10baae (LoadPre 0x10baae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10baae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10baae 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2783) (.out 0x10bab3 (addR64R64Effect 0x10bab3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2779, 2781]
    (.letOp (n := 2784) (.exec 0x10bab3 (fun s => s.RIP = 0x10bab3) (addR64R64Effect 0x10bab3 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2779, 2781]
    (.letOp (n := 2785) (.out 0x10bab6 (movR64M64Effect 0x10bab6 3 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 2786) (.exec 0x10bab6 (LoadPre 0x10bab6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10bab6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10bab6 3 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2787) (.out 0x10babb (subR64R64Effect 0x10babb 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[2785, 2783]
    (.letOp (n := 2788) (.exec 0x10babb (fun s => s.RIP = 0x10babb) (subR64R64Effect 0x10babb 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[2785, 2783]
    (.letOp (n := 2789) (.out 0x10babe (movR64M64Effect 0x10babe 0 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2790) (.exec 0x10babe (LoadPre 0x10babe (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10babe + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10babe 0 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2791) (.out 0x10bac6 (movR64M64Effect 0x10bac6 1 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 2792) (.exec 0x10bac6 (LoadPre 0x10bac6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x10bac6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bac6 1 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2793) (.out 0x10bace (addR64R64Effect 0x10bace 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2789, 2791]
    (.letOp (n := 2794) (.exec 0x10bace (fun s => s.RIP = 0x10bace) (addR64R64Effect 0x10bace 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2789, 2791]
    (.letOp (n := 2795) (.out 0x10bad1 (movR64R64Effect 0x10bad1 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 7] []) (.reg (.gpr 5))) #v[2734]
    (.letOp (n := 2796) (.exec 0x10bad1 (fun s => s.RIP = 0x10bad1) (movR64R64Effect 0x10bad1 5 7) (Reg.operands [.gpr 7] [])) #v[2734]
    (.letOp (n := 2797) (.out 0x10bad4 (subR64R64Effect 0x10bad4 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[2795, 2793]
    (.letOp (n := 2798) (.exec 0x10bad4 (fun s => s.RIP = 0x10bad4) (subR64R64Effect 0x10bad4 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[2795, 2793]
    (.letOp (n := 2799) (.out 0x10bad7 (andR64R64Effect 0x10bad7 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 6] []) (.reg (.gpr 13))) #v[2752, 2745]
    (.letOp (n := 2800) (.exec 0x10bad7 (fun s => s.RIP = 0x10bad7) (andR64R64Effect 0x10bad7 13 6) (Reg.operands [.gpr 13, .gpr 6] [])) #v[2752, 2745]
    (.letOp (n := 2801) (.out 0x10bada (movR64M64Effect 0x10bada 0 (.sib 4 none 0 (.d32 0x1b8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2802) (.exec 0x10bada (LoadPre 0x10bada (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b8)) s (0x10bada + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bada 0 (.sib 4 none 0 (.d32 0x1b8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2803) (.out 0x10bae2 (movR64M64Effect 0x10bae2 1 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 2804) (.exec 0x10bae2 (LoadPre 0x10bae2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10bae2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10bae2 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2805) (.out 0x10baea (addR64R64Effect 0x10baea 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2801, 2803]
    (.letOp (n := 2806) (.exec 0x10baea (fun s => s.RIP = 0x10baea) (addR64R64Effect 0x10baea 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2801, 2803]
    (b_l10a410_65))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_64 : List UInt8 :=
  [0x48, 0x89, 0xEA, 0x48, 0x8B, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0xD8,
    0x01, 0x00, 0x00, 0x48, 0x01, 0xC8, 0x4C, 0x8B, 0x9C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x29,
    0xC3, 0x48, 0x8B, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x68, 0x48, 0x01,
    0xC8, 0x48, 0x8B, 0x5C, 0x24, 0x78, 0x48, 0x29, 0xC3, 0x48, 0x8B, 0x84, 0x24, 0x68, 0x01, 0x00,
    0x00, 0x48, 0x8B, 0x8C, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x48, 0x01, 0xC8, 0x48, 0x89, 0xFD, 0x48,
    0x29, 0xC5, 0x49, 0x21, 0xF5, 0x48, 0x8B, 0x84, 0x24, 0xB8, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x8C,
    0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x01, 0xC8] ++ bytes_l10a410_65

theorem code_l10a410_64 : ∀ x ∈ codeRange 0x10ba85 bytes_l10a410_64, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xba85 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_65

def b_l10a410_63 : Block Op Label signature Reg.count 2723 :=
  .letOp (n := 2723) (.out 0x10ba35 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ba35 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[2718, 2708, 2721]
    (.letOp (n := 2724) (.exec 0x10ba35 (fun s => s.RIP = 0x10ba35) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ba35 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2718, 2708, 2721]
    (.letOp (n := 2725) (.out 0x10ba38 (addR64R64Effect 0x10ba38 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[2720, 2641]
    (.letOp (n := 2726) (.out 0x10ba38 (addR64R64Effect 0x10ba38 7 9) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 9] []) (.flag .CF)) #v[2720, 2641]
    (.letOp (n := 2727) (.exec 0x10ba38 (fun s => s.RIP = 0x10ba38) (addR64R64Effect 0x10ba38 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[2720, 2641]
    (.letOp (n := 2728) (.out 0x10ba3b (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ba3b 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[2723, 2726]
    (.letOp (n := 2729) (.exec 0x10ba3b (fun s => s.RIP = 0x10ba3b) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ba3b 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2723, 2726]
    (.letOp (n := 2730) (.out 0x10ba3f (shldR64R64Effect 0x10ba3f 5 3 10 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[2699, 2696]
    (.letOp (n := 2731) (.exec 0x10ba3f (fun s => s.RIP = 0x10ba3f) (shldR64R64Effect 0x10ba3f 5 3 10 12) (Reg.operands [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2699, 2696]
    (.letOp (n := 2732) (.out 0x10ba44 (shldR64R64Effect 0x10ba44 5 11 7 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[2728, 2725]
    (.letOp (n := 2733) (.exec 0x10ba44 (fun s => s.RIP = 0x10ba44) (shldR64R64Effect 0x10ba44 5 11 7 12) (Reg.operands [.gpr 11, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2728, 2725]
    (.letOp (n := 2734) (.out 0x10ba49 (andR64R64Effect 0x10ba49 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[2725, 2581]
    (.letOp (n := 2735) (.exec 0x10ba49 (fun s => s.RIP = 0x10ba49) (andR64R64Effect 0x10ba49 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[2725, 2581]
    (.letOp (n := 2736) (.out 0x10ba4c (movR64R64Effect 0x10ba4c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[2730]
    (.letOp (n := 2737) (.exec 0x10ba4c (fun s => s.RIP = 0x10ba4c) (movR64R64Effect 0x10ba4c 0 3) (Reg.operands [.gpr 3] [])) #v[2730]
    (.letOp (n := 2738) (.out 0x10ba4f (mulR64Effect 0x10ba4f 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[2705, 2736]
    (.letOp (n := 2739) (.out 0x10ba4f (mulR64Effect 0x10ba4f 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[2705, 2736]
    (.letOp (n := 2740) (.exec 0x10ba4f (fun s => s.RIP = 0x10ba4f) (mulR64Effect 0x10ba4f 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[2705, 2736]
    (.letOp (n := 2741) (.out 0x10ba52 (movR64M64Effect 0x10ba52 13 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 2742) (.exec 0x10ba52 (LoadPre 0x10ba52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ba52 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ba52 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2743) (.out 0x10ba57 (andR64R64Effect 0x10ba57 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[2741, 2581]
    (.letOp (n := 2744) (.exec 0x10ba57 (fun s => s.RIP = 0x10ba57) (andR64R64Effect 0x10ba57 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[2741, 2581]
    (.letOp (n := 2745) (.out 0x10ba5a (movR64R64Effect 0x10ba5a 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[2581]
    (.letOp (n := 2746) (.exec 0x10ba5a (fun s => s.RIP = 0x10ba5a) (movR64R64Effect 0x10ba5a 6 5) (Reg.operands [.gpr 5] [])) #v[2581]
    (.letOp (n := 2747) (.out 0x10ba5d (addR64R64Effect 0x10ba5d 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[2743, 2738]
    (.letOp (n := 2748) (.out 0x10ba5d (addR64R64Effect 0x10ba5d 13 0) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 0] []) (.flag .CF)) #v[2743, 2738]
    (.letOp (n := 2749) (.exec 0x10ba5d (fun s => s.RIP = 0x10ba5d) (addR64R64Effect 0x10ba5d 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2743, 2738]
    (.letOp (n := 2750) (.out 0x10ba60 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ba60 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2739, 2748]
    (.letOp (n := 2751) (.exec 0x10ba60 (fun s => s.RIP = 0x10ba60) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ba60 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2739, 2748]
    (.letOp (n := 2752) (.out 0x10ba64 (addR64R64Effect 0x10ba64 13 11) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 11] []) (.reg (.gpr 13))) #v[2747, 2732]
    (.letOp (n := 2753) (.out 0x10ba64 (addR64R64Effect 0x10ba64 13 11) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 11] []) (.flag .CF)) #v[2747, 2732]
    (.letOp (n := 2754) (.exec 0x10ba64 (fun s => s.RIP = 0x10ba64) (addR64R64Effect 0x10ba64 13 11) (Reg.operands [.gpr 13, .gpr 11] [])) #v[2747, 2732]
    (.letOp (n := 2755) (.out 0x10ba67 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ba67 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2750, 2753]
    (.letOp (n := 2756) (.exec 0x10ba67 (fun s => s.RIP = 0x10ba67) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ba67 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2750, 2753]
    (.letOp (n := 2757) (.out 0x10ba6b (shldR64R64Effect 0x10ba6b 5 2 13 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2755, 2752]
    (.letOp (n := 2758) (.exec 0x10ba6b (fun s => s.RIP = 0x10ba6b) (shldR64R64Effect 0x10ba6b 5 2 13 12) (Reg.operands [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2755, 2752]
    (.letOp (n := 2759) (.out 0x10ba70 (movR64M64Effect 0x10ba70 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 2760) (.exec 0x10ba70 (LoadPre 0x10ba70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10ba70 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ba70 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2761) (.out 0x10ba75 (movR64Imm64Effect 0x10ba75 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 2762) (.exec 0x10ba75 (fun s => s.RIP = 0x10ba75) (movR64Imm64Effect 0x10ba75 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2763) (.out 0x10ba7f (andR64R64Effect 0x10ba7f 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[2759, 2761]
    (.letOp (n := 2764) (.exec 0x10ba7f (fun s => s.RIP = 0x10ba7f) (andR64R64Effect 0x10ba7f 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[2759, 2761]
    (.letOp (n := 2765) (.out 0x10ba82 (addR64R64Effect 0x10ba82 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[2763, 2757]
    (.letOp (n := 2766) (.exec 0x10ba82 (fun s => s.RIP = 0x10ba82) (addR64R64Effect 0x10ba82 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[2763, 2757]
    (b_l10a410_64))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_63 : List UInt8 :=
  [0x49, 0x11, 0xD3, 0x4C, 0x01, 0xCF, 0x49, 0x83, 0xD3, 0x00, 0x4C, 0x0F, 0xA4, 0xD3, 0x0C, 0x49,
    0x0F, 0xA4, 0xFB, 0x0C, 0x48, 0x21, 0xEF, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0xE6, 0x4C, 0x8B, 0x6C,
    0x24, 0x20, 0x49, 0x21, 0xED, 0x48, 0x89, 0xEE, 0x49, 0x01, 0xC5, 0x48, 0x83, 0xD2, 0x00, 0x4D,
    0x01, 0xDD, 0x48, 0x83, 0xD2, 0x00, 0x4C, 0x0F, 0xA4, 0xEA, 0x0C, 0x48, 0x8B, 0x6C, 0x24, 0x40,
    0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x21, 0xC5, 0x48, 0x01, 0xD5] ++ bytes_l10a410_64

theorem code_l10a410_63 : ∀ x ∈ codeRange 0x10ba35 bytes_l10a410_63, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xba35 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_64

def b_l10a410_62 : Block Op Label signature Reg.count 2675 :=
  .letOp (n := 2675) (.out 0x10b9e0 (movR64M64Effect 0x10b9e0 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2676) (.exec 0x10b9e0 (LoadPre 0x10b9e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10b9e0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b9e0 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2677) (.out 0x10b9e8 (mulM64Effect 0x10b9e8 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2675, 65]
    (.letOp (n := 2678) (.out 0x10b9e8 (mulM64Effect 0x10b9e8 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2675, 65]
    (.letOp (n := 2679) (.exec 0x10b9e8 (LoadPre 0x10b9e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10b9e8 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10b9e8 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2675, 65]
    (.letOp (n := 2680) (.out 0x10b9f0 (movR64R64Effect 0x10b9f0 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2678]
    (.letOp (n := 2681) (.exec 0x10b9f0 (fun s => s.RIP = 0x10b9f0) (movR64R64Effect 0x10b9f0 3 2) (Reg.operands [.gpr 2] [])) #v[2678]
    (.letOp (n := 2682) (.out 0x10b9f3 (movR64R64Effect 0x10b9f3 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2677]
    (.letOp (n := 2683) (.exec 0x10b9f3 (fun s => s.RIP = 0x10b9f3) (movR64R64Effect 0x10b9f3 6 0) (Reg.operands [.gpr 0] [])) #v[2677]
    (.letOp (n := 2684) (.out 0x10b9f6 (movR64M64Effect 0x10b9f6 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2685) (.exec 0x10b9f6 (LoadPre 0x10b9f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10b9f6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b9f6 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2686) (.out 0x10b9fb (mulM64Effect 0x10b9fb 8 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2684, 65]
    (.letOp (n := 2687) (.out 0x10b9fb (mulM64Effect 0x10b9fb 8 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2684, 65]
    (.letOp (n := 2688) (.exec 0x10b9fb (LoadPre 0x10b9fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10b9fb + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10b9fb 8 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2684, 65]
    (.letOp (n := 2689) (.out 0x10ba03 (movR64R64Effect 0x10ba03 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2686]
    (.letOp (n := 2690) (.exec 0x10ba03 (fun s => s.RIP = 0x10ba03) (movR64R64Effect 0x10ba03 10 0) (Reg.operands [.gpr 0] [])) #v[2686]
    (.letOp (n := 2691) (.out 0x10ba06 (addR64R64Effect 0x10ba06 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[2689, 2682]
    (.letOp (n := 2692) (.out 0x10ba06 (addR64R64Effect 0x10ba06 10 6) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 6] []) (.flag .CF)) #v[2689, 2682]
    (.letOp (n := 2693) (.exec 0x10ba06 (fun s => s.RIP = 0x10ba06) (addR64R64Effect 0x10ba06 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[2689, 2682]
    (.letOp (n := 2694) (.out 0x10ba09 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ba09 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[2680, 2687, 2692]
    (.letOp (n := 2695) (.exec 0x10ba09 (fun s => s.RIP = 0x10ba09) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ba09 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2680, 2687, 2692]
    (.letOp (n := 2696) (.out 0x10ba0c (addR64R64Effect 0x10ba0c 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[2691, 2617]
    (.letOp (n := 2697) (.out 0x10ba0c (addR64R64Effect 0x10ba0c 10 8) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 8] []) (.flag .CF)) #v[2691, 2617]
    (.letOp (n := 2698) (.exec 0x10ba0c (fun s => s.RIP = 0x10ba0c) (addR64R64Effect 0x10ba0c 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[2691, 2617]
    (.letOp (n := 2699) (.out 0x10ba0f (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ba0f 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[2694, 2697]
    (.letOp (n := 2700) (.exec 0x10ba0f (fun s => s.RIP = 0x10ba0f) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ba0f 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2694, 2697]
    (.letOp (n := 2701) (.out 0x10ba13 (movR64R64Effect 0x10ba13 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[2696]
    (.letOp (n := 2702) (.exec 0x10ba13 (fun s => s.RIP = 0x10ba13) (movR64R64Effect 0x10ba13 0 10) (Reg.operands [.gpr 10] [])) #v[2696]
    (.letOp (n := 2703) (.out 0x10ba16 (andR64R64Effect 0x10ba16 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[2701, 2581]
    (.letOp (n := 2704) (.exec 0x10ba16 (fun s => s.RIP = 0x10ba16) (andR64R64Effect 0x10ba16 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[2701, 2581]
    (.letOp (n := 2705) (.out 0x10ba19 (movR64Imm64Effect 0x10ba19 6 0x1000003d10) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 2706) (.exec 0x10ba19 (fun s => s.RIP = 0x10ba19) (movR64Imm64Effect 0x10ba19 6 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2707) (.out 0x10ba23 (mulR64Effect 0x10ba23 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[2705, 2703]
    (.letOp (n := 2708) (.out 0x10ba23 (mulR64Effect 0x10ba23 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[2705, 2703]
    (.letOp (n := 2709) (.exec 0x10ba23 (fun s => s.RIP = 0x10ba23) (mulR64Effect 0x10ba23 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[2705, 2703]
    (.letOp (n := 2710) (.out 0x10ba26 (addR64R64Effect 0x10ba26 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[2668, 2661]
    (.letOp (n := 2711) (.out 0x10ba26 (addR64R64Effect 0x10ba26 7 12) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 12] []) (.flag .CF)) #v[2668, 2661]
    (.letOp (n := 2712) (.exec 0x10ba26 (fun s => s.RIP = 0x10ba26) (addR64R64Effect 0x10ba26 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[2668, 2661]
    (.letOp (n := 2713) (.out 0x10ba29 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ba29 11 15)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[2670, 2659, 2711]
    (.letOp (n := 2714) (.exec 0x10ba29 (fun s => s.RIP = 0x10ba29) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ba29 11 15)) (Reg.operands [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2670, 2659, 2711]
    (.letOp (n := 2715) (.out 0x10ba2c (addR64R64Effect 0x10ba2c 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[2710, 2652]
    (.letOp (n := 2716) (.out 0x10ba2c (addR64R64Effect 0x10ba2c 7 14) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 14] []) (.flag .CF)) #v[2710, 2652]
    (.letOp (n := 2717) (.exec 0x10ba2c (fun s => s.RIP = 0x10ba2c) (addR64R64Effect 0x10ba2c 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[2710, 2652]
    (.letOp (n := 2718) (.out 0x10ba2f (atFlags StatusFlags.CF (adcR64R64Effect 0x10ba2f 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[2713, 2650, 2716]
    (.letOp (n := 2719) (.exec 0x10ba2f (fun s => s.RIP = 0x10ba2f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ba2f 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2713, 2650, 2716]
    (.letOp (n := 2720) (.out 0x10ba32 (addR64R64Effect 0x10ba32 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[2715, 2707]
    (.letOp (n := 2721) (.out 0x10ba32 (addR64R64Effect 0x10ba32 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[2715, 2707]
    (.letOp (n := 2722) (.exec 0x10ba32 (fun s => s.RIP = 0x10ba32) (addR64R64Effect 0x10ba32 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2715, 2707]
    (b_l10a410_63))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_62 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xD3, 0x48, 0x89, 0xC6, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0xF7, 0xA4, 0x24, 0xF0,
    0x00, 0x00, 0x00, 0x49, 0x89, 0xC2, 0x49, 0x01, 0xF2, 0x48, 0x11, 0xD3, 0x4D, 0x01, 0xC2, 0x48,
    0x83, 0xD3, 0x00, 0x4C, 0x89, 0xD0, 0x48, 0x21, 0xE8, 0x48, 0xBE, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE6, 0x4C, 0x01, 0xE7, 0x4D, 0x11, 0xFB, 0x4C, 0x01, 0xF7, 0x4D,
    0x11, 0xEB, 0x48, 0x01, 0xC7] ++ bytes_l10a410_63

theorem code_l10a410_62 : ∀ x ∈ codeRange 0x10b9e0 bytes_l10a410_62, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb9e0 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_63

def b_l10a410_61 : Block Op Label signature Reg.count 2631 :=
  .letOp (n := 2631) (.out 0x10b995 (addR64R64Effect 0x10b995 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[2626, 2623]
    (.letOp (n := 2632) (.out 0x10b995 (addR64R64Effect 0x10b995 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[2626, 2623]
    (.letOp (n := 2633) (.exec 0x10b995 (fun s => s.RIP = 0x10b995) (addR64R64Effect 0x10b995 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[2626, 2623]
    (.letOp (n := 2634) (.out 0x10b998 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b998 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[2629, 2624, 2632]
    (.letOp (n := 2635) (.exec 0x10b998 (fun s => s.RIP = 0x10b998) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b998 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2629, 2624, 2632]
    (.letOp (n := 2636) (.out 0x10b99b (addR64R64Effect 0x10b99b 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[2631, 2550]
    (.letOp (n := 2637) (.out 0x10b99b (addR64R64Effect 0x10b99b 12 3) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 3] []) (.flag .CF)) #v[2631, 2550]
    (.letOp (n := 2638) (.exec 0x10b99b (fun s => s.RIP = 0x10b99b) (addR64R64Effect 0x10b99b 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[2631, 2550]
    (.letOp (n := 2639) (.out 0x10b99e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b99e 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[2634, 2637]
    (.letOp (n := 2640) (.exec 0x10b99e (fun s => s.RIP = 0x10b99e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b99e 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2634, 2637]
    (.letOp (n := 2641) (.out 0x10b9a2 (shldR64R64Effect 0x10b9a2 5 9 12 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2639, 2636]
    (.letOp (n := 2642) (.exec 0x10b9a2 (fun s => s.RIP = 0x10b9a2) (shldR64R64Effect 0x10b9a2 5 9 12 12) (Reg.operands [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2639, 2636]
    (.letOp (n := 2643) (.out 0x10b9a7 (movR64R64Effect 0x10b9a7 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[2636]
    (.letOp (n := 2644) (.exec 0x10b9a7 (fun s => s.RIP = 0x10b9a7) (movR64R64Effect 0x10b9a7 6 12) (Reg.operands [.gpr 12] [])) #v[2636]
    (.letOp (n := 2645) (.out 0x10b9aa (movR64R64Effect 0x10b9aa 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[2595]
    (.letOp (n := 2646) (.exec 0x10b9aa (fun s => s.RIP = 0x10b9aa) (movR64R64Effect 0x10b9aa 0 13) (Reg.operands [.gpr 13] [])) #v[2595]
    (.letOp (n := 2647) (.out 0x10b9ad (mulM64Effect 0x10b9ad 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2645, 65]
    (.letOp (n := 2648) (.out 0x10b9ad (mulM64Effect 0x10b9ad 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2645, 65]
    (.letOp (n := 2649) (.exec 0x10b9ad (LoadPre 0x10b9ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10b9ad + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10b9ad 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2645, 65]
    (.letOp (n := 2650) (.out 0x10b9b2 (movR64R64Effect 0x10b9b2 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2648]
    (.letOp (n := 2651) (.exec 0x10b9b2 (fun s => s.RIP = 0x10b9b2) (movR64R64Effect 0x10b9b2 13 2) (Reg.operands [.gpr 2] [])) #v[2648]
    (.letOp (n := 2652) (.out 0x10b9b5 (movR64R64Effect 0x10b9b5 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[2647]
    (.letOp (n := 2653) (.exec 0x10b9b5 (fun s => s.RIP = 0x10b9b5) (movR64R64Effect 0x10b9b5 14 0) (Reg.operands [.gpr 0] [])) #v[2647]
    (.letOp (n := 2654) (.out 0x10b9b8 (movR64M64Effect 0x10b9b8 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2655) (.exec 0x10b9b8 (LoadPre 0x10b9b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10b9b8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b9b8 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2656) (.out 0x10b9bd (mulM64Effect 0x10b9bd 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2654, 65]
    (.letOp (n := 2657) (.out 0x10b9bd (mulM64Effect 0x10b9bd 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2654, 65]
    (.letOp (n := 2658) (.exec 0x10b9bd (LoadPre 0x10b9bd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10b9bd + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10b9bd 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2654, 65]
    (.letOp (n := 2659) (.out 0x10b9c5 (movR64R64Effect 0x10b9c5 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2657]
    (.letOp (n := 2660) (.exec 0x10b9c5 (fun s => s.RIP = 0x10b9c5) (movR64R64Effect 0x10b9c5 15 2) (Reg.operands [.gpr 2] [])) #v[2657]
    (.letOp (n := 2661) (.out 0x10b9c8 (movR64R64Effect 0x10b9c8 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[2656]
    (.letOp (n := 2662) (.exec 0x10b9c8 (fun s => s.RIP = 0x10b9c8) (movR64R64Effect 0x10b9c8 12 0) (Reg.operands [.gpr 0] [])) #v[2656]
    (.letOp (n := 2663) (.out 0x10b9cb (movR64M64Effect 0x10b9cb 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2664) (.exec 0x10b9cb (LoadPre 0x10b9cb (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10b9cb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10b9cb 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2665) (.out 0x10b9cf (mulR64Effect 0x10b9cf 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2572, 2663]
    (.letOp (n := 2666) (.out 0x10b9cf (mulR64Effect 0x10b9cf 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2572, 2663]
    (.letOp (n := 2667) (.exec 0x10b9cf (fun s => s.RIP = 0x10b9cf) (mulR64Effect 0x10b9cf 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2572, 2663]
    (.letOp (n := 2668) (.out 0x10b9d2 (movR64R64Effect 0x10b9d2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[2665]
    (.letOp (n := 2669) (.exec 0x10b9d2 (fun s => s.RIP = 0x10b9d2) (movR64R64Effect 0x10b9d2 7 0) (Reg.operands [.gpr 0] [])) #v[2665]
    (.letOp (n := 2670) (.out 0x10b9d5 (movR64R64Effect 0x10b9d5 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2666]
    (.letOp (n := 2671) (.exec 0x10b9d5 (fun s => s.RIP = 0x10b9d5) (movR64R64Effect 0x10b9d5 11 2) (Reg.operands [.gpr 2] [])) #v[2666]
    (.letOp (n := 2672) (.out 0x10b9d8 (andR64R64Effect 0x10b9d8 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[2643, 2581]
    (.letOp (n := 2673) (.exec 0x10b9d8 (fun s => s.RIP = 0x10b9d8) (andR64R64Effect 0x10b9d8 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[2643, 2581]
    (.letOp (n := 2674) (.exec 0x10b9db (StorePre 0x10b9db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10b9db + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b9db 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[2672, 65]
    (b_l10a410_62))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_61 : List UInt8 :=
  [0x49, 0x01, 0xC4, 0x49, 0x11, 0xD1, 0x49, 0x01, 0xDC, 0x49, 0x83, 0xD1, 0x00, 0x4D, 0x0F, 0xA4,
    0xE1, 0x0C, 0x4C, 0x89, 0xE6, 0x4C, 0x89, 0xE8, 0x48, 0xF7, 0x64, 0x24, 0x50, 0x49, 0x89, 0xD5,
    0x49, 0x89, 0xC6, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0xF7, 0xA4, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0x49, 0x89, 0xD7, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x04, 0x24, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC7,
    0x49, 0x89, 0xD3, 0x48, 0x21, 0xEE, 0x48, 0x89, 0x74, 0x24, 0x78] ++ bytes_l10a410_62

theorem code_l10a410_61 : ∀ x ∈ codeRange 0x10b995 bytes_l10a410_61, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb995 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_62

def b_l10a410_60 : Block Op Label signature Reg.count 2585 :=
  .letOp (n := 2585) (.exec 0x10b93e (StorePre 0x10b93e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10b93e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b93e 8 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[2583, 65]
    (.letOp (n := 2586) (.out 0x10b946 (movR64R64Effect 0x10b946 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[2475]
    (.letOp (n := 2587) (.exec 0x10b946 (fun s => s.RIP = 0x10b946) (movR64R64Effect 0x10b946 0 13) (Reg.operands [.gpr 13] [])) #v[2475]
    (.letOp (n := 2588) (.out 0x10b949 (mulR64Effect 0x10b949 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[2490, 2586]
    (.letOp (n := 2589) (.out 0x10b949 (mulR64Effect 0x10b949 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[2490, 2586]
    (.letOp (n := 2590) (.exec 0x10b949 (fun s => s.RIP = 0x10b949) (mulR64Effect 0x10b949 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2490, 2586]
    (.letOp (n := 2591) (.out 0x10b94c (movR64R64Effect 0x10b94c 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2589]
    (.letOp (n := 2592) (.exec 0x10b94c (fun s => s.RIP = 0x10b94c) (movR64R64Effect 0x10b94c 8 2) (Reg.operands [.gpr 2] [])) #v[2589]
    (.letOp (n := 2593) (.out 0x10b94f (movR64R64Effect 0x10b94f 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2588]
    (.letOp (n := 2594) (.exec 0x10b94f (fun s => s.RIP = 0x10b94f) (movR64R64Effect 0x10b94f 10 0) (Reg.operands [.gpr 0] [])) #v[2588]
    (.letOp (n := 2595) (.out 0x10b952 (movR64M64Effect 0x10b952 13 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 2596) (.exec 0x10b952 (LoadPre 0x10b952 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10b952 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b952 13 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2597) (.out 0x10b957 (movR64R64Effect 0x10b957 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[2595]
    (.letOp (n := 2598) (.exec 0x10b957 (fun s => s.RIP = 0x10b957) (movR64R64Effect 0x10b957 0 13) (Reg.operands [.gpr 13] [])) #v[2595]
    (.letOp (n := 2599) (.out 0x10b95a (mulR64Effect 0x10b95a 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[2503, 2597]
    (.letOp (n := 2600) (.out 0x10b95a (mulR64Effect 0x10b95a 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[2503, 2597]
    (.letOp (n := 2601) (.exec 0x10b95a (fun s => s.RIP = 0x10b95a) (mulR64Effect 0x10b95a 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[2503, 2597]
    (.letOp (n := 2602) (.out 0x10b95d (addR64R64Effect 0x10b95d 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[2599, 2593]
    (.letOp (n := 2603) (.out 0x10b95d (addR64R64Effect 0x10b95d 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[2599, 2593]
    (.letOp (n := 2604) (.exec 0x10b95d (fun s => s.RIP = 0x10b95d) (addR64R64Effect 0x10b95d 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[2599, 2593]
    (.letOp (n := 2605) (.out 0x10b960 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b960 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2591, 2600, 2603]
    (.letOp (n := 2606) (.exec 0x10b960 (fun s => s.RIP = 0x10b960) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b960 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2591, 2600, 2603]
    (.letOp (n := 2607) (.out 0x10b963 (addR64R64Effect 0x10b963 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[2602, 2577]
    (.letOp (n := 2608) (.out 0x10b963 (addR64R64Effect 0x10b963 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[2602, 2577]
    (.letOp (n := 2609) (.exec 0x10b963 (fun s => s.RIP = 0x10b963) (addR64R64Effect 0x10b963 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[2602, 2577]
    (.letOp (n := 2610) (.out 0x10b966 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b966 8 7)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2605, 2579, 2608]
    (.letOp (n := 2611) (.exec 0x10b966 (fun s => s.RIP = 0x10b966) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b966 8 7)) (Reg.operands [.gpr 8, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2605, 2579, 2608]
    (.letOp (n := 2612) (.out 0x10b969 (addR64R64Effect 0x10b969 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[2607, 2528]
    (.letOp (n := 2613) (.out 0x10b969 (addR64R64Effect 0x10b969 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[2607, 2528]
    (.letOp (n := 2614) (.exec 0x10b969 (fun s => s.RIP = 0x10b969) (addR64R64Effect 0x10b969 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[2607, 2528]
    (.letOp (n := 2615) (.out 0x10b96c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b96c 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2610, 2613]
    (.letOp (n := 2616) (.exec 0x10b96c (fun s => s.RIP = 0x10b96c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b96c 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2610, 2613]
    (.letOp (n := 2617) (.out 0x10b970 (shldR64R64Effect 0x10b970 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2615, 2612]
    (.letOp (n := 2618) (.exec 0x10b970 (fun s => s.RIP = 0x10b970) (shldR64R64Effect 0x10b970 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2615, 2612]
    (.letOp (n := 2619) (.out 0x10b975 (andR64R64Effect 0x10b975 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[2612, 2581]
    (.letOp (n := 2620) (.exec 0x10b975 (fun s => s.RIP = 0x10b975) (andR64R64Effect 0x10b975 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[2612, 2581]
    (.letOp (n := 2621) (.out 0x10b978 (movR64Imm64Effect 0x10b978 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2622) (.exec 0x10b978 (fun s => s.RIP = 0x10b978) (movR64Imm64Effect 0x10b978 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2623) (.out 0x10b982 (mulR64Effect 0x10b982 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2621, 2619]
    (.letOp (n := 2624) (.out 0x10b982 (mulR64Effect 0x10b982 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2621, 2619]
    (.letOp (n := 2625) (.exec 0x10b982 (fun s => s.RIP = 0x10b982) (mulR64Effect 0x10b982 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2621, 2619]
    (.letOp (n := 2626) (.out 0x10b985 (addR64M64Effect 0x10b985 12 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[2568, 65]
    (.letOp (n := 2627) (.out 0x10b985 (addR64M64Effect 0x10b985 12 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 4] []) (.flag .CF)) #v[2568, 65]
    (.letOp (n := 2628) (.exec 0x10b985 (LoadPre 0x10b985 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x10b985 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10b985 12 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[2568, 65]
    (.letOp (n := 2629) (.out 0x10b98d (atFlags StatusFlags.CF (adcR64M64Effect 0x10b98d 9 (.sib 4 none 0 (.d32 0x130)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[2566, 65, 2627]
    (.letOp (n := 2630) (.exec 0x10b98d (LoadPre 0x10b98d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10b98d + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10b98d 9 (.sib 4 none 0 (.d32 0x130)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2566, 65, 2627]
    (b_l10a410_61))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_60 : List UInt8 :=
  [0x4C, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE2, 0x49, 0x89,
    0xD0, 0x49, 0x89, 0xC2, 0x4C, 0x8B, 0x6C, 0x24, 0x78, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE6, 0x4C,
    0x01, 0xD0, 0x49, 0x11, 0xD0, 0x48, 0x01, 0xF0, 0x49, 0x11, 0xF8, 0x4C, 0x01, 0xD8, 0x49, 0x83,
    0xD0, 0x00, 0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x48, 0x21, 0xE8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x03, 0xA4, 0x24, 0x70, 0x01, 0x00, 0x00, 0x4C,
    0x13, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00] ++ bytes_l10a410_61

theorem code_l10a410_60 : ∀ x ∈ codeRange 0x10b93e bytes_l10a410_60, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb93e 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_61

def b_l10a410_59 : Block Op Label signature Reg.count 2543 :=
  .letOp (n := 2543) (.out 0x10b8e2 (movR64R64Effect 0x10b8e2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2541]
    (.letOp (n := 2544) (.exec 0x10b8e2 (fun s => s.RIP = 0x10b8e2) (movR64R64Effect 0x10b8e2 3 2) (Reg.operands [.gpr 2] [])) #v[2541]
    (.letOp (n := 2545) (.out 0x10b8e5 (addR64M64Effect 0x10b8e5 0 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2540, 65]
    (.letOp (n := 2546) (.out 0x10b8e5 (addR64M64Effect 0x10b8e5 0 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[2540, 65]
    (.letOp (n := 2547) (.exec 0x10b8e5 (LoadPre 0x10b8e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10b8e5 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10b8e5 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2540, 65]
    (.letOp (n := 2548) (.out 0x10b8ed (atFlags StatusFlags.CF (adcR64M64Effect 0x10b8ed 3 (.sib 4 none 0 (.d32 0x90)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[2543, 65, 2546]
    (.letOp (n := 2549) (.exec 0x10b8ed (LoadPre 0x10b8ed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10b8ed + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10b8ed 3 (.sib 4 none 0 (.d32 0x90)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2543, 65, 2546]
    (.letOp (n := 2550) (.out 0x10b8f5 (shldR64R64Effect 0x10b8f5 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[2548, 2545]
    (.letOp (n := 2551) (.exec 0x10b8f5 (fun s => s.RIP = 0x10b8f5) (shldR64R64Effect 0x10b8f5 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2548, 2545]
    (.letOp (n := 2552) (.out 0x10b8fa (movR64R64Effect 0x10b8fa 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[2545]
    (.letOp (n := 2553) (.exec 0x10b8fa (fun s => s.RIP = 0x10b8fa) (movR64R64Effect 0x10b8fa 8 0) (Reg.operands [.gpr 0] [])) #v[2545]
    (.letOp (n := 2554) (.out 0x10b8fd (movR64R64Effect 0x10b8fd 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2499]
    (.letOp (n := 2555) (.exec 0x10b8fd (fun s => s.RIP = 0x10b8fd) (movR64R64Effect 0x10b8fd 0 6) (Reg.operands [.gpr 6] [])) #v[2499]
    (.letOp (n := 2556) (.out 0x10b900 (mulR64Effect 0x10b900 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[2457, 2554]
    (.letOp (n := 2557) (.out 0x10b900 (mulR64Effect 0x10b900 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[2457, 2554]
    (.letOp (n := 2558) (.exec 0x10b900 (fun s => s.RIP = 0x10b900) (mulR64Effect 0x10b900 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2457, 2554]
    (.letOp (n := 2559) (.exec 0x10b903 (StorePre 0x10b903 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10b903 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b903 2 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2557, 65]
    (.letOp (n := 2560) (.exec 0x10b90b (StorePre 0x10b90b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x10b90b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b90b 0 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2556, 65]
    (.letOp (n := 2561) (.out 0x10b913 (movR64M64Effect 0x10b913 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2562) (.exec 0x10b913 (LoadPre 0x10b913 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10b913 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10b913 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2563) (.out 0x10b917 (mulR64Effect 0x10b917 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[2468, 2561]
    (.letOp (n := 2564) (.out 0x10b917 (mulR64Effect 0x10b917 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[2468, 2561]
    (.letOp (n := 2565) (.exec 0x10b917 (fun s => s.RIP = 0x10b917) (mulR64Effect 0x10b917 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[2468, 2561]
    (.letOp (n := 2566) (.out 0x10b91a (movR64R64Effect 0x10b91a 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2564]
    (.letOp (n := 2567) (.exec 0x10b91a (fun s => s.RIP = 0x10b91a) (movR64R64Effect 0x10b91a 9 2) (Reg.operands [.gpr 2] [])) #v[2564]
    (.letOp (n := 2568) (.out 0x10b91d (movR64R64Effect 0x10b91d 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[2563]
    (.letOp (n := 2569) (.exec 0x10b91d (fun s => s.RIP = 0x10b91d) (movR64R64Effect 0x10b91d 12 0) (Reg.operands [.gpr 0] [])) #v[2563]
    (.letOp (n := 2570) (.out 0x10b920 (movR64R64Effect 0x10b920 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[2464]
    (.letOp (n := 2571) (.exec 0x10b920 (fun s => s.RIP = 0x10b920) (movR64R64Effect 0x10b920 0 15) (Reg.operands [.gpr 15] [])) #v[2464]
    (.letOp (n := 2572) (.out 0x10b923 (movR64M64Effect 0x10b923 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 2573) (.exec 0x10b923 (LoadPre 0x10b923 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10b923 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b923 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2574) (.out 0x10b928 (mulR64Effect 0x10b928 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2572, 2570]
    (.letOp (n := 2575) (.out 0x10b928 (mulR64Effect 0x10b928 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2572, 2570]
    (.letOp (n := 2576) (.exec 0x10b928 (fun s => s.RIP = 0x10b928) (mulR64Effect 0x10b928 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2572, 2570]
    (.letOp (n := 2577) (.out 0x10b92b (movR64R64Effect 0x10b92b 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2574]
    (.letOp (n := 2578) (.exec 0x10b92b (fun s => s.RIP = 0x10b92b) (movR64R64Effect 0x10b92b 6 0) (Reg.operands [.gpr 0] [])) #v[2574]
    (.letOp (n := 2579) (.out 0x10b92e (movR64R64Effect 0x10b92e 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2575]
    (.letOp (n := 2580) (.exec 0x10b92e (fun s => s.RIP = 0x10b92e) (movR64R64Effect 0x10b92e 7 2) (Reg.operands [.gpr 2] [])) #v[2575]
    (.letOp (n := 2581) (.out 0x10b931 (movR64Imm64Effect 0x10b931 5 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 2582) (.exec 0x10b931 (fun s => s.RIP = 0x10b931) (movR64Imm64Effect 0x10b931 5 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2583) (.out 0x10b93b (andR64R64Effect 0x10b93b 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[2552, 2581]
    (.letOp (n := 2584) (.exec 0x10b93b (fun s => s.RIP = 0x10b93b) (andR64R64Effect 0x10b93b 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[2552, 2581]
    (b_l10a410_60))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_59 : List UInt8 :=
  [0x48, 0x89, 0xD3, 0x48, 0x03, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x48, 0x13, 0x9C, 0x24, 0x90,
    0x00, 0x00, 0x00, 0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x49, 0x89, 0xC0, 0x48, 0x89, 0xF0, 0x49, 0xF7,
    0xE1, 0x48, 0x89, 0x94, 0x24, 0x30, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x70, 0x01, 0x00,
    0x00, 0x48, 0x8B, 0x04, 0x24, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC4, 0x4C, 0x89,
    0xF8, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC6, 0x48, 0x89, 0xD7, 0x48,
    0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xE8] ++ bytes_l10a410_60

theorem code_l10a410_59 : ∀ x ∈ codeRange 0x10b8e2 bytes_l10a410_59, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb8e2 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_60

def b_l10a410_58 : Block Op Label signature Reg.count 2497 :=
  .letOp (n := 2497) (.out 0x10b883 (movR64R64Effect 0x10b883 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[2492]
    (.letOp (n := 2498) (.exec 0x10b883 (fun s => s.RIP = 0x10b883) (movR64R64Effect 0x10b883 3 0) (Reg.operands [.gpr 0] [])) #v[2492]
    (.letOp (n := 2499) (.out 0x10b886 (movR64M64Effect 0x10b886 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 2500) (.exec 0x10b886 (LoadPre 0x10b886 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10b886 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b886 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2501) (.out 0x10b88b (movR64R64Effect 0x10b88b 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2499]
    (.letOp (n := 2502) (.exec 0x10b88b (fun s => s.RIP = 0x10b88b) (movR64R64Effect 0x10b88b 0 6) (Reg.operands [.gpr 6] [])) #v[2499]
    (.letOp (n := 2503) (.out 0x10b88e (movR64M64Effect 0x10b88e 14 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 2504) (.exec 0x10b88e (LoadPre 0x10b88e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10b88e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b88e 14 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2505) (.out 0x10b896 (mulR64Effect 0x10b896 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[2503, 2501]
    (.letOp (n := 2506) (.out 0x10b896 (mulR64Effect 0x10b896 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[2503, 2501]
    (.letOp (n := 2507) (.exec 0x10b896 (fun s => s.RIP = 0x10b896) (mulR64Effect 0x10b896 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[2503, 2501]
    (.letOp (n := 2508) (.out 0x10b899 (addR64R64Effect 0x10b899 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[2505, 2497]
    (.letOp (n := 2509) (.out 0x10b899 (addR64R64Effect 0x10b899 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[2505, 2497]
    (.letOp (n := 2510) (.exec 0x10b899 (fun s => s.RIP = 0x10b899) (addR64R64Effect 0x10b899 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[2505, 2497]
    (.letOp (n := 2511) (.out 0x10b89c (atFlags StatusFlags.CF (adcR64R64Effect 0x10b89c 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[2495, 2506, 2509]
    (.letOp (n := 2512) (.exec 0x10b89c (fun s => s.RIP = 0x10b89c) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b89c 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2495, 2506, 2509]
    (.letOp (n := 2513) (.out 0x10b89f (addR64R64Effect 0x10b89f 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[2508, 2482]
    (.letOp (n := 2514) (.out 0x10b89f (addR64R64Effect 0x10b89f 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[2508, 2482]
    (.letOp (n := 2515) (.exec 0x10b89f (fun s => s.RIP = 0x10b89f) (addR64R64Effect 0x10b89f 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[2508, 2482]
    (.letOp (n := 2516) (.out 0x10b8a2 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b8a2 11 1)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[2511, 2484, 2514]
    (.letOp (n := 2517) (.exec 0x10b8a2 (fun s => s.RIP = 0x10b8a2) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b8a2 11 1)) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2511, 2484, 2514]
    (.letOp (n := 2518) (.out 0x10b8a5 (addR64M64Effect 0x10b8a5 0 (.sib 4 none 0 (.d32 0x198))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2513, 65]
    (.letOp (n := 2519) (.out 0x10b8a5 (addR64M64Effect 0x10b8a5 0 (.sib 4 none 0 (.d32 0x198))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[2513, 65]
    (.letOp (n := 2520) (.exec 0x10b8a5 (LoadPre 0x10b8a5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x10b8a5 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10b8a5 0 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2513, 65]
    (.letOp (n := 2521) (.out 0x10b8ad (atFlags StatusFlags.CF (adcR64M64Effect 0x10b8ad 11 (.sib 4 none 0 (.d32 0x170)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[2516, 65, 2519]
    (.letOp (n := 2522) (.exec 0x10b8ad (LoadPre 0x10b8ad (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x10b8ad + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10b8ad 11 (.sib 4 none 0 (.d32 0x170)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2516, 65, 2519]
    (.letOp (n := 2523) (.out 0x10b8b5 (addR64R64Effect 0x10b8b5 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[2518, 2449]
    (.letOp (n := 2524) (.out 0x10b8b5 (addR64R64Effect 0x10b8b5 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[2518, 2449]
    (.letOp (n := 2525) (.exec 0x10b8b5 (fun s => s.RIP = 0x10b8b5) (addR64R64Effect 0x10b8b5 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[2518, 2449]
    (.letOp (n := 2526) (.out 0x10b8b8 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b8b8 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[2521, 2524]
    (.letOp (n := 2527) (.exec 0x10b8b8 (fun s => s.RIP = 0x10b8b8) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b8b8 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2521, 2524]
    (.letOp (n := 2528) (.out 0x10b8bc (shldR64R64Effect 0x10b8bc 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[2526, 2523]
    (.letOp (n := 2529) (.exec 0x10b8bc (fun s => s.RIP = 0x10b8bc) (shldR64R64Effect 0x10b8bc 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2526, 2523]
    (.letOp (n := 2530) (.out 0x10b8c1 (shlR64Effect 0x10b8c1 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2523]
    (.letOp (n := 2531) (.exec 0x10b8c1 (fun s => s.RIP = 0x10b8c1) (shlR64Effect 0x10b8c1 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2523]
    (.letOp (n := 2532) (.out 0x10b8c5 (movR64Imm64Effect 0x10b8c5 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2533) (.exec 0x10b8c5 (fun s => s.RIP = 0x10b8c5) (movR64Imm64Effect 0x10b8c5 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 2534) (.out 0x10b8cf (andR64R64Effect 0x10b8cf 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2530, 2532]
    (.letOp (n := 2535) (.exec 0x10b8cf (fun s => s.RIP = 0x10b8cf) (andR64R64Effect 0x10b8cf 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2530, 2532]
    (.letOp (n := 2536) (.out 0x10b8d2 (orR64R64Effect 0x10b8d2 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[2534, 2486]
    (.letOp (n := 2537) (.exec 0x10b8d2 (fun s => s.RIP = 0x10b8d2) (orR64R64Effect 0x10b8d2 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[2534, 2486]
    (.letOp (n := 2538) (.out 0x10b8d5 (movR64Imm64Effect 0x10b8d5 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2539) (.exec 0x10b8d5 (fun s => s.RIP = 0x10b8d5) (movR64Imm64Effect 0x10b8d5 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 2540) (.out 0x10b8df (mulR64Effect 0x10b8df 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2538, 2536]
    (.letOp (n := 2541) (.out 0x10b8df (mulR64Effect 0x10b8df 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2538, 2536]
    (.letOp (n := 2542) (.exec 0x10b8df (fun s => s.RIP = 0x10b8df) (mulR64Effect 0x10b8df 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2538, 2536]
    (b_l10a410_59))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_58 : List UInt8 :=
  [0x48, 0x89, 0xC3, 0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x89, 0xF0, 0x4C, 0x8B, 0xB4, 0x24, 0xF0,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE6, 0x48, 0x01, 0xD8, 0x49, 0x11, 0xD3, 0x48, 0x01, 0xF8, 0x49,
    0x11, 0xCB, 0x48, 0x03, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00, 0x4C, 0x13, 0x9C, 0x24, 0x70, 0x01,
    0x00, 0x00, 0x4C, 0x01, 0xC0, 0x49, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xC1,
    0xE0, 0x04, 0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C,
    0x09, 0xE0, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1] ++ bytes_l10a410_59

theorem code_l10a410_58 : ∀ x ∈ codeRange 0x10b883 bytes_l10a410_58, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb883 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_59

def b_l10a410_57 : Block Op Label signature Reg.count 2457 :=
  .letOp (n := 2457) (.out 0x10b81f (movR64M64Effect 0x10b81f 9 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 2458) (.exec 0x10b81f (LoadPre 0x10b81f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10b81f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b81f 9 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2459) (.out 0x10b824 (mulR64Effect 0x10b824 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[2457, 2455]
    (.letOp (n := 2460) (.out 0x10b824 (mulR64Effect 0x10b824 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[2457, 2455]
    (.letOp (n := 2461) (.exec 0x10b824 (fun s => s.RIP = 0x10b824) (mulR64Effect 0x10b824 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2457, 2455]
    (.letOp (n := 2462) (.exec 0x10b827 (StorePre 0x10b827 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10b827 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b827 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2460, 65]
    (.letOp (n := 2463) (.exec 0x10b82f (StorePre 0x10b82f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10b82f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b82f 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2459, 65]
    (.letOp (n := 2464) (.out 0x10b837 (movR64M64Effect 0x10b837 15 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 2465) (.exec 0x10b837 (LoadPre 0x10b837 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10b837 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b837 15 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2466) (.out 0x10b83f (movR64R64Effect 0x10b83f 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[2464]
    (.letOp (n := 2467) (.exec 0x10b83f (fun s => s.RIP = 0x10b83f) (movR64R64Effect 0x10b83f 0 15) (Reg.operands [.gpr 15] [])) #v[2464]
    (.letOp (n := 2468) (.out 0x10b842 (movR64M64Effect 0x10b842 5 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 2469) (.exec 0x10b842 (LoadPre 0x10b842 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10b842 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b842 5 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2470) (.out 0x10b84a (mulR64Effect 0x10b84a 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[2468, 2466]
    (.letOp (n := 2471) (.out 0x10b84a (mulR64Effect 0x10b84a 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[2468, 2466]
    (.letOp (n := 2472) (.exec 0x10b84a (fun s => s.RIP = 0x10b84a) (mulR64Effect 0x10b84a 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[2468, 2466]
    (.letOp (n := 2473) (.exec 0x10b84d (StorePre 0x10b84d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x10b84d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b84d 2 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2471, 65]
    (.letOp (n := 2474) (.exec 0x10b855 (StorePre 0x10b855 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x10b855 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b855 0 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2470, 65]
    (.letOp (n := 2475) (.out 0x10b85d (movR64M64Effect 0x10b85d 13 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 2476) (.exec 0x10b85d (LoadPre 0x10b85d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10b85d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b85d 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2477) (.out 0x10b862 (movR64R64Effect 0x10b862 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[2475]
    (.letOp (n := 2478) (.exec 0x10b862 (fun s => s.RIP = 0x10b862) (movR64R64Effect 0x10b862 0 13) (Reg.operands [.gpr 13] [])) #v[2475]
    (.letOp (n := 2479) (.out 0x10b865 (mulR64Effect 0x10b865 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2382, 2477]
    (.letOp (n := 2480) (.out 0x10b865 (mulR64Effect 0x10b865 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2382, 2477]
    (.letOp (n := 2481) (.exec 0x10b865 (fun s => s.RIP = 0x10b865) (mulR64Effect 0x10b865 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2382, 2477]
    (.letOp (n := 2482) (.out 0x10b868 (movR64R64Effect 0x10b868 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[2479]
    (.letOp (n := 2483) (.exec 0x10b868 (fun s => s.RIP = 0x10b868) (movR64R64Effect 0x10b868 7 0) (Reg.operands [.gpr 0] [])) #v[2479]
    (.letOp (n := 2484) (.out 0x10b86b (movR64R64Effect 0x10b86b 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2480]
    (.letOp (n := 2485) (.exec 0x10b86b (fun s => s.RIP = 0x10b86b) (movR64R64Effect 0x10b86b 1 2) (Reg.operands [.gpr 2] [])) #v[2480]
    (.letOp (n := 2486) (.out 0x10b86e (andR32Imm8Effect 0x10b86e 4 12 0xf) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[2453]
    (.letOp (n := 2487) (.exec 0x10b86e (fun s => s.RIP = 0x10b86e) (andR32Imm8Effect 0x10b86e 4 12 0xf) (Reg.operands [.gpr 12] [])) #v[2453]
    (.letOp (n := 2488) (.out 0x10b872 (movR64R64Effect 0x10b872 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[2378]
    (.letOp (n := 2489) (.exec 0x10b872 (fun s => s.RIP = 0x10b872) (movR64R64Effect 0x10b872 0 3) (Reg.operands [.gpr 3] [])) #v[2378]
    (.letOp (n := 2490) (.out 0x10b875 (movR64M64Effect 0x10b875 10 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 2491) (.exec 0x10b875 (LoadPre 0x10b875 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10b875 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b875 10 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2492) (.out 0x10b87d (mulR64Effect 0x10b87d 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[2490, 2488]
    (.letOp (n := 2493) (.out 0x10b87d (mulR64Effect 0x10b87d 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[2490, 2488]
    (.letOp (n := 2494) (.exec 0x10b87d (fun s => s.RIP = 0x10b87d) (mulR64Effect 0x10b87d 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2490, 2488]
    (.letOp (n := 2495) (.out 0x10b880 (movR64R64Effect 0x10b880 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2493]
    (.letOp (n := 2496) (.exec 0x10b880 (fun s => s.RIP = 0x10b880) (movR64R64Effect 0x10b880 11 2) (Reg.operands [.gpr 2] [])) #v[2493]
    (b_l10a410_58))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_57 : List UInt8 :=
  [0x4C, 0x8B, 0x4C, 0x24, 0x50, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00,
    0x4C, 0x89, 0xF8, 0x48, 0x8B, 0xAC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x48, 0x89,
    0x94, 0x24, 0x70, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00, 0x4C, 0x8B,
    0x6C, 0x24, 0x38, 0x4C, 0x89, 0xE8, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xC7, 0x48, 0x89, 0xD1, 0x41,
    0x83, 0xE4, 0x0F, 0x48, 0x89, 0xD8, 0x4C, 0x8B, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0xF7,
    0xE2, 0x49, 0x89, 0xD3] ++ bytes_l10a410_58

theorem code_l10a410_57 : ∀ x ∈ codeRange 0x10b81f bytes_l10a410_57, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb81f 100 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_58

def b_l10a410_56 : Block Op Label signature Reg.count 2411 :=
  .letOp (n := 2411) (.out 0x10b7ca (movR64R64Effect 0x10b7ca 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2359]
    (.letOp (n := 2412) (.exec 0x10b7ca (fun s => s.RIP = 0x10b7ca) (movR64R64Effect 0x10b7ca 0 11) (Reg.operands [.gpr 11] [])) #v[2359]
    (.letOp (n := 2413) (.out 0x10b7cd (movR64Imm64Effect 0x10b7cd 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2414) (.exec 0x10b7cd (fun s => s.RIP = 0x10b7cd) (movR64Imm64Effect 0x10b7cd 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2415) (.out 0x10b7d7 (mulR64Effect 0x10b7d7 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2413, 2411]
    (.letOp (n := 2416) (.out 0x10b7d7 (mulR64Effect 0x10b7d7 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2413, 2411]
    (.letOp (n := 2417) (.exec 0x10b7d7 (fun s => s.RIP = 0x10b7d7) (mulR64Effect 0x10b7d7 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2413, 2411]
    (.letOp (n := 2418) (.out 0x10b7da (addR64R64Effect 0x10b7da 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[2409, 2398]
    (.letOp (n := 2419) (.out 0x10b7da (addR64R64Effect 0x10b7da 15 12) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 12] []) (.flag .CF)) #v[2409, 2398]
    (.letOp (n := 2420) (.exec 0x10b7da (fun s => s.RIP = 0x10b7da) (addR64R64Effect 0x10b7da 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[2409, 2398]
    (.letOp (n := 2421) (.out 0x10b7dd (atFlags StatusFlags.CF (adcR64R64Effect 0x10b7dd 8 6)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2407, 2396, 2419]
    (.letOp (n := 2422) (.exec 0x10b7dd (fun s => s.RIP = 0x10b7dd) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b7dd 8 6)) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2407, 2396, 2419]
    (.letOp (n := 2423) (.out 0x10b7e0 (addR64R64Effect 0x10b7e0 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[2418, 2389]
    (.letOp (n := 2424) (.out 0x10b7e0 (addR64R64Effect 0x10b7e0 15 10) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 10] []) (.flag .CF)) #v[2418, 2389]
    (.letOp (n := 2425) (.exec 0x10b7e0 (fun s => s.RIP = 0x10b7e0) (addR64R64Effect 0x10b7e0 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[2418, 2389]
    (.letOp (n := 2426) (.out 0x10b7e3 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b7e3 8 13)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2421, 2387, 2424]
    (.letOp (n := 2427) (.exec 0x10b7e3 (fun s => s.RIP = 0x10b7e3) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b7e3 8 13)) (Reg.operands [.gpr 8, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2421, 2387, 2424]
    (.letOp (n := 2428) (.out 0x10b7e6 (addR64R64Effect 0x10b7e6 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[2423, 2376]
    (.letOp (n := 2429) (.out 0x10b7e6 (addR64R64Effect 0x10b7e6 15 14) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 14] []) (.flag .CF)) #v[2423, 2376]
    (.letOp (n := 2430) (.exec 0x10b7e6 (fun s => s.RIP = 0x10b7e6) (addR64R64Effect 0x10b7e6 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[2423, 2376]
    (.letOp (n := 2431) (.out 0x10b7e9 (atFlags StatusFlags.CF (adcR64M64Effect 0x10b7e9 8 (.sib 4 none 0 (.d32 0x130)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[2426, 65, 2429]
    (.letOp (n := 2432) (.exec 0x10b7e9 (LoadPre 0x10b7e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10b7e9 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10b7e9 8 (.sib 4 none 0 (.d32 0x130)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2426, 65, 2429]
    (.letOp (n := 2433) (.out 0x10b7f1 (addR64M64Effect 0x10b7f1 15 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[2428, 65]
    (.letOp (n := 2434) (.out 0x10b7f1 (addR64M64Effect 0x10b7f1 15 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[2428, 65]
    (.letOp (n := 2435) (.exec 0x10b7f1 (LoadPre 0x10b7f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10b7f1 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10b7f1 15 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[2428, 65]
    (.letOp (n := 2436) (.out 0x10b7f9 (atFlags StatusFlags.CF (adcR64M64Effect 0x10b7f9 8 (.sib 4 none 0 (.d8 0x40)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[2431, 65, 2434]
    (.letOp (n := 2437) (.exec 0x10b7f9 (LoadPre 0x10b7f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10b7f9 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10b7f9 8 (.sib 4 none 0 (.d8 0x40)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2431, 65, 2434]
    (.letOp (n := 2438) (.out 0x10b7fe (addR64R64Effect 0x10b7fe 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[2433, 2415]
    (.letOp (n := 2439) (.out 0x10b7fe (addR64R64Effect 0x10b7fe 15 0) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 0] []) (.flag .CF)) #v[2433, 2415]
    (.letOp (n := 2440) (.exec 0x10b7fe (fun s => s.RIP = 0x10b7fe) (addR64R64Effect 0x10b7fe 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[2433, 2415]
    (.letOp (n := 2441) (.out 0x10b801 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b801 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2436, 2416, 2439]
    (.letOp (n := 2442) (.exec 0x10b801 (fun s => s.RIP = 0x10b801) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b801 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2436, 2416, 2439]
    (.letOp (n := 2443) (.out 0x10b804 (addR64R64Effect 0x10b804 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9] []) (.reg (.gpr 15))) #v[2438, 2361]
    (.letOp (n := 2444) (.out 0x10b804 (addR64R64Effect 0x10b804 15 9) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 9] []) (.flag .CF)) #v[2438, 2361]
    (.letOp (n := 2445) (.exec 0x10b804 (fun s => s.RIP = 0x10b804) (addR64R64Effect 0x10b804 15 9) (Reg.operands [.gpr 15, .gpr 9] [])) #v[2438, 2361]
    (.letOp (n := 2446) (.exec 0x10b807 (StorePre 0x10b807 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10b807 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b807 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[2443, 65]
    (.letOp (n := 2447) (.out 0x10b80c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b80c 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2441, 2444]
    (.letOp (n := 2448) (.exec 0x10b80c (fun s => s.RIP = 0x10b80c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b80c 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2441, 2444]
    (.letOp (n := 2449) (.out 0x10b810 (shldR64R64Effect 0x10b810 5 8 15 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2447, 2443]
    (.letOp (n := 2450) (.exec 0x10b810 (fun s => s.RIP = 0x10b810) (shldR64R64Effect 0x10b810 5 8 15 12) (Reg.operands [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2447, 2443]
    (.letOp (n := 2451) (.out 0x10b815 (movR64R64Effect 0x10b815 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15] []) (.reg (.gpr 12))) #v[2443]
    (.letOp (n := 2452) (.exec 0x10b815 (fun s => s.RIP = 0x10b815) (movR64R64Effect 0x10b815 12 15) (Reg.operands [.gpr 15] [])) #v[2443]
    (.letOp (n := 2453) (.out 0x10b818 (shrR64Effect 0x10b818 4 12 48) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[2451]
    (.letOp (n := 2454) (.exec 0x10b818 (fun s => s.RIP = 0x10b818) (shrR64Effect 0x10b818 4 12 48) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2451]
    (.letOp (n := 2455) (.out 0x10b81c (movR64R64Effect 0x10b81c 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[2400]
    (.letOp (n := 2456) (.exec 0x10b81c (fun s => s.RIP = 0x10b81c) (movR64R64Effect 0x10b81c 0 1) (Reg.operands [.gpr 1] [])) #v[2400]
    (b_l10a410_57))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_56 : List UInt8 :=
  [0x4C, 0x89, 0xD8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x4D, 0x01, 0xE7, 0x49, 0x11, 0xF0, 0x4D, 0x01, 0xD7, 0x4D, 0x11, 0xE8, 0x4D, 0x01, 0xF7, 0x4C,
    0x13, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x4C, 0x03, 0xBC, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C,
    0x13, 0x44, 0x24, 0x40, 0x49, 0x01, 0xC7, 0x49, 0x11, 0xD0, 0x4D, 0x01, 0xCF, 0x4C, 0x89, 0x7C,
    0x24, 0x40, 0x49, 0x83, 0xD0, 0x00, 0x4D, 0x0F, 0xA4, 0xF8, 0x0C, 0x4D, 0x89, 0xFC, 0x49, 0xC1,
    0xEC, 0x30, 0x48, 0x89, 0xC8] ++ bytes_l10a410_57

theorem code_l10a410_56 : ∀ x ∈ codeRange 0x10b7ca bytes_l10a410_56, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb7ca 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_57

def b_l10a410_55 : Block Op Label signature Reg.count 2369 :=
  .letOp (n := 2369) (.exec 0x10b77b (StorePre 0x10b77b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10b77b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b77b 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2365, 65]
    (.letOp (n := 2370) (.out 0x10b783 (movR64M64Effect 0x10b783 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2371) (.exec 0x10b783 (LoadPre 0x10b783 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10b783 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b783 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2372) (.out 0x10b788 (mulR64Effect 0x10b788 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[2239, 2370]
    (.letOp (n := 2373) (.out 0x10b788 (mulR64Effect 0x10b788 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[2239, 2370]
    (.letOp (n := 2374) (.exec 0x10b788 (fun s => s.RIP = 0x10b788) (mulR64Effect 0x10b788 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2239, 2370]
    (.letOp (n := 2375) (.exec 0x10b78b (StorePre 0x10b78b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10b78b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b78b 2 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2373, 65]
    (.letOp (n := 2376) (.out 0x10b793 (movR64R64Effect 0x10b793 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[2372]
    (.letOp (n := 2377) (.exec 0x10b793 (fun s => s.RIP = 0x10b793) (movR64R64Effect 0x10b793 14 0) (Reg.operands [.gpr 0] [])) #v[2372]
    (.letOp (n := 2378) (.out 0x10b796 (movR64M64Effect 0x10b796 3 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 2379) (.exec 0x10b796 (LoadPre 0x10b796 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10b796 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b796 3 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2380) (.out 0x10b79b (movR64R64Effect 0x10b79b 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[2378]
    (.letOp (n := 2381) (.exec 0x10b79b (fun s => s.RIP = 0x10b79b) (movR64R64Effect 0x10b79b 0 3) (Reg.operands [.gpr 3] [])) #v[2378]
    (.letOp (n := 2382) (.out 0x10b79e (movR64M64Effect 0x10b79e 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 2383) (.exec 0x10b79e (LoadPre 0x10b79e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10b79e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b79e 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2384) (.out 0x10b7a3 (mulR64Effect 0x10b7a3 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2382, 2380]
    (.letOp (n := 2385) (.out 0x10b7a3 (mulR64Effect 0x10b7a3 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2382, 2380]
    (.letOp (n := 2386) (.exec 0x10b7a3 (fun s => s.RIP = 0x10b7a3) (mulR64Effect 0x10b7a3 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2382, 2380]
    (.letOp (n := 2387) (.out 0x10b7a6 (movR64R64Effect 0x10b7a6 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2385]
    (.letOp (n := 2388) (.exec 0x10b7a6 (fun s => s.RIP = 0x10b7a6) (movR64R64Effect 0x10b7a6 13 2) (Reg.operands [.gpr 2] [])) #v[2385]
    (.letOp (n := 2389) (.out 0x10b7a9 (movR64R64Effect 0x10b7a9 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2384]
    (.letOp (n := 2390) (.exec 0x10b7a9 (fun s => s.RIP = 0x10b7a9) (movR64R64Effect 0x10b7a9 10 0) (Reg.operands [.gpr 0] [])) #v[2384]
    (.letOp (n := 2391) (.out 0x10b7ac (movR64M64Effect 0x10b7ac 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2392) (.exec 0x10b7ac (LoadPre 0x10b7ac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10b7ac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b7ac 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2393) (.out 0x10b7b1 (mulR64Effect 0x10b7b1 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[2306, 2391]
    (.letOp (n := 2394) (.out 0x10b7b1 (mulR64Effect 0x10b7b1 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[2306, 2391]
    (.letOp (n := 2395) (.exec 0x10b7b1 (fun s => s.RIP = 0x10b7b1) (mulR64Effect 0x10b7b1 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[2306, 2391]
    (.letOp (n := 2396) (.out 0x10b7b4 (movR64R64Effect 0x10b7b4 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2394]
    (.letOp (n := 2397) (.exec 0x10b7b4 (fun s => s.RIP = 0x10b7b4) (movR64R64Effect 0x10b7b4 6 2) (Reg.operands [.gpr 2] [])) #v[2394]
    (.letOp (n := 2398) (.out 0x10b7b7 (movR64R64Effect 0x10b7b7 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[2393]
    (.letOp (n := 2399) (.exec 0x10b7b7 (fun s => s.RIP = 0x10b7b7) (movR64R64Effect 0x10b7b7 12 0) (Reg.operands [.gpr 0] [])) #v[2393]
    (.letOp (n := 2400) (.out 0x10b7ba (movR64M64Effect 0x10b7ba 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 2401) (.exec 0x10b7ba (LoadPre 0x10b7ba (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10b7ba + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10b7ba 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2402) (.out 0x10b7be (movR64R64Effect 0x10b7be 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[2400]
    (.letOp (n := 2403) (.exec 0x10b7be (fun s => s.RIP = 0x10b7be) (movR64R64Effect 0x10b7be 0 1) (Reg.operands [.gpr 1] [])) #v[2400]
    (.letOp (n := 2404) (.out 0x10b7c1 (mulR64Effect 0x10b7c1 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[2252, 2402]
    (.letOp (n := 2405) (.out 0x10b7c1 (mulR64Effect 0x10b7c1 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[2252, 2402]
    (.letOp (n := 2406) (.exec 0x10b7c1 (fun s => s.RIP = 0x10b7c1) (mulR64Effect 0x10b7c1 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[2252, 2402]
    (.letOp (n := 2407) (.out 0x10b7c4 (movR64R64Effect 0x10b7c4 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2405]
    (.letOp (n := 2408) (.exec 0x10b7c4 (fun s => s.RIP = 0x10b7c4) (movR64R64Effect 0x10b7c4 8 2) (Reg.operands [.gpr 2] [])) #v[2405]
    (.letOp (n := 2409) (.out 0x10b7c7 (movR64R64Effect 0x10b7c7 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[2404]
    (.letOp (n := 2410) (.exec 0x10b7c7 (fun s => s.RIP = 0x10b7c7) (movR64R64Effect 0x10b7c7 15 0) (Reg.operands [.gpr 0] [])) #v[2404]
    (b_l10a410_56))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_55 : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x49, 0xF7, 0xE2,
    0x48, 0x89, 0x94, 0x24, 0x30, 0x01, 0x00, 0x00, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x5C, 0x24, 0x78,
    0x48, 0x89, 0xD8, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xD5, 0x49, 0x89,
    0xC2, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x48,
    0x8B, 0x0C, 0x24, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC7] ++ bytes_l10a410_56

theorem code_l10a410_55 : ∀ x ∈ codeRange 0x10b77b bytes_l10a410_55, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb77b 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_56

def b_l10a410_54 : Block Op Label signature Reg.count 2326 :=
  .letOp (n := 2326) (.out 0x10b716 (andR64R64Effect 0x10b716 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[2316, 2324]
    (.letOp (n := 2327) (.exec 0x10b716 (fun s => s.RIP = 0x10b716) (andR64R64Effect 0x10b716 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[2316, 2324]
    (.letOp (n := 2328) (.out 0x10b719 (movR64Imm64Effect 0x10b719 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2329) (.exec 0x10b719 (fun s => s.RIP = 0x10b719) (movR64Imm64Effect 0x10b719 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2330) (.out 0x10b723 (mulR64Effect 0x10b723 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2328, 2326]
    (.letOp (n := 2331) (.out 0x10b723 (mulR64Effect 0x10b723 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2328, 2326]
    (.letOp (n := 2332) (.exec 0x10b723 (fun s => s.RIP = 0x10b723) (mulR64Effect 0x10b723 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2328, 2326]
    (.letOp (n := 2333) (.out 0x10b726 (movR64Imm64Effect 0x10b726 12 0x5fffffffffffa) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 2334) (.exec 0x10b726 (fun s => s.RIP = 0x10b726) (movR64Imm64Effect 0x10b726 12 0x5fffffffffffa) (Reg.operands [] [])) #v[]
    (.letOp (n := 2335) (.out 0x10b730 (addR64R64Effect 0x10b730 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[2215, 2333]
    (.letOp (n := 2336) (.exec 0x10b730 (fun s => s.RIP = 0x10b730) (addR64R64Effect 0x10b730 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[2215, 2333]
    (.letOp (n := 2337) (.exec 0x10b733 (StorePre 0x10b733 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10b733 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b733 15 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[2335, 65]
    (.letOp (n := 2338) (.out 0x10b73b (addR64R64Effect 0x10b73b 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[2311, 2299]
    (.letOp (n := 2339) (.out 0x10b73b (addR64R64Effect 0x10b73b 13 14) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 14] []) (.flag .CF)) #v[2311, 2299]
    (.letOp (n := 2340) (.exec 0x10b73b (fun s => s.RIP = 0x10b73b) (addR64R64Effect 0x10b73b 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[2311, 2299]
    (.letOp (n := 2341) (.out 0x10b73e (atFlags StatusFlags.CF (adcR64R64Effect 0x10b73e 9 7)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[2309, 2297, 2339]
    (.letOp (n := 2342) (.exec 0x10b73e (fun s => s.RIP = 0x10b73e) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b73e 9 7)) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2309, 2297, 2339]
    (.letOp (n := 2343) (.out 0x10b741 (addR64M64Effect 0x10b741 13 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[2338, 65]
    (.letOp (n := 2344) (.out 0x10b741 (addR64M64Effect 0x10b741 13 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[2338, 65]
    (.letOp (n := 2345) (.exec 0x10b741 (LoadPre 0x10b741 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10b741 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10b741 13 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[2338, 65]
    (.letOp (n := 2346) (.out 0x10b749 (atFlags StatusFlags.CF (adcR64M64Effect 0x10b749 9 (.sib 4 none 0 (.d32 0x90)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[2341, 65, 2344]
    (.letOp (n := 2347) (.exec 0x10b749 (LoadPre 0x10b749 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10b749 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10b749 9 (.sib 4 none 0 (.d32 0x90)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2341, 65, 2344]
    (.letOp (n := 2348) (.out 0x10b751 (addR64M64Effect 0x10b751 13 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[2343, 65]
    (.letOp (n := 2349) (.out 0x10b751 (addR64M64Effect 0x10b751 13 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[2343, 65]
    (.letOp (n := 2350) (.exec 0x10b751 (LoadPre 0x10b751 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10b751 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10b751 13 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[2343, 65]
    (.letOp (n := 2351) (.out 0x10b756 (atFlags StatusFlags.CF (adcR64M64Effect 0x10b756 9 (.sib 4 none 0 (.d8 0x20)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[2346, 65, 2349]
    (.letOp (n := 2352) (.exec 0x10b756 (LoadPre 0x10b756 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10b756 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10b756 9 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2346, 65, 2349]
    (.letOp (n := 2353) (.out 0x10b75b (addR64R64Effect 0x10b75b 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[2348, 2330]
    (.letOp (n := 2354) (.out 0x10b75b (addR64R64Effect 0x10b75b 13 0) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 0] []) (.flag .CF)) #v[2348, 2330]
    (.letOp (n := 2355) (.exec 0x10b75b (fun s => s.RIP = 0x10b75b) (addR64R64Effect 0x10b75b 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2348, 2330]
    (.letOp (n := 2356) (.exec 0x10b75e (StorePre 0x10b75e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10b75e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b75e 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[2353, 65]
    (.letOp (n := 2357) (.out 0x10b763 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b763 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[2351, 2331, 2354]
    (.letOp (n := 2358) (.exec 0x10b763 (fun s => s.RIP = 0x10b763) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b763 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2351, 2331, 2354]
    (.letOp (n := 2359) (.out 0x10b766 (shldR64R64Effect 0x10b766 5 11 6 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[2320, 2322]
    (.letOp (n := 2360) (.exec 0x10b766 (fun s => s.RIP = 0x10b766) (shldR64R64Effect 0x10b766 5 11 6 12) (Reg.operands [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2320, 2322]
    (.letOp (n := 2361) (.out 0x10b76b (shldR64R64Effect 0x10b76b 5 9 13 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2357, 2353]
    (.letOp (n := 2362) (.exec 0x10b76b (fun s => s.RIP = 0x10b76b) (shldR64R64Effect 0x10b76b 5 9 13 12) (Reg.operands [.gpr 9, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2357, 2353]
    (.letOp (n := 2363) (.out 0x10b770 (movR64R64Effect 0x10b770 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[2290]
    (.letOp (n := 2364) (.exec 0x10b770 (fun s => s.RIP = 0x10b770) (movR64R64Effect 0x10b770 0 1) (Reg.operands [.gpr 1] [])) #v[2290]
    (.letOp (n := 2365) (.out 0x10b773 (mulR64Effect 0x10b773 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[2235, 2363]
    (.letOp (n := 2366) (.out 0x10b773 (mulR64Effect 0x10b773 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[2235, 2363]
    (.letOp (n := 2367) (.exec 0x10b773 (fun s => s.RIP = 0x10b773) (mulR64Effect 0x10b773 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[2235, 2363]
    (.letOp (n := 2368) (.exec 0x10b776 (StorePre 0x10b776 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10b776 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b776 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2366, 65]
    (b_l10a410_55)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_54 : List UInt8 :=
  [0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x49, 0xBC, 0xFA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x05, 0x00, 0x4D, 0x01, 0xE7, 0x4C, 0x89, 0xBC,
    0x24, 0xE8, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xF5, 0x49, 0x11, 0xF9, 0x4C, 0x03, 0xAC, 0x24, 0x30,
    0x01, 0x00, 0x00, 0x4C, 0x13, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x03, 0x6C, 0x24, 0x40,
    0x4C, 0x13, 0x4C, 0x24, 0x20, 0x49, 0x01, 0xC5, 0x4C, 0x89, 0x6C, 0x24, 0x20, 0x49, 0x11, 0xD1,
    0x49, 0x0F, 0xA4, 0xF3, 0x0C, 0x4D, 0x0F, 0xA4, 0xE9, 0x0C, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0xE3,
    0x48, 0x89, 0x54, 0x24, 0x40] ++ bytes_l10a410_55

theorem code_l10a410_54 : ∀ x ∈ codeRange 0x10b716 bytes_l10a410_54, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb716 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_55

def b_l10a410_53 : Block Op Label signature Reg.count 2287 :=
  .letOp (n := 2287) (.exec 0x10b6b8 (StorePre 0x10b6b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10b6b8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b6b8 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2283, 65]
    (.letOp (n := 2288) (.out 0x10b6c0 (movR64M64Effect 0x10b6c0 1 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 2289) (.exec 0x10b6c0 (LoadPre 0x10b6c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10b6c0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b6c0 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2290) (.out 0x10b6c8 (addR64M64Effect 0x10b6c8 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[2288, 65]
    (.letOp (n := 2291) (.exec 0x10b6c8 (LoadPre 0x10b6c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10b6c8 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10b6c8 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2288, 65]
    (.letOp (n := 2292) (.out 0x10b6cd (movR64R64Effect 0x10b6cd 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[2261]
    (.letOp (n := 2293) (.exec 0x10b6cd (fun s => s.RIP = 0x10b6cd) (movR64R64Effect 0x10b6cd 0 14) (Reg.operands [.gpr 14] [])) #v[2261]
    (.letOp (n := 2294) (.out 0x10b6d0 (mulR64Effect 0x10b6d0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2243, 2292]
    (.letOp (n := 2295) (.out 0x10b6d0 (mulR64Effect 0x10b6d0 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2243, 2292]
    (.letOp (n := 2296) (.exec 0x10b6d0 (fun s => s.RIP = 0x10b6d0) (mulR64Effect 0x10b6d0 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2243, 2292]
    (.letOp (n := 2297) (.out 0x10b6d3 (movR64R64Effect 0x10b6d3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2295]
    (.letOp (n := 2298) (.exec 0x10b6d3 (fun s => s.RIP = 0x10b6d3) (movR64R64Effect 0x10b6d3 7 2) (Reg.operands [.gpr 2] [])) #v[2295]
    (.letOp (n := 2299) (.out 0x10b6d6 (movR64R64Effect 0x10b6d6 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[2294]
    (.letOp (n := 2300) (.exec 0x10b6d6 (fun s => s.RIP = 0x10b6d6) (movR64R64Effect 0x10b6d6 14 0) (Reg.operands [.gpr 0] [])) #v[2294]
    (.letOp (n := 2301) (.out 0x10b6d9 (movR64R64Effect 0x10b6d9 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2256]
    (.letOp (n := 2302) (.exec 0x10b6d9 (fun s => s.RIP = 0x10b6d9) (movR64R64Effect 0x10b6d9 0 9) (Reg.operands [.gpr 9] [])) #v[2256]
    (.letOp (n := 2303) (.out 0x10b6dc (mulR64Effect 0x10b6dc 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[2248, 2301]
    (.letOp (n := 2304) (.out 0x10b6dc (mulR64Effect 0x10b6dc 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[2248, 2301]
    (.letOp (n := 2305) (.exec 0x10b6dc (fun s => s.RIP = 0x10b6dc) (mulR64Effect 0x10b6dc 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[2248, 2301]
    (.letOp (n := 2306) (.out 0x10b6df (movR64R64Effect 0x10b6df 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[2248]
    (.letOp (n := 2307) (.exec 0x10b6df (fun s => s.RIP = 0x10b6df) (movR64R64Effect 0x10b6df 8 11) (Reg.operands [.gpr 11] [])) #v[2248]
    (.letOp (n := 2308) (.exec 0x10b6e2 (StorePre 0x10b6e2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10b6e2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b6e2 11 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[2248, 65]
    (.letOp (n := 2309) (.out 0x10b6ea (movR64R64Effect 0x10b6ea 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2304]
    (.letOp (n := 2310) (.exec 0x10b6ea (fun s => s.RIP = 0x10b6ea) (movR64R64Effect 0x10b6ea 9 2) (Reg.operands [.gpr 2] [])) #v[2304]
    (.letOp (n := 2311) (.out 0x10b6ed (movR64R64Effect 0x10b6ed 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[2303]
    (.letOp (n := 2312) (.exec 0x10b6ed (fun s => s.RIP = 0x10b6ed) (movR64R64Effect 0x10b6ed 13 0) (Reg.operands [.gpr 0] [])) #v[2303]
    (.letOp (n := 2313) (.out 0x10b6f0 (movR64R64Effect 0x10b6f0 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[2290]
    (.letOp (n := 2314) (.exec 0x10b6f0 (fun s => s.RIP = 0x10b6f0) (movR64R64Effect 0x10b6f0 0 1) (Reg.operands [.gpr 1] [])) #v[2290]
    (.letOp (n := 2315) (.exec 0x10b6f3 (StorePre 0x10b6f3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10b6f3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b6f3 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2290, 65]
    (.letOp (n := 2316) (.out 0x10b6fb (mulR64Effect 0x10b6fb 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[2252, 2313]
    (.letOp (n := 2317) (.out 0x10b6fb (mulR64Effect 0x10b6fb 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[2252, 2313]
    (.letOp (n := 2318) (.exec 0x10b6fb (fun s => s.RIP = 0x10b6fb) (mulR64Effect 0x10b6fb 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[2252, 2313]
    (.letOp (n := 2319) (.exec 0x10b6fe (StorePre 0x10b6fe 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10b6fe + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b6fe 5 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[2252, 65]
    (.letOp (n := 2320) (.out 0x10b706 (movR64R64Effect 0x10b706 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2317]
    (.letOp (n := 2321) (.exec 0x10b706 (fun s => s.RIP = 0x10b706) (movR64R64Effect 0x10b706 11 2) (Reg.operands [.gpr 2] [])) #v[2317]
    (.letOp (n := 2322) (.out 0x10b709 (movR64R64Effect 0x10b709 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2316]
    (.letOp (n := 2323) (.exec 0x10b709 (fun s => s.RIP = 0x10b709) (movR64R64Effect 0x10b709 6 0) (Reg.operands [.gpr 0] [])) #v[2316]
    (.letOp (n := 2324) (.out 0x10b70c (movR64Imm64Effect 0x10b70c 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2325) (.exec 0x10b70c (fun s => s.RIP = 0x10b70c) (movR64Imm64Effect 0x10b70c 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l10a410_54)))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_53 : List UInt8 :=
  [0x48, 0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00,
    0x48, 0x03, 0x4C, 0x24, 0x48, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD7, 0x49, 0x89,
    0xC6, 0x4C, 0x89, 0xC8, 0x49, 0xF7, 0xE3, 0x4D, 0x89, 0xD8, 0x4C, 0x89, 0x9C, 0x24, 0x88, 0x00,
    0x00, 0x00, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC5, 0x48, 0x89, 0xC8, 0x48, 0x89, 0x8C, 0x24, 0x00,
    0x01, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xAC, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x49, 0x89,
    0xD3, 0x48, 0x89, 0xC6, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] ++ bytes_l10a410_54

theorem code_l10a410_53 : ∀ x ∈ codeRange 0x10b6b8 bytes_l10a410_53, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb6b8 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_54

def b_l10a410_52 : Block Op Label signature Reg.count 2254 :=
  .letOp (n := 2254) (.out 0x10b656 (movR64M64Effect 0x10b656 9 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 2255) (.exec 0x10b656 (LoadPre 0x10b656 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10b656 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10b656 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2256) (.out 0x10b65a (addR64M64Effect 0x10b65a 9 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[2254, 65]
    (.letOp (n := 2257) (.exec 0x10b65a (LoadPre 0x10b65a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10b65a + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10b65a 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[2254, 65]
    (.letOp (n := 2258) (.exec 0x10b65f (StorePre 0x10b65f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10b65f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10b65f 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[2256, 65]
    (.letOp (n := 2259) (.out 0x10b663 (movR64M64Effect 0x10b663 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 2260) (.exec 0x10b663 (LoadPre 0x10b663 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10b663 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b663 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2261) (.out 0x10b668 (addR64M64Effect 0x10b668 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[2259, 65]
    (.letOp (n := 2262) (.exec 0x10b668 (LoadPre 0x10b668 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10b668 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10b668 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[2259, 65]
    (.letOp (n := 2263) (.exec 0x10b66d (StorePre 0x10b66d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10b66d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b66d 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[2261, 65]
    (.letOp (n := 2264) (.out 0x10b672 (movR64M64Effect 0x10b672 8 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 2265) (.exec 0x10b672 (LoadPre 0x10b672 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10b672 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b672 8 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2266) (.out 0x10b677 (addR64M64Effect 0x10b677 8 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[2264, 65]
    (.letOp (n := 2267) (.exec 0x10b677 (LoadPre 0x10b677 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10b677 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10b677 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[2264, 65]
    (.letOp (n := 2268) (.exec 0x10b67c (StorePre 0x10b67c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10b67c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b67c 8 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[2266, 65]
    (.letOp (n := 2269) (.out 0x10b681 (movR64M64Effect 0x10b681 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2270) (.exec 0x10b681 (LoadPre 0x10b681 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10b681 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b681 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2271) (.out 0x10b686 (addR64M64Effect 0x10b686 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2269, 65]
    (.letOp (n := 2272) (.exec 0x10b686 (LoadPre 0x10b686 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10b686 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10b686 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2269, 65]
    (.letOp (n := 2273) (.exec 0x10b68b (StorePre 0x10b68b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10b68b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b68b 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2271, 65]
    (.letOp (n := 2274) (.out 0x10b690 (mulR64Effect 0x10b690 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[2235, 2271]
    (.letOp (n := 2275) (.out 0x10b690 (mulR64Effect 0x10b690 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[2235, 2271]
    (.letOp (n := 2276) (.exec 0x10b690 (fun s => s.RIP = 0x10b690) (mulR64Effect 0x10b690 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[2235, 2271]
    (.letOp (n := 2277) (.exec 0x10b693 (StorePre 0x10b693 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10b693 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b693 3 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[2235, 65]
    (.letOp (n := 2278) (.exec 0x10b698 (StorePre 0x10b698 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10b698 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b698 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2275, 65]
    (.letOp (n := 2279) (.exec 0x10b69d (StorePre 0x10b69d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10b69d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b69d 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2274, 65]
    (.letOp (n := 2280) (.out 0x10b6a2 (movR64R64Effect 0x10b6a2 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2266]
    (.letOp (n := 2281) (.exec 0x10b6a2 (fun s => s.RIP = 0x10b6a2) (movR64R64Effect 0x10b6a2 0 8) (Reg.operands [.gpr 8] [])) #v[2266]
    (.letOp (n := 2282) (.out 0x10b6a5 (mulR64Effect 0x10b6a5 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[2239, 2280]
    (.letOp (n := 2283) (.out 0x10b6a5 (mulR64Effect 0x10b6a5 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[2239, 2280]
    (.letOp (n := 2284) (.exec 0x10b6a5 (fun s => s.RIP = 0x10b6a5) (mulR64Effect 0x10b6a5 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2239, 2280]
    (.letOp (n := 2285) (.exec 0x10b6a8 (StorePre 0x10b6a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10b6a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b6a8 10 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[2239, 65]
    (.letOp (n := 2286) (.exec 0x10b6b0 (StorePre 0x10b6b0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10b6b0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b6b0 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2282, 65]
    (b_l10a410_53)))))))))))))))))))))))))))))))))

def bytes_l10a410_52 : List UInt8 :=
  [0x4C, 0x8B, 0x0C, 0x24, 0x4C, 0x03, 0x4C, 0x24, 0x18, 0x4C, 0x89, 0x0C, 0x24, 0x4C, 0x8B, 0x74,
    0x24, 0x10, 0x4C, 0x03, 0x74, 0x24, 0x08, 0x4C, 0x89, 0x74, 0x24, 0x10, 0x4C, 0x8B, 0x44, 0x24,
    0x78, 0x4C, 0x03, 0x44, 0x24, 0x30, 0x4C, 0x89, 0x44, 0x24, 0x78, 0x48, 0x8B, 0x44, 0x24, 0x38,
    0x48, 0x03, 0x44, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0x5C,
    0x24, 0x50, 0x48, 0x89, 0x54, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x40, 0x4C, 0x89, 0xC0, 0x49,
    0xF7, 0xE2, 0x4C, 0x89, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x30, 0x01,
    0x00, 0x00] ++ bytes_l10a410_53

theorem code_l10a410_52 : ∀ x ∈ codeRange 0x10b656 bytes_l10a410_52, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb656 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_53

def b_l10a410_51 : Block Op Label signature Reg.count 2219 :=
  .letOp (n := 2219) (.out 0x10b5d7 (addR64R64Effect 0x10b5d7 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2179, 2217]
    (.letOp (n := 2220) (.exec 0x10b5d7 (fun s => s.RIP = 0x10b5d7) (addR64R64Effect 0x10b5d7 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2179, 2217]
    (.letOp (n := 2221) (.exec 0x10b5da (StorePre 0x10b5da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10b5da + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b5da 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2219, 65]
    (.letOp (n := 2222) (.out 0x10b5df (movR64Imm64Effect 0x10b5df 0 0x5ffffffffffffa) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 2223) (.exec 0x10b5df (fun s => s.RIP = 0x10b5df) (movR64Imm64Effect 0x10b5df 0 0x5ffffffffffffa) (Reg.operands [] [])) #v[]
    (.letOp (n := 2224) (.out 0x10b5e9 (addR64R64Effect 0x10b5e9 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[2187, 2222]
    (.letOp (n := 2225) (.exec 0x10b5e9 (fun s => s.RIP = 0x10b5e9) (addR64R64Effect 0x10b5e9 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2187, 2222]
    (.letOp (n := 2226) (.exec 0x10b5ec (StorePre 0x10b5ec 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10b5ec + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b5ec 7 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[2224, 65]
    (.letOp (n := 2227) (.out 0x10b5f4 (addR64R64Effect 0x10b5f4 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[2195, 2222]
    (.letOp (n := 2228) (.exec 0x10b5f4 (fun s => s.RIP = 0x10b5f4) (addR64R64Effect 0x10b5f4 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[2195, 2222]
    (.letOp (n := 2229) (.exec 0x10b5f7 (StorePre 0x10b5f7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10b5f7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b5f7 8 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[2227, 65]
    (.letOp (n := 2230) (.out 0x10b5ff (addR64R64Effect 0x10b5ff 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[2205, 2222]
    (.letOp (n := 2231) (.exec 0x10b5ff (fun s => s.RIP = 0x10b5ff) (addR64R64Effect 0x10b5ff 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[2205, 2222]
    (.letOp (n := 2232) (.exec 0x10b602 (StorePre 0x10b602 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10b602 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b602 6 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[2230, 65]
    (.letOp (n := 2233) (.out 0x10b60a (movR64M64Effect 0x10b60a 3 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 2234) (.exec 0x10b60a (LoadPre 0x10b60a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10b60a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b60a 3 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2235) (.out 0x10b60f (addR64M64Effect 0x10b60f 3 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[2233, 65]
    (.letOp (n := 2236) (.exec 0x10b60f (LoadPre 0x10b60f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10b60f + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10b60f 3 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[2233, 65]
    (.letOp (n := 2237) (.out 0x10b617 (movR64M64Effect 0x10b617 10 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 2238) (.exec 0x10b617 (LoadPre 0x10b617 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10b617 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b617 10 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2239) (.out 0x10b61f (addR64M64Effect 0x10b61f 10 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[2237, 65]
    (.letOp (n := 2240) (.exec 0x10b61f (LoadPre 0x10b61f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10b61f + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10b61f 10 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[2237, 65]
    (.letOp (n := 2241) (.out 0x10b627 (movR64M64Effect 0x10b627 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 2242) (.exec 0x10b627 (LoadPre 0x10b627 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10b627 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b627 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2243) (.out 0x10b62c (addR64M64Effect 0x10b62c 7 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[2241, 65]
    (.letOp (n := 2244) (.exec 0x10b62c (LoadPre 0x10b62c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10b62c + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10b62c 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[2241, 65]
    (.letOp (n := 2245) (.exec 0x10b634 (StorePre 0x10b634 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10b634 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b634 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[2243, 65]
    (.letOp (n := 2246) (.out 0x10b639 (movR64M64Effect 0x10b639 11 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 2247) (.exec 0x10b639 (LoadPre 0x10b639 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10b639 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b639 11 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2248) (.out 0x10b641 (addR64M64Effect 0x10b641 11 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4] []) (.reg (.gpr 11))) #v[2246, 65]
    (.letOp (n := 2249) (.exec 0x10b641 (LoadPre 0x10b641 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10b641 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10b641 11 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[2246, 65]
    (.letOp (n := 2250) (.out 0x10b649 (movR64M64Effect 0x10b649 5 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 2251) (.exec 0x10b649 (LoadPre 0x10b649 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10b649 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b649 5 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2252) (.out 0x10b651 (addR64M64Effect 0x10b651 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[2250, 65]
    (.letOp (n := 2253) (.exec 0x10b651 (LoadPre 0x10b651 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10b651 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10b651 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[2250, 65]
    (b_l10a410_52)))))))))))))))))))))))))))))))))))

def bytes_l10a410_51 : List UInt8 :=
  [0x48, 0x01, 0xC1, 0x48, 0x89, 0x4C, 0x24, 0x60, 0x48, 0xB8, 0xFA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x5F, 0x00, 0x48, 0x01, 0xC7, 0x48, 0x89, 0xBC, 0x24, 0x20, 0x01, 0x00, 0x00, 0x49, 0x01, 0xC0,
    0x4C, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x01, 0xC6, 0x48, 0x89, 0xB4, 0x24, 0x08,
    0x01, 0x00, 0x00, 0x48, 0x8B, 0x5C, 0x24, 0x50, 0x48, 0x03, 0x9C, 0x24, 0xD0, 0x00, 0x00, 0x00,
    0x4C, 0x8B, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x03, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x03, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x7C,
    0x24, 0x28, 0x4C, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x03, 0x9C, 0x24, 0xC0, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0xAC, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x03, 0x6C, 0x24, 0x70] ++ bytes_l10a410_52

theorem code_l10a410_51 : ∀ x ∈ codeRange 0x10b5d7 bytes_l10a410_51, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb5d7 127 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_52

def b_l10a410_50 : Block Op Label signature Reg.count 2179 :=
  .letOp (n := 2179) (.out 0x10b56c (subR64R64Effect 0x10b56c 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2177, 2175]
    (.letOp (n := 2180) (.exec 0x10b56c (fun s => s.RIP = 0x10b56c) (subR64R64Effect 0x10b56c 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2177, 2175]
    (.letOp (n := 2181) (.out 0x10b56f (movR64M64Effect 0x10b56f 0 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2182) (.exec 0x10b56f (LoadPre 0x10b56f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x10b56f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b56f 0 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2183) (.out 0x10b577 (movR64M64Effect 0x10b577 2 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 2184) (.exec 0x10b577 (LoadPre 0x10b577 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10b577 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b577 2 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2185) (.out 0x10b57f (addR64R64Effect 0x10b57f 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[2181, 2183]
    (.letOp (n := 2186) (.exec 0x10b57f (fun s => s.RIP = 0x10b57f) (addR64R64Effect 0x10b57f 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[2181, 2183]
    (.letOp (n := 2187) (.out 0x10b582 (subR64R64Effect 0x10b582 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[2067, 2185]
    (.letOp (n := 2188) (.exec 0x10b582 (fun s => s.RIP = 0x10b582) (subR64R64Effect 0x10b582 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2067, 2185]
    (.letOp (n := 2189) (.out 0x10b585 (movR64M64Effect 0x10b585 0 (.sib 4 none 0 (.d32 0x1a0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2190) (.exec 0x10b585 (LoadPre 0x10b585 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x10b585 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b585 0 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2191) (.out 0x10b58d (movR64M64Effect 0x10b58d 2 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 2192) (.exec 0x10b58d (LoadPre 0x10b58d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10b58d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b58d 2 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2193) (.out 0x10b595 (addR64R64Effect 0x10b595 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[2189, 2191]
    (.letOp (n := 2194) (.exec 0x10b595 (fun s => s.RIP = 0x10b595) (addR64R64Effect 0x10b595 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[2189, 2191]
    (.letOp (n := 2195) (.out 0x10b598 (subR64R64Effect 0x10b598 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[2141, 2193]
    (.letOp (n := 2196) (.exec 0x10b598 (fun s => s.RIP = 0x10b598) (subR64R64Effect 0x10b598 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[2141, 2193]
    (.letOp (n := 2197) (.out 0x10b59b (andR64R64Effect 0x10b59b 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[2161, 2147]
    (.letOp (n := 2198) (.exec 0x10b59b (fun s => s.RIP = 0x10b59b) (andR64R64Effect 0x10b59b 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[2161, 2147]
    (.letOp (n := 2199) (.out 0x10b59e (movR64M64Effect 0x10b59e 0 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2200) (.exec 0x10b59e (LoadPre 0x10b59e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x10b59e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b59e 0 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2201) (.out 0x10b5a6 (movR64M64Effect 0x10b5a6 2 (.sib 4 none 0 (.d32 0x1b8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 2202) (.exec 0x10b5a6 (LoadPre 0x10b5a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b8)) s (0x10b5a6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b5a6 2 (.sib 4 none 0 (.d32 0x1b8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2203) (.out 0x10b5ae (addR64R64Effect 0x10b5ae 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[2199, 2201]
    (.letOp (n := 2204) (.exec 0x10b5ae (fun s => s.RIP = 0x10b5ae) (addR64R64Effect 0x10b5ae 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[2199, 2201]
    (.letOp (n := 2205) (.out 0x10b5b1 (subR64R64Effect 0x10b5b1 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[2197, 2203]
    (.letOp (n := 2206) (.exec 0x10b5b1 (fun s => s.RIP = 0x10b5b1) (subR64R64Effect 0x10b5b1 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[2197, 2203]
    (.letOp (n := 2207) (.out 0x10b5b4 (movR64M64Effect 0x10b5b4 0 (.sib 4 none 0 (.d32 0x190))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2208) (.exec 0x10b5b4 (LoadPre 0x10b5b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x10b5b4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b5b4 0 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2209) (.out 0x10b5bc (movR64M64Effect 0x10b5bc 2 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 2210) (.exec 0x10b5bc (LoadPre 0x10b5bc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10b5bc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b5bc 2 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2211) (.out 0x10b5c4 (addR64R64Effect 0x10b5c4 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[2207, 2209]
    (.letOp (n := 2212) (.exec 0x10b5c4 (fun s => s.RIP = 0x10b5c4) (addR64R64Effect 0x10b5c4 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[2207, 2209]
    (.letOp (n := 2213) (.out 0x10b5c7 (subR64R64Effect 0x10b5c7 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[2169, 2211]
    (.letOp (n := 2214) (.exec 0x10b5c7 (fun s => s.RIP = 0x10b5c7) (subR64R64Effect 0x10b5c7 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2169, 2211]
    (.letOp (n := 2215) (.out 0x10b5ca (movR64R64Effect 0x10b5ca 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 13] []) (.reg (.gpr 15))) #v[2213]
    (.letOp (n := 2216) (.exec 0x10b5ca (fun s => s.RIP = 0x10b5ca) (movR64R64Effect 0x10b5ca 15 13) (Reg.operands [.gpr 13] [])) #v[2213]
    (.letOp (n := 2217) (.out 0x10b5cd (movR64Imm64Effect 0x10b5cd 0 0x5ffff9ffffe91a) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 2218) (.exec 0x10b5cd (fun s => s.RIP = 0x10b5cd) (movR64Imm64Effect 0x10b5cd 0 0x5ffff9ffffe91a) (Reg.operands [] [])) #v[]
    (b_l10a410_51))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_50 : List UInt8 :=
  [0x48, 0x29, 0xC1, 0x48, 0x8B, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0x28,
    0x01, 0x00, 0x00, 0x48, 0x01, 0xD0, 0x48, 0x29, 0xC7, 0x48, 0x8B, 0x84, 0x24, 0xA0, 0x01, 0x00,
    0x00, 0x48, 0x8B, 0x94, 0x24, 0x68, 0x01, 0x00, 0x00, 0x48, 0x01, 0xD0, 0x49, 0x29, 0xC0, 0x4C,
    0x21, 0xD6, 0x48, 0x8B, 0x84, 0x24, 0x78, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0xB8, 0x01,
    0x00, 0x00, 0x48, 0x01, 0xD0, 0x48, 0x29, 0xC6, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x94, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x01, 0xD0, 0x49, 0x29, 0xC5, 0x4D, 0x89,
    0xEF, 0x48, 0xB8, 0x1A, 0xE9, 0xFF, 0xFF, 0xF9, 0xFF, 0x5F, 0x00] ++ bytes_l10a410_51

theorem code_l10a410_50 : ∀ x ∈ codeRange 0x10b56c bytes_l10a410_50, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb56c 107 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_51

def b_l10a410_49 : Block Op Label signature Reg.count 2137 :=
  .letOp (n := 2137) (.out 0x10b50f (movR64R64Effect 0x10b50f 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[2097]
    (.letOp (n := 2138) (.exec 0x10b50f (fun s => s.RIP = 0x10b50f) (movR64R64Effect 0x10b50f 1 8) (Reg.operands [.gpr 8] [])) #v[2097]
    (.letOp (n := 2139) (.out 0x10b512 (andR64R64Effect 0x10b512 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[2123, 2097]
    (.letOp (n := 2140) (.exec 0x10b512 (fun s => s.RIP = 0x10b512) (andR64R64Effect 0x10b512 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[2123, 2097]
    (.letOp (n := 2141) (.out 0x10b515 (movR64R64Effect 0x10b515 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[2139]
    (.letOp (n := 2142) (.exec 0x10b515 (fun s => s.RIP = 0x10b515) (movR64R64Effect 0x10b515 8 6) (Reg.operands [.gpr 6] [])) #v[2139]
    (.letOp (n := 2143) (.out 0x10b518 (movR64M64Effect 0x10b518 6 (.sib 4 none 0 (.d32 0x1b0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 2144) (.exec 0x10b518 (LoadPre 0x10b518 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x10b518 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b518 6 (.sib 4 none 0 (.d32 0x1b0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2145) (.out 0x10b520 (andR64R64Effect 0x10b520 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[2143, 2137]
    (.letOp (n := 2146) (.exec 0x10b520 (fun s => s.RIP = 0x10b520) (andR64R64Effect 0x10b520 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[2143, 2137]
    (.letOp (n := 2147) (.out 0x10b523 (movR64R64Effect 0x10b523 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[2137]
    (.letOp (n := 2148) (.exec 0x10b523 (fun s => s.RIP = 0x10b523) (movR64R64Effect 0x10b523 10 1) (Reg.operands [.gpr 1] [])) #v[2137]
    (.letOp (n := 2149) (.out 0x10b526 (addR64R64Effect 0x10b526 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[2134, 2145]
    (.letOp (n := 2150) (.out 0x10b526 (addR64R64Effect 0x10b526 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[2134, 2145]
    (.letOp (n := 2151) (.exec 0x10b526 (fun s => s.RIP = 0x10b526) (addR64R64Effect 0x10b526 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[2134, 2145]
    (.letOp (n := 2152) (.out 0x10b529 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b529 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2135, 2150]
    (.letOp (n := 2153) (.exec 0x10b529 (fun s => s.RIP = 0x10b529) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b529 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2135, 2150]
    (.letOp (n := 2154) (.out 0x10b52d (addR64R64Effect 0x10b52d 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[2149, 2130]
    (.letOp (n := 2155) (.out 0x10b52d (addR64R64Effect 0x10b52d 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[2149, 2130]
    (.letOp (n := 2156) (.exec 0x10b52d (fun s => s.RIP = 0x10b52d) (addR64R64Effect 0x10b52d 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[2149, 2130]
    (.letOp (n := 2157) (.out 0x10b530 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b530 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2152, 2155]
    (.letOp (n := 2158) (.exec 0x10b530 (fun s => s.RIP = 0x10b530) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b530 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2152, 2155]
    (.letOp (n := 2159) (.out 0x10b534 (shldR64R64Effect 0x10b534 5 2 0 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2157, 2154]
    (.letOp (n := 2160) (.exec 0x10b534 (fun s => s.RIP = 0x10b534) (shldR64R64Effect 0x10b534 5 2 0 12) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2157, 2154]
    (.letOp (n := 2161) (.out 0x10b539 (movR64R64Effect 0x10b539 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2154]
    (.letOp (n := 2162) (.exec 0x10b539 (fun s => s.RIP = 0x10b539) (movR64R64Effect 0x10b539 6 0) (Reg.operands [.gpr 0] [])) #v[2154]
    (.letOp (n := 2163) (.out 0x10b53c (movR64M64Effect 0x10b53c 13 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 2164) (.exec 0x10b53c (LoadPre 0x10b53c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10b53c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b53c 13 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2165) (.out 0x10b544 (movR64Imm64Effect 0x10b544 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 2166) (.exec 0x10b544 (fun s => s.RIP = 0x10b544) (movR64Imm64Effect 0x10b544 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2167) (.out 0x10b54e (andR64R64Effect 0x10b54e 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[2163, 2165]
    (.letOp (n := 2168) (.exec 0x10b54e (fun s => s.RIP = 0x10b54e) (andR64R64Effect 0x10b54e 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2163, 2165]
    (.letOp (n := 2169) (.out 0x10b551 (addR64R64Effect 0x10b551 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[2167, 2159]
    (.letOp (n := 2170) (.exec 0x10b551 (fun s => s.RIP = 0x10b551) (addR64R64Effect 0x10b551 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[2167, 2159]
    (.letOp (n := 2171) (.out 0x10b554 (movR64M64Effect 0x10b554 0 (.sib 4 none 0 (.d32 0x1a8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2172) (.exec 0x10b554 (LoadPre 0x10b554 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x10b554 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b554 0 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2173) (.out 0x10b55c (movR64M64Effect 0x10b55c 1 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 2174) (.exec 0x10b55c (LoadPre 0x10b55c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10b55c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b55c 1 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2175) (.out 0x10b564 (addR64R64Effect 0x10b564 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2171, 2173]
    (.letOp (n := 2176) (.exec 0x10b564 (fun s => s.RIP = 0x10b564) (addR64R64Effect 0x10b564 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2171, 2173]
    (.letOp (n := 2177) (.out 0x10b567 (movR64M64Effect 0x10b567 1 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 2178) (.exec 0x10b567 (LoadPre 0x10b567 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10b567 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b567 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_50))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_49 : List UInt8 :=
  [0x4C, 0x89, 0xC1, 0x4C, 0x21, 0xC6, 0x49, 0x89, 0xF0, 0x48, 0x8B, 0xB4, 0x24, 0xB0, 0x01, 0x00,
    0x00, 0x48, 0x21, 0xCE, 0x49, 0x89, 0xCA, 0x48, 0x01, 0xF0, 0x48, 0x83, 0xD2, 0x00, 0x4C, 0x01,
    0xC8, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x0F, 0xA4, 0xC2, 0x0C, 0x48, 0x89, 0xC6, 0x4C, 0x8B, 0xAC,
    0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x49,
    0x21, 0xC5, 0x49, 0x01, 0xD5, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x8C,
    0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0x01, 0xC8, 0x48, 0x8B, 0x4C, 0x24, 0x60] ++ bytes_l10a410_50

theorem code_l10a410_49 : ∀ x ∈ codeRange 0x10b50f bytes_l10a410_49, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb50f 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_50

def b_l10a410_48 : Block Op Label signature Reg.count 2090 :=
  .letOp (n := 2090) (.out 0x10b4ba (addR64R64Effect 0x10b4ba 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[2085, 2011]
    (.letOp (n := 2091) (.out 0x10b4ba (addR64R64Effect 0x10b4ba 10 8) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 8] []) (.flag .CF)) #v[2085, 2011]
    (.letOp (n := 2092) (.exec 0x10b4ba (fun s => s.RIP = 0x10b4ba) (addR64R64Effect 0x10b4ba 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[2085, 2011]
    (.letOp (n := 2093) (.out 0x10b4bd (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b4bd 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[2088, 2091]
    (.letOp (n := 2094) (.exec 0x10b4bd (fun s => s.RIP = 0x10b4bd) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b4bd 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2088, 2091]
    (.letOp (n := 2095) (.out 0x10b4c1 (movR64R64Effect 0x10b4c1 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[2090]
    (.letOp (n := 2096) (.exec 0x10b4c1 (fun s => s.RIP = 0x10b4c1) (movR64R64Effect 0x10b4c1 0 10) (Reg.operands [.gpr 10] [])) #v[2090]
    (.letOp (n := 2097) (.out 0x10b4c4 (movR64Imm64Effect 0x10b4c4 8 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 2098) (.exec 0x10b4c4 (fun s => s.RIP = 0x10b4c4) (movR64Imm64Effect 0x10b4c4 8 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2099) (.out 0x10b4ce (andR64R64Effect 0x10b4ce 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[2095, 2097]
    (.letOp (n := 2100) (.exec 0x10b4ce (fun s => s.RIP = 0x10b4ce) (andR64R64Effect 0x10b4ce 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[2095, 2097]
    (.letOp (n := 2101) (.out 0x10b4d1 (movR64Imm64Effect 0x10b4d1 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2102) (.exec 0x10b4d1 (fun s => s.RIP = 0x10b4d1) (movR64Imm64Effect 0x10b4d1 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2103) (.out 0x10b4db (mulR64Effect 0x10b4db 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2101, 2099]
    (.letOp (n := 2104) (.out 0x10b4db (mulR64Effect 0x10b4db 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2101, 2099]
    (.letOp (n := 2105) (.exec 0x10b4db (fun s => s.RIP = 0x10b4db) (mulR64Effect 0x10b4db 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2101, 2099]
    (.letOp (n := 2106) (.out 0x10b4de (movR64R64Effect 0x10b4de 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2103]
    (.letOp (n := 2107) (.exec 0x10b4de (fun s => s.RIP = 0x10b4de) (movR64R64Effect 0x10b4de 6 0) (Reg.operands [.gpr 0] [])) #v[2103]
    (.letOp (n := 2108) (.out 0x10b4e1 (addR64R64Effect 0x10b4e1 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 14] []) (.reg (.gpr 12))) #v[2063, 2056]
    (.letOp (n := 2109) (.out 0x10b4e1 (addR64R64Effect 0x10b4e1 12 14) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 14] []) (.flag .CF)) #v[2063, 2056]
    (.letOp (n := 2110) (.exec 0x10b4e1 (fun s => s.RIP = 0x10b4e1) (addR64R64Effect 0x10b4e1 12 14) (Reg.operands [.gpr 12, .gpr 14] [])) #v[2063, 2056]
    (.letOp (n := 2111) (.out 0x10b4e4 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b4e4 9 5)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[2065, 2054, 2109]
    (.letOp (n := 2112) (.exec 0x10b4e4 (fun s => s.RIP = 0x10b4e4) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b4e4 9 5)) (Reg.operands [.gpr 9, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2065, 2054, 2109]
    (.letOp (n := 2113) (.out 0x10b4e7 (addR64R64Effect 0x10b4e7 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[2108, 2047]
    (.letOp (n := 2114) (.out 0x10b4e7 (addR64R64Effect 0x10b4e7 12 13) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 13] []) (.flag .CF)) #v[2108, 2047]
    (.letOp (n := 2115) (.exec 0x10b4e7 (fun s => s.RIP = 0x10b4e7) (addR64R64Effect 0x10b4e7 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[2108, 2047]
    (.letOp (n := 2116) (.out 0x10b4ea (atFlags StatusFlags.CF (adcR64M64Effect 0x10b4ea 9 (.sib 4 none 0 (.d32 0x108)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[2111, 65, 2114]
    (.letOp (n := 2117) (.exec 0x10b4ea (LoadPre 0x10b4ea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10b4ea + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10b4ea 9 (.sib 4 none 0 (.d32 0x108)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2111, 65, 2114]
    (.letOp (n := 2118) (.out 0x10b4f2 (addR64R64Effect 0x10b4f2 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[2106, 2113]
    (.letOp (n := 2119) (.out 0x10b4f2 (addR64R64Effect 0x10b4f2 6 12) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 12] []) (.flag .CF)) #v[2106, 2113]
    (.letOp (n := 2120) (.exec 0x10b4f2 (fun s => s.RIP = 0x10b4f2) (addR64R64Effect 0x10b4f2 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[2106, 2113]
    (.letOp (n := 2121) (.out 0x10b4f5 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b4f5 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[2116, 2104, 2119]
    (.letOp (n := 2122) (.exec 0x10b4f5 (fun s => s.RIP = 0x10b4f5) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b4f5 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2116, 2104, 2119]
    (.letOp (n := 2123) (.out 0x10b4f8 (addR64R64Effect 0x10b4f8 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[2118, 2039]
    (.letOp (n := 2124) (.out 0x10b4f8 (addR64R64Effect 0x10b4f8 6 11) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 11] []) (.flag .CF)) #v[2118, 2039]
    (.letOp (n := 2125) (.exec 0x10b4f8 (fun s => s.RIP = 0x10b4f8) (addR64R64Effect 0x10b4f8 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[2118, 2039]
    (.letOp (n := 2126) (.out 0x10b4fb (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b4fb 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[2121, 2124]
    (.letOp (n := 2127) (.exec 0x10b4fb (fun s => s.RIP = 0x10b4fb) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b4fb 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2121, 2124]
    (.letOp (n := 2128) (.out 0x10b4ff (shldR64R64Effect 0x10b4ff 5 3 10 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[2093, 2090]
    (.letOp (n := 2129) (.exec 0x10b4ff (fun s => s.RIP = 0x10b4ff) (shldR64R64Effect 0x10b4ff 5 3 10 12) (Reg.operands [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2093, 2090]
    (.letOp (n := 2130) (.out 0x10b504 (shldR64R64Effect 0x10b504 5 9 6 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2126, 2123]
    (.letOp (n := 2131) (.exec 0x10b504 (fun s => s.RIP = 0x10b504) (shldR64R64Effect 0x10b504 5 9 6 12) (Reg.operands [.gpr 9, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2126, 2123]
    (.letOp (n := 2132) (.out 0x10b509 (movR64R64Effect 0x10b509 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[2128]
    (.letOp (n := 2133) (.exec 0x10b509 (fun s => s.RIP = 0x10b509) (movR64R64Effect 0x10b509 0 3) (Reg.operands [.gpr 3] [])) #v[2128]
    (.letOp (n := 2134) (.out 0x10b50c (mulR64Effect 0x10b50c 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2101, 2132]
    (.letOp (n := 2135) (.out 0x10b50c (mulR64Effect 0x10b50c 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2101, 2132]
    (.letOp (n := 2136) (.exec 0x10b50c (fun s => s.RIP = 0x10b50c) (mulR64Effect 0x10b50c 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2101, 2132]
    (b_l10a410_49)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_48 : List UInt8 :=
  [0x4D, 0x01, 0xC2, 0x48, 0x83, 0xD3, 0x00, 0x4C, 0x89, 0xD0, 0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xC0, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00,
    0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC6, 0x4D, 0x01, 0xF4, 0x49, 0x11, 0xE9, 0x4D, 0x01, 0xEC,
    0x4C, 0x13, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00, 0x4C, 0x01, 0xE6, 0x49, 0x11, 0xD1, 0x4C, 0x01,
    0xDE, 0x49, 0x83, 0xD1, 0x00, 0x4C, 0x0F, 0xA4, 0xD3, 0x0C, 0x49, 0x0F, 0xA4, 0xF1, 0x0C, 0x48,
    0x89, 0xD8, 0x48, 0xF7, 0xE1] ++ bytes_l10a410_49

theorem code_l10a410_48 : ∀ x ∈ codeRange 0x10b4ba bytes_l10a410_48, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb4ba 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_49

def b_l10a410_47 : Block Op Label signature Reg.count 2046 :=
  .letOp (n := 2046) (.exec 0x10b45e (StorePre 0x10b45e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10b45e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b45e 2 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2044, 65]
    (.letOp (n := 2047) (.out 0x10b466 (movR64R64Effect 0x10b466 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[2043]
    (.letOp (n := 2048) (.exec 0x10b466 (fun s => s.RIP = 0x10b466) (movR64R64Effect 0x10b466 13 0) (Reg.operands [.gpr 0] [])) #v[2043]
    (.letOp (n := 2049) (.out 0x10b469 (movR64M64Effect 0x10b469 0 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2050) (.exec 0x10b469 (LoadPre 0x10b469 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10b469 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b469 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2051) (.out 0x10b471 (mulM64Effect 0x10b471 8 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2049, 65]
    (.letOp (n := 2052) (.out 0x10b471 (mulM64Effect 0x10b471 8 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2049, 65]
    (.letOp (n := 2053) (.exec 0x10b471 (LoadPre 0x10b471 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x10b471 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10b471 8 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2049, 65]
    (.letOp (n := 2054) (.out 0x10b479 (movR64R64Effect 0x10b479 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2052]
    (.letOp (n := 2055) (.exec 0x10b479 (fun s => s.RIP = 0x10b479) (movR64R64Effect 0x10b479 5 2) (Reg.operands [.gpr 2] [])) #v[2052]
    (.letOp (n := 2056) (.out 0x10b47c (movR64R64Effect 0x10b47c 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[2051]
    (.letOp (n := 2057) (.exec 0x10b47c (fun s => s.RIP = 0x10b47c) (movR64R64Effect 0x10b47c 14 0) (Reg.operands [.gpr 0] [])) #v[2051]
    (.letOp (n := 2058) (.out 0x10b47f (movR64M64Effect 0x10b47f 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2059) (.exec 0x10b47f (LoadPre 0x10b47f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10b47f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b47f 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2060) (.out 0x10b484 (mulM64Effect 0x10b484 8 (.sib 4 none 0 (.d32 0x198))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2058, 65]
    (.letOp (n := 2061) (.out 0x10b484 (mulM64Effect 0x10b484 8 (.sib 4 none 0 (.d32 0x198))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2058, 65]
    (.letOp (n := 2062) (.exec 0x10b484 (LoadPre 0x10b484 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x10b484 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10b484 8 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2058, 65]
    (.letOp (n := 2063) (.out 0x10b48c (movR64R64Effect 0x10b48c 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[2060]
    (.letOp (n := 2064) (.exec 0x10b48c (fun s => s.RIP = 0x10b48c) (movR64R64Effect 0x10b48c 12 0) (Reg.operands [.gpr 0] [])) #v[2060]
    (.letOp (n := 2065) (.out 0x10b48f (movR64R64Effect 0x10b48f 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2061]
    (.letOp (n := 2066) (.exec 0x10b48f (fun s => s.RIP = 0x10b48f) (movR64R64Effect 0x10b48f 9 2) (Reg.operands [.gpr 2] [])) #v[2061]
    (.letOp (n := 2067) (.out 0x10b492 (andR64R64Effect 0x10b492 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[2034, 2015]
    (.letOp (n := 2068) (.exec 0x10b492 (fun s => s.RIP = 0x10b492) (andR64R64Effect 0x10b492 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[2034, 2015]
    (.letOp (n := 2069) (.out 0x10b495 (movR64M64Effect 0x10b495 0 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2070) (.exec 0x10b495 (LoadPre 0x10b495 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10b495 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b495 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2071) (.out 0x10b49d (mulR64Effect 0x10b49d 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1978, 2069]
    (.letOp (n := 2072) (.out 0x10b49d (mulR64Effect 0x10b49d 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1978, 2069]
    (.letOp (n := 2073) (.exec 0x10b49d (fun s => s.RIP = 0x10b49d) (mulR64Effect 0x10b49d 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1978, 2069]
    (.letOp (n := 2074) (.out 0x10b4a0 (movR64R64Effect 0x10b4a0 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2072]
    (.letOp (n := 2075) (.exec 0x10b4a0 (fun s => s.RIP = 0x10b4a0) (movR64R64Effect 0x10b4a0 3 2) (Reg.operands [.gpr 2] [])) #v[2072]
    (.letOp (n := 2076) (.out 0x10b4a3 (movR64R64Effect 0x10b4a3 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2071]
    (.letOp (n := 2077) (.exec 0x10b4a3 (fun s => s.RIP = 0x10b4a3) (movR64R64Effect 0x10b4a3 6 0) (Reg.operands [.gpr 0] [])) #v[2071]
    (.letOp (n := 2078) (.out 0x10b4a6 (movR64M64Effect 0x10b4a6 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 2079) (.exec 0x10b4a6 (LoadPre 0x10b4a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10b4a6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b4a6 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 2080) (.out 0x10b4ae (mulR64Effect 0x10b4ae 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[1991, 2078]
    (.letOp (n := 2081) (.out 0x10b4ae (mulR64Effect 0x10b4ae 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[1991, 2078]
    (.letOp (n := 2082) (.exec 0x10b4ae (fun s => s.RIP = 0x10b4ae) (mulR64Effect 0x10b4ae 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[1991, 2078]
    (.letOp (n := 2083) (.out 0x10b4b1 (movR64R64Effect 0x10b4b1 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2080]
    (.letOp (n := 2084) (.exec 0x10b4b1 (fun s => s.RIP = 0x10b4b1) (movR64R64Effect 0x10b4b1 10 0) (Reg.operands [.gpr 0] [])) #v[2080]
    (.letOp (n := 2085) (.out 0x10b4b4 (addR64R64Effect 0x10b4b4 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[2083, 2076]
    (.letOp (n := 2086) (.out 0x10b4b4 (addR64R64Effect 0x10b4b4 10 6) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 6] []) (.flag .CF)) #v[2083, 2076]
    (.letOp (n := 2087) (.exec 0x10b4b4 (fun s => s.RIP = 0x10b4b4) (addR64R64Effect 0x10b4b4 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[2083, 2076]
    (.letOp (n := 2088) (.out 0x10b4b7 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b4b7 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[2074, 2081, 2086]
    (.letOp (n := 2089) (.exec 0x10b4b7 (fun s => s.RIP = 0x10b4b7) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b4b7 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2074, 2081, 2086]
    (b_l10a410_48))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_47 : List UInt8 :=
  [0x48, 0x89, 0x94, 0x24, 0x08, 0x01, 0x00, 0x00, 0x49, 0x89, 0xC5, 0x48, 0x8B, 0x84, 0x24, 0x18,
    0x01, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0x70, 0x01, 0x00, 0x00, 0x48, 0x89, 0xD5, 0x49, 0x89,
    0xC6, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0xF7, 0xA4, 0x24, 0x98, 0x01, 0x00, 0x00, 0x49, 0x89,
    0xC4, 0x49, 0x89, 0xD1, 0x48, 0x21, 0xF7, 0x48, 0x8B, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x48,
    0xF7, 0xE1, 0x48, 0x89, 0xD3, 0x48, 0x89, 0xC6, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x49, 0xF7, 0xE7, 0x49, 0x89, 0xC2, 0x49, 0x01, 0xF2, 0x48, 0x11, 0xD3] ++ bytes_l10a410_48

theorem code_l10a410_47 : ∀ x ∈ codeRange 0x10b45e bytes_l10a410_47, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb45e 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_48

def b_l10a410_46 : Block Op Label signature Reg.count 1999 :=
  .letOp (n := 1999) (.out 0x10b40b (atFlags StatusFlags.CF (adcR64R64Effect 0x10b40b 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1983, 1994, 1997]
    (.letOp (n := 2000) (.exec 0x10b40b (fun s => s.RIP = 0x10b40b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b40b 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1983, 1994, 1997]
    (.letOp (n := 2001) (.out 0x10b40e (addR64R64Effect 0x10b40e 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1996, 1967]
    (.letOp (n := 2002) (.out 0x10b40e (addR64R64Effect 0x10b40e 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[1996, 1967]
    (.letOp (n := 2003) (.exec 0x10b40e (fun s => s.RIP = 0x10b40e) (addR64R64Effect 0x10b40e 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1996, 1967]
    (.letOp (n := 2004) (.out 0x10b411 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b411 8 9)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1999, 1969, 2002]
    (.letOp (n := 2005) (.exec 0x10b411 (fun s => s.RIP = 0x10b411) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b411 8 9)) (Reg.operands [.gpr 8, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1999, 1969, 2002]
    (.letOp (n := 2006) (.out 0x10b414 (addR64R64Effect 0x10b414 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[2001, 1921]
    (.letOp (n := 2007) (.out 0x10b414 (addR64R64Effect 0x10b414 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[2001, 1921]
    (.letOp (n := 2008) (.exec 0x10b414 (fun s => s.RIP = 0x10b414) (addR64R64Effect 0x10b414 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[2001, 1921]
    (.letOp (n := 2009) (.out 0x10b417 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b417 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2004, 2007]
    (.letOp (n := 2010) (.exec 0x10b417 (fun s => s.RIP = 0x10b417) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b417 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2004, 2007]
    (.letOp (n := 2011) (.out 0x10b41b (shldR64R64Effect 0x10b41b 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2009, 2006]
    (.letOp (n := 2012) (.exec 0x10b41b (fun s => s.RIP = 0x10b41b) (shldR64R64Effect 0x10b41b 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2009, 2006]
    (.letOp (n := 2013) (.out 0x10b420 (andR64R64Effect 0x10b420 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[2006, 1971]
    (.letOp (n := 2014) (.exec 0x10b420 (fun s => s.RIP = 0x10b420) (andR64R64Effect 0x10b420 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[2006, 1971]
    (.letOp (n := 2015) (.out 0x10b423 (movR64R64Effect 0x10b423 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[1971]
    (.letOp (n := 2016) (.exec 0x10b423 (fun s => s.RIP = 0x10b423) (movR64R64Effect 0x10b423 6 7) (Reg.operands [.gpr 7] [])) #v[1971]
    (.letOp (n := 2017) (.out 0x10b426 (movR64Imm64Effect 0x10b426 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2018) (.exec 0x10b426 (fun s => s.RIP = 0x10b426) (movR64Imm64Effect 0x10b426 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2019) (.out 0x10b430 (mulR64Effect 0x10b430 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2017, 2013]
    (.letOp (n := 2020) (.out 0x10b430 (mulR64Effect 0x10b430 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2017, 2013]
    (.letOp (n := 2021) (.exec 0x10b430 (fun s => s.RIP = 0x10b430) (mulR64Effect 0x10b430 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2017, 2013]
    (.letOp (n := 2022) (.out 0x10b433 (movR64R64Effect 0x10b433 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[2019]
    (.letOp (n := 2023) (.exec 0x10b433 (fun s => s.RIP = 0x10b433) (movR64R64Effect 0x10b433 7 0) (Reg.operands [.gpr 0] [])) #v[2019]
    (.letOp (n := 2024) (.out 0x10b436 (addR64R64Effect 0x10b436 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[1960, 1951]
    (.letOp (n := 2025) (.out 0x10b436 (addR64R64Effect 0x10b436 3 14) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 14] []) (.flag .CF)) #v[1960, 1951]
    (.letOp (n := 2026) (.exec 0x10b436 (fun s => s.RIP = 0x10b436) (addR64R64Effect 0x10b436 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[1960, 1951]
    (.letOp (n := 2027) (.out 0x10b439 (atFlags StatusFlags.CF (adcR64M64Effect 0x10b439 11 (.sib 4 none 0 (.d32 0x188)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[1958, 65, 2025]
    (.letOp (n := 2028) (.exec 0x10b439 (LoadPre 0x10b439 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x10b439 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10b439 11 (.sib 4 none 0 (.d32 0x188)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1958, 65, 2025]
    (.letOp (n := 2029) (.out 0x10b441 (addR64R64Effect 0x10b441 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[2022, 2024]
    (.letOp (n := 2030) (.out 0x10b441 (addR64R64Effect 0x10b441 7 3) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 3] []) (.flag .CF)) #v[2022, 2024]
    (.letOp (n := 2031) (.exec 0x10b441 (fun s => s.RIP = 0x10b441) (addR64R64Effect 0x10b441 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[2022, 2024]
    (.letOp (n := 2032) (.out 0x10b444 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b444 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[2027, 2020, 2030]
    (.letOp (n := 2033) (.exec 0x10b444 (fun s => s.RIP = 0x10b444) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b444 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2027, 2020, 2030]
    (.letOp (n := 2034) (.out 0x10b447 (addR64R64Effect 0x10b447 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[2029, 1941]
    (.letOp (n := 2035) (.out 0x10b447 (addR64R64Effect 0x10b447 7 5) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 5] []) (.flag .CF)) #v[2029, 1941]
    (.letOp (n := 2036) (.exec 0x10b447 (fun s => s.RIP = 0x10b447) (addR64R64Effect 0x10b447 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[2029, 1941]
    (.letOp (n := 2037) (.out 0x10b44a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b44a 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[2032, 2035]
    (.letOp (n := 2038) (.exec 0x10b44a (fun s => s.RIP = 0x10b44a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b44a 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2032, 2035]
    (.letOp (n := 2039) (.out 0x10b44e (shldR64R64Effect 0x10b44e 5 11 7 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[2037, 2034]
    (.letOp (n := 2040) (.exec 0x10b44e (fun s => s.RIP = 0x10b44e) (shldR64R64Effect 0x10b44e 5 11 7 12) (Reg.operands [.gpr 11, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2037, 2034]
    (.letOp (n := 2041) (.out 0x10b453 (movR64R64Effect 0x10b453 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1987]
    (.letOp (n := 2042) (.exec 0x10b453 (fun s => s.RIP = 0x10b453) (movR64R64Effect 0x10b453 0 13) (Reg.operands [.gpr 13] [])) #v[1987]
    (.letOp (n := 2043) (.out 0x10b456 (mulM64Effect 0x10b456 8 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2041, 65]
    (.letOp (n := 2044) (.out 0x10b456 (mulM64Effect 0x10b456 8 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2041, 65]
    (.letOp (n := 2045) (.exec 0x10b456 (LoadPre 0x10b456 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10b456 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10b456 8 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2041, 65]
    (b_l10a410_47)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_46 : List UInt8 :=
  [0x49, 0x11, 0xD0, 0x48, 0x01, 0xF0, 0x4D, 0x11, 0xC8, 0x4C, 0x01, 0xE0, 0x49, 0x83, 0xD0, 0x00,
    0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x48, 0x21, 0xF8, 0x48, 0x89, 0xFE, 0x48, 0xBA, 0x10, 0x3D, 0x00,
    0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xC7, 0x4C, 0x01, 0xF3, 0x4C, 0x13,
    0x9C, 0x24, 0x88, 0x01, 0x00, 0x00, 0x48, 0x01, 0xDF, 0x49, 0x11, 0xD3, 0x48, 0x01, 0xEF, 0x49,
    0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xFB, 0x0C, 0x4C, 0x89, 0xE8, 0x48, 0xF7, 0xA4, 0x24, 0x30,
    0x01, 0x00, 0x00] ++ bytes_l10a410_47

theorem code_l10a410_46 : ∀ x ∈ codeRange 0x10b40b bytes_l10a410_46, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb40b 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_47

def b_l10a410_45 : Block Op Label signature Reg.count 1955 :=
  .letOp (n := 1955) (.out 0x10b3ba (mulR64Effect 0x10b3ba 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[1863, 1953]
    (.letOp (n := 1956) (.out 0x10b3ba (mulR64Effect 0x10b3ba 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[1863, 1953]
    (.letOp (n := 1957) (.exec 0x10b3ba (fun s => s.RIP = 0x10b3ba) (mulR64Effect 0x10b3ba 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[1863, 1953]
    (.letOp (n := 1958) (.out 0x10b3bd (movR64R64Effect 0x10b3bd 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[1956]
    (.letOp (n := 1959) (.exec 0x10b3bd (fun s => s.RIP = 0x10b3bd) (movR64R64Effect 0x10b3bd 11 2) (Reg.operands [.gpr 2] [])) #v[1956]
    (.letOp (n := 1960) (.out 0x10b3c0 (movR64R64Effect 0x10b3c0 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[1955]
    (.letOp (n := 1961) (.exec 0x10b3c0 (fun s => s.RIP = 0x10b3c0) (movR64R64Effect 0x10b3c0 3 0) (Reg.operands [.gpr 0] [])) #v[1955]
    (.letOp (n := 1962) (.out 0x10b3c3 (movR64R64Effect 0x10b3c3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[1859]
    (.letOp (n := 1963) (.exec 0x10b3c3 (fun s => s.RIP = 0x10b3c3) (movR64R64Effect 0x10b3c3 0 15) (Reg.operands [.gpr 15] [])) #v[1859]
    (.letOp (n := 1964) (.out 0x10b3c6 (mulR64Effect 0x10b3c6 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[1874, 1962]
    (.letOp (n := 1965) (.out 0x10b3c6 (mulR64Effect 0x10b3c6 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[1874, 1962]
    (.letOp (n := 1966) (.exec 0x10b3c6 (fun s => s.RIP = 0x10b3c6) (mulR64Effect 0x10b3c6 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[1874, 1962]
    (.letOp (n := 1967) (.out 0x10b3c9 (movR64R64Effect 0x10b3c9 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1964]
    (.letOp (n := 1968) (.exec 0x10b3c9 (fun s => s.RIP = 0x10b3c9) (movR64R64Effect 0x10b3c9 6 0) (Reg.operands [.gpr 0] [])) #v[1964]
    (.letOp (n := 1969) (.out 0x10b3cc (movR64R64Effect 0x10b3cc 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[1965]
    (.letOp (n := 1970) (.exec 0x10b3cc (fun s => s.RIP = 0x10b3cc) (movR64R64Effect 0x10b3cc 9 2) (Reg.operands [.gpr 2] [])) #v[1965]
    (.letOp (n := 1971) (.out 0x10b3cf (movR64Imm64Effect 0x10b3cf 7 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 1972) (.exec 0x10b3cf (fun s => s.RIP = 0x10b3cf) (movR64Imm64Effect 0x10b3cf 7 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1973) (.out 0x10b3d9 (andR64R64Effect 0x10b3d9 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[1943, 1971]
    (.letOp (n := 1974) (.exec 0x10b3d9 (fun s => s.RIP = 0x10b3d9) (andR64R64Effect 0x10b3d9 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1943, 1971]
    (.letOp (n := 1975) (.exec 0x10b3dc (StorePre 0x10b3dc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10b3dc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b3dc 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1973, 65]
    (.letOp (n := 1976) (.out 0x10b3e1 (movR64R64Effect 0x10b3e1 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1870]
    (.letOp (n := 1977) (.exec 0x10b3e1 (fun s => s.RIP = 0x10b3e1) (movR64R64Effect 0x10b3e1 0 13) (Reg.operands [.gpr 13] [])) #v[1870]
    (.letOp (n := 1978) (.out 0x10b3e4 (movR64M64Effect 0x10b3e4 1 (.sib 4 none 0 (.d32 0x1c8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 1979) (.exec 0x10b3e4 (LoadPre 0x10b3e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x10b3e4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b3e4 1 (.sib 4 none 0 (.d32 0x1c8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1980) (.out 0x10b3ec (mulR64Effect 0x10b3ec 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1978, 1976]
    (.letOp (n := 1981) (.out 0x10b3ec (mulR64Effect 0x10b3ec 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1978, 1976]
    (.letOp (n := 1982) (.exec 0x10b3ec (fun s => s.RIP = 0x10b3ec) (mulR64Effect 0x10b3ec 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1978, 1976]
    (.letOp (n := 1983) (.out 0x10b3ef (movR64R64Effect 0x10b3ef 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[1981]
    (.letOp (n := 1984) (.exec 0x10b3ef (fun s => s.RIP = 0x10b3ef) (movR64R64Effect 0x10b3ef 8 2) (Reg.operands [.gpr 2] [])) #v[1981]
    (.letOp (n := 1985) (.out 0x10b3f2 (movR64R64Effect 0x10b3f2 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[1980]
    (.letOp (n := 1986) (.exec 0x10b3f2 (fun s => s.RIP = 0x10b3f2) (movR64R64Effect 0x10b3f2 10 0) (Reg.operands [.gpr 0] [])) #v[1980]
    (.letOp (n := 1987) (.out 0x10b3f5 (movR64M64Effect 0x10b3f5 13 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 1988) (.exec 0x10b3f5 (LoadPre 0x10b3f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10b3f5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b3f5 13 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1989) (.out 0x10b3fd (movR64R64Effect 0x10b3fd 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1987]
    (.letOp (n := 1990) (.exec 0x10b3fd (fun s => s.RIP = 0x10b3fd) (movR64R64Effect 0x10b3fd 0 13) (Reg.operands [.gpr 13] [])) #v[1987]
    (.letOp (n := 1991) (.out 0x10b400 (movR64M64Effect 0x10b400 15 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 1992) (.exec 0x10b400 (LoadPre 0x10b400 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10b400 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b400 15 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1993) (.out 0x10b405 (mulR64Effect 0x10b405 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[1991, 1989]
    (.letOp (n := 1994) (.out 0x10b405 (mulR64Effect 0x10b405 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[1991, 1989]
    (.letOp (n := 1995) (.exec 0x10b405 (fun s => s.RIP = 0x10b405) (mulR64Effect 0x10b405 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[1991, 1989]
    (.letOp (n := 1996) (.out 0x10b408 (addR64R64Effect 0x10b408 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[1993, 1985]
    (.letOp (n := 1997) (.out 0x10b408 (addR64R64Effect 0x10b408 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[1993, 1985]
    (.letOp (n := 1998) (.exec 0x10b408 (fun s => s.RIP = 0x10b408) (addR64R64Effect 0x10b408 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[1993, 1985]
    (b_l10a410_46))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_45 : List UInt8 :=
  [0x49, 0xF7, 0xE3, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC3, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE2, 0x48,
    0x89, 0xC6, 0x49, 0x89, 0xD1, 0x48, 0xBF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48,
    0x21, 0xF9, 0x48, 0x89, 0x4C, 0x24, 0x60, 0x4C, 0x89, 0xE8, 0x48, 0x8B, 0x8C, 0x24, 0xC8, 0x01,
    0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC2, 0x4C, 0x8B, 0xAC, 0x24, 0x08,
    0x01, 0x00, 0x00, 0x4C, 0x89, 0xE8, 0x4C, 0x8B, 0x7C, 0x24, 0x20, 0x49, 0xF7, 0xE7, 0x4C, 0x01,
    0xD0] ++ bytes_l10a410_46

theorem code_l10a410_45 : ∀ x ∈ codeRange 0x10b3ba bytes_l10a410_45, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb3ba 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_46

def b_l10a410_44 : Block Op Label signature Reg.count 1911 :=
  .letOp (n := 1911) (.out 0x10b357 (addR64M64Effect 0x10b357 0 (.sib 4 none 0 (.d32 0x1e0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1906, 65]
    (.letOp (n := 1912) (.out 0x10b357 (addR64M64Effect 0x10b357 0 (.sib 4 none 0 (.d32 0x1e0))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[1906, 65]
    (.letOp (n := 1913) (.exec 0x10b357 (LoadPre 0x10b357 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x10b357 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10b357 0 (.sib 4 none 0 (.d32 0x1e0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1906, 65]
    (.letOp (n := 1914) (.out 0x10b35f (atFlags StatusFlags.CF (adcR64M64Effect 0x10b35f 12 (.sib 4 none 0 (.d32 0x188)))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 12))) #v[1909, 65, 1912]
    (.letOp (n := 1915) (.exec 0x10b35f (LoadPre 0x10b35f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x10b35f + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10b35f 12 (.sib 4 none 0 (.d32 0x188)))) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1909, 65, 1912]
    (.letOp (n := 1916) (.out 0x10b367 (addR64R64Effect 0x10b367 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[1911, 1847]
    (.letOp (n := 1917) (.out 0x10b367 (addR64R64Effect 0x10b367 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[1911, 1847]
    (.letOp (n := 1918) (.exec 0x10b367 (fun s => s.RIP = 0x10b367) (addR64R64Effect 0x10b367 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[1911, 1847]
    (.letOp (n := 1919) (.out 0x10b36a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b36a 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[1914, 1917]
    (.letOp (n := 1920) (.exec 0x10b36a (fun s => s.RIP = 0x10b36a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b36a 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1914, 1917]
    (.letOp (n := 1921) (.out 0x10b36e (shldR64R64Effect 0x10b36e 5 12 0 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1919, 1916]
    (.letOp (n := 1922) (.exec 0x10b36e (fun s => s.RIP = 0x10b36e) (shldR64R64Effect 0x10b36e 5 12 0 12) (Reg.operands [.gpr 12, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1919, 1916]
    (.letOp (n := 1923) (.out 0x10b373 (shlR64Effect 0x10b373 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1916]
    (.letOp (n := 1924) (.exec 0x10b373 (fun s => s.RIP = 0x10b373) (shlR64Effect 0x10b373 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1916]
    (.letOp (n := 1925) (.out 0x10b377 (movR64Imm64Effect 0x10b377 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1926) (.exec 0x10b377 (fun s => s.RIP = 0x10b377) (movR64Imm64Effect 0x10b377 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 1927) (.out 0x10b381 (andR64R64Effect 0x10b381 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1923, 1925]
    (.letOp (n := 1928) (.exec 0x10b381 (fun s => s.RIP = 0x10b381) (andR64R64Effect 0x10b381 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1923, 1925]
    (.letOp (n := 1929) (.out 0x10b384 (orR64R64Effect 0x10b384 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[1927, 1883]
    (.letOp (n := 1930) (.exec 0x10b384 (fun s => s.RIP = 0x10b384) (orR64R64Effect 0x10b384 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[1927, 1883]
    (.letOp (n := 1931) (.out 0x10b387 (movR64Imm64Effect 0x10b387 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1932) (.exec 0x10b387 (fun s => s.RIP = 0x10b387) (movR64Imm64Effect 0x10b387 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 1933) (.out 0x10b391 (mulR64Effect 0x10b391 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1931, 1929]
    (.letOp (n := 1934) (.out 0x10b391 (mulR64Effect 0x10b391 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1931, 1929]
    (.letOp (n := 1935) (.exec 0x10b391 (fun s => s.RIP = 0x10b391) (mulR64Effect 0x10b391 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1931, 1929]
    (.letOp (n := 1936) (.out 0x10b394 (addR64M64Effect 0x10b394 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1933, 65]
    (.letOp (n := 1937) (.out 0x10b394 (addR64M64Effect 0x10b394 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[1933, 65]
    (.letOp (n := 1938) (.exec 0x10b394 (LoadPre 0x10b394 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10b394 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10b394 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1933, 65]
    (.letOp (n := 1939) (.out 0x10b399 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b399 5 2)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[1856, 1934, 1937]
    (.letOp (n := 1940) (.exec 0x10b399 (fun s => s.RIP = 0x10b399) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b399 5 2)) (Reg.operands [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1856, 1934, 1937]
    (.letOp (n := 1941) (.out 0x10b39c (shldR64R64Effect 0x10b39c 5 5 0 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[1939, 1936]
    (.letOp (n := 1942) (.exec 0x10b39c (fun s => s.RIP = 0x10b39c) (shldR64R64Effect 0x10b39c 5 5 0 12) (Reg.operands [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1939, 1936]
    (.letOp (n := 1943) (.out 0x10b3a1 (movR64R64Effect 0x10b3a1 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1936]
    (.letOp (n := 1944) (.exec 0x10b3a1 (fun s => s.RIP = 0x10b3a1) (movR64R64Effect 0x10b3a1 1 0) (Reg.operands [.gpr 0] [])) #v[1936]
    (.letOp (n := 1945) (.out 0x10b3a4 (movR64R64Effect 0x10b3a4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[1894]
    (.letOp (n := 1946) (.exec 0x10b3a4 (fun s => s.RIP = 0x10b3a4) (movR64R64Effect 0x10b3a4 0 6) (Reg.operands [.gpr 6] [])) #v[1894]
    (.letOp (n := 1947) (.out 0x10b3a7 (mulR64Effect 0x10b3a7 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[1760, 1945]
    (.letOp (n := 1948) (.out 0x10b3a7 (mulR64Effect 0x10b3a7 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[1760, 1945]
    (.letOp (n := 1949) (.exec 0x10b3a7 (fun s => s.RIP = 0x10b3a7) (mulR64Effect 0x10b3a7 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1760, 1945]
    (.letOp (n := 1950) (.exec 0x10b3aa (StorePre 0x10b3aa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x10b3aa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b3aa 2 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1948, 65]
    (.letOp (n := 1951) (.out 0x10b3b2 (movR64R64Effect 0x10b3b2 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[1947]
    (.letOp (n := 1952) (.exec 0x10b3b2 (fun s => s.RIP = 0x10b3b2) (movR64R64Effect 0x10b3b2 14 0) (Reg.operands [.gpr 0] [])) #v[1947]
    (.letOp (n := 1953) (.out 0x10b3b5 (movR64M64Effect 0x10b3b5 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1954) (.exec 0x10b3b5 (LoadPre 0x10b3b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10b3b5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b3b5 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_45))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_44 : List UInt8 :=
  [0x48, 0x03, 0x84, 0x24, 0xE0, 0x01, 0x00, 0x00, 0x4C, 0x13, 0xA4, 0x24, 0x88, 0x01, 0x00, 0x00,
    0x4C, 0x01, 0xC0, 0x49, 0x83, 0xD4, 0x00, 0x49, 0x0F, 0xA4, 0xC4, 0x0C, 0x48, 0xC1, 0xE0, 0x04,
    0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C, 0x09, 0xF0,
    0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x03, 0x44,
    0x24, 0x60, 0x48, 0x11, 0xD5, 0x48, 0x0F, 0xA4, 0xC5, 0x0C, 0x48, 0x89, 0xC1, 0x48, 0x89, 0xF0,
    0x48, 0xF7, 0xE7, 0x48, 0x89, 0x94, 0x24, 0x88, 0x01, 0x00, 0x00, 0x49, 0x89, 0xC6, 0x48, 0x8B,
    0x44, 0x24, 0x40] ++ bytes_l10a410_45

theorem code_l10a410_44 : ∀ x ∈ codeRange 0x10b357 bytes_l10a410_44, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb357 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_45

def b_l10a410_43 : Block Op Label signature Reg.count 1868 :=
  .letOp (n := 1868) (.exec 0x10b2fa (StorePre 0x10b2fa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x10b2fa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b2fa 2 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1866, 65]
    (.letOp (n := 1869) (.exec 0x10b302 (StorePre 0x10b302 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x10b302 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b302 0 (.sib 4 none 0 (.d32 0x1e0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1865, 65]
    (.letOp (n := 1870) (.out 0x10b30a (movR64M64Effect 0x10b30a 13 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 1871) (.exec 0x10b30a (LoadPre 0x10b30a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10b30a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b30a 13 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1872) (.out 0x10b312 (movR64R64Effect 0x10b312 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1870]
    (.letOp (n := 1873) (.exec 0x10b312 (fun s => s.RIP = 0x10b312) (movR64R64Effect 0x10b312 0 13) (Reg.operands [.gpr 13] [])) #v[1870]
    (.letOp (n := 1874) (.out 0x10b315 (movR64M64Effect 0x10b315 10 (.sib 4 none 0 (.d32 0x198))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 1875) (.exec 0x10b315 (LoadPre 0x10b315 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x10b315 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b315 10 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1876) (.out 0x10b31d (mulR64Effect 0x10b31d 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[1874, 1872]
    (.letOp (n := 1877) (.out 0x10b31d (mulR64Effect 0x10b31d 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[1874, 1872]
    (.letOp (n := 1878) (.exec 0x10b31d (fun s => s.RIP = 0x10b31d) (mulR64Effect 0x10b31d 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[1874, 1872]
    (.letOp (n := 1879) (.out 0x10b320 (movR64R64Effect 0x10b320 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[1876]
    (.letOp (n := 1880) (.exec 0x10b320 (fun s => s.RIP = 0x10b320) (movR64R64Effect 0x10b320 9 0) (Reg.operands [.gpr 0] [])) #v[1876]
    (.letOp (n := 1881) (.out 0x10b323 (movR64R64Effect 0x10b323 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1877]
    (.letOp (n := 1882) (.exec 0x10b323 (fun s => s.RIP = 0x10b323) (movR64R64Effect 0x10b323 1 2) (Reg.operands [.gpr 2] [])) #v[1877]
    (.letOp (n := 1883) (.out 0x10b326 (andR32Imm8Effect 0x10b326 4 14 0xf) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[1849]
    (.letOp (n := 1884) (.exec 0x10b326 (fun s => s.RIP = 0x10b326) (andR32Imm8Effect 0x10b326 4 14 0xf) (Reg.operands [.gpr 14] [])) #v[1849]
    (.letOp (n := 1885) (.out 0x10b32a (movR64M64Effect 0x10b32a 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1886) (.exec 0x10b32a (LoadPre 0x10b32a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10b32a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b32a 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1887) (.out 0x10b332 (mulR64Effect 0x10b332 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[1787, 1885]
    (.letOp (n := 1888) (.out 0x10b332 (mulR64Effect 0x10b332 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[1787, 1885]
    (.letOp (n := 1889) (.exec 0x10b332 (fun s => s.RIP = 0x10b332) (mulR64Effect 0x10b332 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1787, 1885]
    (.letOp (n := 1890) (.out 0x10b335 (movR64R64Effect 0x10b335 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[1888]
    (.letOp (n := 1891) (.exec 0x10b335 (fun s => s.RIP = 0x10b335) (movR64R64Effect 0x10b335 12 2) (Reg.operands [.gpr 2] [])) #v[1888]
    (.letOp (n := 1892) (.out 0x10b338 (movR64R64Effect 0x10b338 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[1887]
    (.letOp (n := 1893) (.exec 0x10b338 (fun s => s.RIP = 0x10b338) (movR64R64Effect 0x10b338 3 0) (Reg.operands [.gpr 0] [])) #v[1887]
    (.letOp (n := 1894) (.out 0x10b33b (movR64M64Effect 0x10b33b 6 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 1895) (.exec 0x10b33b (LoadPre 0x10b33b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10b33b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b33b 6 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1896) (.out 0x10b343 (movR64R64Effect 0x10b343 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[1894]
    (.letOp (n := 1897) (.exec 0x10b343 (fun s => s.RIP = 0x10b343) (movR64R64Effect 0x10b343 0 6) (Reg.operands [.gpr 6] [])) #v[1894]
    (.letOp (n := 1898) (.out 0x10b346 (mulM64Effect 0x10b346 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1896, 65]
    (.letOp (n := 1899) (.out 0x10b346 (mulM64Effect 0x10b346 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1896, 65]
    (.letOp (n := 1900) (.exec 0x10b346 (LoadPre 0x10b346 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10b346 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10b346 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1896, 65]
    (.letOp (n := 1901) (.out 0x10b34b (addR64R64Effect 0x10b34b 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[1898, 1892]
    (.letOp (n := 1902) (.out 0x10b34b (addR64R64Effect 0x10b34b 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[1898, 1892]
    (.letOp (n := 1903) (.exec 0x10b34b (fun s => s.RIP = 0x10b34b) (addR64R64Effect 0x10b34b 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[1898, 1892]
    (.letOp (n := 1904) (.out 0x10b34e (atFlags StatusFlags.CF (adcR64R64Effect 0x10b34e 12 2)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[1890, 1899, 1902]
    (.letOp (n := 1905) (.exec 0x10b34e (fun s => s.RIP = 0x10b34e) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b34e 12 2)) (Reg.operands [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1890, 1899, 1902]
    (.letOp (n := 1906) (.out 0x10b351 (addR64R64Effect 0x10b351 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[1901, 1879]
    (.letOp (n := 1907) (.out 0x10b351 (addR64R64Effect 0x10b351 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[1901, 1879]
    (.letOp (n := 1908) (.exec 0x10b351 (fun s => s.RIP = 0x10b351) (addR64R64Effect 0x10b351 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[1901, 1879]
    (.letOp (n := 1909) (.out 0x10b354 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b354 12 1)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[1904, 1881, 1907]
    (.letOp (n := 1910) (.exec 0x10b354 (fun s => s.RIP = 0x10b354) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b354 12 1)) (Reg.operands [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1904, 1881, 1907]
    (b_l10a410_44)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_43 : List UInt8 :=
  [0x48, 0x89, 0x94, 0x24, 0x88, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xE0, 0x01, 0x00, 0x00,
    0x4C, 0x8B, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE8, 0x4C, 0x8B, 0x94, 0x24, 0x98,
    0x01, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xC1, 0x48, 0x89, 0xD1, 0x41, 0x83, 0xE6, 0x0F,
    0x48, 0x8B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD4, 0x48, 0x89,
    0xC3, 0x48, 0x8B, 0xB4, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0x64, 0x24,
    0x20, 0x48, 0x01, 0xD8, 0x49, 0x11, 0xD4, 0x4C, 0x01, 0xC8, 0x49, 0x11, 0xCC] ++ bytes_l10a410_44

theorem code_l10a410_43 : ∀ x ∈ codeRange 0x10b2fa bytes_l10a410_43, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb2fa 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_44

def b_l10a410_42 : Block Op Label signature Reg.count 1824 :=
  .letOp (n := 1824) (.out 0x10b2a2 (addR64R64Effect 0x10b2a2 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[1819, 1774]
    (.letOp (n := 1825) (.out 0x10b2a2 (addR64R64Effect 0x10b2a2 13 10) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 10] []) (.flag .CF)) #v[1819, 1774]
    (.letOp (n := 1826) (.exec 0x10b2a2 (fun s => s.RIP = 0x10b2a2) (addR64R64Effect 0x10b2a2 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[1819, 1774]
    (.letOp (n := 1827) (.out 0x10b2a5 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b2a5 8 14)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1822, 1772, 1825]
    (.letOp (n := 1828) (.exec 0x10b2a5 (fun s => s.RIP = 0x10b2a5) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b2a5 8 14)) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1822, 1772, 1825]
    (.letOp (n := 1829) (.out 0x10b2a8 (addR64M64Effect 0x10b2a8 13 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[1824, 65]
    (.letOp (n := 1830) (.out 0x10b2a8 (addR64M64Effect 0x10b2a8 13 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[1824, 65]
    (.letOp (n := 1831) (.exec 0x10b2a8 (LoadPre 0x10b2a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10b2a8 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10b2a8 13 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[1824, 65]
    (.letOp (n := 1832) (.out 0x10b2b0 (atFlags StatusFlags.CF (adcR64M64Effect 0x10b2b0 8 (.sib 4 none 0 (.d8 0x60)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[1827, 65, 1830]
    (.letOp (n := 1833) (.exec 0x10b2b0 (LoadPre 0x10b2b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10b2b0 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10b2b0 8 (.sib 4 none 0 (.d8 0x60)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1827, 65, 1830]
    (.letOp (n := 1834) (.out 0x10b2b5 (addR64R64Effect 0x10b2b5 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[1811, 1829]
    (.letOp (n := 1835) (.out 0x10b2b5 (addR64R64Effect 0x10b2b5 0 13) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 13] []) (.flag .CF)) #v[1811, 1829]
    (.letOp (n := 1836) (.exec 0x10b2b5 (fun s => s.RIP = 0x10b2b5) (addR64R64Effect 0x10b2b5 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[1811, 1829]
    (.letOp (n := 1837) (.out 0x10b2b8 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b2b8 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1832, 1812, 1835]
    (.letOp (n := 1838) (.exec 0x10b2b8 (fun s => s.RIP = 0x10b2b8) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b2b8 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1832, 1812, 1835]
    (.letOp (n := 1839) (.out 0x10b2bb (movR64R64Effect 0x10b2bb 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[1834]
    (.letOp (n := 1840) (.exec 0x10b2bb (fun s => s.RIP = 0x10b2bb) (movR64R64Effect 0x10b2bb 14 0) (Reg.operands [.gpr 0] [])) #v[1834]
    (.letOp (n := 1841) (.out 0x10b2be (addR64R64Effect 0x10b2be 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[1839, 1756]
    (.letOp (n := 1842) (.out 0x10b2be (addR64R64Effect 0x10b2be 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[1839, 1756]
    (.letOp (n := 1843) (.exec 0x10b2be (fun s => s.RIP = 0x10b2be) (addR64R64Effect 0x10b2be 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[1839, 1756]
    (.letOp (n := 1844) (.exec 0x10b2c1 (StorePre 0x10b2c1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10b2c1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b2c1 14 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[1841, 65]
    (.letOp (n := 1845) (.out 0x10b2c9 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b2c9 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1837, 1842]
    (.letOp (n := 1846) (.exec 0x10b2c9 (fun s => s.RIP = 0x10b2c9) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b2c9 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1837, 1842]
    (.letOp (n := 1847) (.out 0x10b2cd (shldR64R64Effect 0x10b2cd 5 8 14 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[1845, 1841]
    (.letOp (n := 1848) (.exec 0x10b2cd (fun s => s.RIP = 0x10b2cd) (shldR64R64Effect 0x10b2cd 5 8 14 12) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1845, 1841]
    (.letOp (n := 1849) (.out 0x10b2d2 (shrR64Effect 0x10b2d2 4 14 48) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[1841]
    (.letOp (n := 1850) (.exec 0x10b2d2 (fun s => s.RIP = 0x10b2d2) (shrR64Effect 0x10b2d2 4 14 48) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1841]
    (.letOp (n := 1851) (.out 0x10b2d6 (movR64R64Effect 0x10b2d6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1796]
    (.letOp (n := 1852) (.exec 0x10b2d6 (fun s => s.RIP = 0x10b2d6) (movR64R64Effect 0x10b2d6 0 1) (Reg.operands [.gpr 1] [])) #v[1796]
    (.letOp (n := 1853) (.out 0x10b2d9 (mulR64Effect 0x10b2d9 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[1760, 1851]
    (.letOp (n := 1854) (.out 0x10b2d9 (mulR64Effect 0x10b2d9 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[1760, 1851]
    (.letOp (n := 1855) (.exec 0x10b2d9 (fun s => s.RIP = 0x10b2d9) (mulR64Effect 0x10b2d9 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1760, 1851]
    (.letOp (n := 1856) (.out 0x10b2dc (movR64R64Effect 0x10b2dc 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[1854]
    (.letOp (n := 1857) (.exec 0x10b2dc (fun s => s.RIP = 0x10b2dc) (movR64R64Effect 0x10b2dc 5 2) (Reg.operands [.gpr 2] [])) #v[1854]
    (.letOp (n := 1858) (.exec 0x10b2df (StorePre 0x10b2df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10b2df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b2df 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1853, 65]
    (.letOp (n := 1859) (.out 0x10b2e4 (movR64M64Effect 0x10b2e4 15 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 1860) (.exec 0x10b2e4 (LoadPre 0x10b2e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10b2e4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b2e4 15 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1861) (.out 0x10b2ec (movR64R64Effect 0x10b2ec 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[1859]
    (.letOp (n := 1862) (.exec 0x10b2ec (fun s => s.RIP = 0x10b2ec) (movR64R64Effect 0x10b2ec 0 15) (Reg.operands [.gpr 15] [])) #v[1859]
    (.letOp (n := 1863) (.out 0x10b2ef (movR64M64Effect 0x10b2ef 11 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 1864) (.exec 0x10b2ef (LoadPre 0x10b2ef (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x10b2ef + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b2ef 11 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1865) (.out 0x10b2f7 (mulR64Effect 0x10b2f7 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[1863, 1861]
    (.letOp (n := 1866) (.out 0x10b2f7 (mulR64Effect 0x10b2f7 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[1863, 1861]
    (.letOp (n := 1867) (.exec 0x10b2f7 (fun s => s.RIP = 0x10b2f7) (mulR64Effect 0x10b2f7 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[1863, 1861]
    (b_l10a410_43))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_42 : List UInt8 :=
  [0x4D, 0x01, 0xD5, 0x4D, 0x11, 0xF0, 0x4C, 0x03, 0xAC, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x4C, 0x13,
    0x44, 0x24, 0x60, 0x4C, 0x01, 0xE8, 0x49, 0x11, 0xD0, 0x49, 0x89, 0xC6, 0x4D, 0x01, 0xDE, 0x4C,
    0x89, 0xB4, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x49, 0x83, 0xD0, 0x00, 0x4D, 0x0F, 0xA4, 0xF0, 0x0C,
    0x49, 0xC1, 0xEE, 0x30, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD5, 0x48, 0x89, 0x44,
    0x24, 0x60, 0x4C, 0x8B, 0xBC, 0x24, 0x20, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF8, 0x4C, 0x8B, 0x9C,
    0x24, 0x70, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE3] ++ bytes_l10a410_43

theorem code_l10a410_42 : ∀ x ∈ codeRange 0x10b2a2 bytes_l10a410_42, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb2a2 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_43

def b_l10a410_41 : Block Op Label signature Reg.count 1778 :=
  .letOp (n := 1778) (.out 0x10b256 (mulR64Effect 0x10b256 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[1649, 1776]
    (.letOp (n := 1779) (.out 0x10b256 (mulR64Effect 0x10b256 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[1649, 1776]
    (.letOp (n := 1780) (.exec 0x10b256 (fun s => s.RIP = 0x10b256) (mulR64Effect 0x10b256 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1649, 1776]
    (.letOp (n := 1781) (.out 0x10b259 (movR64R64Effect 0x10b259 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1779]
    (.letOp (n := 1782) (.exec 0x10b259 (fun s => s.RIP = 0x10b259) (movR64R64Effect 0x10b259 6 2) (Reg.operands [.gpr 2] [])) #v[1779]
    (.letOp (n := 1783) (.out 0x10b25c (movR64R64Effect 0x10b25c 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[1778]
    (.letOp (n := 1784) (.exec 0x10b25c (fun s => s.RIP = 0x10b25c) (movR64R64Effect 0x10b25c 9 0) (Reg.operands [.gpr 0] [])) #v[1778]
    (.letOp (n := 1785) (.out 0x10b25f (movR64R64Effect 0x10b25f 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1655]
    (.letOp (n := 1786) (.exec 0x10b25f (fun s => s.RIP = 0x10b25f) (movR64R64Effect 0x10b25f 0 5) (Reg.operands [.gpr 5] [])) #v[1655]
    (.letOp (n := 1787) (.out 0x10b262 (movR64M64Effect 0x10b262 3 (.sib 4 none 0 (.d32 0x1c8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 1788) (.exec 0x10b262 (LoadPre 0x10b262 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x10b262 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b262 3 (.sib 4 none 0 (.d32 0x1c8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1789) (.out 0x10b26a (mulR64Effect 0x10b26a 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[1787, 1785]
    (.letOp (n := 1790) (.out 0x10b26a (mulR64Effect 0x10b26a 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[1787, 1785]
    (.letOp (n := 1791) (.exec 0x10b26a (fun s => s.RIP = 0x10b26a) (mulR64Effect 0x10b26a 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1787, 1785]
    (.letOp (n := 1792) (.out 0x10b26d (movR64R64Effect 0x10b26d 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[1790]
    (.letOp (n := 1793) (.exec 0x10b26d (fun s => s.RIP = 0x10b26d) (movR64R64Effect 0x10b26d 12 2) (Reg.operands [.gpr 2] [])) #v[1790]
    (.letOp (n := 1794) (.out 0x10b270 (movR64R64Effect 0x10b270 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[1789]
    (.letOp (n := 1795) (.exec 0x10b270 (fun s => s.RIP = 0x10b270) (movR64R64Effect 0x10b270 5 0) (Reg.operands [.gpr 0] [])) #v[1789]
    (.letOp (n := 1796) (.out 0x10b273 (movR64M64Effect 0x10b273 1 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 1797) (.exec 0x10b273 (LoadPre 0x10b273 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10b273 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b273 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1798) (.out 0x10b278 (movR64R64Effect 0x10b278 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1796]
    (.letOp (n := 1799) (.exec 0x10b278 (fun s => s.RIP = 0x10b278) (movR64R64Effect 0x10b278 0 1) (Reg.operands [.gpr 1] [])) #v[1796]
    (.letOp (n := 1800) (.out 0x10b27b (mulM64Effect 0x10b27b 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1798, 65]
    (.letOp (n := 1801) (.out 0x10b27b (mulM64Effect 0x10b27b 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1798, 65]
    (.letOp (n := 1802) (.exec 0x10b27b (LoadPre 0x10b27b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10b27b + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10b27b 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1798, 65]
    (.letOp (n := 1803) (.out 0x10b280 (movR64R64Effect 0x10b280 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[1801]
    (.letOp (n := 1804) (.exec 0x10b280 (fun s => s.RIP = 0x10b280) (movR64R64Effect 0x10b280 8 2) (Reg.operands [.gpr 2] [])) #v[1801]
    (.letOp (n := 1805) (.out 0x10b283 (movR64R64Effect 0x10b283 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[1800]
    (.letOp (n := 1806) (.exec 0x10b283 (fun s => s.RIP = 0x10b283) (movR64R64Effect 0x10b283 13 0) (Reg.operands [.gpr 0] [])) #v[1800]
    (.letOp (n := 1807) (.out 0x10b286 (movR64R64Effect 0x10b286 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[1754]
    (.letOp (n := 1808) (.exec 0x10b286 (fun s => s.RIP = 0x10b286) (movR64R64Effect 0x10b286 0 15) (Reg.operands [.gpr 15] [])) #v[1754]
    (.letOp (n := 1809) (.out 0x10b289 (movR64Imm64Effect 0x10b289 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1810) (.exec 0x10b289 (fun s => s.RIP = 0x10b289) (movR64Imm64Effect 0x10b289 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1811) (.out 0x10b293 (mulR64Effect 0x10b293 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1809, 1807]
    (.letOp (n := 1812) (.out 0x10b293 (mulR64Effect 0x10b293 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1809, 1807]
    (.letOp (n := 1813) (.exec 0x10b293 (fun s => s.RIP = 0x10b293) (mulR64Effect 0x10b293 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1809, 1807]
    (.letOp (n := 1814) (.out 0x10b296 (addR64R64Effect 0x10b296 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[1805, 1794]
    (.letOp (n := 1815) (.out 0x10b296 (addR64R64Effect 0x10b296 13 5) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 5] []) (.flag .CF)) #v[1805, 1794]
    (.letOp (n := 1816) (.exec 0x10b296 (fun s => s.RIP = 0x10b296) (addR64R64Effect 0x10b296 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[1805, 1794]
    (.letOp (n := 1817) (.out 0x10b299 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b299 8 12)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1803, 1792, 1815]
    (.letOp (n := 1818) (.exec 0x10b299 (fun s => s.RIP = 0x10b299) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b299 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1803, 1792, 1815]
    (.letOp (n := 1819) (.out 0x10b29c (addR64R64Effect 0x10b29c 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[1814, 1783]
    (.letOp (n := 1820) (.out 0x10b29c (addR64R64Effect 0x10b29c 13 9) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 9] []) (.flag .CF)) #v[1814, 1783]
    (.letOp (n := 1821) (.exec 0x10b29c (fun s => s.RIP = 0x10b29c) (addR64R64Effect 0x10b29c 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[1814, 1783]
    (.letOp (n := 1822) (.out 0x10b29f (atFlags StatusFlags.CF (adcR64R64Effect 0x10b29f 8 6)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1817, 1781, 1820]
    (.letOp (n := 1823) (.exec 0x10b29f (fun s => s.RIP = 0x10b29f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b29f 8 6)) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1817, 1781, 1820]
    (b_l10a410_42))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_41 : List UInt8 :=
  [0x48, 0xF7, 0xE3, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC1, 0x48, 0x89, 0xE8, 0x48, 0x8B, 0x9C, 0x24,
    0xC8, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD4, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0x4C,
    0x24, 0x40, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0x64, 0x24, 0x20, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC5,
    0x4C, 0x89, 0xF8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x49, 0x01, 0xED, 0x4D, 0x11, 0xE0, 0x4D, 0x01, 0xCD, 0x49, 0x11, 0xF0] ++ bytes_l10a410_42

theorem code_l10a410_41 : ∀ x ∈ codeRange 0x10b256 bytes_l10a410_41, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb256 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_42

def b_l10a410_40 : Block Op Label signature Reg.count 1736 :=
  .letOp (n := 1736) (.out 0x10b1ea (atFlags StatusFlags.CF (adcR64R64Effect 0x10b1ea 11 14)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1687, 1666, 1734]
    (.letOp (n := 1737) (.exec 0x10b1ea (fun s => s.RIP = 0x10b1ea) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b1ea 11 14)) (Reg.operands [.gpr 11, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1687, 1666, 1734]
    (.letOp (n := 1738) (.out 0x10b1ed (addR64M64Effect 0x10b1ed 10 (.sib 4 none 0 (.d32 0x188))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[1733, 65]
    (.letOp (n := 1739) (.out 0x10b1ed (addR64M64Effect 0x10b1ed 10 (.sib 4 none 0 (.d32 0x188))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[1733, 65]
    (.letOp (n := 1740) (.exec 0x10b1ed (LoadPre 0x10b1ed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x10b1ed + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10b1ed 10 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[1733, 65]
    (.letOp (n := 1741) (.out 0x10b1f5 (atFlags StatusFlags.CF (adcR64M64Effect 0x10b1f5 11 (.sib 4 none 0 (.d32 0x1b0)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[1736, 65, 1739]
    (.letOp (n := 1742) (.exec 0x10b1f5 (LoadPre 0x10b1f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x10b1f5 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10b1f5 11 (.sib 4 none 0 (.d32 0x1b0)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1736, 65, 1739]
    (.letOp (n := 1743) (.out 0x10b1fd (addR64M64Effect 0x10b1fd 10 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[1738, 65]
    (.letOp (n := 1744) (.out 0x10b1fd (addR64M64Effect 0x10b1fd 10 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[1738, 65]
    (.letOp (n := 1745) (.exec 0x10b1fd (LoadPre 0x10b1fd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10b1fd + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10b1fd 10 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[1738, 65]
    (.letOp (n := 1746) (.out 0x10b205 (atFlags StatusFlags.CF (adcR64M64Effect 0x10b205 11 (.sib 4 none 0 (.d8 0x60)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[1741, 65, 1744]
    (.letOp (n := 1747) (.exec 0x10b205 (LoadPre 0x10b205 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10b205 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10b205 11 (.sib 4 none 0 (.d8 0x60)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1741, 65, 1744]
    (.letOp (n := 1748) (.out 0x10b20a (addR64R64Effect 0x10b20a 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[1727, 1743]
    (.letOp (n := 1749) (.out 0x10b20a (addR64R64Effect 0x10b20a 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[1727, 1743]
    (.letOp (n := 1750) (.exec 0x10b20a (fun s => s.RIP = 0x10b20a) (addR64R64Effect 0x10b20a 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[1727, 1743]
    (.letOp (n := 1751) (.exec 0x10b20d (StorePre 0x10b20d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x10b20d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b20d 0 (.sib 4 none 0 (.d32 0x1b0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1748, 65]
    (.letOp (n := 1752) (.out 0x10b215 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b215 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1746, 1728, 1749]
    (.letOp (n := 1753) (.exec 0x10b215 (fun s => s.RIP = 0x10b215) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b215 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1746, 1728, 1749]
    (.letOp (n := 1754) (.out 0x10b218 (shldR64R64Effect 0x10b218 5 15 9 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[1716, 1714]
    (.letOp (n := 1755) (.exec 0x10b218 (fun s => s.RIP = 0x10b218) (shldR64R64Effect 0x10b218 5 15 9 12) (Reg.operands [.gpr 15, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1716, 1714]
    (.letOp (n := 1756) (.out 0x10b21d (shldR64R64Effect 0x10b21d 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1752, 1748]
    (.letOp (n := 1757) (.exec 0x10b21d (fun s => s.RIP = 0x10b21d) (shldR64R64Effect 0x10b21d 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1752, 1748]
    (.letOp (n := 1758) (.out 0x10b222 (movR64R64Effect 0x10b222 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1706]
    (.letOp (n := 1759) (.exec 0x10b222 (fun s => s.RIP = 0x10b222) (movR64R64Effect 0x10b222 0 1) (Reg.operands [.gpr 1] [])) #v[1706]
    (.letOp (n := 1760) (.out 0x10b225 (movR64M64Effect 0x10b225 7 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 1761) (.exec 0x10b225 (LoadPre 0x10b225 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10b225 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b225 7 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1762) (.out 0x10b22d (mulR64Effect 0x10b22d 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[1760, 1758]
    (.letOp (n := 1763) (.out 0x10b22d (mulR64Effect 0x10b22d 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[1760, 1758]
    (.letOp (n := 1764) (.exec 0x10b22d (fun s => s.RIP = 0x10b22d) (mulR64Effect 0x10b22d 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1760, 1758]
    (.letOp (n := 1765) (.exec 0x10b230 (StorePre 0x10b230 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10b230 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b230 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1763, 65]
    (.letOp (n := 1766) (.exec 0x10b235 (StorePre 0x10b235 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10b235 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b235 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1762, 65]
    (.letOp (n := 1767) (.out 0x10b23d (movR64M64Effect 0x10b23d 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1768) (.exec 0x10b23d (LoadPre 0x10b23d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10b23d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b23d 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1769) (.out 0x10b245 (mulR64Effect 0x10b245 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[1630, 1767]
    (.letOp (n := 1770) (.out 0x10b245 (mulR64Effect 0x10b245 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[1630, 1767]
    (.letOp (n := 1771) (.exec 0x10b245 (fun s => s.RIP = 0x10b245) (mulR64Effect 0x10b245 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[1630, 1767]
    (.letOp (n := 1772) (.out 0x10b248 (movR64R64Effect 0x10b248 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[1770]
    (.letOp (n := 1773) (.exec 0x10b248 (fun s => s.RIP = 0x10b248) (movR64R64Effect 0x10b248 14 2) (Reg.operands [.gpr 2] [])) #v[1770]
    (.letOp (n := 1774) (.out 0x10b24b (movR64R64Effect 0x10b24b 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[1769]
    (.letOp (n := 1775) (.exec 0x10b24b (fun s => s.RIP = 0x10b24b) (movR64R64Effect 0x10b24b 10 0) (Reg.operands [.gpr 0] [])) #v[1769]
    (.letOp (n := 1776) (.out 0x10b24e (movR64M64Effect 0x10b24e 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1777) (.exec 0x10b24e (LoadPre 0x10b24e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10b24e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b24e 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_41))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_40 : List UInt8 :=
  [0x4D, 0x11, 0xF3, 0x4C, 0x03, 0x94, 0x24, 0x88, 0x01, 0x00, 0x00, 0x4C, 0x13, 0x9C, 0x24, 0xB0,
    0x01, 0x00, 0x00, 0x4C, 0x03, 0x94, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x5C, 0x24, 0x60,
    0x4C, 0x01, 0xD0, 0x48, 0x89, 0x84, 0x24, 0xB0, 0x01, 0x00, 0x00, 0x49, 0x11, 0xD3, 0x4D, 0x0F,
    0xA4, 0xCF, 0x0C, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0x89, 0xC8, 0x48, 0x8B, 0xBC, 0x24, 0x30,
    0x01, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0x54, 0x24, 0x60, 0x48, 0x89, 0x84, 0x24, 0xE8,
    0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE4, 0x49, 0x89,
    0xD6, 0x49, 0x89, 0xC2, 0x48, 0x8B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] ++ bytes_l10a410_41

theorem code_l10a410_40 : ∀ x ∈ codeRange 0x10b1ea bytes_l10a410_40, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb1ea 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_41

def b_l10a410_39 : Block Op Label signature Reg.count 1697 :=
  .letOp (n := 1697) (.out 0x10b17e (movR64M64Effect 0x10b17e 2 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 1698) (.exec 0x10b17e (LoadPre 0x10b17e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10b17e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b17e 2 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1699) (.out 0x10b186 (leaR64Effect 0x10b186 9 (.sib 2 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2, .gpr 0] []) (.reg (.gpr 9))) #v[1697, 1695]
    (.letOp (n := 1700) (.exec 0x10b186 (fun s => s.RIP = 0x10b186) (leaR64Effect 0x10b186 9 (.sib 2 (some 0) 0 .none)) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1697, 1695]
    (.letOp (n := 1701) (.exec 0x10b18a (StorePre 0x10b18a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10b18a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b18a 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[1699, 65]
    (.letOp (n := 1702) (.out 0x10b18f (movR64M64Effect 0x10b18f 0 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1703) (.exec 0x10b18f (LoadPre 0x10b18f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10b18f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b18f 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1704) (.out 0x10b197 (movR64M64Effect 0x10b197 2 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 1705) (.exec 0x10b197 (LoadPre 0x10b197 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10b197 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b197 2 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1706) (.out 0x10b19f (leaR64Effect 0x10b19f 1 (.sib 2 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 0] []) (.reg (.gpr 1))) #v[1704, 1702]
    (.letOp (n := 1707) (.exec 0x10b19f (fun s => s.RIP = 0x10b19f) (leaR64Effect 0x10b19f 1 (.sib 2 (some 0) 0 .none)) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1704, 1702]
    (.letOp (n := 1708) (.out 0x10b1a3 (movR64R64Effect 0x10b1a3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1706]
    (.letOp (n := 1709) (.exec 0x10b1a3 (fun s => s.RIP = 0x10b1a3) (movR64R64Effect 0x10b1a3 0 1) (Reg.operands [.gpr 1] [])) #v[1706]
    (.letOp (n := 1710) (.exec 0x10b1a6 (StorePre 0x10b1a6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10b1a6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b1a6 1 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1706, 65]
    (.letOp (n := 1711) (.out 0x10b1ae (mulR64Effect 0x10b1ae 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[1699, 1708]
    (.letOp (n := 1712) (.out 0x10b1ae (mulR64Effect 0x10b1ae 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[1699, 1708]
    (.letOp (n := 1713) (.exec 0x10b1ae (fun s => s.RIP = 0x10b1ae) (mulR64Effect 0x10b1ae 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1699, 1708]
    (.letOp (n := 1714) (.out 0x10b1b1 (movR64R64Effect 0x10b1b1 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[1711]
    (.letOp (n := 1715) (.exec 0x10b1b1 (fun s => s.RIP = 0x10b1b1) (movR64R64Effect 0x10b1b1 9 0) (Reg.operands [.gpr 0] [])) #v[1711]
    (.letOp (n := 1716) (.out 0x10b1b4 (movR64R64Effect 0x10b1b4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[1712]
    (.letOp (n := 1717) (.exec 0x10b1b4 (fun s => s.RIP = 0x10b1b4) (movR64R64Effect 0x10b1b4 15 2) (Reg.operands [.gpr 2] [])) #v[1712]
    (.letOp (n := 1718) (.out 0x10b1b7 (addR64R64Effect 0x10b1b7 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[1693, 1605]
    (.letOp (n := 1719) (.exec 0x10b1b7 (fun s => s.RIP = 0x10b1b7) (addR64R64Effect 0x10b1b7 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[1693, 1605]
    (.letOp (n := 1720) (.exec 0x10b1ba (StorePre 0x10b1ba 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10b1ba + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b1ba 13 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[1718, 65]
    (.letOp (n := 1721) (.out 0x10b1c2 (movR64Imm64Effect 0x10b1c2 8 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 1722) (.exec 0x10b1c2 (fun s => s.RIP = 0x10b1c2) (movR64Imm64Effect 0x10b1c2 8 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1723) (.out 0x10b1cc (andR64R64Effect 0x10b1cc 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[1711, 1721]
    (.letOp (n := 1724) (.exec 0x10b1cc (fun s => s.RIP = 0x10b1cc) (andR64R64Effect 0x10b1cc 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[1711, 1721]
    (.letOp (n := 1725) (.out 0x10b1cf (movR64Imm64Effect 0x10b1cf 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1726) (.exec 0x10b1cf (fun s => s.RIP = 0x10b1cf) (movR64Imm64Effect 0x10b1cf 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1727) (.out 0x10b1d9 (mulR64Effect 0x10b1d9 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1725, 1723]
    (.letOp (n := 1728) (.out 0x10b1d9 (mulR64Effect 0x10b1d9 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1725, 1723]
    (.letOp (n := 1729) (.exec 0x10b1d9 (fun s => s.RIP = 0x10b1d9) (mulR64Effect 0x10b1d9 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1725, 1723]
    (.letOp (n := 1730) (.out 0x10b1dc (andR64R64Effect 0x10b1dc 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[1600, 1721]
    (.letOp (n := 1731) (.exec 0x10b1dc (fun s => s.RIP = 0x10b1dc) (andR64R64Effect 0x10b1dc 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[1600, 1721]
    (.letOp (n := 1732) (.exec 0x10b1df (StorePre 0x10b1df 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10b1df + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b1df 7 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1730, 65]
    (.letOp (n := 1733) (.out 0x10b1e7 (addR64R64Effect 0x10b1e7 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[1685, 1664]
    (.letOp (n := 1734) (.out 0x10b1e7 (addR64R64Effect 0x10b1e7 10 6) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 6] []) (.flag .CF)) #v[1685, 1664]
    (.letOp (n := 1735) (.exec 0x10b1e7 (fun s => s.RIP = 0x10b1e7) (addR64R64Effect 0x10b1e7 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[1685, 1664]
    (b_l10a410_40)))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_39 : List UInt8 :=
  [0x48, 0x8B, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0x0C, 0x02, 0x4C, 0x89, 0x4C, 0x24,
    0x20, 0x48, 0x8B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0x00, 0x01, 0x00,
    0x00, 0x48, 0x8D, 0x0C, 0x02, 0x48, 0x89, 0xC8, 0x48, 0x89, 0x8C, 0x24, 0x20, 0x01, 0x00, 0x00,
    0x49, 0xF7, 0xE1, 0x49, 0x89, 0xC1, 0x49, 0x89, 0xD7, 0x4D, 0x01, 0xC5, 0x4C, 0x89, 0xAC, 0x24,
    0x98, 0x00, 0x00, 0x00, 0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21,
    0xC0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x21,
    0xC7, 0x48, 0x89, 0xBC, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x49, 0x01, 0xF2] ++ bytes_l10a410_40

theorem code_l10a410_39 : ∀ x ∈ codeRange 0x10b17e bytes_l10a410_39, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb17e 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_40

def b_l10a410_38 : Block Op Label signature Reg.count 1659 :=
  .letOp (n := 1659) (.exec 0x10b10f (StorePre 0x10b10f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10b10f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b10f 5 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[1655, 65]
    (.letOp (n := 1660) (.out 0x10b117 (mulR64Effect 0x10b117 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[1649, 1657]
    (.letOp (n := 1661) (.out 0x10b117 (mulR64Effect 0x10b117 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[1649, 1657]
    (.letOp (n := 1662) (.exec 0x10b117 (fun s => s.RIP = 0x10b117) (mulR64Effect 0x10b117 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1649, 1657]
    (.letOp (n := 1663) (.exec 0x10b11a (StorePre 0x10b11a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x10b11a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b11a 3 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1649, 65]
    (.letOp (n := 1664) (.out 0x10b122 (movR64R64Effect 0x10b122 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1660]
    (.letOp (n := 1665) (.exec 0x10b122 (fun s => s.RIP = 0x10b122) (movR64R64Effect 0x10b122 6 0) (Reg.operands [.gpr 0] [])) #v[1660]
    (.letOp (n := 1666) (.out 0x10b125 (movR64R64Effect 0x10b125 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[1661]
    (.letOp (n := 1667) (.exec 0x10b125 (fun s => s.RIP = 0x10b125) (movR64R64Effect 0x10b125 14 2) (Reg.operands [.gpr 2] [])) #v[1661]
    (.letOp (n := 1668) (.out 0x10b128 (movR64M64Effect 0x10b128 0 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1669) (.exec 0x10b128 (LoadPre 0x10b128 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10b128 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b128 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1670) (.out 0x10b130 (movR64M64Effect 0x10b130 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 1671) (.exec 0x10b130 (LoadPre 0x10b130 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10b130 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b130 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1672) (.out 0x10b138 (leaR64Effect 0x10b138 1 (.sib 2 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 0] []) (.reg (.gpr 1))) #v[1670, 1668]
    (.letOp (n := 1673) (.exec 0x10b138 (fun s => s.RIP = 0x10b138) (leaR64Effect 0x10b138 1 (.sib 2 (some 0) 0 .none)) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1670, 1668]
    (.letOp (n := 1674) (.exec 0x10b13c (StorePre 0x10b13c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x10b13c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b13c 1 (.sib 4 none 0 (.d32 0x1c8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1672, 65]
    (.letOp (n := 1675) (.out 0x10b144 (movR64M64Effect 0x10b144 0 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1676) (.exec 0x10b144 (LoadPre 0x10b144 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10b144 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b144 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1677) (.out 0x10b14c (movR64M64Effect 0x10b14c 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 1678) (.exec 0x10b14c (LoadPre 0x10b14c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10b14c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10b14c 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1679) (.out 0x10b150 (addR64R64Effect 0x10b150 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1675, 1677]
    (.letOp (n := 1680) (.exec 0x10b150 (fun s => s.RIP = 0x10b150) (addR64R64Effect 0x10b150 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1675, 1677]
    (.letOp (n := 1681) (.exec 0x10b153 (StorePre 0x10b153 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10b153 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b153 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1679, 65]
    (.letOp (n := 1682) (.out 0x10b158 (mulR64Effect 0x10b158 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1672, 1679]
    (.letOp (n := 1683) (.out 0x10b158 (mulR64Effect 0x10b158 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1672, 1679]
    (.letOp (n := 1684) (.exec 0x10b158 (fun s => s.RIP = 0x10b158) (mulR64Effect 0x10b158 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1672, 1679]
    (.letOp (n := 1685) (.out 0x10b15b (movR64R64Effect 0x10b15b 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[1682]
    (.letOp (n := 1686) (.exec 0x10b15b (fun s => s.RIP = 0x10b15b) (movR64R64Effect 0x10b15b 10 0) (Reg.operands [.gpr 0] [])) #v[1682]
    (.letOp (n := 1687) (.out 0x10b15e (movR64R64Effect 0x10b15e 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[1683]
    (.letOp (n := 1688) (.exec 0x10b15e (fun s => s.RIP = 0x10b15e) (movR64R64Effect 0x10b15e 11 2) (Reg.operands [.gpr 2] [])) #v[1683]
    (.letOp (n := 1689) (.out 0x10b161 (movR64Imm64Effect 0x10b161 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1690) (.exec 0x10b161 (fun s => s.RIP = 0x10b161) (movR64Imm64Effect 0x10b161 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1691) (.out 0x10b16b (movR64M64Effect 0x10b16b 13 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 1692) (.exec 0x10b16b (LoadPre 0x10b16b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10b16b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b16b 13 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1693) (.out 0x10b173 (andR64R64Effect 0x10b173 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[1691, 1689]
    (.letOp (n := 1694) (.exec 0x10b173 (fun s => s.RIP = 0x10b173) (andR64R64Effect 0x10b173 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1691, 1689]
    (.letOp (n := 1695) (.out 0x10b176 (movR64M64Effect 0x10b176 0 (.sib 4 none 0 (.d32 0x1c0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1696) (.exec 0x10b176 (LoadPre 0x10b176 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x10b176 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b176 0 (.sib 4 none 0 (.d32 0x1c0))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_39))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_38 : List UInt8 :=
  [0x48, 0x89, 0xAC, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0x9C, 0x24, 0x98,
    0x01, 0x00, 0x00, 0x48, 0x89, 0xC6, 0x49, 0x89, 0xD6, 0x48, 0x8B, 0x84, 0x24, 0xE0, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x0C, 0x02, 0x48, 0x89, 0x8C,
    0x24, 0xC8, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x14,
    0x24, 0x48, 0x01, 0xD0, 0x48, 0x89, 0x44, 0x24, 0x40, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xC2, 0x49,
    0x89, 0xD3, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x4C, 0x8B, 0xAC, 0x24,
    0x98, 0x00, 0x00, 0x00, 0x49, 0x21, 0xC5, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x01, 0x00, 0x00] ++ bytes_l10a410_39

theorem code_l10a410_38 : ∀ x ∈ codeRange 0x10b10f bytes_l10a410_38, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb10f 111 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_39

def b_l10a410_37 : Block Op Label signature Reg.count 1624 :=
  .letOp (n := 1624) (.exec 0x10b096 (StorePre 0x10b096 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10b096 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b096 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1621, 65]
    (.letOp (n := 1625) (.exec 0x10b09e (StorePre 0x10b09e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10b09e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10b09e 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1622, 65]
    (.letOp (n := 1626) (.out 0x10b0a3 (movR64M64Effect 0x10b0a3 0 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1627) (.exec 0x10b0a3 (LoadPre 0x10b0a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10b0a3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b0a3 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1628) (.out 0x10b0ab (movR64M64Effect 0x10b0ab 2 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 1629) (.exec 0x10b0ab (LoadPre 0x10b0ab (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10b0ab + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b0ab 2 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1630) (.out 0x10b0b3 (leaR64Effect 0x10b0b3 12 (.sib 2 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2, .gpr 0] []) (.reg (.gpr 12))) #v[1628, 1626]
    (.letOp (n := 1631) (.exec 0x10b0b3 (fun s => s.RIP = 0x10b0b3) (leaR64Effect 0x10b0b3 12 (.sib 2 (some 0) 0 .none)) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1628, 1626]
    (.letOp (n := 1632) (.out 0x10b0b7 (movR64M64Effect 0x10b0b7 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1633) (.exec 0x10b0b7 (LoadPre 0x10b0b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10b0b7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b0b7 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1634) (.out 0x10b0bf (movR64M64Effect 0x10b0bf 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 1635) (.exec 0x10b0bf (LoadPre 0x10b0bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10b0bf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b0bf 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1636) (.out 0x10b0c4 (addR64R64Effect 0x10b0c4 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1632, 1634]
    (.letOp (n := 1637) (.exec 0x10b0c4 (fun s => s.RIP = 0x10b0c4) (addR64R64Effect 0x10b0c4 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1632, 1634]
    (.letOp (n := 1638) (.exec 0x10b0c7 (StorePre 0x10b0c7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10b0c7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b0c7 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1636, 65]
    (.letOp (n := 1639) (.out 0x10b0cf (mulR64Effect 0x10b0cf 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[1630, 1636]
    (.letOp (n := 1640) (.out 0x10b0cf (mulR64Effect 0x10b0cf 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[1630, 1636]
    (.letOp (n := 1641) (.exec 0x10b0cf (fun s => s.RIP = 0x10b0cf) (mulR64Effect 0x10b0cf 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[1630, 1636]
    (.letOp (n := 1642) (.exec 0x10b0d2 (StorePre 0x10b0d2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x10b0d2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b0d2 12 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[1630, 65]
    (.letOp (n := 1643) (.exec 0x10b0da (StorePre 0x10b0da 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x10b0da + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b0da 0 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1639, 65]
    (.letOp (n := 1644) (.exec 0x10b0e2 (StorePre 0x10b0e2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x10b0e2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b0e2 2 (.sib 4 none 0 (.d32 0x1b0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1640, 65]
    (.letOp (n := 1645) (.out 0x10b0ea (movR64M64Effect 0x10b0ea 0 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1646) (.exec 0x10b0ea (LoadPre 0x10b0ea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10b0ea + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b0ea 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1647) (.out 0x10b0f2 (movR64M64Effect 0x10b0f2 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 1648) (.exec 0x10b0f2 (LoadPre 0x10b0f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10b0f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b0f2 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1649) (.out 0x10b0f7 (leaR64Effect 0x10b0f7 3 (.sib 2 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2, .gpr 0] []) (.reg (.gpr 3))) #v[1647, 1645]
    (.letOp (n := 1650) (.exec 0x10b0f7 (fun s => s.RIP = 0x10b0f7) (leaR64Effect 0x10b0f7 3 (.sib 2 (some 0) 0 .none)) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1647, 1645]
    (.letOp (n := 1651) (.out 0x10b0fb (movR64M64Effect 0x10b0fb 0 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1652) (.exec 0x10b0fb (LoadPre 0x10b0fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x10b0fb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b0fb 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1653) (.out 0x10b103 (movR64M64Effect 0x10b103 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 1654) (.exec 0x10b103 (LoadPre 0x10b103 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10b103 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b103 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1655) (.out 0x10b108 (leaR64Effect 0x10b108 5 (.sib 2 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2, .gpr 0] []) (.reg (.gpr 5))) #v[1653, 1651]
    (.letOp (n := 1656) (.exec 0x10b108 (fun s => s.RIP = 0x10b108) (leaR64Effect 0x10b108 5 (.sib 2 (some 0) 0 .none)) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1653, 1651]
    (.letOp (n := 1657) (.out 0x10b10c (movR64R64Effect 0x10b10c 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1655]
    (.letOp (n := 1658) (.exec 0x10b10c (fun s => s.RIP = 0x10b10c) (movR64R64Effect 0x10b10c 0 5) (Reg.operands [.gpr 5] [])) #v[1655]
    (b_l10a410_38)))))))))))))))))))))))))))))))))))

def bytes_l10a410_37 : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x60, 0x48, 0x8B, 0x84,
    0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0x24,
    0x02, 0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x78, 0x48, 0x01,
    0xD0, 0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE4, 0x4C, 0x89, 0xA4, 0x24,
    0x70, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24,
    0xB0, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24,
    0x28, 0x48, 0x8D, 0x1C, 0x02, 0x48, 0x8B, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x54,
    0x24, 0x10, 0x48, 0x8D, 0x2C, 0x02, 0x48, 0x89, 0xE8] ++ bytes_l10a410_38

theorem code_l10a410_37 : ∀ x ∈ codeRange 0x10b096 bytes_l10a410_37, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb096 121 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_38

def b_l10a410_36 : Block Op Label signature Reg.count 1583 :=
  .letOp (n := 1583) (.exec 0x10b033 (StorePre 0x10b033 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x10b033 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b033 10 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[1581, 65]
    (.letOp (n := 1584) (.out 0x10b03b (movR64R64Effect 0x10b03b 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[1577]
    (.letOp (n := 1585) (.exec 0x10b03b (fun s => s.RIP = 0x10b03b) (movR64R64Effect 0x10b03b 0 3) (Reg.operands [.gpr 3] [])) #v[1577]
    (.letOp (n := 1586) (.out 0x10b03e (mulR64Effect 0x10b03e 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1552, 1584]
    (.letOp (n := 1587) (.out 0x10b03e (mulR64Effect 0x10b03e 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1552, 1584]
    (.letOp (n := 1588) (.exec 0x10b03e (fun s => s.RIP = 0x10b03e) (mulR64Effect 0x10b03e 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1552, 1584]
    (.letOp (n := 1589) (.out 0x10b041 (movR64R64Effect 0x10b041 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[1587]
    (.letOp (n := 1590) (.exec 0x10b041 (fun s => s.RIP = 0x10b041) (movR64R64Effect 0x10b041 8 2) (Reg.operands [.gpr 2] [])) #v[1587]
    (.letOp (n := 1591) (.out 0x10b044 (movR64M64Effect 0x10b044 7 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 1592) (.exec 0x10b044 (LoadPre 0x10b044 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10b044 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b044 7 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1593) (.out 0x10b04c (andR64R64Effect 0x10b04c 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[1591, 1517]
    (.letOp (n := 1594) (.exec 0x10b04c (fun s => s.RIP = 0x10b04c) (andR64R64Effect 0x10b04c 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[1591, 1517]
    (.letOp (n := 1595) (.out 0x10b04f (addR64R64Effect 0x10b04f 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[1593, 1586]
    (.letOp (n := 1596) (.out 0x10b04f (addR64R64Effect 0x10b04f 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[1593, 1586]
    (.letOp (n := 1597) (.exec 0x10b04f (fun s => s.RIP = 0x10b04f) (addR64R64Effect 0x10b04f 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1593, 1586]
    (.letOp (n := 1598) (.out 0x10b052 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b052 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1589, 1596]
    (.letOp (n := 1599) (.exec 0x10b052 (fun s => s.RIP = 0x10b052) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b052 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1589, 1596]
    (.letOp (n := 1600) (.out 0x10b056 (addR64R64Effect 0x10b056 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[1595, 1579]
    (.letOp (n := 1601) (.out 0x10b056 (addR64R64Effect 0x10b056 7 11) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 11] []) (.flag .CF)) #v[1595, 1579]
    (.letOp (n := 1602) (.exec 0x10b056 (fun s => s.RIP = 0x10b056) (addR64R64Effect 0x10b056 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[1595, 1579]
    (.letOp (n := 1603) (.out 0x10b059 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b059 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1598, 1601]
    (.letOp (n := 1604) (.exec 0x10b059 (fun s => s.RIP = 0x10b059) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b059 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1598, 1601]
    (.letOp (n := 1605) (.out 0x10b05d (shldR64R64Effect 0x10b05d 5 8 7 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[1603, 1600]
    (.letOp (n := 1606) (.exec 0x10b05d (fun s => s.RIP = 0x10b05d) (shldR64R64Effect 0x10b05d 5 8 7 12) (Reg.operands [.gpr 8, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1603, 1600]
    (.letOp (n := 1607) (.out 0x10b062 (movR64M64Effect 0x10b062 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1608) (.exec 0x10b062 (LoadPre 0x10b062 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10b062 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b062 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1609) (.out 0x10b06a (movR64M64Effect 0x10b06a 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 1610) (.exec 0x10b06a (LoadPre 0x10b06a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10b06a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b06a 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1611) (.out 0x10b06f (leaR64Effect 0x10b06f 1 (.sib 2 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 0] []) (.reg (.gpr 1))) #v[1609, 1607]
    (.letOp (n := 1612) (.exec 0x10b06f (fun s => s.RIP = 0x10b06f) (leaR64Effect 0x10b06f 1 (.sib 2 (some 0) 0 .none)) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1609, 1607]
    (.letOp (n := 1613) (.exec 0x10b073 (StorePre 0x10b073 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10b073 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b073 1 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1611, 65]
    (.letOp (n := 1614) (.out 0x10b07b (movR64M64Effect 0x10b07b 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1615) (.exec 0x10b07b (LoadPre 0x10b07b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10b07b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10b07b 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1616) (.out 0x10b083 (movR64M64Effect 0x10b083 2 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 1617) (.exec 0x10b083 (LoadPre 0x10b083 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10b083 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10b083 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1618) (.out 0x10b088 (addR64R64Effect 0x10b088 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1614, 1616]
    (.letOp (n := 1619) (.exec 0x10b088 (fun s => s.RIP = 0x10b088) (addR64R64Effect 0x10b088 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1614, 1616]
    (.letOp (n := 1620) (.exec 0x10b08b (StorePre 0x10b08b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10b08b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10b08b 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1618, 65]
    (.letOp (n := 1621) (.out 0x10b093 (mulR64Effect 0x10b093 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1611, 1618]
    (.letOp (n := 1622) (.out 0x10b093 (mulR64Effect 0x10b093 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1611, 1618]
    (.letOp (n := 1623) (.exec 0x10b093 (fun s => s.RIP = 0x10b093) (mulR64Effect 0x10b093 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1611, 1618]
    (b_l10a410_37)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_36 : List UInt8 :=
  [0x4C, 0x89, 0x94, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0xE1, 0x49, 0x89,
    0xD0, 0x48, 0x8B, 0xBC, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x21, 0xEF, 0x48, 0x01, 0xC7, 0x49,
    0x83, 0xD0, 0x00, 0x4C, 0x01, 0xDF, 0x49, 0x83, 0xD0, 0x00, 0x49, 0x0F, 0xA4, 0xF8, 0x0C, 0x48,
    0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x50, 0x48, 0x8D, 0x0C, 0x02,
    0x48, 0x89, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x54, 0x24, 0x38, 0x48, 0x01, 0xD0, 0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE1] ++ bytes_l10a410_37

theorem code_l10a410_36 : ∀ x ∈ codeRange 0x10b033 bytes_l10a410_36, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb033 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_37

def b_l10a410_35 : Block Op Label signature Reg.count 1536 :=
  .letOp (n := 1536) (.out 0x10afea (movR64R64Effect 0x10afea 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[1533]
    (.letOp (n := 1537) (.exec 0x10afea (fun s => s.RIP = 0x10afea) (movR64R64Effect 0x10afea 13 0) (Reg.operands [.gpr 0] [])) #v[1533]
    (.letOp (n := 1538) (.out 0x10afed (addR64R64Effect 0x10afed 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 6] []) (.reg (.gpr 13))) #v[1536, 1529]
    (.letOp (n := 1539) (.out 0x10afed (addR64R64Effect 0x10afed 13 6) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 6] []) (.flag .CF)) #v[1536, 1529]
    (.letOp (n := 1540) (.exec 0x10afed (fun s => s.RIP = 0x10afed) (addR64R64Effect 0x10afed 13 6) (Reg.operands [.gpr 13, .gpr 6] [])) #v[1536, 1529]
    (.letOp (n := 1541) (.out 0x10aff0 (atFlags StatusFlags.CF (adcR64R64Effect 0x10aff0 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1527, 1534, 1539]
    (.letOp (n := 1542) (.exec 0x10aff0 (fun s => s.RIP = 0x10aff0) (atFlags StatusFlags.CF (adcR64R64Effect 0x10aff0 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1527, 1534, 1539]
    (.letOp (n := 1543) (.out 0x10aff3 (addR64R64Effect 0x10aff3 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[1538, 1460]
    (.letOp (n := 1544) (.out 0x10aff3 (addR64R64Effect 0x10aff3 13 8) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 8] []) (.flag .CF)) #v[1538, 1460]
    (.letOp (n := 1545) (.exec 0x10aff3 (fun s => s.RIP = 0x10aff3) (addR64R64Effect 0x10aff3 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[1538, 1460]
    (.letOp (n := 1546) (.out 0x10aff6 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10aff6 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1541, 1544]
    (.letOp (n := 1547) (.exec 0x10aff6 (fun s => s.RIP = 0x10aff6) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10aff6 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1541, 1544]
    (.letOp (n := 1548) (.out 0x10affa (movR64R64Effect 0x10affa 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1543]
    (.letOp (n := 1549) (.exec 0x10affa (fun s => s.RIP = 0x10affa) (movR64R64Effect 0x10affa 0 13) (Reg.operands [.gpr 13] [])) #v[1543]
    (.letOp (n := 1550) (.out 0x10affd (andR64R64Effect 0x10affd 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[1548, 1517]
    (.letOp (n := 1551) (.exec 0x10affd (fun s => s.RIP = 0x10affd) (andR64R64Effect 0x10affd 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[1548, 1517]
    (.letOp (n := 1552) (.out 0x10b000 (movR64Imm64Effect 0x10b000 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1553) (.exec 0x10b000 (fun s => s.RIP = 0x10b000) (movR64Imm64Effect 0x10b000 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1554) (.out 0x10b00a (mulR64Effect 0x10b00a 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1552, 1550]
    (.letOp (n := 1555) (.out 0x10b00a (mulR64Effect 0x10b00a 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1552, 1550]
    (.letOp (n := 1556) (.exec 0x10b00a (fun s => s.RIP = 0x10b00a) (mulR64Effect 0x10b00a 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1552, 1550]
    (.letOp (n := 1557) (.out 0x10b00d (addR64R64Effect 0x10b00d 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[1513, 1506]
    (.letOp (n := 1558) (.out 0x10b00d (addR64R64Effect 0x10b00d 10 12) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 12] []) (.flag .CF)) #v[1513, 1506]
    (.letOp (n := 1559) (.exec 0x10b00d (fun s => s.RIP = 0x10b00d) (addR64R64Effect 0x10b00d 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[1513, 1506]
    (.letOp (n := 1560) (.out 0x10b010 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b010 11 15)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1515, 1504, 1558]
    (.letOp (n := 1561) (.exec 0x10b010 (fun s => s.RIP = 0x10b010) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b010 11 15)) (Reg.operands [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1515, 1504, 1558]
    (.letOp (n := 1562) (.out 0x10b013 (addR64R64Effect 0x10b013 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[1557, 1497]
    (.letOp (n := 1563) (.out 0x10b013 (addR64R64Effect 0x10b013 10 14) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 14] []) (.flag .CF)) #v[1557, 1497]
    (.letOp (n := 1564) (.exec 0x10b013 (fun s => s.RIP = 0x10b013) (addR64R64Effect 0x10b013 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[1557, 1497]
    (.letOp (n := 1565) (.out 0x10b016 (atFlags StatusFlags.CF (adcR64R64Effect 0x10b016 11 7)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1560, 1495, 1563]
    (.letOp (n := 1566) (.exec 0x10b016 (fun s => s.RIP = 0x10b016) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b016 11 7)) (Reg.operands [.gpr 11, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1560, 1495, 1563]
    (.letOp (n := 1567) (.out 0x10b019 (addR64R64Effect 0x10b019 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[1562, 1554]
    (.letOp (n := 1568) (.out 0x10b019 (addR64R64Effect 0x10b019 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[1562, 1554]
    (.letOp (n := 1569) (.exec 0x10b019 (fun s => s.RIP = 0x10b019) (addR64R64Effect 0x10b019 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[1562, 1554]
    (.letOp (n := 1570) (.out 0x10b01c (atFlags StatusFlags.CF (adcR64R64Effect 0x10b01c 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1565, 1555, 1568]
    (.letOp (n := 1571) (.exec 0x10b01c (fun s => s.RIP = 0x10b01c) (atFlags StatusFlags.CF (adcR64R64Effect 0x10b01c 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1565, 1555, 1568]
    (.letOp (n := 1572) (.out 0x10b01f (addR64R64Effect 0x10b01f 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[1567, 1486]
    (.letOp (n := 1573) (.out 0x10b01f (addR64R64Effect 0x10b01f 10 9) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 9] []) (.flag .CF)) #v[1567, 1486]
    (.letOp (n := 1574) (.exec 0x10b01f (fun s => s.RIP = 0x10b01f) (addR64R64Effect 0x10b01f 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[1567, 1486]
    (.letOp (n := 1575) (.out 0x10b022 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b022 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1570, 1573]
    (.letOp (n := 1576) (.exec 0x10b022 (fun s => s.RIP = 0x10b022) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10b022 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1570, 1573]
    (.letOp (n := 1577) (.out 0x10b026 (shldR64R64Effect 0x10b026 5 3 13 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1546, 1543]
    (.letOp (n := 1578) (.exec 0x10b026 (fun s => s.RIP = 0x10b026) (shldR64R64Effect 0x10b026 5 3 13 12) (Reg.operands [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1546, 1543]
    (.letOp (n := 1579) (.out 0x10b02b (shldR64R64Effect 0x10b02b 5 11 10 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1575, 1572]
    (.letOp (n := 1580) (.exec 0x10b02b (fun s => s.RIP = 0x10b02b) (shldR64R64Effect 0x10b02b 5 11 10 12) (Reg.operands [.gpr 11, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1575, 1572]
    (.letOp (n := 1581) (.out 0x10b030 (andR64R64Effect 0x10b030 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[1572, 1517]
    (.letOp (n := 1582) (.exec 0x10b030 (fun s => s.RIP = 0x10b030) (andR64R64Effect 0x10b030 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[1572, 1517]
    (b_l10a410_36)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_35 : List UInt8 :=
  [0x49, 0x89, 0xC5, 0x49, 0x01, 0xF5, 0x48, 0x11, 0xD3, 0x4D, 0x01, 0xC5, 0x48, 0x83, 0xD3, 0x00,
    0x4C, 0x89, 0xE8, 0x48, 0x21, 0xE8, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE1, 0x4D, 0x01, 0xE2, 0x4D, 0x11, 0xFB, 0x4D, 0x01, 0xF2, 0x49, 0x11, 0xFB, 0x49,
    0x01, 0xC2, 0x49, 0x11, 0xD3, 0x4D, 0x01, 0xCA, 0x49, 0x83, 0xD3, 0x00, 0x4C, 0x0F, 0xA4, 0xEB,
    0x0C, 0x4D, 0x0F, 0xA4, 0xD3, 0x0C, 0x49, 0x21, 0xEA] ++ bytes_l10a410_36

theorem code_l10a410_35 : ∀ x ∈ codeRange 0x10afea bytes_l10a410_35, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xafea 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_36

def b_l10a410_34 : Block Op Label signature Reg.count 1492 :=
  .letOp (n := 1492) (.out 0x10af95 (mulM64Effect 0x10af95 8 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1490, 65]
    (.letOp (n := 1493) (.out 0x10af95 (mulM64Effect 0x10af95 8 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1490, 65]
    (.letOp (n := 1494) (.exec 0x10af95 (LoadPre 0x10af95 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10af95 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10af95 8 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1490, 65]
    (.letOp (n := 1495) (.out 0x10af9d (movR64R64Effect 0x10af9d 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[1493]
    (.letOp (n := 1496) (.exec 0x10af9d (fun s => s.RIP = 0x10af9d) (movR64R64Effect 0x10af9d 7 2) (Reg.operands [.gpr 2] [])) #v[1493]
    (.letOp (n := 1497) (.out 0x10afa0 (movR64R64Effect 0x10afa0 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[1492]
    (.letOp (n := 1498) (.exec 0x10afa0 (fun s => s.RIP = 0x10afa0) (movR64R64Effect 0x10afa0 14 0) (Reg.operands [.gpr 0] [])) #v[1492]
    (.letOp (n := 1499) (.out 0x10afa3 (movR64M64Effect 0x10afa3 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1500) (.exec 0x10afa3 (LoadPre 0x10afa3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10afa3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10afa3 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1501) (.out 0x10afa8 (mulR64Effect 0x10afa8 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[1401, 1499]
    (.letOp (n := 1502) (.out 0x10afa8 (mulR64Effect 0x10afa8 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[1401, 1499]
    (.letOp (n := 1503) (.exec 0x10afa8 (fun s => s.RIP = 0x10afa8) (mulR64Effect 0x10afa8 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[1401, 1499]
    (.letOp (n := 1504) (.out 0x10afab (movR64R64Effect 0x10afab 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[1502]
    (.letOp (n := 1505) (.exec 0x10afab (fun s => s.RIP = 0x10afab) (movR64R64Effect 0x10afab 15 2) (Reg.operands [.gpr 2] [])) #v[1502]
    (.letOp (n := 1506) (.out 0x10afae (movR64R64Effect 0x10afae 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[1501]
    (.letOp (n := 1507) (.exec 0x10afae (fun s => s.RIP = 0x10afae) (movR64R64Effect 0x10afae 12 0) (Reg.operands [.gpr 0] [])) #v[1501]
    (.letOp (n := 1508) (.out 0x10afb1 (movR64M64Effect 0x10afb1 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1509) (.exec 0x10afb1 (LoadPre 0x10afb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10afb1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10afb1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1510) (.out 0x10afb6 (mulM64Effect 0x10afb6 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1508, 65]
    (.letOp (n := 1511) (.out 0x10afb6 (mulM64Effect 0x10afb6 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1508, 65]
    (.letOp (n := 1512) (.exec 0x10afb6 (LoadPre 0x10afb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10afb6 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10afb6 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1508, 65]
    (.letOp (n := 1513) (.out 0x10afbe (movR64R64Effect 0x10afbe 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[1510]
    (.letOp (n := 1514) (.exec 0x10afbe (fun s => s.RIP = 0x10afbe) (movR64R64Effect 0x10afbe 10 0) (Reg.operands [.gpr 0] [])) #v[1510]
    (.letOp (n := 1515) (.out 0x10afc1 (movR64R64Effect 0x10afc1 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[1511]
    (.letOp (n := 1516) (.exec 0x10afc1 (fun s => s.RIP = 0x10afc1) (movR64R64Effect 0x10afc1 11 2) (Reg.operands [.gpr 2] [])) #v[1511]
    (.letOp (n := 1517) (.out 0x10afc4 (movR64Imm64Effect 0x10afc4 5 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 1518) (.exec 0x10afc4 (fun s => s.RIP = 0x10afc4) (movR64Imm64Effect 0x10afc4 5 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1519) (.out 0x10afce (andR64R64Effect 0x10afce 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[1488, 1517]
    (.letOp (n := 1520) (.exec 0x10afce (fun s => s.RIP = 0x10afce) (andR64R64Effect 0x10afce 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[1488, 1517]
    (.letOp (n := 1521) (.exec 0x10afd1 (StorePre 0x10afd1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10afd1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10afd1 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1519, 65]
    (.letOp (n := 1522) (.out 0x10afd6 (movR64R64Effect 0x10afd6 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[1409]
    (.letOp (n := 1523) (.exec 0x10afd6 (fun s => s.RIP = 0x10afd6) (movR64R64Effect 0x10afd6 0 3) (Reg.operands [.gpr 3] [])) #v[1409]
    (.letOp (n := 1524) (.out 0x10afd9 (mulR64Effect 0x10afd9 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[1427, 1522]
    (.letOp (n := 1525) (.out 0x10afd9 (mulR64Effect 0x10afd9 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[1427, 1522]
    (.letOp (n := 1526) (.exec 0x10afd9 (fun s => s.RIP = 0x10afd9) (mulR64Effect 0x10afd9 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1427, 1522]
    (.letOp (n := 1527) (.out 0x10afdc (movR64R64Effect 0x10afdc 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[1525]
    (.letOp (n := 1528) (.exec 0x10afdc (fun s => s.RIP = 0x10afdc) (movR64R64Effect 0x10afdc 3 2) (Reg.operands [.gpr 2] [])) #v[1525]
    (.letOp (n := 1529) (.out 0x10afdf (movR64R64Effect 0x10afdf 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1524]
    (.letOp (n := 1530) (.exec 0x10afdf (fun s => s.RIP = 0x10afdf) (movR64R64Effect 0x10afdf 6 0) (Reg.operands [.gpr 0] [])) #v[1524]
    (.letOp (n := 1531) (.out 0x10afe2 (movR64M64Effect 0x10afe2 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1532) (.exec 0x10afe2 (LoadPre 0x10afe2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10afe2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10afe2 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1533) (.out 0x10afe7 (mulR64Effect 0x10afe7 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1440, 1531]
    (.letOp (n := 1534) (.out 0x10afe7 (mulR64Effect 0x10afe7 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1440, 1531]
    (.letOp (n := 1535) (.exec 0x10afe7 (fun s => s.RIP = 0x10afe7) (mulR64Effect 0x10afe7 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1440, 1531]
    (b_l10a410_35))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_34 : List UInt8 :=
  [0x48, 0xF7, 0xA4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC6, 0x48, 0x8B,
    0x44, 0x24, 0x08, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x44, 0x24,
    0x18, 0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC2, 0x49, 0x89, 0xD3, 0x48,
    0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xEE, 0x48, 0x89, 0x74, 0x24,
    0x68, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0xD3, 0x48, 0x89, 0xC6, 0x48, 0x8B, 0x44,
    0x24, 0x58, 0x48, 0xF7, 0xE1] ++ bytes_l10a410_35

theorem code_l10a410_34 : ∀ x ∈ codeRange 0x10af95 bytes_l10a410_34, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xaf95 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_35

def b_l10a410_33 : Block Op Label signature Reg.count 1445 :=
  .letOp (n := 1445) (.out 0x10af46 (addR64R64Effect 0x10af46 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[1442, 1434]
    (.letOp (n := 1446) (.out 0x10af46 (addR64R64Effect 0x10af46 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[1442, 1434]
    (.letOp (n := 1447) (.exec 0x10af46 (fun s => s.RIP = 0x10af46) (addR64R64Effect 0x10af46 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[1442, 1434]
    (.letOp (n := 1448) (.out 0x10af49 (atFlags StatusFlags.CF (adcR64R64Effect 0x10af49 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1432, 1443, 1446]
    (.letOp (n := 1449) (.exec 0x10af49 (fun s => s.RIP = 0x10af49) (atFlags StatusFlags.CF (adcR64R64Effect 0x10af49 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1432, 1443, 1446]
    (.letOp (n := 1450) (.out 0x10af4c (addR64R64Effect 0x10af4c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1445, 1416]
    (.letOp (n := 1451) (.out 0x10af4c (addR64R64Effect 0x10af4c 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[1445, 1416]
    (.letOp (n := 1452) (.exec 0x10af4c (fun s => s.RIP = 0x10af4c) (addR64R64Effect 0x10af4c 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1445, 1416]
    (.letOp (n := 1453) (.out 0x10af4f (atFlags StatusFlags.CF (adcR64R64Effect 0x10af4f 8 14)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1448, 1418, 1451]
    (.letOp (n := 1454) (.exec 0x10af4f (fun s => s.RIP = 0x10af4f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10af4f 8 14)) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1448, 1418, 1451]
    (.letOp (n := 1455) (.out 0x10af52 (addR64R64Effect 0x10af52 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[1450, 1366]
    (.letOp (n := 1456) (.out 0x10af52 (addR64R64Effect 0x10af52 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[1450, 1366]
    (.letOp (n := 1457) (.exec 0x10af52 (fun s => s.RIP = 0x10af52) (addR64R64Effect 0x10af52 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[1450, 1366]
    (.letOp (n := 1458) (.out 0x10af55 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10af55 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1453, 1456]
    (.letOp (n := 1459) (.exec 0x10af55 (fun s => s.RIP = 0x10af55) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10af55 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1453, 1456]
    (.letOp (n := 1460) (.out 0x10af59 (shldR64R64Effect 0x10af59 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[1458, 1455]
    (.letOp (n := 1461) (.exec 0x10af59 (fun s => s.RIP = 0x10af59) (shldR64R64Effect 0x10af59 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1458, 1455]
    (.letOp (n := 1462) (.out 0x10af5e (andR64R64Effect 0x10af5e 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[1455, 1420]
    (.letOp (n := 1463) (.exec 0x10af5e (fun s => s.RIP = 0x10af5e) (andR64R64Effect 0x10af5e 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[1455, 1420]
    (.letOp (n := 1464) (.out 0x10af61 (movR64Imm64Effect 0x10af61 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1465) (.exec 0x10af61 (fun s => s.RIP = 0x10af61) (movR64Imm64Effect 0x10af61 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1466) (.out 0x10af6b (mulR64Effect 0x10af6b 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1464, 1462]
    (.letOp (n := 1467) (.out 0x10af6b (mulR64Effect 0x10af6b 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1464, 1462]
    (.letOp (n := 1468) (.exec 0x10af6b (fun s => s.RIP = 0x10af6b) (mulR64Effect 0x10af6b 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1464, 1462]
    (.letOp (n := 1469) (.out 0x10af6e (movR64M64Effect 0x10af6e 12 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 1470) (.exec 0x10af6e (LoadPre 0x10af6e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10af6e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10af6e 12 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1471) (.out 0x10af73 (addR64M64Effect 0x10af73 12 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[1469, 65]
    (.letOp (n := 1472) (.out 0x10af73 (addR64M64Effect 0x10af73 12 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 4] []) (.flag .CF)) #v[1469, 65]
    (.letOp (n := 1473) (.exec 0x10af73 (LoadPre 0x10af73 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10af73 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10af73 12 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[1469, 65]
    (.letOp (n := 1474) (.out 0x10af78 (atFlags StatusFlags.CF (adcR64M64Effect 0x10af78 9 (.sib 4 none 0 (.d8 0x60)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[1406, 65, 1472]
    (.letOp (n := 1475) (.exec 0x10af78 (LoadPre 0x10af78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10af78 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10af78 9 (.sib 4 none 0 (.d8 0x60)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1406, 65, 1472]
    (.letOp (n := 1476) (.out 0x10af7d (addR64R64Effect 0x10af7d 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[1471, 1466]
    (.letOp (n := 1477) (.out 0x10af7d (addR64R64Effect 0x10af7d 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[1471, 1466]
    (.letOp (n := 1478) (.exec 0x10af7d (fun s => s.RIP = 0x10af7d) (addR64R64Effect 0x10af7d 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[1471, 1466]
    (.letOp (n := 1479) (.out 0x10af80 (atFlags StatusFlags.CF (adcR64R64Effect 0x10af80 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[1474, 1467, 1477]
    (.letOp (n := 1480) (.exec 0x10af80 (fun s => s.RIP = 0x10af80) (atFlags StatusFlags.CF (adcR64R64Effect 0x10af80 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1474, 1467, 1477]
    (.letOp (n := 1481) (.out 0x10af83 (addR64R64Effect 0x10af83 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[1476, 1388]
    (.letOp (n := 1482) (.out 0x10af83 (addR64R64Effect 0x10af83 12 11) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 11] []) (.flag .CF)) #v[1476, 1388]
    (.letOp (n := 1483) (.exec 0x10af83 (fun s => s.RIP = 0x10af83) (addR64R64Effect 0x10af83 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[1476, 1388]
    (.letOp (n := 1484) (.out 0x10af86 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10af86 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[1479, 1482]
    (.letOp (n := 1485) (.exec 0x10af86 (fun s => s.RIP = 0x10af86) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10af86 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1479, 1482]
    (.letOp (n := 1486) (.out 0x10af8a (shldR64R64Effect 0x10af8a 5 9 12 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[1484, 1481]
    (.letOp (n := 1487) (.exec 0x10af8a (fun s => s.RIP = 0x10af8a) (shldR64R64Effect 0x10af8a 5 9 12 12) (Reg.operands [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1484, 1481]
    (.letOp (n := 1488) (.out 0x10af8f (movR64R64Effect 0x10af8f 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[1481]
    (.letOp (n := 1489) (.exec 0x10af8f (fun s => s.RIP = 0x10af8f) (movR64R64Effect 0x10af8f 6 12) (Reg.operands [.gpr 12] [])) #v[1481]
    (.letOp (n := 1490) (.out 0x10af92 (movR64R64Effect 0x10af92 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1436]
    (.letOp (n := 1491) (.exec 0x10af92 (fun s => s.RIP = 0x10af92) (movR64R64Effect 0x10af92 0 7) (Reg.operands [.gpr 7] [])) #v[1436]
    (b_l10a410_34)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_33 : List UInt8 :=
  [0x4C, 0x01, 0xF8, 0x49, 0x11, 0xD0, 0x48, 0x01, 0xF0, 0x4D, 0x11, 0xF0, 0x4C, 0x01, 0xD0, 0x49,
    0x83, 0xD0, 0x00, 0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x4C, 0x21, 0xE0, 0x48, 0xBA, 0x10, 0x3D, 0x00,
    0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x8B, 0x64, 0x24, 0x68, 0x4C, 0x03, 0x64,
    0x24, 0x20, 0x4C, 0x13, 0x4C, 0x24, 0x60, 0x49, 0x01, 0xC4, 0x49, 0x11, 0xD1, 0x4D, 0x01, 0xDC,
    0x49, 0x83, 0xD1, 0x00, 0x4D, 0x0F, 0xA4, 0xE1, 0x0C, 0x4C, 0x89, 0xE6, 0x48, 0x89, 0xF8] ++ bytes_l10a410_34

theorem code_l10a410_33 : ∀ x ∈ codeRange 0x10af46 bytes_l10a410_33, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xaf46 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_34

def b_l10a410_32 : Block Op Label signature Reg.count 1403 :=
  .letOp (n := 1403) (.out 0x10aef1 (mulR64Effect 0x10aef1 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[1401, 1399]
    (.letOp (n := 1404) (.out 0x10aef1 (mulR64Effect 0x10aef1 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[1401, 1399]
    (.letOp (n := 1405) (.exec 0x10aef1 (fun s => s.RIP = 0x10aef1) (mulR64Effect 0x10aef1 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[1401, 1399]
    (.letOp (n := 1406) (.out 0x10aef4 (movR64R64Effect 0x10aef4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[1404]
    (.letOp (n := 1407) (.exec 0x10aef4 (fun s => s.RIP = 0x10aef4) (movR64R64Effect 0x10aef4 9 2) (Reg.operands [.gpr 2] [])) #v[1404]
    (.letOp (n := 1408) (.exec 0x10aef7 (StorePre 0x10aef7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10aef7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10aef7 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1403, 65]
    (.letOp (n := 1409) (.out 0x10aefc (movR64M64Effect 0x10aefc 3 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 1410) (.exec 0x10aefc (LoadPre 0x10aefc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10aefc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10aefc 3 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1411) (.out 0x10af01 (movR64R64Effect 0x10af01 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[1409]
    (.letOp (n := 1412) (.exec 0x10af01 (fun s => s.RIP = 0x10af01) (movR64R64Effect 0x10af01 0 3) (Reg.operands [.gpr 3] [])) #v[1409]
    (.letOp (n := 1413) (.out 0x10af04 (mulR64Effect 0x10af04 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1319, 1411]
    (.letOp (n := 1414) (.out 0x10af04 (mulR64Effect 0x10af04 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1319, 1411]
    (.letOp (n := 1415) (.exec 0x10af04 (fun s => s.RIP = 0x10af04) (mulR64Effect 0x10af04 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1319, 1411]
    (.letOp (n := 1416) (.out 0x10af07 (movR64R64Effect 0x10af07 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1413]
    (.letOp (n := 1417) (.exec 0x10af07 (fun s => s.RIP = 0x10af07) (movR64R64Effect 0x10af07 6 0) (Reg.operands [.gpr 0] [])) #v[1413]
    (.letOp (n := 1418) (.out 0x10af0a (movR64R64Effect 0x10af0a 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[1414]
    (.letOp (n := 1419) (.exec 0x10af0a (fun s => s.RIP = 0x10af0a) (movR64R64Effect 0x10af0a 14 2) (Reg.operands [.gpr 2] [])) #v[1414]
    (.letOp (n := 1420) (.out 0x10af0d (movR64Imm64Effect 0x10af0d 12 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 1421) (.exec 0x10af0d (fun s => s.RIP = 0x10af0d) (movR64Imm64Effect 0x10af0d 12 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1422) (.out 0x10af17 (andR64R64Effect 0x10af17 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[1390, 1420]
    (.letOp (n := 1423) (.exec 0x10af17 (fun s => s.RIP = 0x10af17) (andR64R64Effect 0x10af17 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[1390, 1420]
    (.letOp (n := 1424) (.exec 0x10af1a (StorePre 0x10af1a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x10af1a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10af1a 8 (.sib 4 none 0 (.d32 0x1d8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1422, 65]
    (.letOp (n := 1425) (.out 0x10af22 (movR64R64Effect 0x10af22 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1315]
    (.letOp (n := 1426) (.exec 0x10af22 (fun s => s.RIP = 0x10af22) (movR64R64Effect 0x10af22 0 13) (Reg.operands [.gpr 13] [])) #v[1315]
    (.letOp (n := 1427) (.out 0x10af25 (movR64M64Effect 0x10af25 13 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 1428) (.exec 0x10af25 (LoadPre 0x10af25 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10af25 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10af25 13 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1429) (.out 0x10af2d (mulR64Effect 0x10af2d 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[1427, 1425]
    (.letOp (n := 1430) (.out 0x10af2d (mulR64Effect 0x10af2d 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[1427, 1425]
    (.letOp (n := 1431) (.exec 0x10af2d (fun s => s.RIP = 0x10af2d) (mulR64Effect 0x10af2d 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1427, 1425]
    (.letOp (n := 1432) (.out 0x10af30 (movR64R64Effect 0x10af30 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[1430]
    (.letOp (n := 1433) (.exec 0x10af30 (fun s => s.RIP = 0x10af30) (movR64R64Effect 0x10af30 8 2) (Reg.operands [.gpr 2] [])) #v[1430]
    (.letOp (n := 1434) (.out 0x10af33 (movR64R64Effect 0x10af33 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1429]
    (.letOp (n := 1435) (.exec 0x10af33 (fun s => s.RIP = 0x10af33) (movR64R64Effect 0x10af33 15 0) (Reg.operands [.gpr 0] [])) #v[1429]
    (.letOp (n := 1436) (.out 0x10af36 (movR64M64Effect 0x10af36 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 1437) (.exec 0x10af36 (LoadPre 0x10af36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10af36 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10af36 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1438) (.out 0x10af3b (movR64R64Effect 0x10af3b 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1436]
    (.letOp (n := 1439) (.exec 0x10af3b (fun s => s.RIP = 0x10af3b) (movR64R64Effect 0x10af3b 0 7) (Reg.operands [.gpr 7] [])) #v[1436]
    (.letOp (n := 1440) (.out 0x10af3e (movR64M64Effect 0x10af3e 1 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 1441) (.exec 0x10af3e (LoadPre 0x10af3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10af3e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10af3e 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1442) (.out 0x10af43 (mulR64Effect 0x10af43 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1440, 1438]
    (.letOp (n := 1443) (.out 0x10af43 (mulR64Effect 0x10af43 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1440, 1438]
    (.letOp (n := 1444) (.exec 0x10af43 (fun s => s.RIP = 0x10af43) (mulR64Effect 0x10af43 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1440, 1438]
    (b_l10a410_33))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_32 : List UInt8 :=
  [0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD1, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x8B, 0x5C, 0x24, 0x48,
    0x48, 0x89, 0xD8, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC6, 0x49, 0x89, 0xD6, 0x49, 0xBC, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4D, 0x21, 0xE0, 0x4C, 0x89, 0x84, 0x24, 0xD8, 0x01, 0x00,
    0x00, 0x4C, 0x89, 0xE8, 0x4C, 0x8B, 0xAC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x49,
    0x89, 0xD0, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x7C, 0x24, 0x30, 0x48, 0x89, 0xF8, 0x48, 0x8B, 0x4C,
    0x24, 0x70, 0x48, 0xF7, 0xE1] ++ bytes_l10a410_33

theorem code_l10a410_32 : ∀ x ∈ codeRange 0x10aef1 bytes_l10a410_32, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xaef1 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_33

def b_l10a410_31 : Block Op Label signature Reg.count 1361 :=
  .letOp (n := 1361) (.out 0x10ae92 (addR64R64Effect 0x10ae92 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[1356, 1291]
    (.letOp (n := 1362) (.out 0x10ae92 (addR64R64Effect 0x10ae92 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[1356, 1291]
    (.letOp (n := 1363) (.exec 0x10ae92 (fun s => s.RIP = 0x10ae92) (addR64R64Effect 0x10ae92 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[1356, 1291]
    (.letOp (n := 1364) (.out 0x10ae95 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ae95 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1359, 1362]
    (.letOp (n := 1365) (.exec 0x10ae95 (fun s => s.RIP = 0x10ae95) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ae95 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1359, 1362]
    (.letOp (n := 1366) (.out 0x10ae99 (shldR64R64Effect 0x10ae99 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[1364, 1361]
    (.letOp (n := 1367) (.exec 0x10ae99 (fun s => s.RIP = 0x10ae99) (shldR64R64Effect 0x10ae99 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1364, 1361]
    (.letOp (n := 1368) (.out 0x10ae9e (shlR64Effect 0x10ae9e 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1361]
    (.letOp (n := 1369) (.exec 0x10ae9e (fun s => s.RIP = 0x10ae9e) (shlR64Effect 0x10ae9e 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1361]
    (.letOp (n := 1370) (.out 0x10aea2 (movR64Imm64Effect 0x10aea2 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1371) (.exec 0x10aea2 (fun s => s.RIP = 0x10aea2) (movR64Imm64Effect 0x10aea2 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 1372) (.out 0x10aeac (andR64R64Effect 0x10aeac 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1368, 1370]
    (.letOp (n := 1373) (.exec 0x10aeac (fun s => s.RIP = 0x10aeac) (andR64R64Effect 0x10aeac 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1368, 1370]
    (.letOp (n := 1374) (.out 0x10aeaf (orR64R64Effect 0x10aeaf 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[1372, 1328]
    (.letOp (n := 1375) (.exec 0x10aeaf (fun s => s.RIP = 0x10aeaf) (orR64R64Effect 0x10aeaf 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[1372, 1328]
    (.letOp (n := 1376) (.out 0x10aeb2 (movR64Imm64Effect 0x10aeb2 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1377) (.exec 0x10aeb2 (fun s => s.RIP = 0x10aeb2) (movR64Imm64Effect 0x10aeb2 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 1378) (.out 0x10aebc (mulR64Effect 0x10aebc 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1376, 1374]
    (.letOp (n := 1379) (.out 0x10aebc (mulR64Effect 0x10aebc 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1376, 1374]
    (.letOp (n := 1380) (.exec 0x10aebc (fun s => s.RIP = 0x10aebc) (mulR64Effect 0x10aebc 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1376, 1374]
    (.letOp (n := 1381) (.out 0x10aebf (movR64R64Effect 0x10aebf 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[1379]
    (.letOp (n := 1382) (.exec 0x10aebf (fun s => s.RIP = 0x10aebf) (movR64R64Effect 0x10aebf 11 2) (Reg.operands [.gpr 2] [])) #v[1379]
    (.letOp (n := 1383) (.out 0x10aec2 (addR64M64Effect 0x10aec2 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1378, 65]
    (.letOp (n := 1384) (.out 0x10aec2 (addR64M64Effect 0x10aec2 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[1378, 65]
    (.letOp (n := 1385) (.exec 0x10aec2 (LoadPre 0x10aec2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10aec2 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10aec2 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1378, 65]
    (.letOp (n := 1386) (.out 0x10aec7 (atFlags StatusFlags.CF (adcR64M64Effect 0x10aec7 11 (.sib 4 none 0 (.d8 0x60)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[1381, 65, 1384]
    (.letOp (n := 1387) (.exec 0x10aec7 (LoadPre 0x10aec7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10aec7 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10aec7 11 (.sib 4 none 0 (.d8 0x60)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1381, 65, 1384]
    (.letOp (n := 1388) (.out 0x10aecc (shldR64R64Effect 0x10aecc 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1386, 1383]
    (.letOp (n := 1389) (.exec 0x10aecc (fun s => s.RIP = 0x10aecc) (shldR64R64Effect 0x10aecc 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1386, 1383]
    (.letOp (n := 1390) (.out 0x10aed1 (movR64R64Effect 0x10aed1 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[1383]
    (.letOp (n := 1391) (.exec 0x10aed1 (fun s => s.RIP = 0x10aed1) (movR64R64Effect 0x10aed1 8 0) (Reg.operands [.gpr 0] [])) #v[1383]
    (.letOp (n := 1392) (.out 0x10aed4 (movR64R64Effect 0x10aed4 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1339]
    (.letOp (n := 1393) (.exec 0x10aed4 (fun s => s.RIP = 0x10aed4) (movR64R64Effect 0x10aed4 0 5) (Reg.operands [.gpr 5] [])) #v[1339]
    (.letOp (n := 1394) (.out 0x10aed7 (mulR64Effect 0x10aed7 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[1299, 1392]
    (.letOp (n := 1395) (.out 0x10aed7 (mulR64Effect 0x10aed7 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[1299, 1392]
    (.letOp (n := 1396) (.exec 0x10aed7 (fun s => s.RIP = 0x10aed7) (mulR64Effect 0x10aed7 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[1299, 1392]
    (.letOp (n := 1397) (.exec 0x10aeda (StorePre 0x10aeda 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10aeda + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10aeda 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1395, 65]
    (.letOp (n := 1398) (.exec 0x10aedf (StorePre 0x10aedf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10aedf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10aedf 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1394, 65]
    (.letOp (n := 1399) (.out 0x10aee4 (movR64M64Effect 0x10aee4 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1400) (.exec 0x10aee4 (LoadPre 0x10aee4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10aee4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10aee4 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1401) (.out 0x10aee9 (movR64M64Effect 0x10aee9 5 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 1402) (.exec 0x10aee9 (LoadPre 0x10aee9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10aee9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10aee9 5 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_32))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_31 : List UInt8 :=
  [0x4C, 0x01, 0xC8, 0x49, 0x83, 0xD2, 0x00, 0x49, 0x0F, 0xA4, 0xC2, 0x0C, 0x48, 0xC1, 0xE0, 0x04,
    0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x48, 0x09, 0xF8,
    0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xD3,
    0x48, 0x03, 0x44, 0x24, 0x20, 0x4C, 0x13, 0x5C, 0x24, 0x60, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x49,
    0x89, 0xC0, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE4, 0x48, 0x89, 0x54, 0x24, 0x60, 0x48, 0x89, 0x44,
    0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x8B, 0xAC, 0x24, 0xB8, 0x00, 0x00, 0x00] ++ bytes_l10a410_32

theorem code_l10a410_31 : ∀ x ∈ codeRange 0x10ae92 bytes_l10a410_31, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xae92 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_32

def b_l10a410_30 : Block Op Label signature Reg.count 1315 :=
  .letOp (n := 1315) (.out 0x10ae46 (movR64M64Effect 0x10ae46 13 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 1316) (.exec 0x10ae46 (LoadPre 0x10ae46 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10ae46 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ae46 13 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1317) (.out 0x10ae4b (movR64R64Effect 0x10ae4b 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1315]
    (.letOp (n := 1318) (.exec 0x10ae4b (fun s => s.RIP = 0x10ae4b) (movR64R64Effect 0x10ae4b 0 13) (Reg.operands [.gpr 13] [])) #v[1315]
    (.letOp (n := 1319) (.out 0x10ae4e (movR64M64Effect 0x10ae4e 1 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 1320) (.exec 0x10ae4e (LoadPre 0x10ae4e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10ae4e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ae4e 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1321) (.out 0x10ae56 (mulR64Effect 0x10ae56 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1319, 1317]
    (.letOp (n := 1322) (.out 0x10ae56 (mulR64Effect 0x10ae56 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1319, 1317]
    (.letOp (n := 1323) (.exec 0x10ae56 (fun s => s.RIP = 0x10ae56) (mulR64Effect 0x10ae56 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1319, 1317]
    (.letOp (n := 1324) (.out 0x10ae59 (movR64R64Effect 0x10ae59 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[1321]
    (.letOp (n := 1325) (.exec 0x10ae59 (fun s => s.RIP = 0x10ae59) (movR64R64Effect 0x10ae59 3 0) (Reg.operands [.gpr 0] [])) #v[1321]
    (.letOp (n := 1326) (.out 0x10ae5c (movR64R64Effect 0x10ae5c 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[1322]
    (.letOp (n := 1327) (.exec 0x10ae5c (fun s => s.RIP = 0x10ae5c) (movR64R64Effect 0x10ae5c 14 2) (Reg.operands [.gpr 2] [])) #v[1322]
    (.letOp (n := 1328) (.out 0x10ae5f (andR32Imm8Effect 0x10ae5f 3 7 0xf) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[1295]
    (.letOp (n := 1329) (.exec 0x10ae5f (fun s => s.RIP = 0x10ae5f) (andR32Imm8Effect 0x10ae5f 3 7 0xf) (Reg.operands [.gpr 7] [])) #v[1295]
    (.letOp (n := 1330) (.out 0x10ae62 (movR64R64Effect 0x10ae62 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[1222]
    (.letOp (n := 1331) (.exec 0x10ae62 (fun s => s.RIP = 0x10ae62) (movR64R64Effect 0x10ae62 0 11) (Reg.operands [.gpr 11] [])) #v[1222]
    (.letOp (n := 1332) (.out 0x10ae65 (mulM64Effect 0x10ae65 8 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1330, 65]
    (.letOp (n := 1333) (.out 0x10ae65 (mulM64Effect 0x10ae65 8 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1330, 65]
    (.letOp (n := 1334) (.exec 0x10ae65 (LoadPre 0x10ae65 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10ae65 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10ae65 8 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1330, 65]
    (.letOp (n := 1335) (.out 0x10ae6d (movR64R64Effect 0x10ae6d 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[1333]
    (.letOp (n := 1336) (.exec 0x10ae6d (fun s => s.RIP = 0x10ae6d) (movR64R64Effect 0x10ae6d 10 2) (Reg.operands [.gpr 2] [])) #v[1333]
    (.letOp (n := 1337) (.out 0x10ae70 (movR64R64Effect 0x10ae70 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1332]
    (.letOp (n := 1338) (.exec 0x10ae70 (fun s => s.RIP = 0x10ae70) (movR64R64Effect 0x10ae70 15 0) (Reg.operands [.gpr 0] [])) #v[1332]
    (.letOp (n := 1339) (.out 0x10ae73 (movR64M64Effect 0x10ae73 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 1340) (.exec 0x10ae73 (LoadPre 0x10ae73 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10ae73 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ae73 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1341) (.out 0x10ae78 (movR64R64Effect 0x10ae78 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1339]
    (.letOp (n := 1342) (.exec 0x10ae78 (fun s => s.RIP = 0x10ae78) (movR64R64Effect 0x10ae78 0 5) (Reg.operands [.gpr 5] [])) #v[1339]
    (.letOp (n := 1343) (.out 0x10ae7b (mulM64Effect 0x10ae7b 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1341, 65]
    (.letOp (n := 1344) (.out 0x10ae7b (mulM64Effect 0x10ae7b 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1341, 65]
    (.letOp (n := 1345) (.exec 0x10ae7b (LoadPre 0x10ae7b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10ae7b + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ae7b 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1341, 65]
    (.letOp (n := 1346) (.out 0x10ae80 (addR64R64Effect 0x10ae80 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[1343, 1337]
    (.letOp (n := 1347) (.out 0x10ae80 (addR64R64Effect 0x10ae80 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[1343, 1337]
    (.letOp (n := 1348) (.exec 0x10ae80 (fun s => s.RIP = 0x10ae80) (addR64R64Effect 0x10ae80 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[1343, 1337]
    (.letOp (n := 1349) (.out 0x10ae83 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ae83 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1335, 1344, 1347]
    (.letOp (n := 1350) (.exec 0x10ae83 (fun s => s.RIP = 0x10ae83) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ae83 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1335, 1344, 1347]
    (.letOp (n := 1351) (.out 0x10ae86 (addR64R64Effect 0x10ae86 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[1346, 1324]
    (.letOp (n := 1352) (.out 0x10ae86 (addR64R64Effect 0x10ae86 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[1346, 1324]
    (.letOp (n := 1353) (.exec 0x10ae86 (fun s => s.RIP = 0x10ae86) (addR64R64Effect 0x10ae86 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[1346, 1324]
    (.letOp (n := 1354) (.out 0x10ae89 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ae89 10 14)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1349, 1326, 1352]
    (.letOp (n := 1355) (.exec 0x10ae89 (fun s => s.RIP = 0x10ae89) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ae89 10 14)) (Reg.operands [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1349, 1326, 1352]
    (.letOp (n := 1356) (.out 0x10ae8c (addR64R64Effect 0x10ae8c 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[1351, 1313]
    (.letOp (n := 1357) (.out 0x10ae8c (addR64R64Effect 0x10ae8c 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[1351, 1313]
    (.letOp (n := 1358) (.exec 0x10ae8c (fun s => s.RIP = 0x10ae8c) (addR64R64Effect 0x10ae8c 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[1351, 1313]
    (.letOp (n := 1359) (.out 0x10ae8f (atFlags StatusFlags.CF (adcR64R64Effect 0x10ae8f 10 6)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1354, 1311, 1357]
    (.letOp (n := 1360) (.exec 0x10ae8f (fun s => s.RIP = 0x10ae8f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ae8f 10 6)) (Reg.operands [.gpr 10, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1354, 1311, 1357]
    (b_l10a410_31))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_30 : List UInt8 :=
  [0x4C, 0x8B, 0x6C, 0x24, 0x58, 0x4C, 0x89, 0xE8, 0x48, 0x8B, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC3, 0x49, 0x89, 0xD6, 0x83, 0xE7, 0x0F, 0x4C, 0x89, 0xD8, 0x48,
    0xF7, 0xA4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x6C,
    0x24, 0x08, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0x64, 0x24, 0x70, 0x4C, 0x01, 0xF8, 0x49, 0x11, 0xD2,
    0x48, 0x01, 0xD8, 0x4D, 0x11, 0xF2, 0x4C, 0x01, 0xC0, 0x49, 0x11, 0xF2] ++ bytes_l10a410_31

theorem code_l10a410_30 : ∀ x ∈ codeRange 0x10ae46 bytes_l10a410_30, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xae46 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_31

def b_l10a410_29 : Block Op Label signature Reg.count 1273 :=
  .letOp (n := 1273) (.out 0x10adf0 (atFlags StatusFlags.CF (adcR64M64Effect 0x10adf0 9 (.sib 4 none 0 (.d8 0x40)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[1268, 65, 1271]
    (.letOp (n := 1274) (.exec 0x10adf0 (LoadPre 0x10adf0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10adf0 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10adf0 9 (.sib 4 none 0 (.d8 0x40)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1268, 65, 1271]
    (.letOp (n := 1275) (.out 0x10adf5 (addR64M64Effect 0x10adf5 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[1270, 65]
    (.letOp (n := 1276) (.out 0x10adf5 (addR64M64Effect 0x10adf5 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[1270, 65]
    (.letOp (n := 1277) (.exec 0x10adf5 (LoadPre 0x10adf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10adf5 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10adf5 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[1270, 65]
    (.letOp (n := 1278) (.out 0x10adfa (atFlags StatusFlags.CF (adcR64M64Effect 0x10adfa 9 (.sib 4 none 0 (.d8 0x60)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[1273, 65, 1276]
    (.letOp (n := 1279) (.exec 0x10adfa (LoadPre 0x10adfa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10adfa + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10adfa 9 (.sib 4 none 0 (.d8 0x60)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1273, 65, 1276]
    (.letOp (n := 1280) (.out 0x10adff (addR64R64Effect 0x10adff 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[1275, 1257]
    (.letOp (n := 1281) (.out 0x10adff (addR64R64Effect 0x10adff 5 0) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 0] []) (.flag .CF)) #v[1275, 1257]
    (.letOp (n := 1282) (.exec 0x10adff (fun s => s.RIP = 0x10adff) (addR64R64Effect 0x10adff 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[1275, 1257]
    (.letOp (n := 1283) (.out 0x10ae02 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ae02 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[1278, 1258, 1281]
    (.letOp (n := 1284) (.exec 0x10ae02 (fun s => s.RIP = 0x10ae02) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ae02 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1278, 1258, 1281]
    (.letOp (n := 1285) (.out 0x10ae05 (addR64R64Effect 0x10ae05 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[1280, 1203]
    (.letOp (n := 1286) (.out 0x10ae05 (addR64R64Effect 0x10ae05 5 1) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 1] []) (.flag .CF)) #v[1280, 1203]
    (.letOp (n := 1287) (.exec 0x10ae05 (fun s => s.RIP = 0x10ae05) (addR64R64Effect 0x10ae05 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[1280, 1203]
    (.letOp (n := 1288) (.exec 0x10ae08 (StorePre 0x10ae08 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10ae08 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ae08 5 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[1285, 65]
    (.letOp (n := 1289) (.out 0x10ae10 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ae10 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[1283, 1286]
    (.letOp (n := 1290) (.exec 0x10ae10 (fun s => s.RIP = 0x10ae10) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ae10 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1283, 1286]
    (.letOp (n := 1291) (.out 0x10ae14 (shldR64R64Effect 0x10ae14 5 9 5 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[1289, 1285]
    (.letOp (n := 1292) (.exec 0x10ae14 (fun s => s.RIP = 0x10ae14) (shldR64R64Effect 0x10ae14 5 9 5 12) (Reg.operands [.gpr 9, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1289, 1285]
    (.letOp (n := 1293) (.out 0x10ae19 (movR64R64Effect 0x10ae19 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[1285]
    (.letOp (n := 1294) (.exec 0x10ae19 (fun s => s.RIP = 0x10ae19) (movR64R64Effect 0x10ae19 7 5) (Reg.operands [.gpr 5] [])) #v[1285]
    (.letOp (n := 1295) (.out 0x10ae1c (shrR64Effect 0x10ae1c 4 7 48) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1293]
    (.letOp (n := 1296) (.exec 0x10ae1c (fun s => s.RIP = 0x10ae1c) (shrR64Effect 0x10ae1c 4 7 48) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1293]
    (.letOp (n := 1297) (.out 0x10ae20 (movR64R64Effect 0x10ae20 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[1242]
    (.letOp (n := 1298) (.exec 0x10ae20 (fun s => s.RIP = 0x10ae20) (movR64R64Effect 0x10ae20 0 8) (Reg.operands [.gpr 8] [])) #v[1242]
    (.letOp (n := 1299) (.out 0x10ae23 (movR64M64Effect 0x10ae23 12 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 1300) (.exec 0x10ae23 (LoadPre 0x10ae23 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10ae23 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ae23 12 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1301) (.out 0x10ae2b (mulR64Effect 0x10ae2b 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[1299, 1297]
    (.letOp (n := 1302) (.out 0x10ae2b (mulR64Effect 0x10ae2b 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[1299, 1297]
    (.letOp (n := 1303) (.exec 0x10ae2b (fun s => s.RIP = 0x10ae2b) (mulR64Effect 0x10ae2b 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[1299, 1297]
    (.letOp (n := 1304) (.exec 0x10ae2e (StorePre 0x10ae2e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10ae2e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ae2e 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1302, 65]
    (.letOp (n := 1305) (.exec 0x10ae33 (StorePre 0x10ae33 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ae33 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ae33 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1301, 65]
    (.letOp (n := 1306) (.out 0x10ae38 (movR64M64Effect 0x10ae38 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1307) (.exec 0x10ae38 (LoadPre 0x10ae38 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10ae38 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ae38 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1308) (.out 0x10ae3d (mulR64Effect 0x10ae3d 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[1214, 1306]
    (.letOp (n := 1309) (.out 0x10ae3d (mulR64Effect 0x10ae3d 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[1214, 1306]
    (.letOp (n := 1310) (.exec 0x10ae3d (fun s => s.RIP = 0x10ae3d) (mulR64Effect 0x10ae3d 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[1214, 1306]
    (.letOp (n := 1311) (.out 0x10ae40 (movR64R64Effect 0x10ae40 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1309]
    (.letOp (n := 1312) (.exec 0x10ae40 (fun s => s.RIP = 0x10ae40) (movR64R64Effect 0x10ae40 6 2) (Reg.operands [.gpr 2] [])) #v[1309]
    (.letOp (n := 1313) (.out 0x10ae43 (movR64R64Effect 0x10ae43 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[1308]
    (.letOp (n := 1314) (.exec 0x10ae43 (fun s => s.RIP = 0x10ae43) (movR64R64Effect 0x10ae43 8 0) (Reg.operands [.gpr 0] [])) #v[1308]
    (b_l10a410_30))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_29 : List UInt8 :=
  [0x4C, 0x13, 0x4C, 0x24, 0x40, 0x48, 0x03, 0x6C, 0x24, 0x20, 0x4C, 0x13, 0x4C, 0x24, 0x60, 0x48,
    0x01, 0xC5, 0x49, 0x11, 0xD1, 0x48, 0x01, 0xCD, 0x48, 0x89, 0xAC, 0x24, 0x98, 0x00, 0x00, 0x00,
    0x49, 0x83, 0xD1, 0x00, 0x49, 0x0F, 0xA4, 0xE9, 0x0C, 0x48, 0x89, 0xEF, 0x48, 0xC1, 0xEF, 0x30,
    0x4C, 0x89, 0xC0, 0x4C, 0x8B, 0xA4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE4, 0x48, 0x89,
    0x54, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0xF7, 0xE6,
    0x48, 0x89, 0xD6, 0x49, 0x89, 0xC0] ++ bytes_l10a410_30

theorem code_l10a410_29 : ∀ x ∈ codeRange 0x10adf0 bytes_l10a410_29, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xadf0 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_30

def b_l10a410_28 : Block Op Label signature Reg.count 1226 :=
  .letOp (n := 1226) (.out 0x10ada4 (mulM64Effect 0x10ada4 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1224, 65]
    (.letOp (n := 1227) (.out 0x10ada4 (mulM64Effect 0x10ada4 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1224, 65]
    (.letOp (n := 1228) (.exec 0x10ada4 (LoadPre 0x10ada4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10ada4 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10ada4 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1224, 65]
    (.letOp (n := 1229) (.out 0x10adac (movR64R64Effect 0x10adac 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[1227]
    (.letOp (n := 1230) (.exec 0x10adac (fun s => s.RIP = 0x10adac) (movR64R64Effect 0x10adac 7 2) (Reg.operands [.gpr 2] [])) #v[1227]
    (.letOp (n := 1231) (.out 0x10adaf (movR64R64Effect 0x10adaf 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1226]
    (.letOp (n := 1232) (.exec 0x10adaf (fun s => s.RIP = 0x10adaf) (movR64R64Effect 0x10adaf 15 0) (Reg.operands [.gpr 0] [])) #v[1226]
    (.letOp (n := 1233) (.out 0x10adb2 (movR64M64Effect 0x10adb2 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1234) (.exec 0x10adb2 (LoadPre 0x10adb2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10adb2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10adb2 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1235) (.out 0x10adb7 (mulR64Effect 0x10adb7 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[1140, 1233]
    (.letOp (n := 1236) (.out 0x10adb7 (mulR64Effect 0x10adb7 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[1140, 1233]
    (.letOp (n := 1237) (.exec 0x10adb7 (fun s => s.RIP = 0x10adb7) (mulR64Effect 0x10adb7 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1140, 1233]
    (.letOp (n := 1238) (.out 0x10adba (movR64R64Effect 0x10adba 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[1236]
    (.letOp (n := 1239) (.exec 0x10adba (fun s => s.RIP = 0x10adba) (movR64R64Effect 0x10adba 12 2) (Reg.operands [.gpr 2] [])) #v[1236]
    (.letOp (n := 1240) (.out 0x10adbd (movR64R64Effect 0x10adbd 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[1235]
    (.letOp (n := 1241) (.exec 0x10adbd (fun s => s.RIP = 0x10adbd) (movR64R64Effect 0x10adbd 13 0) (Reg.operands [.gpr 0] [])) #v[1235]
    (.letOp (n := 1242) (.out 0x10adc0 (movR64M64Effect 0x10adc0 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 1243) (.exec 0x10adc0 (LoadPre 0x10adc0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10adc0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10adc0 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1244) (.out 0x10adc5 (movR64R64Effect 0x10adc5 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[1242]
    (.letOp (n := 1245) (.exec 0x10adc5 (fun s => s.RIP = 0x10adc5) (movR64R64Effect 0x10adc5 0 8) (Reg.operands [.gpr 8] [])) #v[1242]
    (.letOp (n := 1246) (.out 0x10adc8 (mulR64Effect 0x10adc8 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[1152, 1244]
    (.letOp (n := 1247) (.out 0x10adc8 (mulR64Effect 0x10adc8 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[1152, 1244]
    (.letOp (n := 1248) (.exec 0x10adc8 (fun s => s.RIP = 0x10adc8) (mulR64Effect 0x10adc8 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1152, 1244]
    (.letOp (n := 1249) (.out 0x10adcb (movR64R64Effect 0x10adcb 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[1247]
    (.letOp (n := 1250) (.exec 0x10adcb (fun s => s.RIP = 0x10adcb) (movR64R64Effect 0x10adcb 9 2) (Reg.operands [.gpr 2] [])) #v[1247]
    (.letOp (n := 1251) (.out 0x10adce (movR64R64Effect 0x10adce 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[1246]
    (.letOp (n := 1252) (.exec 0x10adce (fun s => s.RIP = 0x10adce) (movR64R64Effect 0x10adce 5 0) (Reg.operands [.gpr 0] [])) #v[1246]
    (.letOp (n := 1253) (.out 0x10add1 (movR64R64Effect 0x10add1 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[1201]
    (.letOp (n := 1254) (.exec 0x10add1 (fun s => s.RIP = 0x10add1) (movR64R64Effect 0x10add1 0 10) (Reg.operands [.gpr 10] [])) #v[1201]
    (.letOp (n := 1255) (.out 0x10add4 (movR64Imm64Effect 0x10add4 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1256) (.exec 0x10add4 (fun s => s.RIP = 0x10add4) (movR64Imm64Effect 0x10add4 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1257) (.out 0x10adde (mulR64Effect 0x10adde 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1255, 1253]
    (.letOp (n := 1258) (.out 0x10adde (mulR64Effect 0x10adde 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1255, 1253]
    (.letOp (n := 1259) (.exec 0x10adde (fun s => s.RIP = 0x10adde) (mulR64Effect 0x10adde 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1255, 1253]
    (.letOp (n := 1260) (.out 0x10ade1 (addR64R64Effect 0x10ade1 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[1251, 1240]
    (.letOp (n := 1261) (.out 0x10ade1 (addR64R64Effect 0x10ade1 5 13) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 13] []) (.flag .CF)) #v[1251, 1240]
    (.letOp (n := 1262) (.exec 0x10ade1 (fun s => s.RIP = 0x10ade1) (addR64R64Effect 0x10ade1 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[1251, 1240]
    (.letOp (n := 1263) (.out 0x10ade4 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ade4 9 12)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[1249, 1238, 1261]
    (.letOp (n := 1264) (.exec 0x10ade4 (fun s => s.RIP = 0x10ade4) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ade4 9 12)) (Reg.operands [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1249, 1238, 1261]
    (.letOp (n := 1265) (.out 0x10ade7 (addR64R64Effect 0x10ade7 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[1260, 1231]
    (.letOp (n := 1266) (.out 0x10ade7 (addR64R64Effect 0x10ade7 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[1260, 1231]
    (.letOp (n := 1267) (.exec 0x10ade7 (fun s => s.RIP = 0x10ade7) (addR64R64Effect 0x10ade7 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[1260, 1231]
    (.letOp (n := 1268) (.out 0x10adea (atFlags StatusFlags.CF (adcR64R64Effect 0x10adea 9 7)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[1263, 1229, 1266]
    (.letOp (n := 1269) (.exec 0x10adea (fun s => s.RIP = 0x10adea) (atFlags StatusFlags.CF (adcR64R64Effect 0x10adea 9 7)) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1263, 1229, 1266]
    (.letOp (n := 1270) (.out 0x10aded (addR64R64Effect 0x10aded 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[1265, 1220]
    (.letOp (n := 1271) (.out 0x10aded (addR64R64Effect 0x10aded 5 14) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 14] []) (.flag .CF)) #v[1265, 1220]
    (.letOp (n := 1272) (.exec 0x10aded (fun s => s.RIP = 0x10aded) (addR64R64Effect 0x10aded 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[1265, 1220]
    (b_l10a410_29)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_28 : List UInt8 :=
  [0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC7, 0x48, 0x8B,
    0x44, 0x24, 0x08, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD4, 0x49, 0x89, 0xC5, 0x4C, 0x8B, 0x44, 0x24,
    0x18, 0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE1, 0x49, 0x89, 0xD1, 0x48, 0x89, 0xC5, 0x4C, 0x89, 0xD0,
    0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x01, 0xED,
    0x4D, 0x11, 0xE1, 0x4C, 0x01, 0xFD, 0x49, 0x11, 0xF9, 0x4C, 0x01, 0xF5] ++ bytes_l10a410_29

theorem code_l10a410_28 : ∀ x ∈ codeRange 0x10ada4 bytes_l10a410_28, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xada4 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_29

def b_l10a410_27 : Block Op Label signature Reg.count 1185 :=
  .letOp (n := 1185) (.out 0x10ad45 (addR64M64Effect 0x10ad45 6 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[1180, 65]
    (.letOp (n := 1186) (.out 0x10ad45 (addR64M64Effect 0x10ad45 6 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[1180, 65]
    (.letOp (n := 1187) (.exec 0x10ad45 (LoadPre 0x10ad45 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10ad45 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10ad45 6 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1180, 65]
    (.letOp (n := 1188) (.out 0x10ad4d (atFlags StatusFlags.CF (adcR64M64Effect 0x10ad4d 1 (.sib 4 none 0 (.d8 0x40)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[1183, 65, 1186]
    (.letOp (n := 1189) (.exec 0x10ad4d (LoadPre 0x10ad4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10ad4d + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10ad4d 1 (.sib 4 none 0 (.d8 0x40)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1183, 65, 1186]
    (.letOp (n := 1190) (.out 0x10ad52 (addR64M64Effect 0x10ad52 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[1185, 65]
    (.letOp (n := 1191) (.out 0x10ad52 (addR64M64Effect 0x10ad52 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[1185, 65]
    (.letOp (n := 1192) (.exec 0x10ad52 (LoadPre 0x10ad52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ad52 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10ad52 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1185, 65]
    (.letOp (n := 1193) (.out 0x10ad57 (atFlags StatusFlags.CF (adcR64M64Effect 0x10ad57 1 (.sib 4 none 0 (.d8 0x60)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[1188, 65, 1191]
    (.letOp (n := 1194) (.exec 0x10ad57 (LoadPre 0x10ad57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10ad57 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10ad57 1 (.sib 4 none 0 (.d8 0x60)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1188, 65, 1191]
    (.letOp (n := 1195) (.out 0x10ad5c (addR64R64Effect 0x10ad5c 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[1190, 1174]
    (.letOp (n := 1196) (.out 0x10ad5c (addR64R64Effect 0x10ad5c 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[1190, 1174]
    (.letOp (n := 1197) (.exec 0x10ad5c (fun s => s.RIP = 0x10ad5c) (addR64R64Effect 0x10ad5c 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[1190, 1174]
    (.letOp (n := 1198) (.exec 0x10ad5f (StorePre 0x10ad5f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10ad5f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ad5f 6 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1195, 65]
    (.letOp (n := 1199) (.out 0x10ad67 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ad67 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1193, 1175, 1196]
    (.letOp (n := 1200) (.exec 0x10ad67 (fun s => s.RIP = 0x10ad67) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ad67 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1193, 1175, 1196]
    (.letOp (n := 1201) (.out 0x10ad6a (shldR64R64Effect 0x10ad6a 5 10 14 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[1163, 1161]
    (.letOp (n := 1202) (.exec 0x10ad6a (fun s => s.RIP = 0x10ad6a) (shldR64R64Effect 0x10ad6a 5 10 14 12) (Reg.operands [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1163, 1161]
    (.letOp (n := 1203) (.out 0x10ad6f (shldR64R64Effect 0x10ad6f 5 1 6 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1199, 1195]
    (.letOp (n := 1204) (.exec 0x10ad6f (fun s => s.RIP = 0x10ad6f) (shldR64R64Effect 0x10ad6f 5 1 6 12) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1199, 1195]
    (.letOp (n := 1205) (.out 0x10ad74 (movR64R64Effect 0x10ad74 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1106]
    (.letOp (n := 1206) (.exec 0x10ad74 (fun s => s.RIP = 0x10ad74) (movR64R64Effect 0x10ad74 0 13) (Reg.operands [.gpr 13] [])) #v[1106]
    (.letOp (n := 1207) (.out 0x10ad77 (mulR64Effect 0x10ad77 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[1110, 1205]
    (.letOp (n := 1208) (.out 0x10ad77 (mulR64Effect 0x10ad77 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[1110, 1205]
    (.letOp (n := 1209) (.exec 0x10ad77 (fun s => s.RIP = 0x10ad77) (mulR64Effect 0x10ad77 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[1110, 1205]
    (.letOp (n := 1210) (.exec 0x10ad7a (StorePre 0x10ad7a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10ad7a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ad7a 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1208, 65]
    (.letOp (n := 1211) (.exec 0x10ad7f (StorePre 0x10ad7f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ad7f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ad7f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1207, 65]
    (.letOp (n := 1212) (.out 0x10ad84 (movR64M64Effect 0x10ad84 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1213) (.exec 0x10ad84 (LoadPre 0x10ad84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10ad84 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ad84 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1214) (.out 0x10ad89 (movR64M64Effect 0x10ad89 6 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 1215) (.exec 0x10ad89 (LoadPre 0x10ad89 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10ad89 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ad89 6 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1216) (.out 0x10ad91 (mulR64Effect 0x10ad91 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[1214, 1212]
    (.letOp (n := 1217) (.out 0x10ad91 (mulR64Effect 0x10ad91 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[1214, 1212]
    (.letOp (n := 1218) (.exec 0x10ad91 (fun s => s.RIP = 0x10ad91) (mulR64Effect 0x10ad91 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[1214, 1212]
    (.letOp (n := 1219) (.exec 0x10ad94 (StorePre 0x10ad94 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10ad94 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ad94 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1217, 65]
    (.letOp (n := 1220) (.out 0x10ad99 (movR64R64Effect 0x10ad99 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[1216]
    (.letOp (n := 1221) (.exec 0x10ad99 (fun s => s.RIP = 0x10ad99) (movR64R64Effect 0x10ad99 14 0) (Reg.operands [.gpr 0] [])) #v[1216]
    (.letOp (n := 1222) (.out 0x10ad9c (movR64M64Effect 0x10ad9c 11 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 1223) (.exec 0x10ad9c (LoadPre 0x10ad9c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10ad9c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ad9c 11 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1224) (.out 0x10ada1 (movR64R64Effect 0x10ada1 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[1222]
    (.letOp (n := 1225) (.exec 0x10ada1 (fun s => s.RIP = 0x10ada1) (movR64R64Effect 0x10ada1 0 11) (Reg.operands [.gpr 11] [])) #v[1222]
    (b_l10a410_28)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_27 : List UInt8 :=
  [0x48, 0x03, 0xB4, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x13, 0x4C, 0x24, 0x40, 0x48, 0x03, 0x74,
    0x24, 0x20, 0x48, 0x13, 0x4C, 0x24, 0x60, 0x48, 0x01, 0xC6, 0x48, 0x89, 0xB4, 0x24, 0xD8, 0x00,
    0x00, 0x00, 0x48, 0x11, 0xD1, 0x4D, 0x0F, 0xA4, 0xF2, 0x0C, 0x48, 0x0F, 0xA4, 0xF1, 0x0C, 0x4C,
    0x89, 0xE8, 0x49, 0xF7, 0xE3, 0x48, 0x89, 0x54, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48,
    0x8B, 0x44, 0x24, 0x58, 0x48, 0x8B, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE6, 0x48,
    0x89, 0x54, 0x24, 0x40, 0x49, 0x89, 0xC6, 0x4C, 0x8B, 0x5C, 0x24, 0x30, 0x4C, 0x89, 0xD8] ++ bytes_l10a410_28

theorem code_l10a410_27 : ∀ x ∈ codeRange 0x10ad45 bytes_l10a410_27, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xad45 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_28

def b_l10a410_26 : Block Op Label signature Reg.count 1147 :=
  .letOp (n := 1147) (.exec 0x10ace7 (StorePre 0x10ace7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10ace7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ace7 3 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1140, 65]
    (.letOp (n := 1148) (.out 0x10acef (movR64R64Effect 0x10acef 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1144]
    (.letOp (n := 1149) (.exec 0x10acef (fun s => s.RIP = 0x10acef) (movR64R64Effect 0x10acef 6 0) (Reg.operands [.gpr 0] [])) #v[1144]
    (.letOp (n := 1150) (.out 0x10acf2 (movR64R64Effect 0x10acf2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1145]
    (.letOp (n := 1151) (.exec 0x10acf2 (fun s => s.RIP = 0x10acf2) (movR64R64Effect 0x10acf2 1 2) (Reg.operands [.gpr 2] [])) #v[1145]
    (.letOp (n := 1152) (.out 0x10acf5 (movR64M64Effect 0x10acf5 9 (.base 10 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[1108]
    (.letOp (n := 1153) (.exec 0x10acf5 (LoadPre 0x10acf5 (fun s => AddrMode.addr (.base 10 (.d8 0x70)) s (0x10acf5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10acf5 9 (.base 10 (.d8 0x70))) (Reg.operands [.gpr 10] [])) #v[1108]
    (.letOp (n := 1154) (.out 0x10acf9 (movR64R64Effect 0x10acf9 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1106]
    (.letOp (n := 1155) (.exec 0x10acf9 (fun s => s.RIP = 0x10acf9) (movR64R64Effect 0x10acf9 0 13) (Reg.operands [.gpr 13] [])) #v[1106]
    (.letOp (n := 1156) (.exec 0x10acfc (StorePre 0x10acfc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10acfc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10acfc 13 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[1106, 65]
    (.letOp (n := 1157) (.out 0x10ad01 (mulR64Effect 0x10ad01 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[1152, 1154]
    (.letOp (n := 1158) (.out 0x10ad01 (mulR64Effect 0x10ad01 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[1152, 1154]
    (.letOp (n := 1159) (.exec 0x10ad01 (fun s => s.RIP = 0x10ad01) (mulR64Effect 0x10ad01 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1152, 1154]
    (.letOp (n := 1160) (.exec 0x10ad04 (StorePre 0x10ad04 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10ad04 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ad04 9 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[1152, 65]
    (.letOp (n := 1161) (.out 0x10ad09 (movR64R64Effect 0x10ad09 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[1157]
    (.letOp (n := 1162) (.exec 0x10ad09 (fun s => s.RIP = 0x10ad09) (movR64R64Effect 0x10ad09 14 0) (Reg.operands [.gpr 0] [])) #v[1157]
    (.letOp (n := 1163) (.out 0x10ad0c (movR64R64Effect 0x10ad0c 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[1158]
    (.letOp (n := 1164) (.exec 0x10ad0c (fun s => s.RIP = 0x10ad0c) (movR64R64Effect 0x10ad0c 10 2) (Reg.operands [.gpr 2] [])) #v[1158]
    (.letOp (n := 1165) (.out 0x10ad0f (addR64R64Effect 0x10ad0f 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[1090, 1082]
    (.letOp (n := 1166) (.exec 0x10ad0f (fun s => s.RIP = 0x10ad0f) (addR64R64Effect 0x10ad0f 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[1090, 1082]
    (.letOp (n := 1167) (.exec 0x10ad12 (StorePre 0x10ad12 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10ad12 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ad12 5 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[1165, 65]
    (.letOp (n := 1168) (.out 0x10ad1a (movR64Imm64Effect 0x10ad1a 8 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 1169) (.exec 0x10ad1a (fun s => s.RIP = 0x10ad1a) (movR64Imm64Effect 0x10ad1a 8 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1170) (.out 0x10ad24 (andR64R64Effect 0x10ad24 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[1157, 1168]
    (.letOp (n := 1171) (.exec 0x10ad24 (fun s => s.RIP = 0x10ad24) (andR64R64Effect 0x10ad24 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[1157, 1168]
    (.letOp (n := 1172) (.out 0x10ad27 (movR64Imm64Effect 0x10ad27 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1173) (.exec 0x10ad27 (fun s => s.RIP = 0x10ad27) (movR64Imm64Effect 0x10ad27 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1174) (.out 0x10ad31 (mulR64Effect 0x10ad31 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1172, 1170]
    (.letOp (n := 1175) (.out 0x10ad31 (mulR64Effect 0x10ad31 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1172, 1170]
    (.letOp (n := 1176) (.exec 0x10ad31 (fun s => s.RIP = 0x10ad31) (mulR64Effect 0x10ad31 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1172, 1170]
    (.letOp (n := 1177) (.out 0x10ad34 (andR64R64Effect 0x10ad34 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 8] []) (.reg (.gpr 12))) #v[1084, 1168]
    (.letOp (n := 1178) (.exec 0x10ad34 (fun s => s.RIP = 0x10ad34) (andR64R64Effect 0x10ad34 12 8) (Reg.operands [.gpr 12, .gpr 8] [])) #v[1084, 1168]
    (.letOp (n := 1179) (.exec 0x10ad37 (StorePre 0x10ad37 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b8)) s (0x10ad37 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ad37 12 (.sib 4 none 0 (.d32 0x1b8))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[1177, 65]
    (.letOp (n := 1180) (.out 0x10ad3f (addR64R64Effect 0x10ad3f 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[1148, 1136]
    (.letOp (n := 1181) (.out 0x10ad3f (addR64R64Effect 0x10ad3f 6 15) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 15] []) (.flag .CF)) #v[1148, 1136]
    (.letOp (n := 1182) (.exec 0x10ad3f (fun s => s.RIP = 0x10ad3f) (addR64R64Effect 0x10ad3f 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[1148, 1136]
    (.letOp (n := 1183) (.out 0x10ad42 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ad42 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1150, 1138, 1181]
    (.letOp (n := 1184) (.exec 0x10ad42 (fun s => s.RIP = 0x10ad42) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ad42 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1150, 1138, 1181]
    (b_l10a410_27))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_26 : List UInt8 :=
  [0x48, 0x89, 0x9C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC6, 0x48, 0x89, 0xD1, 0x4D, 0x8B,
    0x4A, 0x70, 0x4C, 0x89, 0xE8, 0x4C, 0x89, 0x6C, 0x24, 0x48, 0x49, 0xF7, 0xE1, 0x4C, 0x89, 0x4C,
    0x24, 0x70, 0x49, 0x89, 0xC6, 0x49, 0x89, 0xD2, 0x4C, 0x01, 0xC5, 0x48, 0x89, 0xAC, 0x24, 0x38,
    0x01, 0x00, 0x00, 0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xC0,
    0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4D, 0x21, 0xC4,
    0x4C, 0x89, 0xA4, 0x24, 0xB8, 0x01, 0x00, 0x00, 0x4C, 0x01, 0xFE, 0x48, 0x11, 0xF9] ++ bytes_l10a410_27

theorem code_l10a410_26 : ∀ x ∈ codeRange 0x10ace7 bytes_l10a410_26, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xace7 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_27

def b_l10a410_25 : Block Op Label signature Reg.count 1110 :=
  .letOp (n := 1110) (.out 0x10ac8d (movR64M64Effect 0x10ac8d 11 (.base 10 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[1108]
    (.letOp (n := 1111) (.exec 0x10ac8d (LoadPre 0x10ac8d (fun s => AddrMode.addr (.base 10 (.d8 0x50)) s (0x10ac8d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10ac8d 11 (.base 10 (.d8 0x50))) (Reg.operands [.gpr 10] [])) #v[1108]
    (.letOp (n := 1112) (.out 0x10ac91 (mulR64Effect 0x10ac91 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[1110, 1103]
    (.letOp (n := 1113) (.out 0x10ac91 (mulR64Effect 0x10ac91 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[1110, 1103]
    (.letOp (n := 1114) (.exec 0x10ac91 (fun s => s.RIP = 0x10ac91) (mulR64Effect 0x10ac91 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[1110, 1103]
    (.letOp (n := 1115) (.exec 0x10ac94 (StorePre 0x10ac94 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10ac94 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ac94 11 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[1110, 65]
    (.letOp (n := 1116) (.exec 0x10ac9c (StorePre 0x10ac9c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ac9c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ac9c 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1112, 65]
    (.letOp (n := 1117) (.exec 0x10aca1 (StorePre 0x10aca1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10aca1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10aca1 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1113, 65]
    (.letOp (n := 1118) (.out 0x10aca6 (movR64M64Effect 0x10aca6 1 (.base 10 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[1108]
    (.letOp (n := 1119) (.exec 0x10aca6 (LoadPre 0x10aca6 (fun s => AddrMode.addr (.base 10 (.d8 0x58)) s (0x10aca6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10aca6 1 (.base 10 (.d8 0x58))) (Reg.operands [.gpr 10] [])) #v[1108]
    (.letOp (n := 1120) (.exec 0x10acaa (StorePre 0x10acaa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10acaa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10acaa 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1118, 65]
    (.letOp (n := 1121) (.out 0x10acb2 (movR64R64Effect 0x10acb2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[1100]
    (.letOp (n := 1122) (.exec 0x10acb2 (fun s => s.RIP = 0x10acb2) (movR64R64Effect 0x10acb2 0 6) (Reg.operands [.gpr 6] [])) #v[1100]
    (.letOp (n := 1123) (.out 0x10acb5 (mulR64Effect 0x10acb5 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1118, 1121]
    (.letOp (n := 1124) (.out 0x10acb5 (mulR64Effect 0x10acb5 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1118, 1121]
    (.letOp (n := 1125) (.exec 0x10acb5 (fun s => s.RIP = 0x10acb5) (mulR64Effect 0x10acb5 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1118, 1121]
    (.letOp (n := 1126) (.exec 0x10acb8 (StorePre 0x10acb8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10acb8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10acb8 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1123, 65]
    (.letOp (n := 1127) (.exec 0x10acc0 (StorePre 0x10acc0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10acc0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10acc0 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1124, 65]
    (.letOp (n := 1128) (.out 0x10acc5 (movR64M64Effect 0x10acc5 1 (.base 10 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[1108]
    (.letOp (n := 1129) (.exec 0x10acc5 (LoadPre 0x10acc5 (fun s => AddrMode.addr (.base 10 (.d8 0x60)) s (0x10acc5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10acc5 1 (.base 10 (.d8 0x60))) (Reg.operands [.gpr 10] [])) #v[1108]
    (.letOp (n := 1130) (.exec 0x10acc9 (StorePre 0x10acc9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10acc9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10acc9 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1128, 65]
    (.letOp (n := 1131) (.out 0x10acd1 (movR64R64Effect 0x10acd1 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1097]
    (.letOp (n := 1132) (.exec 0x10acd1 (fun s => s.RIP = 0x10acd1) (movR64R64Effect 0x10acd1 0 7) (Reg.operands [.gpr 7] [])) #v[1097]
    (.letOp (n := 1133) (.out 0x10acd4 (mulR64Effect 0x10acd4 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1128, 1131]
    (.letOp (n := 1134) (.out 0x10acd4 (mulR64Effect 0x10acd4 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1128, 1131]
    (.letOp (n := 1135) (.exec 0x10acd4 (fun s => s.RIP = 0x10acd4) (mulR64Effect 0x10acd4 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1128, 1131]
    (.letOp (n := 1136) (.out 0x10acd7 (movR64R64Effect 0x10acd7 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1133]
    (.letOp (n := 1137) (.exec 0x10acd7 (fun s => s.RIP = 0x10acd7) (movR64R64Effect 0x10acd7 15 0) (Reg.operands [.gpr 0] [])) #v[1133]
    (.letOp (n := 1138) (.out 0x10acda (movR64R64Effect 0x10acda 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[1134]
    (.letOp (n := 1139) (.exec 0x10acda (fun s => s.RIP = 0x10acda) (movR64R64Effect 0x10acda 7 2) (Reg.operands [.gpr 2] [])) #v[1134]
    (.letOp (n := 1140) (.out 0x10acdd (movR64M64Effect 0x10acdd 3 (.base 10 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 10] []) (.reg (.gpr 3))) #v[1108]
    (.letOp (n := 1141) (.exec 0x10acdd (LoadPre 0x10acdd (fun s => AddrMode.addr (.base 10 (.d8 0x68)) s (0x10acdd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10acdd 3 (.base 10 (.d8 0x68))) (Reg.operands [.gpr 10] [])) #v[1108]
    (.letOp (n := 1142) (.out 0x10ace1 (movR64R64Effect 0x10ace1 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[1094]
    (.letOp (n := 1143) (.exec 0x10ace1 (fun s => s.RIP = 0x10ace1) (movR64R64Effect 0x10ace1 0 9) (Reg.operands [.gpr 9] [])) #v[1094]
    (.letOp (n := 1144) (.out 0x10ace4 (mulR64Effect 0x10ace4 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[1140, 1142]
    (.letOp (n := 1145) (.out 0x10ace4 (mulR64Effect 0x10ace4 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[1140, 1142]
    (.letOp (n := 1146) (.exec 0x10ace4 (fun s => s.RIP = 0x10ace4) (mulR64Effect 0x10ace4 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1140, 1142]
    (b_l10a410_26)))))))))))))))))))))))))))))))))))))

def bytes_l10a410_25 : List UInt8 :=
  [0x4D, 0x8B, 0x5A, 0x50, 0x49, 0xF7, 0xE3, 0x4C, 0x89, 0x9C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0x54, 0x24, 0x60, 0x49, 0x8B, 0x4A, 0x58, 0x48, 0x89, 0x8C,
    0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0x84, 0x24, 0xE8,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x40, 0x49, 0x8B, 0x4A, 0x60, 0x48, 0x89, 0x8C, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xC7, 0x48, 0x89, 0xD7,
    0x49, 0x8B, 0x5A, 0x68, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0xE3] ++ bytes_l10a410_26

theorem code_l10a410_25 : ∀ x ∈ codeRange 0x10ac8d bytes_l10a410_25, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xac8d 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_26

def b_l10a410_24 : Block Op Label signature Reg.count 1072 :=
  .letOp (n := 1072) (.out 0x10ac2d (addR64R64Effect 0x10ac2d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1063, 1070]
    (.letOp (n := 1073) (.out 0x10ac2d (addR64R64Effect 0x10ac2d 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[1063, 1070]
    (.letOp (n := 1074) (.exec 0x10ac2d (fun s => s.RIP = 0x10ac2d) (addR64R64Effect 0x10ac2d 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1063, 1070]
    (.letOp (n := 1075) (.out 0x10ac30 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ac30 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1066, 1073]
    (.letOp (n := 1076) (.exec 0x10ac30 (fun s => s.RIP = 0x10ac30) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ac30 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1066, 1073]
    (.letOp (n := 1077) (.out 0x10ac34 (addR64R64Effect 0x10ac34 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[1072, 1056]
    (.letOp (n := 1078) (.out 0x10ac34 (addR64R64Effect 0x10ac34 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[1072, 1056]
    (.letOp (n := 1079) (.exec 0x10ac34 (fun s => s.RIP = 0x10ac34) (addR64R64Effect 0x10ac34 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[1072, 1056]
    (.letOp (n := 1080) (.out 0x10ac37 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ac37 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[1075, 1078]
    (.letOp (n := 1081) (.exec 0x10ac37 (fun s => s.RIP = 0x10ac37) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ac37 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1075, 1078]
    (.letOp (n := 1082) (.out 0x10ac3b (shldR64R64Effect 0x10ac3b 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[1080, 1077]
    (.letOp (n := 1083) (.exec 0x10ac3b (fun s => s.RIP = 0x10ac3b) (shldR64R64Effect 0x10ac3b 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1080, 1077]
    (.letOp (n := 1084) (.out 0x10ac40 (movR64R64Effect 0x10ac40 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[1077]
    (.letOp (n := 1085) (.exec 0x10ac40 (fun s => s.RIP = 0x10ac40) (movR64R64Effect 0x10ac40 12 0) (Reg.operands [.gpr 0] [])) #v[1077]
    (.letOp (n := 1086) (.out 0x10ac43 (movR64M64Effect 0x10ac43 5 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 1087) (.exec 0x10ac43 (LoadPre 0x10ac43 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10ac43 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ac43 5 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1088) (.out 0x10ac4b (movR64Imm64Effect 0x10ac4b 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1089) (.exec 0x10ac4b (fun s => s.RIP = 0x10ac4b) (movR64Imm64Effect 0x10ac4b 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1090) (.out 0x10ac55 (andR64R64Effect 0x10ac55 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[1086, 1088]
    (.letOp (n := 1091) (.exec 0x10ac55 (fun s => s.RIP = 0x10ac55) (andR64R64Effect 0x10ac55 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[1086, 1088]
    (.letOp (n := 1092) (.out 0x10ac58 (movR64M64Effect 0x10ac58 1 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 1093) (.exec 0x10ac58 (LoadPre 0x10ac58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10ac58 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ac58 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1094) (.out 0x10ac5d (movR64M64Effect 0x10ac5d 9 (.base 1 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[1092]
    (.letOp (n := 1095) (.exec 0x10ac5d (LoadPre 0x10ac5d (fun s => AddrMode.addr (.base 1 (.d8 0x50)) s (0x10ac5d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10ac5d 9 (.base 1 (.d8 0x50))) (Reg.operands [.gpr 1] [])) #v[1092]
    (.letOp (n := 1096) (.exec 0x10ac61 (StorePre 0x10ac61 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ac61 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ac61 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[1094, 65]
    (.letOp (n := 1097) (.out 0x10ac66 (movR64M64Effect 0x10ac66 7 (.base 1 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1092]
    (.letOp (n := 1098) (.exec 0x10ac66 (LoadPre 0x10ac66 (fun s => AddrMode.addr (.base 1 (.d8 0x58)) s (0x10ac66 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10ac66 7 (.base 1 (.d8 0x58))) (Reg.operands [.gpr 1] [])) #v[1092]
    (.letOp (n := 1099) (.exec 0x10ac6a (StorePre 0x10ac6a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10ac6a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ac6a 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1097, 65]
    (.letOp (n := 1100) (.out 0x10ac6f (movR64M64Effect 0x10ac6f 6 (.base 1 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[1092]
    (.letOp (n := 1101) (.exec 0x10ac6f (LoadPre 0x10ac6f (fun s => AddrMode.addr (.base 1 (.d8 0x60)) s (0x10ac6f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10ac6f 6 (.base 1 (.d8 0x60))) (Reg.operands [.gpr 1] [])) #v[1092]
    (.letOp (n := 1102) (.exec 0x10ac73 (StorePre 0x10ac73 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10ac73 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ac73 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1100, 65]
    (.letOp (n := 1103) (.out 0x10ac78 (movR64M64Effect 0x10ac78 0 (.base 1 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1092]
    (.letOp (n := 1104) (.exec 0x10ac78 (LoadPre 0x10ac78 (fun s => AddrMode.addr (.base 1 (.d8 0x68)) s (0x10ac78 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10ac78 0 (.base 1 (.d8 0x68))) (Reg.operands [.gpr 1] [])) #v[1092]
    (.letOp (n := 1105) (.exec 0x10ac7c (StorePre 0x10ac7c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10ac7c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ac7c 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1103, 65]
    (.letOp (n := 1106) (.out 0x10ac81 (movR64M64Effect 0x10ac81 13 (.base 1 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[1092]
    (.letOp (n := 1107) (.exec 0x10ac81 (LoadPre 0x10ac81 (fun s => AddrMode.addr (.base 1 (.d8 0x70)) s (0x10ac81 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10ac81 13 (.base 1 (.d8 0x70))) (Reg.operands [.gpr 1] [])) #v[1092]
    (.letOp (n := 1108) (.out 0x10ac85 (movR64M64Effect 0x10ac85 10 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 1109) (.exec 0x10ac85 (LoadPre 0x10ac85 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x10ac85 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ac85 10 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_25))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_24 : List UInt8 :=
  [0x48, 0x01, 0xC8, 0x49, 0x83, 0xD0, 0x00, 0x48, 0x01, 0xF8, 0x49, 0x83, 0xD0, 0x00, 0x49, 0x0F,
    0xA4, 0xC0, 0x0C, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0xAC, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0xB8,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x21, 0xC5, 0x48, 0x8B, 0x4C, 0x24, 0x60,
    0x4C, 0x8B, 0x49, 0x50, 0x4C, 0x89, 0x4C, 0x24, 0x18, 0x48, 0x8B, 0x79, 0x58, 0x48, 0x89, 0x7C,
    0x24, 0x08, 0x48, 0x8B, 0x71, 0x60, 0x48, 0x89, 0x74, 0x24, 0x30, 0x48, 0x8B, 0x41, 0x68, 0x48,
    0x89, 0x44, 0x24, 0x58, 0x4C, 0x8B, 0x69, 0x70, 0x4C, 0x8B, 0x94, 0x24, 0x80, 0x01, 0x00, 0x00] ++ bytes_l10a410_25

theorem code_l10a410_24 : ∀ x ∈ codeRange 0x10ac2d bytes_l10a410_24, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xac2d 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_25

def b_l10a410_23 : Block Op Label signature Reg.count 1027 :=
  .letOp (n := 1027) (.out 0x10abdc (andR64R64Effect 0x10abdc 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[1025, 942]
    (.letOp (n := 1028) (.exec 0x10abdc (fun s => s.RIP = 0x10abdc) (andR64R64Effect 0x10abdc 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[1025, 942]
    (.letOp (n := 1029) (.out 0x10abdf (movR64Imm64Effect 0x10abdf 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1030) (.exec 0x10abdf (fun s => s.RIP = 0x10abdf) (movR64Imm64Effect 0x10abdf 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1031) (.out 0x10abe9 (mulR64Effect 0x10abe9 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1029, 1027]
    (.letOp (n := 1032) (.out 0x10abe9 (mulR64Effect 0x10abe9 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1029, 1027]
    (.letOp (n := 1033) (.exec 0x10abe9 (fun s => s.RIP = 0x10abe9) (mulR64Effect 0x10abe9 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1029, 1027]
    (.letOp (n := 1034) (.out 0x10abec (addR64R64Effect 0x10abec 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[992, 985]
    (.letOp (n := 1035) (.out 0x10abec (addR64R64Effect 0x10abec 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[992, 985]
    (.letOp (n := 1036) (.exec 0x10abec (fun s => s.RIP = 0x10abec) (addR64R64Effect 0x10abec 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[992, 985]
    (.letOp (n := 1037) (.out 0x10abef (atFlags StatusFlags.CF (adcR64R64Effect 0x10abef 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[994, 983, 1035]
    (.letOp (n := 1038) (.exec 0x10abef (fun s => s.RIP = 0x10abef) (atFlags StatusFlags.CF (adcR64R64Effect 0x10abef 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[994, 983, 1035]
    (.letOp (n := 1039) (.out 0x10abf2 (addR64R64Effect 0x10abf2 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[1034, 976]
    (.letOp (n := 1040) (.out 0x10abf2 (addR64R64Effect 0x10abf2 14 5) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 5] []) (.flag .CF)) #v[1034, 976]
    (.letOp (n := 1041) (.exec 0x10abf2 (fun s => s.RIP = 0x10abf2) (addR64R64Effect 0x10abf2 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[1034, 976]
    (.letOp (n := 1042) (.out 0x10abf5 (atFlags StatusFlags.CF (adcR64M64Effect 0x10abf5 7 (.sib 4 none 0 (.d8 0x18)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[1037, 65, 1040]
    (.letOp (n := 1043) (.exec 0x10abf5 (LoadPre 0x10abf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10abf5 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10abf5 7 (.sib 4 none 0 (.d8 0x18)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1037, 65, 1040]
    (.letOp (n := 1044) (.out 0x10abfa (addR64R64Effect 0x10abfa 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[1031, 1039]
    (.letOp (n := 1045) (.out 0x10abfa (addR64R64Effect 0x10abfa 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[1031, 1039]
    (.letOp (n := 1046) (.exec 0x10abfa (fun s => s.RIP = 0x10abfa) (addR64R64Effect 0x10abfa 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[1031, 1039]
    (.letOp (n := 1047) (.out 0x10abfd (atFlags StatusFlags.CF (adcR64R64Effect 0x10abfd 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[1042, 1032, 1045]
    (.letOp (n := 1048) (.exec 0x10abfd (fun s => s.RIP = 0x10abfd) (atFlags StatusFlags.CF (adcR64R64Effect 0x10abfd 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1042, 1032, 1045]
    (.letOp (n := 1049) (.out 0x10ac00 (addR64R64Effect 0x10ac00 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[1044, 966]
    (.letOp (n := 1050) (.out 0x10ac00 (addR64R64Effect 0x10ac00 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[1044, 966]
    (.letOp (n := 1051) (.exec 0x10ac00 (fun s => s.RIP = 0x10ac00) (addR64R64Effect 0x10ac00 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[1044, 966]
    (.letOp (n := 1052) (.out 0x10ac03 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ac03 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[1047, 1050]
    (.letOp (n := 1053) (.exec 0x10ac03 (fun s => s.RIP = 0x10ac03) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ac03 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1047, 1050]
    (.letOp (n := 1054) (.out 0x10ac07 (shldR64R64Effect 0x10ac07 5 11 13 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1023, 1020]
    (.letOp (n := 1055) (.exec 0x10ac07 (fun s => s.RIP = 0x10ac07) (shldR64R64Effect 0x10ac07 5 11 13 12) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1023, 1020]
    (.letOp (n := 1056) (.out 0x10ac0c (shldR64R64Effect 0x10ac0c 5 7 0 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1052, 1049]
    (.letOp (n := 1057) (.exec 0x10ac0c (fun s => s.RIP = 0x10ac0c) (shldR64R64Effect 0x10ac0c 5 7 0 12) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1052, 1049]
    (.letOp (n := 1058) (.out 0x10ac11 (andR64R64Effect 0x10ac11 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[1049, 942]
    (.letOp (n := 1059) (.exec 0x10ac11 (fun s => s.RIP = 0x10ac11) (andR64R64Effect 0x10ac11 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[1049, 942]
    (.letOp (n := 1060) (.exec 0x10ac14 (StorePre 0x10ac14 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10ac14 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ac14 0 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1058, 65]
    (.letOp (n := 1061) (.out 0x10ac1c (movR64R64Effect 0x10ac1c 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[1054]
    (.letOp (n := 1062) (.exec 0x10ac1c (fun s => s.RIP = 0x10ac1c) (movR64R64Effect 0x10ac1c 0 11) (Reg.operands [.gpr 11] [])) #v[1054]
    (.letOp (n := 1063) (.out 0x10ac1f (mulR64Effect 0x10ac1f 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1029, 1061]
    (.letOp (n := 1064) (.out 0x10ac1f (mulR64Effect 0x10ac1f 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1029, 1061]
    (.letOp (n := 1065) (.exec 0x10ac1f (fun s => s.RIP = 0x10ac1f) (mulR64Effect 0x10ac1f 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1029, 1061]
    (.letOp (n := 1066) (.out 0x10ac22 (movR64R64Effect 0x10ac22 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[1064]
    (.letOp (n := 1067) (.exec 0x10ac22 (fun s => s.RIP = 0x10ac22) (movR64R64Effect 0x10ac22 8 2) (Reg.operands [.gpr 2] [])) #v[1064]
    (.letOp (n := 1068) (.out 0x10ac25 (movR64M64Effect 0x10ac25 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 1069) (.exec 0x10ac25 (LoadPre 0x10ac25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ac25 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ac25 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1070) (.out 0x10ac2a (andR64R64Effect 0x10ac2a 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[1068, 942]
    (.letOp (n := 1071) (.exec 0x10ac2a (fun s => s.RIP = 0x10ac2a) (andR64R64Effect 0x10ac2a 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[1068, 942]
    (b_l10a410_24)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_23 : List UInt8 :=
  [0x4C, 0x21, 0xD0, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1,
    0x4D, 0x01, 0xE6, 0x4C, 0x11, 0xFF, 0x49, 0x01, 0xEE, 0x48, 0x13, 0x7C, 0x24, 0x18, 0x4C, 0x01,
    0xF0, 0x48, 0x11, 0xD7, 0x4C, 0x01, 0xC8, 0x48, 0x83, 0xD7, 0x00, 0x4D, 0x0F, 0xA4, 0xEB, 0x0C,
    0x48, 0x0F, 0xA4, 0xC7, 0x0C, 0x4C, 0x21, 0xD0, 0x48, 0x89, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00,
    0x4C, 0x89, 0xD8, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD0, 0x48, 0x8B, 0x4C, 0x24, 0x20, 0x4C, 0x21,
    0xD1] ++ bytes_l10a410_24

theorem code_l10a410_23 : ∀ x ∈ codeRange 0x10abdc bytes_l10a410_23, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xabdc 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_24

def b_l10a410_22 : Block Op Label signature Reg.count 983 :=
  .letOp (n := 983) (.out 0x10ab95 (movR64R64Effect 0x10ab95 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[981]
    (.letOp (n := 984) (.exec 0x10ab95 (fun s => s.RIP = 0x10ab95) (movR64R64Effect 0x10ab95 15 2) (Reg.operands [.gpr 2] [])) #v[981]
    (.letOp (n := 985) (.out 0x10ab98 (movR64R64Effect 0x10ab98 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[980]
    (.letOp (n := 986) (.exec 0x10ab98 (fun s => s.RIP = 0x10ab98) (movR64R64Effect 0x10ab98 12 0) (Reg.operands [.gpr 0] [])) #v[980]
    (.letOp (n := 987) (.out 0x10ab9b (movR64M64Effect 0x10ab9b 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 988) (.exec 0x10ab9b (LoadPre 0x10ab9b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10ab9b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10ab9b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 989) (.out 0x10ab9f (mulM64Effect 0x10ab9f 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[987, 65]
    (.letOp (n := 990) (.out 0x10ab9f (mulM64Effect 0x10ab9f 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[987, 65]
    (.letOp (n := 991) (.exec 0x10ab9f (LoadPre 0x10ab9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10ab9f + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ab9f 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[987, 65]
    (.letOp (n := 992) (.out 0x10aba4 (movR64R64Effect 0x10aba4 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[989]
    (.letOp (n := 993) (.exec 0x10aba4 (fun s => s.RIP = 0x10aba4) (movR64R64Effect 0x10aba4 14 0) (Reg.operands [.gpr 0] [])) #v[989]
    (.letOp (n := 994) (.out 0x10aba7 (movR64R64Effect 0x10aba7 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[990]
    (.letOp (n := 995) (.exec 0x10aba7 (fun s => s.RIP = 0x10aba7) (movR64R64Effect 0x10aba7 7 2) (Reg.operands [.gpr 2] [])) #v[990]
    (.letOp (n := 996) (.out 0x10abaa (andR64R64Effect 0x10abaa 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[968, 942]
    (.letOp (n := 997) (.exec 0x10abaa (fun s => s.RIP = 0x10abaa) (andR64R64Effect 0x10abaa 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[968, 942]
    (.letOp (n := 998) (.exec 0x10abad (StorePre 0x10abad 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10abad + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10abad 1 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[996, 65]
    (.letOp (n := 999) (.out 0x10abb5 (movR64R64Effect 0x10abb5 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[889]
    (.letOp (n := 1000) (.exec 0x10abb5 (fun s => s.RIP = 0x10abb5) (movR64R64Effect 0x10abb5 0 3) (Reg.operands [.gpr 3] [])) #v[889]
    (.letOp (n := 1001) (.out 0x10abb8 (mulR64Effect 0x10abb8 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[907, 999]
    (.letOp (n := 1002) (.out 0x10abb8 (mulR64Effect 0x10abb8 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[907, 999]
    (.letOp (n := 1003) (.exec 0x10abb8 (fun s => s.RIP = 0x10abb8) (mulR64Effect 0x10abb8 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[907, 999]
    (.letOp (n := 1004) (.out 0x10abbb (movR64R64Effect 0x10abbb 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[1002]
    (.letOp (n := 1005) (.exec 0x10abbb (fun s => s.RIP = 0x10abbb) (movR64R64Effect 0x10abbb 11 2) (Reg.operands [.gpr 2] [])) #v[1002]
    (.letOp (n := 1006) (.out 0x10abbe (movR64R64Effect 0x10abbe 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1001]
    (.letOp (n := 1007) (.exec 0x10abbe (fun s => s.RIP = 0x10abbe) (movR64R64Effect 0x10abbe 1 0) (Reg.operands [.gpr 0] [])) #v[1001]
    (.letOp (n := 1008) (.out 0x10abc1 (movR64M64Effect 0x10abc1 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1009) (.exec 0x10abc1 (LoadPre 0x10abc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10abc1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10abc1 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1010) (.out 0x10abc6 (mulR64Effect 0x10abc6 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[920, 1008]
    (.letOp (n := 1011) (.out 0x10abc6 (mulR64Effect 0x10abc6 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[920, 1008]
    (.letOp (n := 1012) (.exec 0x10abc6 (fun s => s.RIP = 0x10abc6) (mulR64Effect 0x10abc6 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[920, 1008]
    (.letOp (n := 1013) (.out 0x10abc9 (movR64R64Effect 0x10abc9 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[1010]
    (.letOp (n := 1014) (.exec 0x10abc9 (fun s => s.RIP = 0x10abc9) (movR64R64Effect 0x10abc9 13 0) (Reg.operands [.gpr 0] [])) #v[1010]
    (.letOp (n := 1015) (.out 0x10abcc (addR64R64Effect 0x10abcc 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[1013, 1006]
    (.letOp (n := 1016) (.out 0x10abcc (addR64R64Effect 0x10abcc 13 1) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 1] []) (.flag .CF)) #v[1013, 1006]
    (.letOp (n := 1017) (.exec 0x10abcc (fun s => s.RIP = 0x10abcc) (addR64R64Effect 0x10abcc 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[1013, 1006]
    (.letOp (n := 1018) (.out 0x10abcf (atFlags StatusFlags.CF (adcR64R64Effect 0x10abcf 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1004, 1011, 1016]
    (.letOp (n := 1019) (.exec 0x10abcf (fun s => s.RIP = 0x10abcf) (atFlags StatusFlags.CF (adcR64R64Effect 0x10abcf 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1004, 1011, 1016]
    (.letOp (n := 1020) (.out 0x10abd2 (addR64R64Effect 0x10abd2 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[1015, 940]
    (.letOp (n := 1021) (.out 0x10abd2 (addR64R64Effect 0x10abd2 13 8) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 8] []) (.flag .CF)) #v[1015, 940]
    (.letOp (n := 1022) (.exec 0x10abd2 (fun s => s.RIP = 0x10abd2) (addR64R64Effect 0x10abd2 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[1015, 940]
    (.letOp (n := 1023) (.out 0x10abd5 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10abd5 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1018, 1021]
    (.letOp (n := 1024) (.exec 0x10abd5 (fun s => s.RIP = 0x10abd5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10abd5 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1018, 1021]
    (.letOp (n := 1025) (.out 0x10abd9 (movR64R64Effect 0x10abd9 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1020]
    (.letOp (n := 1026) (.exec 0x10abd9 (fun s => s.RIP = 0x10abd9) (movR64R64Effect 0x10abd9 0 13) (Reg.operands [.gpr 13] [])) #v[1020]
    (b_l10a410_23))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_22 : List UInt8 :=
  [0x49, 0x89, 0xD7, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x04, 0x24, 0x48, 0xF7, 0x64, 0x24, 0x28, 0x49,
    0x89, 0xC6, 0x48, 0x89, 0xD7, 0x4C, 0x21, 0xD1, 0x48, 0x89, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00,
    0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE3, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC1, 0x48, 0x8B, 0x44, 0x24,
    0x38, 0x48, 0xF7, 0xE6, 0x49, 0x89, 0xC5, 0x49, 0x01, 0xCD, 0x49, 0x11, 0xD3, 0x4D, 0x01, 0xC5,
    0x49, 0x83, 0xD3, 0x00, 0x4C, 0x89, 0xE8] ++ bytes_l10a410_23

theorem code_l10a410_22 : ∀ x ∈ codeRange 0x10ab95 bytes_l10a410_22, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xab95 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_23

def b_l10a410_21 : Block Op Label signature Reg.count 938 :=
  .letOp (n := 938) (.out 0x10ab3b (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ab3b 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[933, 936]
    (.letOp (n := 939) (.exec 0x10ab3b (fun s => s.RIP = 0x10ab3b) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ab3b 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[933, 936]
    (.letOp (n := 940) (.out 0x10ab3f (shldR64R64Effect 0x10ab3f 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[938, 935]
    (.letOp (n := 941) (.exec 0x10ab3f (fun s => s.RIP = 0x10ab3f) (shldR64R64Effect 0x10ab3f 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[938, 935]
    (.letOp (n := 942) (.out 0x10ab44 (movR64Imm64Effect 0x10ab44 10 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 943) (.exec 0x10ab44 (fun s => s.RIP = 0x10ab44) (movR64Imm64Effect 0x10ab44 10 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 944) (.out 0x10ab4e (andR64R64Effect 0x10ab4e 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[935, 942]
    (.letOp (n := 945) (.exec 0x10ab4e (fun s => s.RIP = 0x10ab4e) (andR64R64Effect 0x10ab4e 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[935, 942]
    (.letOp (n := 946) (.out 0x10ab51 (movR64Imm64Effect 0x10ab51 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 947) (.exec 0x10ab51 (fun s => s.RIP = 0x10ab51) (movR64Imm64Effect 0x10ab51 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 948) (.out 0x10ab5b (mulR64Effect 0x10ab5b 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[946, 944]
    (.letOp (n := 949) (.out 0x10ab5b (mulR64Effect 0x10ab5b 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[946, 944]
    (.letOp (n := 950) (.exec 0x10ab5b (fun s => s.RIP = 0x10ab5b) (mulR64Effect 0x10ab5b 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[946, 944]
    (.letOp (n := 951) (.out 0x10ab5e (addR64M64Effect 0x10ab5e 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[887, 65]
    (.letOp (n := 952) (.out 0x10ab5e (addR64M64Effect 0x10ab5e 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 4] []) (.flag .CF)) #v[887, 65]
    (.letOp (n := 953) (.exec 0x10ab5e (LoadPre 0x10ab5e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10ab5e + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10ab5e 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[887, 65]
    (.letOp (n := 954) (.out 0x10ab63 (atFlags StatusFlags.CF (adcR64M64Effect 0x10ab63 9 (.sib 4 none 0 (.d8 0x18)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[885, 65, 952]
    (.letOp (n := 955) (.exec 0x10ab63 (LoadPre 0x10ab63 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ab63 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10ab63 9 (.sib 4 none 0 (.d8 0x18)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[885, 65, 952]
    (.letOp (n := 956) (.out 0x10ab68 (addR64R64Effect 0x10ab68 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[948, 951]
    (.letOp (n := 957) (.out 0x10ab68 (addR64R64Effect 0x10ab68 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[948, 951]
    (.letOp (n := 958) (.exec 0x10ab68 (fun s => s.RIP = 0x10ab68) (addR64R64Effect 0x10ab68 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[948, 951]
    (.letOp (n := 959) (.out 0x10ab6b (atFlags StatusFlags.CF (adcR64R64Effect 0x10ab6b 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[954, 949, 957]
    (.letOp (n := 960) (.exec 0x10ab6b (fun s => s.RIP = 0x10ab6b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ab6b 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[954, 949, 957]
    (.letOp (n := 961) (.out 0x10ab6e (addR64R64Effect 0x10ab6e 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[956, 867]
    (.letOp (n := 962) (.out 0x10ab6e (addR64R64Effect 0x10ab6e 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[956, 867]
    (.letOp (n := 963) (.exec 0x10ab6e (fun s => s.RIP = 0x10ab6e) (addR64R64Effect 0x10ab6e 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[956, 867]
    (.letOp (n := 964) (.out 0x10ab71 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ab71 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[959, 962]
    (.letOp (n := 965) (.exec 0x10ab71 (fun s => s.RIP = 0x10ab71) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ab71 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[959, 962]
    (.letOp (n := 966) (.out 0x10ab75 (shldR64R64Effect 0x10ab75 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[964, 961]
    (.letOp (n := 967) (.exec 0x10ab75 (fun s => s.RIP = 0x10ab75) (shldR64R64Effect 0x10ab75 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[964, 961]
    (.letOp (n := 968) (.out 0x10ab7a (movR64R64Effect 0x10ab7a 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[961]
    (.letOp (n := 969) (.exec 0x10ab7a (fun s => s.RIP = 0x10ab7a) (movR64R64Effect 0x10ab7a 1 0) (Reg.operands [.gpr 0] [])) #v[961]
    (.letOp (n := 970) (.out 0x10ab7d (movR64R64Effect 0x10ab7d 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[916]
    (.letOp (n := 971) (.exec 0x10ab7d (fun s => s.RIP = 0x10ab7d) (movR64R64Effect 0x10ab7d 0 13) (Reg.operands [.gpr 13] [])) #v[916]
    (.letOp (n := 972) (.out 0x10ab80 (mulM64Effect 0x10ab80 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[970, 65]
    (.letOp (n := 973) (.out 0x10ab80 (mulM64Effect 0x10ab80 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[970, 65]
    (.letOp (n := 974) (.exec 0x10ab80 (LoadPre 0x10ab80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10ab80 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ab80 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[970, 65]
    (.letOp (n := 975) (.exec 0x10ab85 (StorePre 0x10ab85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ab85 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ab85 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[973, 65]
    (.letOp (n := 976) (.out 0x10ab8a (movR64R64Effect 0x10ab8a 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[972]
    (.letOp (n := 977) (.exec 0x10ab8a (fun s => s.RIP = 0x10ab8a) (movR64R64Effect 0x10ab8a 5 0) (Reg.operands [.gpr 0] [])) #v[972]
    (.letOp (n := 978) (.out 0x10ab8d (movR64M64Effect 0x10ab8d 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 979) (.exec 0x10ab8d (LoadPre 0x10ab8d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10ab8d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ab8d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 980) (.out 0x10ab92 (mulR64Effect 0x10ab92 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[880, 978]
    (.letOp (n := 981) (.out 0x10ab92 (mulR64Effect 0x10ab92 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[880, 978]
    (.letOp (n := 982) (.exec 0x10ab92 (fun s => s.RIP = 0x10ab92) (mulR64Effect 0x10ab92 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[880, 978]
    (b_l10a410_22)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_21 : List UInt8 :=
  [0x49, 0x83, 0xD0, 0x00, 0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x49, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xD0, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE1, 0x4C, 0x03, 0x74, 0x24, 0x08, 0x4C, 0x13, 0x4C, 0x24, 0x18, 0x4C, 0x01, 0xF0,
    0x49, 0x11, 0xD1, 0x48, 0x01, 0xE8, 0x49, 0x83, 0xD1, 0x00, 0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48,
    0x89, 0xC1, 0x4C, 0x89, 0xE8, 0x48, 0xF7, 0x64, 0x24, 0x50, 0x48, 0x89, 0x54, 0x24, 0x18, 0x48,
    0x89, 0xC5, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0xF7, 0xE7] ++ bytes_l10a410_22

theorem code_l10a410_21 : ∀ x ∈ codeRange 0x10ab3b bytes_l10a410_21, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xab3b 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_22

def b_l10a410_20 : Block Op Label signature Reg.count 893 :=
  .letOp (n := 893) (.out 0x10aae7 (mulR64Effect 0x10aae7 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[800, 891]
    (.letOp (n := 894) (.out 0x10aae7 (mulR64Effect 0x10aae7 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[800, 891]
    (.letOp (n := 895) (.exec 0x10aae7 (fun s => s.RIP = 0x10aae7) (mulR64Effect 0x10aae7 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[800, 891]
    (.letOp (n := 896) (.out 0x10aaea (movR64R64Effect 0x10aaea 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[893]
    (.letOp (n := 897) (.exec 0x10aaea (fun s => s.RIP = 0x10aaea) (movR64R64Effect 0x10aaea 1 0) (Reg.operands [.gpr 0] [])) #v[893]
    (.letOp (n := 898) (.out 0x10aaed (movR64R64Effect 0x10aaed 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[894]
    (.letOp (n := 899) (.exec 0x10aaed (fun s => s.RIP = 0x10aaed) (movR64R64Effect 0x10aaed 15 2) (Reg.operands [.gpr 2] [])) #v[894]
    (.letOp (n := 900) (.out 0x10aaf0 (movR64Imm64Effect 0x10aaf0 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 901) (.exec 0x10aaf0 (fun s => s.RIP = 0x10aaf0) (movR64Imm64Effect 0x10aaf0 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 902) (.out 0x10aafa (andR64R64Effect 0x10aafa 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[869, 900]
    (.letOp (n := 903) (.exec 0x10aafa (fun s => s.RIP = 0x10aafa) (andR64R64Effect 0x10aafa 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[869, 900]
    (.letOp (n := 904) (.exec 0x10aafd (StorePre 0x10aafd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10aafd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10aafd 8 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[902, 65]
    (.letOp (n := 905) (.out 0x10ab05 (movR64R64Effect 0x10ab05 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[796]
    (.letOp (n := 906) (.exec 0x10ab05 (fun s => s.RIP = 0x10ab05) (movR64R64Effect 0x10ab05 0 13) (Reg.operands [.gpr 13] [])) #v[796]
    (.letOp (n := 907) (.out 0x10ab08 (movR64M64Effect 0x10ab08 11 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 908) (.exec 0x10ab08 (LoadPre 0x10ab08 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10ab08 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ab08 11 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 909) (.out 0x10ab10 (mulR64Effect 0x10ab10 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[907, 905]
    (.letOp (n := 910) (.out 0x10ab10 (mulR64Effect 0x10ab10 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[907, 905]
    (.letOp (n := 911) (.exec 0x10ab10 (fun s => s.RIP = 0x10ab10) (mulR64Effect 0x10ab10 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[907, 905]
    (.letOp (n := 912) (.out 0x10ab13 (movR64R64Effect 0x10ab13 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[910]
    (.letOp (n := 913) (.exec 0x10ab13 (fun s => s.RIP = 0x10ab13) (movR64R64Effect 0x10ab13 8 2) (Reg.operands [.gpr 2] [])) #v[910]
    (.letOp (n := 914) (.out 0x10ab16 (movR64R64Effect 0x10ab16 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[909]
    (.letOp (n := 915) (.exec 0x10ab16 (fun s => s.RIP = 0x10ab16) (movR64R64Effect 0x10ab16 12 0) (Reg.operands [.gpr 0] [])) #v[909]
    (.letOp (n := 916) (.out 0x10ab19 (movR64M64Effect 0x10ab19 13 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 917) (.exec 0x10ab19 (LoadPre 0x10ab19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10ab19 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ab19 13 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 918) (.out 0x10ab1e (movR64R64Effect 0x10ab1e 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[916]
    (.letOp (n := 919) (.exec 0x10ab1e (fun s => s.RIP = 0x10ab1e) (movR64R64Effect 0x10ab1e 0 13) (Reg.operands [.gpr 13] [])) #v[916]
    (.letOp (n := 920) (.out 0x10ab21 (movR64M64Effect 0x10ab21 6 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 921) (.exec 0x10ab21 (LoadPre 0x10ab21 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10ab21 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ab21 6 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 922) (.out 0x10ab29 (mulR64Effect 0x10ab29 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[920, 918]
    (.letOp (n := 923) (.out 0x10ab29 (mulR64Effect 0x10ab29 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[920, 918]
    (.letOp (n := 924) (.exec 0x10ab29 (fun s => s.RIP = 0x10ab29) (mulR64Effect 0x10ab29 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[920, 918]
    (.letOp (n := 925) (.out 0x10ab2c (addR64R64Effect 0x10ab2c 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[922, 914]
    (.letOp (n := 926) (.out 0x10ab2c (addR64R64Effect 0x10ab2c 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[922, 914]
    (.letOp (n := 927) (.exec 0x10ab2c (fun s => s.RIP = 0x10ab2c) (addR64R64Effect 0x10ab2c 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[922, 914]
    (.letOp (n := 928) (.out 0x10ab2f (atFlags StatusFlags.CF (adcR64R64Effect 0x10ab2f 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[912, 923, 926]
    (.letOp (n := 929) (.exec 0x10ab2f (fun s => s.RIP = 0x10ab2f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ab2f 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[912, 923, 926]
    (.letOp (n := 930) (.out 0x10ab32 (addR64R64Effect 0x10ab32 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[925, 896]
    (.letOp (n := 931) (.out 0x10ab32 (addR64R64Effect 0x10ab32 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[925, 896]
    (.letOp (n := 932) (.exec 0x10ab32 (fun s => s.RIP = 0x10ab32) (addR64R64Effect 0x10ab32 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[925, 896]
    (.letOp (n := 933) (.out 0x10ab35 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ab35 8 15)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[928, 898, 931]
    (.letOp (n := 934) (.exec 0x10ab35 (fun s => s.RIP = 0x10ab35) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ab35 8 15)) (Reg.operands [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[928, 898, 931]
    (.letOp (n := 935) (.out 0x10ab38 (addR64R64Effect 0x10ab38 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[930, 847]
    (.letOp (n := 936) (.out 0x10ab38 (addR64R64Effect 0x10ab38 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[930, 847]
    (.letOp (n := 937) (.exec 0x10ab38 (fun s => s.RIP = 0x10ab38) (addR64R64Effect 0x10ab38 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[930, 847]
    (b_l10a410_21)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_20 : List UInt8 :=
  [0x49, 0xF7, 0xE3, 0x48, 0x89, 0xC1, 0x49, 0x89, 0xD7, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x0F, 0x00, 0x49, 0x21, 0xC0, 0x4C, 0x89, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00, 0x4C, 0x89,
    0xE8, 0x4C, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE3, 0x49, 0x89, 0xD0, 0x49,
    0x89, 0xC4, 0x4C, 0x8B, 0x6C, 0x24, 0x78, 0x4C, 0x89, 0xE8, 0x48, 0x8B, 0xB4, 0x24, 0xF0, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0xE6, 0x4C, 0x01, 0xE0, 0x49, 0x11, 0xD0, 0x48, 0x01, 0xC8, 0x4D, 0x11,
    0xF8, 0x4C, 0x01, 0xD0] ++ bytes_l10a410_21

theorem code_l10a410_20 : ∀ x ∈ codeRange 0x10aae7 bytes_l10a410_20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xaae7 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_21

def b_l10a410_19 : Block Op Label signature Reg.count 851 :=
  .letOp (n := 851) (.out 0x10aa8a (movR64Imm64Effect 0x10aa8a 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 852) (.exec 0x10aa8a (fun s => s.RIP = 0x10aa8a) (movR64Imm64Effect 0x10aa8a 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 853) (.out 0x10aa94 (andR64R64Effect 0x10aa94 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[849, 851]
    (.letOp (n := 854) (.exec 0x10aa94 (fun s => s.RIP = 0x10aa94) (andR64R64Effect 0x10aa94 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[849, 851]
    (.letOp (n := 855) (.out 0x10aa97 (orR64R64Effect 0x10aa97 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[853, 809]
    (.letOp (n := 856) (.exec 0x10aa97 (fun s => s.RIP = 0x10aa97) (orR64R64Effect 0x10aa97 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[853, 809]
    (.letOp (n := 857) (.out 0x10aa9a (movR64Imm64Effect 0x10aa9a 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 858) (.exec 0x10aa9a (fun s => s.RIP = 0x10aa9a) (movR64Imm64Effect 0x10aa9a 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 859) (.out 0x10aaa4 (mulR64Effect 0x10aaa4 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[857, 855]
    (.letOp (n := 860) (.out 0x10aaa4 (mulR64Effect 0x10aaa4 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[857, 855]
    (.letOp (n := 861) (.exec 0x10aaa4 (fun s => s.RIP = 0x10aaa4) (mulR64Effect 0x10aaa4 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[857, 855]
    (.letOp (n := 862) (.out 0x10aaa7 (addR64M64Effect 0x10aaa7 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[859, 65]
    (.letOp (n := 863) (.out 0x10aaa7 (addR64M64Effect 0x10aaa7 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[859, 65]
    (.letOp (n := 864) (.exec 0x10aaa7 (LoadPre 0x10aaa7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10aaa7 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10aaa7 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[859, 65]
    (.letOp (n := 865) (.out 0x10aaac (atFlags StatusFlags.CF (adcR64R64Effect 0x10aaac 5 2)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[785, 860, 863]
    (.letOp (n := 866) (.exec 0x10aaac (fun s => s.RIP = 0x10aaac) (atFlags StatusFlags.CF (adcR64R64Effect 0x10aaac 5 2)) (Reg.operands [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[785, 860, 863]
    (.letOp (n := 867) (.out 0x10aaaf (shldR64R64Effect 0x10aaaf 5 5 0 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[865, 862]
    (.letOp (n := 868) (.exec 0x10aaaf (fun s => s.RIP = 0x10aaaf) (shldR64R64Effect 0x10aaaf 5 5 0 12) (Reg.operands [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[865, 862]
    (.letOp (n := 869) (.out 0x10aab4 (movR64R64Effect 0x10aab4 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[862]
    (.letOp (n := 870) (.exec 0x10aab4 (fun s => s.RIP = 0x10aab4) (movR64R64Effect 0x10aab4 8 0) (Reg.operands [.gpr 0] [])) #v[862]
    (.letOp (n := 871) (.out 0x10aab7 (movR64R64Effect 0x10aab7 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[820]
    (.letOp (n := 872) (.exec 0x10aab7 (fun s => s.RIP = 0x10aab7) (movR64R64Effect 0x10aab7 0 1) (Reg.operands [.gpr 1] [])) #v[820]
    (.letOp (n := 873) (.out 0x10aaba (mulR64Effect 0x10aaba 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[780, 871]
    (.letOp (n := 874) (.out 0x10aaba (mulR64Effect 0x10aaba 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[780, 871]
    (.letOp (n := 875) (.exec 0x10aaba (fun s => s.RIP = 0x10aaba) (mulR64Effect 0x10aaba 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[780, 871]
    (.letOp (n := 876) (.exec 0x10aabd (StorePre 0x10aabd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10aabd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10aabd 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[874, 65]
    (.letOp (n := 877) (.exec 0x10aac2 (StorePre 0x10aac2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10aac2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10aac2 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[873, 65]
    (.letOp (n := 878) (.out 0x10aac7 (movR64M64Effect 0x10aac7 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 879) (.exec 0x10aac7 (LoadPre 0x10aac7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10aac7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10aac7 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 880) (.out 0x10aacb (movR64M64Effect 0x10aacb 7 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 881) (.exec 0x10aacb (LoadPre 0x10aacb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10aacb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10aacb 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 882) (.out 0x10aad3 (mulR64Effect 0x10aad3 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[880, 878]
    (.letOp (n := 883) (.out 0x10aad3 (mulR64Effect 0x10aad3 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[880, 878]
    (.letOp (n := 884) (.exec 0x10aad3 (fun s => s.RIP = 0x10aad3) (mulR64Effect 0x10aad3 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[880, 878]
    (.letOp (n := 885) (.out 0x10aad6 (movR64R64Effect 0x10aad6 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[883]
    (.letOp (n := 886) (.exec 0x10aad6 (fun s => s.RIP = 0x10aad6) (movR64R64Effect 0x10aad6 9 2) (Reg.operands [.gpr 2] [])) #v[883]
    (.letOp (n := 887) (.out 0x10aad9 (movR64R64Effect 0x10aad9 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[882]
    (.letOp (n := 888) (.exec 0x10aad9 (fun s => s.RIP = 0x10aad9) (movR64R64Effect 0x10aad9 14 0) (Reg.operands [.gpr 0] [])) #v[882]
    (.letOp (n := 889) (.out 0x10aadc (movR64M64Effect 0x10aadc 3 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 890) (.exec 0x10aadc (LoadPre 0x10aadc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10aadc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10aadc 3 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 891) (.out 0x10aae4 (movR64R64Effect 0x10aae4 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[889]
    (.letOp (n := 892) (.exec 0x10aae4 (fun s => s.RIP = 0x10aae4) (movR64R64Effect 0x10aae4 0 3) (Reg.operands [.gpr 3] [])) #v[889]
    (b_l10a410_20))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_19 : List UInt8 :=
  [0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x4C, 0x09, 0xE0,
    0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x03, 0x44,
    0x24, 0x18, 0x48, 0x11, 0xD5, 0x48, 0x0F, 0xA4, 0xC5, 0x0C, 0x49, 0x89, 0xC0, 0x48, 0x89, 0xC8,
    0x48, 0xF7, 0xE7, 0x48, 0x89, 0x54, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x04,
    0x24, 0x48, 0x8B, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xD1, 0x49,
    0x89, 0xC6, 0x48, 0x8B, 0x9C, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x89, 0xD8] ++ bytes_l10a410_20

theorem code_l10a410_19 : ∀ x ∈ codeRange 0x10aa8a bytes_l10a410_19, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xaa8a 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_20

def b_l10a410_18 : Block Op Label signature Reg.count 805 :=
  .letOp (n := 805) (.out 0x10aa40 (movR64R64Effect 0x10aa40 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[802]
    (.letOp (n := 806) (.exec 0x10aa40 (fun s => s.RIP = 0x10aa40) (movR64R64Effect 0x10aa40 6 0) (Reg.operands [.gpr 0] [])) #v[802]
    (.letOp (n := 807) (.out 0x10aa43 (movR64R64Effect 0x10aa43 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[803]
    (.letOp (n := 808) (.exec 0x10aa43 (fun s => s.RIP = 0x10aa43) (movR64R64Effect 0x10aa43 14 2) (Reg.operands [.gpr 2] [])) #v[803]
    (.letOp (n := 809) (.out 0x10aa46 (andR32Imm8Effect 0x10aa46 4 12 0xf) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[776]
    (.letOp (n := 810) (.exec 0x10aa46 (fun s => s.RIP = 0x10aa46) (andR32Imm8Effect 0x10aa46 4 12 0xf) (Reg.operands [.gpr 12] [])) #v[776]
    (.letOp (n := 811) (.out 0x10aa4a (movR64R64Effect 0x10aa4a 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[701]
    (.letOp (n := 812) (.exec 0x10aa4a (fun s => s.RIP = 0x10aa4a) (movR64R64Effect 0x10aa4a 0 15) (Reg.operands [.gpr 15] [])) #v[701]
    (.letOp (n := 813) (.out 0x10aa4d (mulR64Effect 0x10aa4d 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[714, 811]
    (.letOp (n := 814) (.out 0x10aa4d (mulR64Effect 0x10aa4d 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[714, 811]
    (.letOp (n := 815) (.exec 0x10aa4d (fun s => s.RIP = 0x10aa4d) (mulR64Effect 0x10aa4d 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[714, 811]
    (.letOp (n := 816) (.out 0x10aa50 (movR64R64Effect 0x10aa50 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[814]
    (.letOp (n := 817) (.exec 0x10aa50 (fun s => s.RIP = 0x10aa50) (movR64R64Effect 0x10aa50 10 2) (Reg.operands [.gpr 2] [])) #v[814]
    (.letOp (n := 818) (.out 0x10aa53 (movR64R64Effect 0x10aa53 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[813]
    (.letOp (n := 819) (.exec 0x10aa53 (fun s => s.RIP = 0x10aa53) (movR64R64Effect 0x10aa53 15 0) (Reg.operands [.gpr 0] [])) #v[813]
    (.letOp (n := 820) (.out 0x10aa56 (movR64M64Effect 0x10aa56 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 821) (.exec 0x10aa56 (LoadPre 0x10aa56 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10aa56 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10aa56 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 822) (.out 0x10aa5b (movR64R64Effect 0x10aa5b 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[820]
    (.letOp (n := 823) (.exec 0x10aa5b (fun s => s.RIP = 0x10aa5b) (movR64R64Effect 0x10aa5b 0 1) (Reg.operands [.gpr 1] [])) #v[820]
    (.letOp (n := 824) (.out 0x10aa5e (mulM64Effect 0x10aa5e 8 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[822, 65]
    (.letOp (n := 825) (.out 0x10aa5e (mulM64Effect 0x10aa5e 8 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[822, 65]
    (.letOp (n := 826) (.exec 0x10aa5e (LoadPre 0x10aa5e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10aa5e + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10aa5e 8 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[822, 65]
    (.letOp (n := 827) (.out 0x10aa66 (addR64R64Effect 0x10aa66 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[824, 818]
    (.letOp (n := 828) (.out 0x10aa66 (addR64R64Effect 0x10aa66 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[824, 818]
    (.letOp (n := 829) (.exec 0x10aa66 (fun s => s.RIP = 0x10aa66) (addR64R64Effect 0x10aa66 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[824, 818]
    (.letOp (n := 830) (.out 0x10aa69 (atFlags StatusFlags.CF (adcR64R64Effect 0x10aa69 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[816, 825, 828]
    (.letOp (n := 831) (.exec 0x10aa69 (fun s => s.RIP = 0x10aa69) (atFlags StatusFlags.CF (adcR64R64Effect 0x10aa69 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[816, 825, 828]
    (.letOp (n := 832) (.out 0x10aa6c (addR64R64Effect 0x10aa6c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[827, 805]
    (.letOp (n := 833) (.out 0x10aa6c (addR64R64Effect 0x10aa6c 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[827, 805]
    (.letOp (n := 834) (.exec 0x10aa6c (fun s => s.RIP = 0x10aa6c) (addR64R64Effect 0x10aa6c 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[827, 805]
    (.letOp (n := 835) (.out 0x10aa6f (atFlags StatusFlags.CF (adcR64R64Effect 0x10aa6f 10 14)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[830, 807, 833]
    (.letOp (n := 836) (.exec 0x10aa6f (fun s => s.RIP = 0x10aa6f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10aa6f 10 14)) (Reg.operands [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[830, 807, 833]
    (.letOp (n := 837) (.out 0x10aa72 (addR64R64Effect 0x10aa72 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[832, 794]
    (.letOp (n := 838) (.out 0x10aa72 (addR64R64Effect 0x10aa72 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[832, 794]
    (.letOp (n := 839) (.exec 0x10aa72 (fun s => s.RIP = 0x10aa72) (addR64R64Effect 0x10aa72 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[832, 794]
    (.letOp (n := 840) (.out 0x10aa75 (atFlags StatusFlags.CF (adcR64M64Effect 0x10aa75 10 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 10))) #v[835, 65, 838]
    (.letOp (n := 841) (.exec 0x10aa75 (LoadPre 0x10aa75 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10aa75 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10aa75 10 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[835, 65, 838]
    (.letOp (n := 842) (.out 0x10aa7a (addR64R64Effect 0x10aa7a 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[837, 774]
    (.letOp (n := 843) (.out 0x10aa7a (addR64R64Effect 0x10aa7a 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[837, 774]
    (.letOp (n := 844) (.exec 0x10aa7a (fun s => s.RIP = 0x10aa7a) (addR64R64Effect 0x10aa7a 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[837, 774]
    (.letOp (n := 845) (.out 0x10aa7d (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10aa7d 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[840, 843]
    (.letOp (n := 846) (.exec 0x10aa7d (fun s => s.RIP = 0x10aa7d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10aa7d 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[840, 843]
    (.letOp (n := 847) (.out 0x10aa81 (shldR64R64Effect 0x10aa81 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[845, 842]
    (.letOp (n := 848) (.exec 0x10aa81 (fun s => s.RIP = 0x10aa81) (shldR64R64Effect 0x10aa81 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[845, 842]
    (.letOp (n := 849) (.out 0x10aa86 (shlR64Effect 0x10aa86 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[842]
    (.letOp (n := 850) (.exec 0x10aa86 (fun s => s.RIP = 0x10aa86) (shlR64Effect 0x10aa86 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[842]
    (b_l10a410_19))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_18 : List UInt8 :=
  [0x48, 0x89, 0xC6, 0x49, 0x89, 0xD6, 0x41, 0x83, 0xE4, 0x0F, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0xE3,
    0x49, 0x89, 0xD2, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0xC8, 0x48, 0xF7,
    0xA4, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xF8, 0x49, 0x11, 0xD2, 0x48, 0x01, 0xF0, 0x4D,
    0x11, 0xF2, 0x4C, 0x01, 0xC0, 0x4C, 0x13, 0x54, 0x24, 0x08, 0x4C, 0x01, 0xC8, 0x49, 0x83, 0xD2,
    0x00, 0x49, 0x0F, 0xA4, 0xC2, 0x0C, 0x48, 0xC1, 0xE0, 0x04] ++ bytes_l10a410_19

theorem code_l10a410_18 : ∀ x ∈ codeRange 0x10aa40 bytes_l10a410_18, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xaa40 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_19

def b_l10a410_17 : Block Op Label signature Reg.count 764 :=
  .letOp (n := 764) (.out 0x10a9f1 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a9f1 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[759, 739, 762]
    (.letOp (n := 765) (.exec 0x10a9f1 (fun s => s.RIP = 0x10a9f1) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a9f1 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[759, 739, 762]
    (.letOp (n := 766) (.out 0x10a9f4 (movR64R64Effect 0x10a9f4 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[761]
    (.letOp (n := 767) (.exec 0x10a9f4 (fun s => s.RIP = 0x10a9f4) (movR64R64Effect 0x10a9f4 12 0) (Reg.operands [.gpr 0] [])) #v[761]
    (.letOp (n := 768) (.out 0x10a9f7 (addR64R64Effect 0x10a9f7 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[766, 682]
    (.letOp (n := 769) (.out 0x10a9f7 (addR64R64Effect 0x10a9f7 12 7) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 7] []) (.flag .CF)) #v[766, 682]
    (.letOp (n := 770) (.exec 0x10a9f7 (fun s => s.RIP = 0x10a9f7) (addR64R64Effect 0x10a9f7 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[766, 682]
    (.letOp (n := 771) (.exec 0x10a9fa (StorePre 0x10a9fa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10a9fa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a9fa 12 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[768, 65]
    (.letOp (n := 772) (.out 0x10aa02 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10aa02 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[764, 769]
    (.letOp (n := 773) (.exec 0x10aa02 (fun s => s.RIP = 0x10aa02) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10aa02 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[764, 769]
    (.letOp (n := 774) (.out 0x10aa06 (shldR64R64Effect 0x10aa06 5 9 12 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[772, 768]
    (.letOp (n := 775) (.exec 0x10aa06 (fun s => s.RIP = 0x10aa06) (shldR64R64Effect 0x10aa06 5 9 12 12) (Reg.operands [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[772, 768]
    (.letOp (n := 776) (.out 0x10aa0b (shrR64Effect 0x10aa0b 4 12 48) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[768]
    (.letOp (n := 777) (.exec 0x10aa0b (fun s => s.RIP = 0x10aa0b) (shrR64Effect 0x10aa0b 4 12 48) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[768]
    (.letOp (n := 778) (.out 0x10aa0f (movR64R64Effect 0x10aa0f 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[723]
    (.letOp (n := 779) (.exec 0x10aa0f (fun s => s.RIP = 0x10aa0f) (movR64R64Effect 0x10aa0f 0 6) (Reg.operands [.gpr 6] [])) #v[723]
    (.letOp (n := 780) (.out 0x10aa12 (movR64M64Effect 0x10aa12 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 781) (.exec 0x10aa12 (LoadPre 0x10aa12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10aa12 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10aa12 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 782) (.out 0x10aa17 (mulR64Effect 0x10aa17 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[780, 778]
    (.letOp (n := 783) (.out 0x10aa17 (mulR64Effect 0x10aa17 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[780, 778]
    (.letOp (n := 784) (.exec 0x10aa17 (fun s => s.RIP = 0x10aa17) (mulR64Effect 0x10aa17 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[780, 778]
    (.letOp (n := 785) (.out 0x10aa1a (movR64R64Effect 0x10aa1a 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[783]
    (.letOp (n := 786) (.exec 0x10aa1a (fun s => s.RIP = 0x10aa1a) (movR64R64Effect 0x10aa1a 5 2) (Reg.operands [.gpr 2] [])) #v[783]
    (.letOp (n := 787) (.exec 0x10aa1d (StorePre 0x10aa1d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10aa1d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10aa1d 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[782, 65]
    (.letOp (n := 788) (.out 0x10aa22 (movR64R64Effect 0x10aa22 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[630]
    (.letOp (n := 789) (.exec 0x10aa22 (fun s => s.RIP = 0x10aa22) (movR64R64Effect 0x10aa22 0 11) (Reg.operands [.gpr 11] [])) #v[630]
    (.letOp (n := 790) (.out 0x10aa25 (mulR64Effect 0x10aa25 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[694, 788]
    (.letOp (n := 791) (.out 0x10aa25 (mulR64Effect 0x10aa25 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[694, 788]
    (.letOp (n := 792) (.exec 0x10aa25 (fun s => s.RIP = 0x10aa25) (mulR64Effect 0x10aa25 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[694, 788]
    (.letOp (n := 793) (.exec 0x10aa28 (StorePre 0x10aa28 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10aa28 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10aa28 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[791, 65]
    (.letOp (n := 794) (.out 0x10aa2d (movR64R64Effect 0x10aa2d 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[790]
    (.letOp (n := 795) (.exec 0x10aa2d (fun s => s.RIP = 0x10aa2d) (movR64R64Effect 0x10aa2d 8 0) (Reg.operands [.gpr 0] [])) #v[790]
    (.letOp (n := 796) (.out 0x10aa30 (movR64M64Effect 0x10aa30 13 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 797) (.exec 0x10aa30 (LoadPre 0x10aa30 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10aa30 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10aa30 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 798) (.out 0x10aa35 (movR64R64Effect 0x10aa35 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[796]
    (.letOp (n := 799) (.exec 0x10aa35 (fun s => s.RIP = 0x10aa35) (movR64R64Effect 0x10aa35 0 13) (Reg.operands [.gpr 13] [])) #v[796]
    (.letOp (n := 800) (.out 0x10aa38 (movR64M64Effect 0x10aa38 11 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 801) (.exec 0x10aa38 (LoadPre 0x10aa38 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10aa38 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10aa38 11 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 802) (.out 0x10aa3d (mulR64Effect 0x10aa3d 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[800, 798]
    (.letOp (n := 803) (.out 0x10aa3d (mulR64Effect 0x10aa3d 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[800, 798]
    (.letOp (n := 804) (.exec 0x10aa3d (fun s => s.RIP = 0x10aa3d) (mulR64Effect 0x10aa3d 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[800, 798]
    (b_l10a410_18)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_17 : List UInt8 :=
  [0x49, 0x11, 0xD1, 0x49, 0x89, 0xC4, 0x49, 0x01, 0xFC, 0x4C, 0x89, 0xA4, 0x24, 0x38, 0x01, 0x00,
    0x00, 0x49, 0x83, 0xD1, 0x00, 0x4D, 0x0F, 0xA4, 0xE1, 0x0C, 0x49, 0xC1, 0xEC, 0x30, 0x48, 0x89,
    0xF0, 0x48, 0x8B, 0x7C, 0x24, 0x50, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD5, 0x48, 0x89, 0x44, 0x24,
    0x18, 0x4C, 0x89, 0xD8, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0x54, 0x24, 0x08, 0x49, 0x89, 0xC0, 0x4C,
    0x8B, 0x6C, 0x24, 0x38, 0x4C, 0x89, 0xE8, 0x4C, 0x8B, 0x5C, 0x24, 0x28, 0x49, 0xF7, 0xE3] ++ bytes_l10a410_18

theorem code_l10a410_17 : ∀ x ∈ codeRange 0x10a9f1 bytes_l10a410_17, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa9f1 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_18

def b_l10a410_16 : Block Op Label signature Reg.count 716 :=
  .letOp (n := 716) (.out 0x10a9a2 (mulR64Effect 0x10a9a2 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[714, 712]
    (.letOp (n := 717) (.out 0x10a9a2 (mulR64Effect 0x10a9a2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[714, 712]
    (.letOp (n := 718) (.exec 0x10a9a2 (fun s => s.RIP = 0x10a9a2) (mulR64Effect 0x10a9a2 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[714, 712]
    (.letOp (n := 719) (.out 0x10a9a5 (movR64R64Effect 0x10a9a5 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[717]
    (.letOp (n := 720) (.exec 0x10a9a5 (fun s => s.RIP = 0x10a9a5) (movR64R64Effect 0x10a9a5 13 2) (Reg.operands [.gpr 2] [])) #v[717]
    (.letOp (n := 721) (.out 0x10a9a8 (movR64R64Effect 0x10a9a8 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[716]
    (.letOp (n := 722) (.exec 0x10a9a8 (fun s => s.RIP = 0x10a9a8) (movR64R64Effect 0x10a9a8 5 0) (Reg.operands [.gpr 0] [])) #v[716]
    (.letOp (n := 723) (.out 0x10a9ab (movR64M64Effect 0x10a9ab 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 724) (.exec 0x10a9ab (LoadPre 0x10a9ab (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a9ab + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a9ab 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 725) (.out 0x10a9af (movR64R64Effect 0x10a9af 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[723]
    (.letOp (n := 726) (.exec 0x10a9af (fun s => s.RIP = 0x10a9af) (movR64R64Effect 0x10a9af 0 6) (Reg.operands [.gpr 6] [])) #v[723]
    (.letOp (n := 727) (.out 0x10a9b2 (mulR64Effect 0x10a9b2 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[637, 725]
    (.letOp (n := 728) (.out 0x10a9b2 (mulR64Effect 0x10a9b2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[637, 725]
    (.letOp (n := 729) (.exec 0x10a9b2 (fun s => s.RIP = 0x10a9b2) (mulR64Effect 0x10a9b2 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[637, 725]
    (.letOp (n := 730) (.out 0x10a9b5 (movR64R64Effect 0x10a9b5 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[728]
    (.letOp (n := 731) (.exec 0x10a9b5 (fun s => s.RIP = 0x10a9b5) (movR64R64Effect 0x10a9b5 9 2) (Reg.operands [.gpr 2] [])) #v[728]
    (.letOp (n := 732) (.out 0x10a9b8 (movR64R64Effect 0x10a9b8 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[727]
    (.letOp (n := 733) (.exec 0x10a9b8 (fun s => s.RIP = 0x10a9b8) (movR64R64Effect 0x10a9b8 1 0) (Reg.operands [.gpr 0] [])) #v[727]
    (.letOp (n := 734) (.out 0x10a9bb (movR64R64Effect 0x10a9bb 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[680]
    (.letOp (n := 735) (.exec 0x10a9bb (fun s => s.RIP = 0x10a9bb) (movR64R64Effect 0x10a9bb 0 8) (Reg.operands [.gpr 8] [])) #v[680]
    (.letOp (n := 736) (.out 0x10a9be (movR64Imm64Effect 0x10a9be 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 737) (.exec 0x10a9be (fun s => s.RIP = 0x10a9be) (movR64Imm64Effect 0x10a9be 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 738) (.out 0x10a9c8 (mulR64Effect 0x10a9c8 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[736, 734]
    (.letOp (n := 739) (.out 0x10a9c8 (mulR64Effect 0x10a9c8 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[736, 734]
    (.letOp (n := 740) (.exec 0x10a9c8 (fun s => s.RIP = 0x10a9c8) (mulR64Effect 0x10a9c8 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[736, 734]
    (.letOp (n := 741) (.out 0x10a9cb (addR64R64Effect 0x10a9cb 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[732, 721]
    (.letOp (n := 742) (.out 0x10a9cb (addR64R64Effect 0x10a9cb 1 5) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 5] []) (.flag .CF)) #v[732, 721]
    (.letOp (n := 743) (.exec 0x10a9cb (fun s => s.RIP = 0x10a9cb) (addR64R64Effect 0x10a9cb 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[732, 721]
    (.letOp (n := 744) (.out 0x10a9ce (atFlags StatusFlags.CF (adcR64R64Effect 0x10a9ce 9 13)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[730, 719, 742]
    (.letOp (n := 745) (.exec 0x10a9ce (fun s => s.RIP = 0x10a9ce) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a9ce 9 13)) (Reg.operands [.gpr 9, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[730, 719, 742]
    (.letOp (n := 746) (.out 0x10a9d1 (addR64R64Effect 0x10a9d1 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[741, 710]
    (.letOp (n := 747) (.out 0x10a9d1 (addR64R64Effect 0x10a9d1 1 12) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 12] []) (.flag .CF)) #v[741, 710]
    (.letOp (n := 748) (.exec 0x10a9d1 (fun s => s.RIP = 0x10a9d1) (addR64R64Effect 0x10a9d1 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[741, 710]
    (.letOp (n := 749) (.out 0x10a9d4 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a9d4 9 14)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[744, 708, 747]
    (.letOp (n := 750) (.exec 0x10a9d4 (fun s => s.RIP = 0x10a9d4) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a9d4 9 14)) (Reg.operands [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[744, 708, 747]
    (.letOp (n := 751) (.out 0x10a9d7 (addR64M64Effect 0x10a9d7 1 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[746, 65]
    (.letOp (n := 752) (.out 0x10a9d7 (addR64M64Effect 0x10a9d7 1 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 4] []) (.flag .CF)) #v[746, 65]
    (.letOp (n := 753) (.exec 0x10a9d7 (LoadPre 0x10a9d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10a9d7 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10a9d7 1 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[746, 65]
    (.letOp (n := 754) (.out 0x10a9df (atFlags StatusFlags.CF (adcR64M64Effect 0x10a9df 9 (.sib 4 none 0 (.d8 0x40)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[749, 65, 752]
    (.letOp (n := 755) (.exec 0x10a9df (LoadPre 0x10a9df (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10a9df + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10a9df 9 (.sib 4 none 0 (.d8 0x40)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[749, 65, 752]
    (.letOp (n := 756) (.out 0x10a9e4 (addR64M64Effect 0x10a9e4 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[751, 65]
    (.letOp (n := 757) (.out 0x10a9e4 (addR64M64Effect 0x10a9e4 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 4] []) (.flag .CF)) #v[751, 65]
    (.letOp (n := 758) (.exec 0x10a9e4 (LoadPre 0x10a9e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a9e4 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10a9e4 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[751, 65]
    (.letOp (n := 759) (.out 0x10a9e9 (atFlags StatusFlags.CF (adcR64M64Effect 0x10a9e9 9 (.sib 4 none 0 (.d8 0x18)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[754, 65, 757]
    (.letOp (n := 760) (.exec 0x10a9e9 (LoadPre 0x10a9e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10a9e9 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10a9e9 9 (.sib 4 none 0 (.d8 0x18)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[754, 65, 757]
    (.letOp (n := 761) (.out 0x10a9ee (addR64R64Effect 0x10a9ee 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[738, 756]
    (.letOp (n := 762) (.out 0x10a9ee (addR64R64Effect 0x10a9ee 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[738, 756]
    (.letOp (n := 763) (.exec 0x10a9ee (fun s => s.RIP = 0x10a9ee) (addR64R64Effect 0x10a9ee 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[738, 756]
    (b_l10a410_17))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_16 : List UInt8 :=
  [0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD5, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0x34, 0x24, 0x48, 0x89, 0xF0,
    0x49, 0xF7, 0xE1, 0x49, 0x89, 0xD1, 0x48, 0x89, 0xC1, 0x4C, 0x89, 0xC0, 0x48, 0xBA, 0x10, 0x3D,
    0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x01, 0xE9, 0x4D, 0x11, 0xE9, 0x4C,
    0x01, 0xE1, 0x4D, 0x11, 0xF1, 0x48, 0x03, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x4C,
    0x24, 0x40, 0x48, 0x03, 0x4C, 0x24, 0x08, 0x4C, 0x13, 0x4C, 0x24, 0x18, 0x48, 0x01, 0xC8] ++ bytes_l10a410_17

theorem code_l10a410_16 : ∀ x ∈ codeRange 0x10a9a2 bytes_l10a410_16, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa9a2 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_17

def b_l10a410_15 : Block Op Label signature Reg.count 678 :=
  .letOp (n := 678) (.out 0x10a942 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a942 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[672, 654, 675]
    (.letOp (n := 679) (.exec 0x10a942 (fun s => s.RIP = 0x10a942) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a942 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[672, 654, 675]
    (.letOp (n := 680) (.out 0x10a945 (shldR64R64Effect 0x10a945 5 8 13 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[642, 640]
    (.letOp (n := 681) (.exec 0x10a945 (fun s => s.RIP = 0x10a945) (shldR64R64Effect 0x10a945 5 8 13 12) (Reg.operands [.gpr 8, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[642, 640]
    (.letOp (n := 682) (.out 0x10a94a (shldR64R64Effect 0x10a94a 5 7 0 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[678, 674]
    (.letOp (n := 683) (.exec 0x10a94a (fun s => s.RIP = 0x10a94a) (shldR64R64Effect 0x10a94a 5 7 0 12) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[678, 674]
    (.letOp (n := 684) (.exec 0x10a94f (StorePre 0x10a94f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10a94f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a94f 11 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[630, 65]
    (.letOp (n := 685) (.out 0x10a957 (movR64R64Effect 0x10a957 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[630]
    (.letOp (n := 686) (.exec 0x10a957 (fun s => s.RIP = 0x10a957) (movR64R64Effect 0x10a957 0 11) (Reg.operands [.gpr 11] [])) #v[630]
    (.letOp (n := 687) (.out 0x10a95a (mulR64Effect 0x10a95a 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[572, 685]
    (.letOp (n := 688) (.out 0x10a95a (mulR64Effect 0x10a95a 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[572, 685]
    (.letOp (n := 689) (.exec 0x10a95a (fun s => s.RIP = 0x10a95a) (mulR64Effect 0x10a95a 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[572, 685]
    (.letOp (n := 690) (.exec 0x10a95d (StorePre 0x10a95d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10a95d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a95d 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[688, 65]
    (.letOp (n := 691) (.exec 0x10a962 (StorePre 0x10a962 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a962 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a962 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[687, 65]
    (.letOp (n := 692) (.out 0x10a967 (movR64M64Effect 0x10a967 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 693) (.exec 0x10a967 (LoadPre 0x10a967 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10a967 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a967 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 694) (.out 0x10a96c (movR64M64Effect 0x10a96c 10 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 695) (.exec 0x10a96c (LoadPre 0x10a96c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10a96c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a96c 10 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 696) (.out 0x10a974 (mulR64Effect 0x10a974 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[694, 692]
    (.letOp (n := 697) (.out 0x10a974 (mulR64Effect 0x10a974 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[694, 692]
    (.letOp (n := 698) (.exec 0x10a974 (fun s => s.RIP = 0x10a974) (mulR64Effect 0x10a974 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[694, 692]
    (.letOp (n := 699) (.exec 0x10a977 (StorePre 0x10a977 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10a977 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a977 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[697, 65]
    (.letOp (n := 700) (.exec 0x10a97c (StorePre 0x10a97c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10a97c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a97c 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[696, 65]
    (.letOp (n := 701) (.out 0x10a984 (movR64M64Effect 0x10a984 15 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 702) (.exec 0x10a984 (LoadPre 0x10a984 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10a984 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a984 15 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 703) (.out 0x10a989 (movR64R64Effect 0x10a989 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[701]
    (.letOp (n := 704) (.exec 0x10a989 (fun s => s.RIP = 0x10a989) (movR64R64Effect 0x10a989 0 15) (Reg.operands [.gpr 15] [])) #v[701]
    (.letOp (n := 705) (.out 0x10a98c (mulR64Effect 0x10a98c 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[596, 703]
    (.letOp (n := 706) (.out 0x10a98c (mulR64Effect 0x10a98c 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[596, 703]
    (.letOp (n := 707) (.exec 0x10a98c (fun s => s.RIP = 0x10a98c) (mulR64Effect 0x10a98c 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[596, 703]
    (.letOp (n := 708) (.out 0x10a98f (movR64R64Effect 0x10a98f 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[706]
    (.letOp (n := 709) (.exec 0x10a98f (fun s => s.RIP = 0x10a98f) (movR64R64Effect 0x10a98f 14 2) (Reg.operands [.gpr 2] [])) #v[706]
    (.letOp (n := 710) (.out 0x10a992 (movR64R64Effect 0x10a992 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[705]
    (.letOp (n := 711) (.exec 0x10a992 (fun s => s.RIP = 0x10a992) (movR64R64Effect 0x10a992 12 0) (Reg.operands [.gpr 0] [])) #v[705]
    (.letOp (n := 712) (.out 0x10a995 (movR64M64Effect 0x10a995 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 713) (.exec 0x10a995 (LoadPre 0x10a995 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a995 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a995 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 714) (.out 0x10a99a (movR64M64Effect 0x10a99a 3 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 715) (.exec 0x10a99a (LoadPre 0x10a99a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10a99a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a99a 3 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_16))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_15 : List UInt8 :=
  [0x48, 0x11, 0xD7, 0x4D, 0x0F, 0xA4, 0xE8, 0x0C, 0x48, 0x0F, 0xA4, 0xC7, 0x0C, 0x4C, 0x89, 0x9C,
    0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xD8, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0x54, 0x24, 0x18,
    0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x4C, 0x8B, 0x94, 0x24, 0xB0, 0x00,
    0x00, 0x00, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0x54, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0xE8, 0x00,
    0x00, 0x00, 0x4C, 0x8B, 0x7C, 0x24, 0x78, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD6,
    0x49, 0x89, 0xC4, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00] ++ bytes_l10a410_16

theorem code_l10a410_15 : ∀ x ∈ codeRange 0x10a942 bytes_l10a410_15, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa942 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_16

def b_l10a410_14 : Block Op Label signature Reg.count 637 :=
  .letOp (n := 637) (.out 0x10a8df (movR64R64Effect 0x10a8df 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[628]
    (.letOp (n := 638) (.exec 0x10a8df (fun s => s.RIP = 0x10a8df) (movR64R64Effect 0x10a8df 9 8) (Reg.operands [.gpr 8] [])) #v[628]
    (.letOp (n := 639) (.exec 0x10a8e2 (StorePre 0x10a8e2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10a8e2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a8e2 8 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[628, 65]
    (.letOp (n := 640) (.out 0x10a8ea (movR64R64Effect 0x10a8ea 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[634]
    (.letOp (n := 641) (.exec 0x10a8ea (fun s => s.RIP = 0x10a8ea) (movR64R64Effect 0x10a8ea 13 0) (Reg.operands [.gpr 0] [])) #v[634]
    (.letOp (n := 642) (.out 0x10a8ed (movR64R64Effect 0x10a8ed 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[635]
    (.letOp (n := 643) (.exec 0x10a8ed (fun s => s.RIP = 0x10a8ed) (movR64R64Effect 0x10a8ed 8 2) (Reg.operands [.gpr 2] [])) #v[635]
    (.letOp (n := 644) (.out 0x10a8f0 (addR64R64Effect 0x10a8f0 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[626, 568]
    (.letOp (n := 645) (.exec 0x10a8f0 (fun s => s.RIP = 0x10a8f0) (addR64R64Effect 0x10a8f0 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[626, 568]
    (.letOp (n := 646) (.exec 0x10a8f3 (StorePre 0x10a8f3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x10a8f3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a8f3 6 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[644, 65]
    (.letOp (n := 647) (.out 0x10a8fb (movR64Imm64Effect 0x10a8fb 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 648) (.exec 0x10a8fb (fun s => s.RIP = 0x10a8fb) (movR64Imm64Effect 0x10a8fb 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 649) (.out 0x10a905 (andR64R64Effect 0x10a905 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[634, 647]
    (.letOp (n := 650) (.exec 0x10a905 (fun s => s.RIP = 0x10a905) (andR64R64Effect 0x10a905 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[634, 647]
    (.letOp (n := 651) (.out 0x10a908 (movR64Imm64Effect 0x10a908 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 652) (.exec 0x10a908 (fun s => s.RIP = 0x10a908) (movR64Imm64Effect 0x10a908 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 653) (.out 0x10a912 (mulR64Effect 0x10a912 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[651, 649]
    (.letOp (n := 654) (.out 0x10a912 (mulR64Effect 0x10a912 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[651, 649]
    (.letOp (n := 655) (.exec 0x10a912 (fun s => s.RIP = 0x10a912) (mulR64Effect 0x10a912 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[651, 649]
    (.letOp (n := 656) (.out 0x10a915 (andR64R64Effect 0x10a915 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[563, 647]
    (.letOp (n := 657) (.exec 0x10a915 (fun s => s.RIP = 0x10a915) (andR64R64Effect 0x10a915 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[563, 647]
    (.letOp (n := 658) (.exec 0x10a918 (StorePre 0x10a918 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x10a918 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a918 5 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[656, 65]
    (.letOp (n := 659) (.out 0x10a920 (addR64R64Effect 0x10a920 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[618, 605]
    (.letOp (n := 660) (.out 0x10a920 (addR64R64Effect 0x10a920 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[618, 605]
    (.letOp (n := 661) (.exec 0x10a920 (fun s => s.RIP = 0x10a920) (addR64R64Effect 0x10a920 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[618, 605]
    (.letOp (n := 662) (.out 0x10a923 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a923 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[620, 607, 660]
    (.letOp (n := 663) (.exec 0x10a923 (fun s => s.RIP = 0x10a923) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a923 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[620, 607, 660]
    (.letOp (n := 664) (.out 0x10a926 (addR64M64Effect 0x10a926 14 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[659, 65]
    (.letOp (n := 665) (.out 0x10a926 (addR64M64Effect 0x10a926 14 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 4] []) (.flag .CF)) #v[659, 65]
    (.letOp (n := 666) (.exec 0x10a926 (LoadPre 0x10a926 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10a926 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10a926 14 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[659, 65]
    (.letOp (n := 667) (.out 0x10a92b (atFlags StatusFlags.CF (adcR64M64Effect 0x10a92b 7 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[662, 65, 665]
    (.letOp (n := 668) (.exec 0x10a92b (LoadPre 0x10a92b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a92b + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10a92b 7 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[662, 65, 665]
    (.letOp (n := 669) (.out 0x10a930 (addR64M64Effect 0x10a930 14 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[664, 65]
    (.letOp (n := 670) (.out 0x10a930 (addR64M64Effect 0x10a930 14 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 4] []) (.flag .CF)) #v[664, 65]
    (.letOp (n := 671) (.exec 0x10a930 (LoadPre 0x10a930 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10a930 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10a930 14 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[664, 65]
    (.letOp (n := 672) (.out 0x10a935 (atFlags StatusFlags.CF (adcR64M64Effect 0x10a935 7 (.sib 4 none 0 (.d8 0x20)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[667, 65, 670]
    (.letOp (n := 673) (.exec 0x10a935 (LoadPre 0x10a935 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10a935 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10a935 7 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[667, 65, 670]
    (.letOp (n := 674) (.out 0x10a93a (addR64R64Effect 0x10a93a 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[653, 669]
    (.letOp (n := 675) (.out 0x10a93a (addR64R64Effect 0x10a93a 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[653, 669]
    (.letOp (n := 676) (.exec 0x10a93a (fun s => s.RIP = 0x10a93a) (addR64R64Effect 0x10a93a 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[653, 669]
    (.letOp (n := 677) (.exec 0x10a93d (StorePre 0x10a93d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10a93d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a93d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[674, 65]
    (b_l10a410_15)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_14 : List UInt8 :=
  [0x4D, 0x89, 0xC1, 0x4C, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC5, 0x49, 0x89,
    0xD0, 0x48, 0x01, 0xCE, 0x48, 0x89, 0xB4, 0x24, 0x90, 0x01, 0x00, 0x00, 0x48, 0xB9, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x21, 0xCD, 0x48, 0x89, 0xAC, 0x24, 0x78, 0x01, 0x00,
    0x00, 0x4D, 0x01, 0xE6, 0x4C, 0x11, 0xFF, 0x4C, 0x03, 0x74, 0x24, 0x40, 0x48, 0x13, 0x7C, 0x24,
    0x08, 0x4C, 0x03, 0x74, 0x24, 0x18, 0x48, 0x13, 0x7C, 0x24, 0x20, 0x4C, 0x01, 0xF0, 0x48, 0x89,
    0x44, 0x24, 0x20] ++ bytes_l10a410_15

theorem code_l10a410_14 : ∀ x ∈ codeRange 0x10a8df bytes_l10a410_14, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa8df 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_15

def b_l10a410_13 : Block Op Label signature Reg.count 598 :=
  .letOp (n := 598) (.out 0x10a888 (movR64M64Effect 0x10a888 0 (.base 9 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[574]
    (.letOp (n := 599) (.exec 0x10a888 (LoadPre 0x10a888 (fun s => AddrMode.addr (.base 9 (.d8 0x30)) s (0x10a888 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a888 0 (.base 9 (.d8 0x30))) (Reg.operands [.gpr 9] [])) #v[574]
    (.letOp (n := 600) (.exec 0x10a88c (StorePre 0x10a88c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a88c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a88c 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[598, 65]
    (.letOp (n := 601) (.out 0x10a891 (mulR64Effect 0x10a891 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[596, 598]
    (.letOp (n := 602) (.out 0x10a891 (mulR64Effect 0x10a891 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[596, 598]
    (.letOp (n := 603) (.exec 0x10a891 (fun s => s.RIP = 0x10a891) (mulR64Effect 0x10a891 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[596, 598]
    (.letOp (n := 604) (.exec 0x10a894 (StorePre 0x10a894 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10a894 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a894 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[596, 65]
    (.letOp (n := 605) (.out 0x10a899 (movR64R64Effect 0x10a899 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[601]
    (.letOp (n := 606) (.exec 0x10a899 (fun s => s.RIP = 0x10a899) (movR64R64Effect 0x10a899 12 0) (Reg.operands [.gpr 0] [])) #v[601]
    (.letOp (n := 607) (.out 0x10a89c (movR64R64Effect 0x10a89c 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[602]
    (.letOp (n := 608) (.exec 0x10a89c (fun s => s.RIP = 0x10a89c) (movR64R64Effect 0x10a89c 15 2) (Reg.operands [.gpr 2] [])) #v[602]
    (.letOp (n := 609) (.out 0x10a89f (movR64M64Effect 0x10a89f 2 (.base 8 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[570]
    (.letOp (n := 610) (.exec 0x10a89f (LoadPre 0x10a89f (fun s => AddrMode.addr (.base 8 (.d8 0x40)) s (0x10a89f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a89f 2 (.base 8 (.d8 0x40))) (Reg.operands [.gpr 8] [])) #v[570]
    (.letOp (n := 611) (.exec 0x10a8a3 (StorePre 0x10a8a3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10a8a3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a8a3 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[609, 65]
    (.letOp (n := 612) (.out 0x10a8ab (movR64M64Effect 0x10a8ab 0 (.base 9 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[574]
    (.letOp (n := 613) (.exec 0x10a8ab (LoadPre 0x10a8ab (fun s => AddrMode.addr (.base 9 (.d8 0x28)) s (0x10a8ab + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a8ab 0 (.base 9 (.d8 0x28))) (Reg.operands [.gpr 9] [])) #v[574]
    (.letOp (n := 614) (.exec 0x10a8af (StorePre 0x10a8af 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a8af + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a8af 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[612, 65]
    (.letOp (n := 615) (.out 0x10a8b3 (mulR64Effect 0x10a8b3 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[609, 612]
    (.letOp (n := 616) (.out 0x10a8b3 (mulR64Effect 0x10a8b3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[609, 612]
    (.letOp (n := 617) (.exec 0x10a8b3 (fun s => s.RIP = 0x10a8b3) (mulR64Effect 0x10a8b3 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[609, 612]
    (.letOp (n := 618) (.out 0x10a8b6 (movR64R64Effect 0x10a8b6 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[615]
    (.letOp (n := 619) (.exec 0x10a8b6 (fun s => s.RIP = 0x10a8b6) (movR64R64Effect 0x10a8b6 14 0) (Reg.operands [.gpr 0] [])) #v[615]
    (.letOp (n := 620) (.out 0x10a8b9 (movR64R64Effect 0x10a8b9 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[616]
    (.letOp (n := 621) (.exec 0x10a8b9 (fun s => s.RIP = 0x10a8b9) (movR64R64Effect 0x10a8b9 7 2) (Reg.operands [.gpr 2] [])) #v[616]
    (.letOp (n := 622) (.out 0x10a8bc (movR64Imm64Effect 0x10a8bc 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 623) (.exec 0x10a8bc (fun s => s.RIP = 0x10a8bc) (movR64Imm64Effect 0x10a8bc 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 624) (.out 0x10a8c6 (movR64M64Effect 0x10a8c6 6 (.sib 4 none 0 (.d32 0x190))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 625) (.exec 0x10a8c6 (LoadPre 0x10a8c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x10a8c6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a8c6 6 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 626) (.out 0x10a8ce (andR64R64Effect 0x10a8ce 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[624, 622]
    (.letOp (n := 627) (.exec 0x10a8ce (fun s => s.RIP = 0x10a8ce) (andR64R64Effect 0x10a8ce 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[624, 622]
    (.letOp (n := 628) (.out 0x10a8d1 (movR64M64Effect 0x10a8d1 8 (.base 8 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[570]
    (.letOp (n := 629) (.exec 0x10a8d1 (LoadPre 0x10a8d1 (fun s => AddrMode.addr (.base 8 (.d8 0x48)) s (0x10a8d1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a8d1 8 (.base 8 (.d8 0x48))) (Reg.operands [.gpr 8] [])) #v[570]
    (.letOp (n := 630) (.out 0x10a8d5 (movR64M64Effect 0x10a8d5 11 (.base 9 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[574]
    (.letOp (n := 631) (.exec 0x10a8d5 (LoadPre 0x10a8d5 (fun s => AddrMode.addr (.base 9 (.d8 0x48)) s (0x10a8d5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a8d5 11 (.base 9 (.d8 0x48))) (Reg.operands [.gpr 9] [])) #v[574]
    (.letOp (n := 632) (.out 0x10a8d9 (movR64R64Effect 0x10a8d9 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[630]
    (.letOp (n := 633) (.exec 0x10a8d9 (fun s => s.RIP = 0x10a8d9) (movR64R64Effect 0x10a8d9 0 11) (Reg.operands [.gpr 11] [])) #v[630]
    (.letOp (n := 634) (.out 0x10a8dc (mulR64Effect 0x10a8dc 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[628, 632]
    (.letOp (n := 635) (.out 0x10a8dc (mulR64Effect 0x10a8dc 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[628, 632]
    (.letOp (n := 636) (.exec 0x10a8dc (fun s => s.RIP = 0x10a8dc) (mulR64Effect 0x10a8dc 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[628, 632]
    (b_l10a410_14)))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_13 : List UInt8 :=
  [0x49, 0x8B, 0x41, 0x30, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0x5C, 0x24,
    0x28, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD7, 0x49, 0x8B, 0x50, 0x40, 0x48, 0x89, 0x94, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x49, 0x8B, 0x41, 0x28, 0x48, 0x89, 0x04, 0x24, 0x48, 0xF7, 0xE2, 0x49, 0x89,
    0xC6, 0x48, 0x89, 0xD7, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x8B,
    0xB4, 0x24, 0x90, 0x01, 0x00, 0x00, 0x48, 0x21, 0xC6, 0x4D, 0x8B, 0x40, 0x48, 0x4D, 0x8B, 0x59,
    0x48, 0x4C, 0x89, 0xD8, 0x49, 0xF7, 0xE0] ++ bytes_l10a410_14

theorem code_l10a410_13 : ∀ x ∈ codeRange 0x10a888 bytes_l10a410_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa888 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_14

def b_l10a410_12 : Block Op Label signature Reg.count 563 :=
  .letOp (n := 563) (.out 0x10a82a (addR64R64Effect 0x10a82a 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 7] []) (.reg (.gpr 5))) #v[558, 542]
    (.letOp (n := 564) (.out 0x10a82a (addR64R64Effect 0x10a82a 5 7) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 7] []) (.flag .CF)) #v[558, 542]
    (.letOp (n := 565) (.exec 0x10a82a (fun s => s.RIP = 0x10a82a) (addR64R64Effect 0x10a82a 5 7) (Reg.operands [.gpr 5, .gpr 7] [])) #v[558, 542]
    (.letOp (n := 566) (.out 0x10a82d (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a82d 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[561, 564]
    (.letOp (n := 567) (.exec 0x10a82d (fun s => s.RIP = 0x10a82d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a82d 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[561, 564]
    (.letOp (n := 568) (.out 0x10a831 (shldR64R64Effect 0x10a831 5 1 5 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[566, 563]
    (.letOp (n := 569) (.exec 0x10a831 (fun s => s.RIP = 0x10a831) (shldR64R64Effect 0x10a831 5 1 5 12) (Reg.operands [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[566, 563]
    (.letOp (n := 570) (.out 0x10a836 (movR64M64Effect 0x10a836 8 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 571) (.exec 0x10a836 (LoadPre 0x10a836 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x10a836 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a836 8 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 572) (.out 0x10a83e (movR64M64Effect 0x10a83e 10 (.base 8 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[570]
    (.letOp (n := 573) (.exec 0x10a83e (LoadPre 0x10a83e (fun s => AddrMode.addr (.base 8 (.d8 0x28)) s (0x10a83e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a83e 10 (.base 8 (.d8 0x28))) (Reg.operands [.gpr 8] [])) #v[570]
    (.letOp (n := 574) (.out 0x10a842 (movR64M64Effect 0x10a842 9 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 575) (.exec 0x10a842 (LoadPre 0x10a842 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10a842 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a842 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 576) (.out 0x10a847 (movR64M64Effect 0x10a847 0 (.base 9 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[574]
    (.letOp (n := 577) (.exec 0x10a847 (LoadPre 0x10a847 (fun s => AddrMode.addr (.base 9 (.d8 0x40)) s (0x10a847 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a847 0 (.base 9 (.d8 0x40))) (Reg.operands [.gpr 9] [])) #v[574]
    (.letOp (n := 578) (.exec 0x10a84b (StorePre 0x10a84b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10a84b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a84b 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[576, 65]
    (.letOp (n := 579) (.out 0x10a850 (mulR64Effect 0x10a850 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[572, 576]
    (.letOp (n := 580) (.out 0x10a850 (mulR64Effect 0x10a850 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[572, 576]
    (.letOp (n := 581) (.exec 0x10a850 (fun s => s.RIP = 0x10a850) (mulR64Effect 0x10a850 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[572, 576]
    (.letOp (n := 582) (.exec 0x10a853 (StorePre 0x10a853 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10a853 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a853 10 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[572, 65]
    (.letOp (n := 583) (.exec 0x10a858 (StorePre 0x10a858 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10a858 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a858 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[579, 65]
    (.letOp (n := 584) (.exec 0x10a85d (StorePre 0x10a85d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10a85d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a85d 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[580, 65]
    (.letOp (n := 585) (.out 0x10a862 (movR64M64Effect 0x10a862 2 (.base 8 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[570]
    (.letOp (n := 586) (.exec 0x10a862 (LoadPre 0x10a862 (fun s => AddrMode.addr (.base 8 (.d8 0x30)) s (0x10a862 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a862 2 (.base 8 (.d8 0x30))) (Reg.operands [.gpr 8] [])) #v[570]
    (.letOp (n := 587) (.exec 0x10a866 (StorePre 0x10a866 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10a866 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a866 2 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[585, 65]
    (.letOp (n := 588) (.out 0x10a86e (movR64M64Effect 0x10a86e 0 (.base 9 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[574]
    (.letOp (n := 589) (.exec 0x10a86e (LoadPre 0x10a86e (fun s => AddrMode.addr (.base 9 (.d8 0x38)) s (0x10a86e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a86e 0 (.base 9 (.d8 0x38))) (Reg.operands [.gpr 9] [])) #v[574]
    (.letOp (n := 590) (.exec 0x10a872 (StorePre 0x10a872 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10a872 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a872 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[588, 65]
    (.letOp (n := 591) (.out 0x10a877 (mulR64Effect 0x10a877 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[585, 588]
    (.letOp (n := 592) (.out 0x10a877 (mulR64Effect 0x10a877 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[585, 588]
    (.letOp (n := 593) (.exec 0x10a877 (fun s => s.RIP = 0x10a877) (mulR64Effect 0x10a877 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[585, 588]
    (.letOp (n := 594) (.exec 0x10a87a (StorePre 0x10a87a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10a87a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a87a 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[591, 65]
    (.letOp (n := 595) (.exec 0x10a87f (StorePre 0x10a87f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a87f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a87f 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[592, 65]
    (.letOp (n := 596) (.out 0x10a884 (movR64M64Effect 0x10a884 3 (.base 8 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[570]
    (.letOp (n := 597) (.exec 0x10a884 (LoadPre 0x10a884 (fun s => AddrMode.addr (.base 8 (.d8 0x38)) s (0x10a884 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a884 3 (.base 8 (.d8 0x38))) (Reg.operands [.gpr 8] [])) #v[570]
    (b_l10a410_13)))))))))))))))))))))))))))))))))))

def bytes_l10a410_12 : List UInt8 :=
  [0x48, 0x01, 0xFD, 0x48, 0x83, 0xD1, 0x00, 0x48, 0x0F, 0xA4, 0xE9, 0x0C, 0x4C, 0x8B, 0x84, 0x24,
    0x80, 0x01, 0x00, 0x00, 0x4D, 0x8B, 0x50, 0x28, 0x4C, 0x8B, 0x4C, 0x24, 0x60, 0x49, 0x8B, 0x41,
    0x40, 0x48, 0x89, 0x44, 0x24, 0x38, 0x49, 0xF7, 0xE2, 0x4C, 0x89, 0x54, 0x24, 0x50, 0x48, 0x89,
    0x44, 0x24, 0x18, 0x48, 0x89, 0x54, 0x24, 0x20, 0x49, 0x8B, 0x50, 0x30, 0x48, 0x89, 0x94, 0x24,
    0xB0, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x41, 0x38, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0xF7, 0xE2,
    0x48, 0x89, 0x44, 0x24, 0x40, 0x48, 0x89, 0x54, 0x24, 0x08, 0x49, 0x8B, 0x58, 0x38] ++ bytes_l10a410_13

theorem code_l10a410_12 : ∀ x ∈ codeRange 0x10a82a bytes_l10a410_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa82a 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_13

def b_l10a410_11 : Block Op Label signature Reg.count 517 :=
  .letOp (n := 517) (.out 0x10a7dd (mulR64Effect 0x10a7dd 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[515, 513]
    (.letOp (n := 518) (.out 0x10a7dd (mulR64Effect 0x10a7dd 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[515, 513]
    (.letOp (n := 519) (.exec 0x10a7dd (fun s => s.RIP = 0x10a7dd) (mulR64Effect 0x10a7dd 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[515, 513]
    (.letOp (n := 520) (.out 0x10a7e0 (addR64R64Effect 0x10a7e0 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[476, 469]
    (.letOp (n := 521) (.out 0x10a7e0 (addR64R64Effect 0x10a7e0 6 14) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 14] []) (.flag .CF)) #v[476, 469]
    (.letOp (n := 522) (.exec 0x10a7e0 (fun s => s.RIP = 0x10a7e0) (addR64R64Effect 0x10a7e0 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[476, 469]
    (.letOp (n := 523) (.out 0x10a7e3 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a7e3 7 3)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[478, 467, 521]
    (.letOp (n := 524) (.exec 0x10a7e3 (fun s => s.RIP = 0x10a7e3) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a7e3 7 3)) (Reg.operands [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[478, 467, 521]
    (.letOp (n := 525) (.out 0x10a7e6 (addR64R64Effect 0x10a7e6 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[520, 460]
    (.letOp (n := 526) (.out 0x10a7e6 (addR64R64Effect 0x10a7e6 6 9) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 9] []) (.flag .CF)) #v[520, 460]
    (.letOp (n := 527) (.exec 0x10a7e6 (fun s => s.RIP = 0x10a7e6) (addR64R64Effect 0x10a7e6 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[520, 460]
    (.letOp (n := 528) (.out 0x10a7e9 (atFlags StatusFlags.CF (adcR64M64Effect 0x10a7e9 7 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[523, 65, 526]
    (.letOp (n := 529) (.exec 0x10a7e9 (LoadPre 0x10a7e9 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a7e9 + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10a7e9 7 (.sib 4 none 0 .none))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[523, 65, 526]
    (.letOp (n := 530) (.out 0x10a7ed (addR64R64Effect 0x10a7ed 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[525, 517]
    (.letOp (n := 531) (.out 0x10a7ed (addR64R64Effect 0x10a7ed 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[525, 517]
    (.letOp (n := 532) (.exec 0x10a7ed (fun s => s.RIP = 0x10a7ed) (addR64R64Effect 0x10a7ed 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[525, 517]
    (.letOp (n := 533) (.out 0x10a7f0 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a7f0 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[528, 518, 531]
    (.letOp (n := 534) (.exec 0x10a7f0 (fun s => s.RIP = 0x10a7f0) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a7f0 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[528, 518, 531]
    (.letOp (n := 535) (.out 0x10a7f3 (addR64R64Effect 0x10a7f3 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[530, 452]
    (.letOp (n := 536) (.out 0x10a7f3 (addR64R64Effect 0x10a7f3 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[530, 452]
    (.letOp (n := 537) (.exec 0x10a7f3 (fun s => s.RIP = 0x10a7f3) (addR64R64Effect 0x10a7f3 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[530, 452]
    (.letOp (n := 538) (.out 0x10a7f6 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a7f6 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[533, 536]
    (.letOp (n := 539) (.exec 0x10a7f6 (fun s => s.RIP = 0x10a7f6) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a7f6 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[533, 536]
    (.letOp (n := 540) (.out 0x10a7fa (shldR64R64Effect 0x10a7fa 5 10 15 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[509, 506]
    (.letOp (n := 541) (.exec 0x10a7fa (fun s => s.RIP = 0x10a7fa) (shldR64R64Effect 0x10a7fa 5 10 15 12) (Reg.operands [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[509, 506]
    (.letOp (n := 542) (.out 0x10a7ff (shldR64R64Effect 0x10a7ff 5 7 6 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[538, 535]
    (.letOp (n := 543) (.exec 0x10a7ff (fun s => s.RIP = 0x10a7ff) (shldR64R64Effect 0x10a7ff 5 7 6 12) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[538, 535]
    (.letOp (n := 544) (.out 0x10a804 (andR64R64Effect 0x10a804 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[535, 482]
    (.letOp (n := 545) (.exec 0x10a804 (fun s => s.RIP = 0x10a804) (andR64R64Effect 0x10a804 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[535, 482]
    (.letOp (n := 546) (.exec 0x10a807 (StorePre 0x10a807 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x10a807 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a807 6 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[544, 65]
    (.letOp (n := 547) (.out 0x10a80f (movR64R64Effect 0x10a80f 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[540]
    (.letOp (n := 548) (.exec 0x10a80f (fun s => s.RIP = 0x10a80f) (movR64R64Effect 0x10a80f 0 10) (Reg.operands [.gpr 10] [])) #v[540]
    (.letOp (n := 549) (.out 0x10a812 (mulR64Effect 0x10a812 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[515, 547]
    (.letOp (n := 550) (.out 0x10a812 (mulR64Effect 0x10a812 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[515, 547]
    (.letOp (n := 551) (.exec 0x10a812 (fun s => s.RIP = 0x10a812) (mulR64Effect 0x10a812 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[515, 547]
    (.letOp (n := 552) (.out 0x10a815 (movR64R64Effect 0x10a815 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[550]
    (.letOp (n := 553) (.exec 0x10a815 (fun s => s.RIP = 0x10a815) (movR64R64Effect 0x10a815 1 2) (Reg.operands [.gpr 2] [])) #v[550]
    (.letOp (n := 554) (.out 0x10a818 (movR64M64Effect 0x10a818 5 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 555) (.exec 0x10a818 (LoadPre 0x10a818 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x10a818 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a818 5 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 556) (.out 0x10a820 (andR64R64Effect 0x10a820 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[554, 482]
    (.letOp (n := 557) (.exec 0x10a820 (fun s => s.RIP = 0x10a820) (andR64R64Effect 0x10a820 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[554, 482]
    (.letOp (n := 558) (.out 0x10a823 (addR64R64Effect 0x10a823 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[556, 549]
    (.letOp (n := 559) (.out 0x10a823 (addR64R64Effect 0x10a823 5 0) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 0] []) (.flag .CF)) #v[556, 549]
    (.letOp (n := 560) (.exec 0x10a823 (fun s => s.RIP = 0x10a823) (addR64R64Effect 0x10a823 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[556, 549]
    (.letOp (n := 561) (.out 0x10a826 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a826 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[552, 559]
    (.letOp (n := 562) (.exec 0x10a826 (fun s => s.RIP = 0x10a826) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a826 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[552, 559]
    (b_l10a410_12))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_11 : List UInt8 :=
  [0x49, 0xF7, 0xE0, 0x4C, 0x01, 0xF6, 0x48, 0x11, 0xDF, 0x4C, 0x01, 0xCE, 0x48, 0x13, 0x3C, 0x24,
    0x48, 0x01, 0xC6, 0x48, 0x11, 0xD7, 0x48, 0x01, 0xCE, 0x48, 0x83, 0xD7, 0x00, 0x4D, 0x0F, 0xA4,
    0xFA, 0x0C, 0x48, 0x0F, 0xA4, 0xF7, 0x0C, 0x4C, 0x21, 0xEE, 0x48, 0x89, 0xB4, 0x24, 0xA0, 0x01,
    0x00, 0x00, 0x4C, 0x89, 0xD0, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0xD1, 0x48, 0x8B, 0xAC, 0x24, 0x78,
    0x01, 0x00, 0x00, 0x4C, 0x21, 0xED, 0x48, 0x01, 0xC5, 0x48, 0x83, 0xD1, 0x00] ++ bytes_l10a410_12

theorem code_l10a410_11 : ∀ x ∈ codeRange 0x10a7dd bytes_l10a410_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa7dd 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_12

def b_l10a410_10 : Block Op Label signature Reg.count 473 :=
  .letOp (n := 473) (.out 0x10a78f (mulR64Effect 0x10a78f 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[377, 471]
    (.letOp (n := 474) (.out 0x10a78f (mulR64Effect 0x10a78f 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[377, 471]
    (.letOp (n := 475) (.exec 0x10a78f (fun s => s.RIP = 0x10a78f) (mulR64Effect 0x10a78f 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[377, 471]
    (.letOp (n := 476) (.out 0x10a792 (movR64R64Effect 0x10a792 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[473]
    (.letOp (n := 477) (.exec 0x10a792 (fun s => s.RIP = 0x10a792) (movR64R64Effect 0x10a792 6 0) (Reg.operands [.gpr 0] [])) #v[473]
    (.letOp (n := 478) (.out 0x10a795 (movR64R64Effect 0x10a795 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[474]
    (.letOp (n := 479) (.exec 0x10a795 (fun s => s.RIP = 0x10a795) (movR64R64Effect 0x10a795 7 2) (Reg.operands [.gpr 2] [])) #v[474]
    (.letOp (n := 480) (.out 0x10a798 (andR64R64Effect 0x10a798 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[447, 426]
    (.letOp (n := 481) (.exec 0x10a798 (fun s => s.RIP = 0x10a798) (andR64R64Effect 0x10a798 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[447, 426]
    (.letOp (n := 482) (.out 0x10a79b (movR64R64Effect 0x10a79b 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[426]
    (.letOp (n := 483) (.exec 0x10a79b (fun s => s.RIP = 0x10a79b) (movR64R64Effect 0x10a79b 13 15) (Reg.operands [.gpr 15] [])) #v[426]
    (.letOp (n := 484) (.exec 0x10a79e (StorePre 0x10a79e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x10a79e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a79e 12 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[480, 65]
    (.letOp (n := 485) (.out 0x10a7a6 (movR64R64Effect 0x10a7a6 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[373]
    (.letOp (n := 486) (.exec 0x10a7a6 (fun s => s.RIP = 0x10a7a6) (movR64R64Effect 0x10a7a6 0 5) (Reg.operands [.gpr 5] [])) #v[373]
    (.letOp (n := 487) (.out 0x10a7a9 (mulR64Effect 0x10a7a9 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[393, 485]
    (.letOp (n := 488) (.out 0x10a7a9 (mulR64Effect 0x10a7a9 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[393, 485]
    (.letOp (n := 489) (.exec 0x10a7a9 (fun s => s.RIP = 0x10a7a9) (mulR64Effect 0x10a7a9 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[393, 485]
    (.letOp (n := 490) (.out 0x10a7ac (movR64R64Effect 0x10a7ac 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[488]
    (.letOp (n := 491) (.exec 0x10a7ac (fun s => s.RIP = 0x10a7ac) (movR64R64Effect 0x10a7ac 10 2) (Reg.operands [.gpr 2] [])) #v[488]
    (.letOp (n := 492) (.out 0x10a7af (movR64R64Effect 0x10a7af 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[487]
    (.letOp (n := 493) (.exec 0x10a7af (fun s => s.RIP = 0x10a7af) (movR64R64Effect 0x10a7af 12 0) (Reg.operands [.gpr 0] [])) #v[487]
    (.letOp (n := 494) (.out 0x10a7b2 (movR64M64Effect 0x10a7b2 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 495) (.exec 0x10a7b2 (LoadPre 0x10a7b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10a7b2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a7b2 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 496) (.out 0x10a7ba (mulR64Effect 0x10a7ba 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[307, 494]
    (.letOp (n := 497) (.out 0x10a7ba (mulR64Effect 0x10a7ba 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[307, 494]
    (.letOp (n := 498) (.exec 0x10a7ba (fun s => s.RIP = 0x10a7ba) (mulR64Effect 0x10a7ba 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[307, 494]
    (.letOp (n := 499) (.out 0x10a7bd (movR64R64Effect 0x10a7bd 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[496]
    (.letOp (n := 500) (.exec 0x10a7bd (fun s => s.RIP = 0x10a7bd) (movR64R64Effect 0x10a7bd 15 0) (Reg.operands [.gpr 0] [])) #v[496]
    (.letOp (n := 501) (.out 0x10a7c0 (addR64R64Effect 0x10a7c0 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[499, 492]
    (.letOp (n := 502) (.out 0x10a7c0 (addR64R64Effect 0x10a7c0 15 12) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 12] []) (.flag .CF)) #v[499, 492]
    (.letOp (n := 503) (.exec 0x10a7c0 (fun s => s.RIP = 0x10a7c0) (addR64R64Effect 0x10a7c0 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[499, 492]
    (.letOp (n := 504) (.out 0x10a7c3 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a7c3 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[490, 497, 502]
    (.letOp (n := 505) (.exec 0x10a7c3 (fun s => s.RIP = 0x10a7c3) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a7c3 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[490, 497, 502]
    (.letOp (n := 506) (.out 0x10a7c6 (addR64R64Effect 0x10a7c6 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[501, 424]
    (.letOp (n := 507) (.out 0x10a7c6 (addR64R64Effect 0x10a7c6 15 8) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 8] []) (.flag .CF)) #v[501, 424]
    (.letOp (n := 508) (.exec 0x10a7c6 (fun s => s.RIP = 0x10a7c6) (addR64R64Effect 0x10a7c6 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[501, 424]
    (.letOp (n := 509) (.out 0x10a7c9 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a7c9 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[504, 507]
    (.letOp (n := 510) (.exec 0x10a7c9 (fun s => s.RIP = 0x10a7c9) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a7c9 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[504, 507]
    (.letOp (n := 511) (.out 0x10a7cd (movR64R64Effect 0x10a7cd 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[506]
    (.letOp (n := 512) (.exec 0x10a7cd (fun s => s.RIP = 0x10a7cd) (movR64R64Effect 0x10a7cd 0 15) (Reg.operands [.gpr 15] [])) #v[506]
    (.letOp (n := 513) (.out 0x10a7d0 (andR64R64Effect 0x10a7d0 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[511, 482]
    (.letOp (n := 514) (.exec 0x10a7d0 (fun s => s.RIP = 0x10a7d0) (andR64R64Effect 0x10a7d0 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[511, 482]
    (.letOp (n := 515) (.out 0x10a7d3 (movR64Imm64Effect 0x10a7d3 8 0x1000003d10) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 516) (.exec 0x10a7d3 (fun s => s.RIP = 0x10a7d3) (movR64Imm64Effect 0x10a7d3 8 0x1000003d10) (Reg.operands [] [])) #v[]
    (b_l10a410_11))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_10 : List UInt8 :=
  [0x49, 0xF7, 0xE5, 0x48, 0x89, 0xC6, 0x48, 0x89, 0xD7, 0x4D, 0x21, 0xFC, 0x4D, 0x89, 0xFD, 0x4C,
    0x89, 0xA4, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD2,
    0x49, 0x89, 0xC4, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE3, 0x49, 0x89,
    0xC7, 0x4D, 0x01, 0xE7, 0x49, 0x11, 0xD2, 0x4D, 0x01, 0xC7, 0x49, 0x83, 0xD2, 0x00, 0x4C, 0x89,
    0xF8, 0x4C, 0x21, 0xE8, 0x49, 0xB8, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] ++ bytes_l10a410_11

theorem code_l10a410_10 : ∀ x ∈ codeRange 0x10a78f bytes_l10a410_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa78f 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_11

def b_l10a410_9 : Block Op Label signature Reg.count 428 :=
  .letOp (n := 428) (.out 0x10a72c (andR64R64Effect 0x10a72c 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[419, 426]
    (.letOp (n := 429) (.exec 0x10a72c (fun s => s.RIP = 0x10a72c) (andR64R64Effect 0x10a72c 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[419, 426]
    (.letOp (n := 430) (.out 0x10a72f (movR64Imm64Effect 0x10a72f 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 431) (.exec 0x10a72f (fun s => s.RIP = 0x10a72f) (movR64Imm64Effect 0x10a72f 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 432) (.out 0x10a739 (mulR64Effect 0x10a739 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[430, 428]
    (.letOp (n := 433) (.out 0x10a739 (mulR64Effect 0x10a739 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[430, 428]
    (.letOp (n := 434) (.exec 0x10a739 (fun s => s.RIP = 0x10a739) (mulR64Effect 0x10a739 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[430, 428]
    (.letOp (n := 435) (.out 0x10a73c (movR64M64Effect 0x10a73c 12 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 436) (.exec 0x10a73c (LoadPre 0x10a73c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x10a73c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a73c 12 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 437) (.out 0x10a744 (addR64M64Effect 0x10a744 12 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[435, 65]
    (.letOp (n := 438) (.out 0x10a744 (addR64M64Effect 0x10a744 12 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 4] []) (.flag .CF)) #v[435, 65]
    (.letOp (n := 439) (.exec 0x10a744 (LoadPre 0x10a744 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a744 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10a744 12 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[435, 65]
    (.letOp (n := 440) (.out 0x10a749 (atFlags StatusFlags.CF (adcR64M64Effect 0x10a749 1 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[370, 65, 438]
    (.letOp (n := 441) (.exec 0x10a749 (LoadPre 0x10a749 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a749 + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10a749 1 (.sib 4 none 0 .none))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[370, 65, 438]
    (.letOp (n := 442) (.out 0x10a74d (addR64R64Effect 0x10a74d 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[437, 432]
    (.letOp (n := 443) (.out 0x10a74d (addR64R64Effect 0x10a74d 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[437, 432]
    (.letOp (n := 444) (.exec 0x10a74d (fun s => s.RIP = 0x10a74d) (addR64R64Effect 0x10a74d 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[437, 432]
    (.letOp (n := 445) (.out 0x10a750 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a750 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[440, 433, 443]
    (.letOp (n := 446) (.exec 0x10a750 (fun s => s.RIP = 0x10a750) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a750 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[440, 433, 443]
    (.letOp (n := 447) (.out 0x10a753 (addR64R64Effect 0x10a753 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 9] []) (.reg (.gpr 12))) #v[442, 354]
    (.letOp (n := 448) (.out 0x10a753 (addR64R64Effect 0x10a753 12 9) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 9] []) (.flag .CF)) #v[442, 354]
    (.letOp (n := 449) (.exec 0x10a753 (fun s => s.RIP = 0x10a753) (addR64R64Effect 0x10a753 12 9) (Reg.operands [.gpr 12, .gpr 9] [])) #v[442, 354]
    (.letOp (n := 450) (.out 0x10a756 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a756 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[445, 448]
    (.letOp (n := 451) (.exec 0x10a756 (fun s => s.RIP = 0x10a756) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a756 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[445, 448]
    (.letOp (n := 452) (.out 0x10a75a (shldR64R64Effect 0x10a75a 5 1 12 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[450, 447]
    (.letOp (n := 453) (.exec 0x10a75a (fun s => s.RIP = 0x10a75a) (shldR64R64Effect 0x10a75a 5 1 12 12) (Reg.operands [.gpr 1, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[450, 447]
    (.letOp (n := 454) (.out 0x10a75f (movR64R64Effect 0x10a75f 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[402]
    (.letOp (n := 455) (.exec 0x10a75f (fun s => s.RIP = 0x10a75f) (movR64R64Effect 0x10a75f 0 6) (Reg.operands [.gpr 6] [])) #v[402]
    (.letOp (n := 456) (.out 0x10a762 (mulM64Effect 0x10a762 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[454, 65]
    (.letOp (n := 457) (.out 0x10a762 (mulM64Effect 0x10a762 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[454, 65]
    (.letOp (n := 458) (.exec 0x10a762 (LoadPre 0x10a762 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10a762 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10a762 8 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[454, 65]
    (.letOp (n := 459) (.exec 0x10a76a (StorePre 0x10a76a 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a76a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a76a 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[457, 65]
    (.letOp (n := 460) (.out 0x10a76e (movR64R64Effect 0x10a76e 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[456]
    (.letOp (n := 461) (.exec 0x10a76e (fun s => s.RIP = 0x10a76e) (movR64R64Effect 0x10a76e 9 0) (Reg.operands [.gpr 0] [])) #v[456]
    (.letOp (n := 462) (.out 0x10a771 (movR64M64Effect 0x10a771 0 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 463) (.exec 0x10a771 (LoadPre 0x10a771 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x10a771 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a771 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 464) (.out 0x10a779 (mulM64Effect 0x10a779 8 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[462, 65]
    (.letOp (n := 465) (.out 0x10a779 (mulM64Effect 0x10a779 8 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[462, 65]
    (.letOp (n := 466) (.exec 0x10a779 (LoadPre 0x10a779 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10a779 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10a779 8 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[462, 65]
    (.letOp (n := 467) (.out 0x10a781 (movR64R64Effect 0x10a781 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[465]
    (.letOp (n := 468) (.exec 0x10a781 (fun s => s.RIP = 0x10a781) (movR64R64Effect 0x10a781 3 2) (Reg.operands [.gpr 2] [])) #v[465]
    (.letOp (n := 469) (.out 0x10a784 (movR64R64Effect 0x10a784 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[464]
    (.letOp (n := 470) (.exec 0x10a784 (fun s => s.RIP = 0x10a784) (movR64R64Effect 0x10a784 14 0) (Reg.operands [.gpr 0] [])) #v[464]
    (.letOp (n := 471) (.out 0x10a787 (movR64M64Effect 0x10a787 0 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 472) (.exec 0x10a787 (LoadPre 0x10a787 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10a787 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a787 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_10)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_9 : List UInt8 :=
  [0x4C, 0x21, 0xF8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x4C, 0x8B, 0xA4, 0x24, 0x60, 0x01, 0x00, 0x00, 0x4C, 0x03, 0x64, 0x24, 0x10, 0x48, 0x13, 0x0C,
    0x24, 0x49, 0x01, 0xC4, 0x48, 0x11, 0xD1, 0x4D, 0x01, 0xCC, 0x48, 0x83, 0xD1, 0x00, 0x4C, 0x0F,
    0xA4, 0xE1, 0x0C, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89,
    0x14, 0x24, 0x49, 0x89, 0xC1, 0x48, 0x8B, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xA4,
    0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x84, 0x24, 0x40,
    0x01, 0x00, 0x00] ++ bytes_l10a410_10

theorem code_l10a410_9 : ∀ x ∈ codeRange 0x10a72c bytes_l10a410_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa72c 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_10

def b_l10a410_8 : Block Op Label signature Reg.count 384 :=
  .letOp (n := 384) (.out 0x10a6d0 (movR64R64Effect 0x10a6d0 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[380]
    (.letOp (n := 385) (.exec 0x10a6d0 (fun s => s.RIP = 0x10a6d0) (movR64R64Effect 0x10a6d0 14 2) (Reg.operands [.gpr 2] [])) #v[380]
    (.letOp (n := 386) (.out 0x10a6d3 (movR64Imm64Effect 0x10a6d3 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 387) (.exec 0x10a6d3 (fun s => s.RIP = 0x10a6d3) (movR64Imm64Effect 0x10a6d3 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 388) (.out 0x10a6dd (andR64R64Effect 0x10a6dd 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[356, 386]
    (.letOp (n := 389) (.exec 0x10a6dd (fun s => s.RIP = 0x10a6dd) (andR64R64Effect 0x10a6dd 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[356, 386]
    (.letOp (n := 390) (.exec 0x10a6e0 (StorePre 0x10a6e0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x10a6e0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a6e0 6 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[388, 65]
    (.letOp (n := 391) (.out 0x10a6e8 (movR64R64Effect 0x10a6e8 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[281]
    (.letOp (n := 392) (.exec 0x10a6e8 (fun s => s.RIP = 0x10a6e8) (movR64R64Effect 0x10a6e8 0 12) (Reg.operands [.gpr 12] [])) #v[281]
    (.letOp (n := 393) (.out 0x10a6eb (movR64M64Effect 0x10a6eb 10 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 394) (.exec 0x10a6eb (LoadPre 0x10a6eb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10a6eb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a6eb 10 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 395) (.out 0x10a6f3 (mulR64Effect 0x10a6f3 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[393, 391]
    (.letOp (n := 396) (.out 0x10a6f3 (mulR64Effect 0x10a6f3 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[393, 391]
    (.letOp (n := 397) (.exec 0x10a6f3 (fun s => s.RIP = 0x10a6f3) (mulR64Effect 0x10a6f3 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[393, 391]
    (.letOp (n := 398) (.out 0x10a6f6 (movR64R64Effect 0x10a6f6 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[396]
    (.letOp (n := 399) (.exec 0x10a6f6 (fun s => s.RIP = 0x10a6f6) (movR64R64Effect 0x10a6f6 8 2) (Reg.operands [.gpr 2] [])) #v[396]
    (.letOp (n := 400) (.out 0x10a6f9 (movR64R64Effect 0x10a6f9 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[395]
    (.letOp (n := 401) (.exec 0x10a6f9 (fun s => s.RIP = 0x10a6f9) (movR64R64Effect 0x10a6f9 15 0) (Reg.operands [.gpr 0] [])) #v[395]
    (.letOp (n := 402) (.out 0x10a6fc (movR64M64Effect 0x10a6fc 6 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 403) (.exec 0x10a6fc (LoadPre 0x10a6fc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10a6fc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a6fc 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 404) (.out 0x10a704 (movR64R64Effect 0x10a704 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[402]
    (.letOp (n := 405) (.exec 0x10a704 (fun s => s.RIP = 0x10a704) (movR64R64Effect 0x10a704 0 6) (Reg.operands [.gpr 6] [])) #v[402]
    (.letOp (n := 406) (.out 0x10a707 (mulR64Effect 0x10a707 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[307, 404]
    (.letOp (n := 407) (.out 0x10a707 (mulR64Effect 0x10a707 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[307, 404]
    (.letOp (n := 408) (.exec 0x10a707 (fun s => s.RIP = 0x10a707) (mulR64Effect 0x10a707 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[307, 404]
    (.letOp (n := 409) (.out 0x10a70a (addR64R64Effect 0x10a70a 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[406, 400]
    (.letOp (n := 410) (.out 0x10a70a (addR64R64Effect 0x10a70a 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[406, 400]
    (.letOp (n := 411) (.exec 0x10a70a (fun s => s.RIP = 0x10a70a) (addR64R64Effect 0x10a70a 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[406, 400]
    (.letOp (n := 412) (.out 0x10a70d (atFlags StatusFlags.CF (adcR64R64Effect 0x10a70d 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[398, 407, 410]
    (.letOp (n := 413) (.exec 0x10a70d (fun s => s.RIP = 0x10a70d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a70d 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[398, 407, 410]
    (.letOp (n := 414) (.out 0x10a710 (addR64R64Effect 0x10a710 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[409, 382]
    (.letOp (n := 415) (.out 0x10a710 (addR64R64Effect 0x10a710 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[409, 382]
    (.letOp (n := 416) (.exec 0x10a710 (fun s => s.RIP = 0x10a710) (addR64R64Effect 0x10a710 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[409, 382]
    (.letOp (n := 417) (.out 0x10a713 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a713 8 14)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[412, 384, 415]
    (.letOp (n := 418) (.exec 0x10a713 (fun s => s.RIP = 0x10a713) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a713 8 14)) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[412, 384, 415]
    (.letOp (n := 419) (.out 0x10a716 (addR64R64Effect 0x10a716 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[414, 332]
    (.letOp (n := 420) (.out 0x10a716 (addR64R64Effect 0x10a716 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[414, 332]
    (.letOp (n := 421) (.exec 0x10a716 (fun s => s.RIP = 0x10a716) (addR64R64Effect 0x10a716 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[414, 332]
    (.letOp (n := 422) (.out 0x10a719 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a719 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[417, 420]
    (.letOp (n := 423) (.exec 0x10a719 (fun s => s.RIP = 0x10a719) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a719 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[417, 420]
    (.letOp (n := 424) (.out 0x10a71d (shldR64R64Effect 0x10a71d 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[422, 419]
    (.letOp (n := 425) (.exec 0x10a71d (fun s => s.RIP = 0x10a71d) (shldR64R64Effect 0x10a71d 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[422, 419]
    (.letOp (n := 426) (.out 0x10a722 (movR64Imm64Effect 0x10a722 15 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 427) (.exec 0x10a722 (fun s => s.RIP = 0x10a722) (movR64Imm64Effect 0x10a722 15 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l10a410_9))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_8 : List UInt8 :=
  [0x49, 0x89, 0xD6, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC6,
    0x48, 0x89, 0xB4, 0x24, 0xA8, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x4C, 0x8B, 0x94, 0x24, 0xE0,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0xB4, 0x24,
    0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE3, 0x4C, 0x01, 0xF8, 0x49, 0x11, 0xD0,
    0x48, 0x01, 0xD8, 0x4D, 0x11, 0xF0, 0x48, 0x01, 0xF8, 0x49, 0x83, 0xD0, 0x00, 0x49, 0x0F, 0xA4,
    0xC0, 0x0C, 0x49, 0xBF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] ++ bytes_l10a410_9

theorem code_l10a410_8 : ∀ x ∈ codeRange 0x10a6d0 bytes_l10a410_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa6d0 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_9

def b_l10a410_7 : Block Op Label signature Reg.count 342 :=
  .letOp (n := 342) (.out 0x10a671 (movR64Imm64Effect 0x10a671 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 343) (.exec 0x10a671 (fun s => s.RIP = 0x10a671) (movR64Imm64Effect 0x10a671 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 344) (.out 0x10a67b (mulR64Effect 0x10a67b 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[342, 340]
    (.letOp (n := 345) (.out 0x10a67b (mulR64Effect 0x10a67b 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[342, 340]
    (.letOp (n := 346) (.exec 0x10a67b (fun s => s.RIP = 0x10a67b) (mulR64Effect 0x10a67b 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[342, 340]
    (.letOp (n := 347) (.out 0x10a67e (movR64R64Effect 0x10a67e 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[345]
    (.letOp (n := 348) (.exec 0x10a67e (fun s => s.RIP = 0x10a67e) (movR64R64Effect 0x10a67e 9 2) (Reg.operands [.gpr 2] [])) #v[345]
    (.letOp (n := 349) (.out 0x10a681 (addR64M64Effect 0x10a681 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[344, 65]
    (.letOp (n := 350) (.out 0x10a681 (addR64M64Effect 0x10a681 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[344, 65]
    (.letOp (n := 351) (.exec 0x10a681 (LoadPre 0x10a681 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a681 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10a681 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[344, 65]
    (.letOp (n := 352) (.out 0x10a686 (atFlags StatusFlags.CF (adcR64M64Effect 0x10a686 9 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[347, 65, 350]
    (.letOp (n := 353) (.exec 0x10a686 (LoadPre 0x10a686 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a686 + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10a686 9 (.sib 4 none 0 .none))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[347, 65, 350]
    (.letOp (n := 354) (.out 0x10a68a (shldR64R64Effect 0x10a68a 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[352, 349]
    (.letOp (n := 355) (.exec 0x10a68a (fun s => s.RIP = 0x10a68a) (shldR64R64Effect 0x10a68a 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[352, 349]
    (.letOp (n := 356) (.out 0x10a68f (movR64R64Effect 0x10a68f 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[349]
    (.letOp (n := 357) (.exec 0x10a68f (fun s => s.RIP = 0x10a68f) (movR64R64Effect 0x10a68f 6 0) (Reg.operands [.gpr 0] [])) #v[349]
    (.letOp (n := 358) (.out 0x10a692 (movR64R64Effect 0x10a692 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[303]
    (.letOp (n := 359) (.exec 0x10a692 (fun s => s.RIP = 0x10a692) (movR64R64Effect 0x10a692 0 1) (Reg.operands [.gpr 1] [])) #v[303]
    (.letOp (n := 360) (.out 0x10a695 (mulR64Effect 0x10a695 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[263, 358]
    (.letOp (n := 361) (.out 0x10a695 (mulR64Effect 0x10a695 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[263, 358]
    (.letOp (n := 362) (.exec 0x10a695 (fun s => s.RIP = 0x10a695) (mulR64Effect 0x10a695 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[263, 358]
    (.letOp (n := 363) (.exec 0x10a698 (StorePre 0x10a698 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a698 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a698 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[361, 65]
    (.letOp (n := 364) (.exec 0x10a69c (StorePre 0x10a69c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a69c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a69c 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[360, 65]
    (.letOp (n := 365) (.out 0x10a6a1 (movR64M64Effect 0x10a6a1 0 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 366) (.exec 0x10a6a1 (LoadPre 0x10a6a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10a6a1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a6a1 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 367) (.out 0x10a6a9 (mulR64Effect 0x10a6a9 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[272, 365]
    (.letOp (n := 368) (.out 0x10a6a9 (mulR64Effect 0x10a6a9 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[272, 365]
    (.letOp (n := 369) (.exec 0x10a6a9 (fun s => s.RIP = 0x10a6a9) (mulR64Effect 0x10a6a9 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[272, 365]
    (.letOp (n := 370) (.out 0x10a6ac (movR64R64Effect 0x10a6ac 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[368]
    (.letOp (n := 371) (.exec 0x10a6ac (fun s => s.RIP = 0x10a6ac) (movR64R64Effect 0x10a6ac 1 2) (Reg.operands [.gpr 2] [])) #v[368]
    (.letOp (n := 372) (.exec 0x10a6af (StorePre 0x10a6af 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x10a6af + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a6af 0 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[367, 65]
    (.letOp (n := 373) (.out 0x10a6b7 (movR64M64Effect 0x10a6b7 5 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 374) (.exec 0x10a6b7 (LoadPre 0x10a6b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10a6b7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a6b7 5 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 375) (.out 0x10a6bf (movR64R64Effect 0x10a6bf 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[373]
    (.letOp (n := 376) (.exec 0x10a6bf (fun s => s.RIP = 0x10a6bf) (movR64R64Effect 0x10a6bf 0 5) (Reg.operands [.gpr 5] [])) #v[373]
    (.letOp (n := 377) (.out 0x10a6c2 (movR64M64Effect 0x10a6c2 13 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 378) (.exec 0x10a6c2 (LoadPre 0x10a6c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10a6c2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a6c2 13 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 379) (.out 0x10a6ca (mulR64Effect 0x10a6ca 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[377, 375]
    (.letOp (n := 380) (.out 0x10a6ca (mulR64Effect 0x10a6ca 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[377, 375]
    (.letOp (n := 381) (.exec 0x10a6ca (fun s => s.RIP = 0x10a6ca) (mulR64Effect 0x10a6ca 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[377, 375]
    (.letOp (n := 382) (.out 0x10a6cd (movR64R64Effect 0x10a6cd 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[379]
    (.letOp (n := 383) (.exec 0x10a6cd (fun s => s.RIP = 0x10a6cd) (movR64R64Effect 0x10a6cd 3 0) (Reg.operands [.gpr 0] [])) #v[379]
    (b_l10a410_8))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_7 : List UInt8 :=
  [0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xD1,
    0x48, 0x03, 0x44, 0x24, 0x10, 0x4C, 0x13, 0x0C, 0x24, 0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89,
    0xC6, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0x14, 0x24, 0x48, 0x89, 0x44, 0x24, 0x10,
    0x48, 0x8B, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xD1, 0x48, 0x89,
    0x84, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x8B, 0xAC, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x89,
    0xE8, 0x4C, 0x8B, 0xAC, 0x24, 0x58, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0xC3] ++ bytes_l10a410_8

theorem code_l10a410_7 : ∀ x ∈ codeRange 0x10a671 bytes_l10a410_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa671 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_8

def b_l10a410_6 : Block Op Label signature Reg.count 296 :=
  .letOp (n := 296) (.out 0x10a620 (mulR64Effect 0x10a620 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[199, 294]
    (.letOp (n := 297) (.out 0x10a620 (mulR64Effect 0x10a620 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[199, 294]
    (.letOp (n := 298) (.exec 0x10a620 (fun s => s.RIP = 0x10a620) (mulR64Effect 0x10a620 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[199, 294]
    (.letOp (n := 299) (.out 0x10a623 (movR64R64Effect 0x10a623 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[297]
    (.letOp (n := 300) (.exec 0x10a623 (fun s => s.RIP = 0x10a623) (movR64R64Effect 0x10a623 7 2) (Reg.operands [.gpr 2] [])) #v[297]
    (.letOp (n := 301) (.out 0x10a626 (movR64R64Effect 0x10a626 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[296]
    (.letOp (n := 302) (.exec 0x10a626 (fun s => s.RIP = 0x10a626) (movR64R64Effect 0x10a626 15 0) (Reg.operands [.gpr 0] [])) #v[296]
    (.letOp (n := 303) (.out 0x10a629 (movR64M64Effect 0x10a629 1 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 304) (.exec 0x10a629 (LoadPre 0x10a629 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x10a629 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a629 1 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 305) (.out 0x10a631 (movR64R64Effect 0x10a631 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[303]
    (.letOp (n := 306) (.exec 0x10a631 (fun s => s.RIP = 0x10a631) (movR64R64Effect 0x10a631 0 1) (Reg.operands [.gpr 1] [])) #v[303]
    (.letOp (n := 307) (.out 0x10a634 (movR64M64Effect 0x10a634 11 (.sib 4 none 0 (.d32 0x1c0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 308) (.exec 0x10a634 (LoadPre 0x10a634 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x10a634 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a634 11 (.sib 4 none 0 (.d32 0x1c0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 309) (.out 0x10a63c (mulR64Effect 0x10a63c 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[307, 305]
    (.letOp (n := 310) (.out 0x10a63c (mulR64Effect 0x10a63c 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[307, 305]
    (.letOp (n := 311) (.exec 0x10a63c (fun s => s.RIP = 0x10a63c) (mulR64Effect 0x10a63c 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[307, 305]
    (.letOp (n := 312) (.out 0x10a63f (addR64R64Effect 0x10a63f 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[309, 301]
    (.letOp (n := 313) (.out 0x10a63f (addR64R64Effect 0x10a63f 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[309, 301]
    (.letOp (n := 314) (.exec 0x10a63f (fun s => s.RIP = 0x10a63f) (addR64R64Effect 0x10a63f 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[309, 301]
    (.letOp (n := 315) (.out 0x10a642 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a642 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[299, 310, 313]
    (.letOp (n := 316) (.exec 0x10a642 (fun s => s.RIP = 0x10a642) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a642 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[299, 310, 313]
    (.letOp (n := 317) (.out 0x10a645 (addR64R64Effect 0x10a645 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[312, 288]
    (.letOp (n := 318) (.out 0x10a645 (addR64R64Effect 0x10a645 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[312, 288]
    (.letOp (n := 319) (.exec 0x10a645 (fun s => s.RIP = 0x10a645) (addR64R64Effect 0x10a645 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[312, 288]
    (.letOp (n := 320) (.out 0x10a648 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a648 7 14)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[315, 290, 318]
    (.letOp (n := 321) (.exec 0x10a648 (fun s => s.RIP = 0x10a648) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a648 7 14)) (Reg.operands [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[315, 290, 318]
    (.letOp (n := 322) (.out 0x10a64b (addR64R64Effect 0x10a64b 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[317, 279]
    (.letOp (n := 323) (.out 0x10a64b (addR64R64Effect 0x10a64b 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[317, 279]
    (.letOp (n := 324) (.exec 0x10a64b (fun s => s.RIP = 0x10a64b) (addR64R64Effect 0x10a64b 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[317, 279]
    (.letOp (n := 325) (.out 0x10a64e (atFlags StatusFlags.CF (adcR64R64Effect 0x10a64e 7 5)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[320, 277, 323]
    (.letOp (n := 326) (.exec 0x10a64e (fun s => s.RIP = 0x10a64e) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a64e 7 5)) (Reg.operands [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[320, 277, 323]
    (.letOp (n := 327) (.out 0x10a651 (addR64R64Effect 0x10a651 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[322, 257]
    (.letOp (n := 328) (.out 0x10a651 (addR64R64Effect 0x10a651 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[322, 257]
    (.letOp (n := 329) (.exec 0x10a651 (fun s => s.RIP = 0x10a651) (addR64R64Effect 0x10a651 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[322, 257]
    (.letOp (n := 330) (.out 0x10a654 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a654 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[325, 328]
    (.letOp (n := 331) (.exec 0x10a654 (fun s => s.RIP = 0x10a654) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a654 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[325, 328]
    (.letOp (n := 332) (.out 0x10a658 (shldR64R64Effect 0x10a658 5 7 0 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[330, 327]
    (.letOp (n := 333) (.exec 0x10a658 (fun s => s.RIP = 0x10a658) (shldR64R64Effect 0x10a658 5 7 0 12) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[330, 327]
    (.letOp (n := 334) (.out 0x10a65d (shlR64Effect 0x10a65d 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[327]
    (.letOp (n := 335) (.exec 0x10a65d (fun s => s.RIP = 0x10a65d) (shlR64Effect 0x10a65d 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[327]
    (.letOp (n := 336) (.out 0x10a661 (movR64Imm64Effect 0x10a661 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 337) (.exec 0x10a661 (fun s => s.RIP = 0x10a661) (movR64Imm64Effect 0x10a661 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 338) (.out 0x10a66b (andR64R64Effect 0x10a66b 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[334, 336]
    (.letOp (n := 339) (.exec 0x10a66b (fun s => s.RIP = 0x10a66b) (andR64R64Effect 0x10a66b 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[334, 336]
    (.letOp (n := 340) (.out 0x10a66e (orR64R64Effect 0x10a66e 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[338, 292]
    (.letOp (n := 341) (.exec 0x10a66e (fun s => s.RIP = 0x10a66e) (orR64R64Effect 0x10a66e 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[338, 292]
    (b_l10a410_7))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_6 : List UInt8 :=
  [0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x8C, 0x24, 0x48, 0x01, 0x00,
    0x00, 0x48, 0x89, 0xC8, 0x4C, 0x8B, 0x9C, 0x24, 0xC0, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE3, 0x4C,
    0x01, 0xF8, 0x48, 0x11, 0xD7, 0x48, 0x01, 0xD8, 0x4C, 0x11, 0xF7, 0x4C, 0x01, 0xC8, 0x48, 0x11,
    0xEF, 0x4C, 0x01, 0xC0, 0x48, 0x83, 0xD7, 0x00, 0x48, 0x0F, 0xA4, 0xC7, 0x0C, 0x48, 0xC1, 0xE0,
    0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x48, 0x09,
    0xF0] ++ bytes_l10a410_7

theorem code_l10a410_6 : ∀ x ∈ codeRange 0x10a620 bytes_l10a410_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa620 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_7

def b_l10a410_5 : Block Op Label signature Reg.count 255 :=
  .letOp (n := 255) (.out 0x10a5c4 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a5c4 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[249, 252]
    (.letOp (n := 256) (.exec 0x10a5c4 (fun s => s.RIP = 0x10a5c4) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10a5c4 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[249, 252]
    (.letOp (n := 257) (.out 0x10a5c8 (shldR64R64Effect 0x10a5c8 5 8 6 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[255, 251]
    (.letOp (n := 258) (.exec 0x10a5c8 (fun s => s.RIP = 0x10a5c8) (shldR64R64Effect 0x10a5c8 5 8 6 12) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[255, 251]
    (.letOp (n := 259) (.out 0x10a5cd (shrR64Effect 0x10a5cd 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[251]
    (.letOp (n := 260) (.exec 0x10a5cd (fun s => s.RIP = 0x10a5cd) (shrR64Effect 0x10a5cd 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[251]
    (.letOp (n := 261) (.out 0x10a5d1 (movR64R64Effect 0x10a5d1 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[208]
    (.letOp (n := 262) (.exec 0x10a5d1 (fun s => s.RIP = 0x10a5d1) (movR64R64Effect 0x10a5d1 0 9) (Reg.operands [.gpr 9] [])) #v[208]
    (.letOp (n := 263) (.out 0x10a5d4 (movR64M64Effect 0x10a5d4 13 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 264) (.exec 0x10a5d4 (LoadPre 0x10a5d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10a5d4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a5d4 13 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 265) (.out 0x10a5dc (mulR64Effect 0x10a5dc 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[263, 261]
    (.letOp (n := 266) (.out 0x10a5dc (mulR64Effect 0x10a5dc 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[263, 261]
    (.letOp (n := 267) (.exec 0x10a5dc (fun s => s.RIP = 0x10a5dc) (mulR64Effect 0x10a5dc 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[263, 261]
    (.letOp (n := 268) (.exec 0x10a5df (StorePre 0x10a5df 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a5df + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a5df 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[266, 65]
    (.letOp (n := 269) (.exec 0x10a5e3 (StorePre 0x10a5e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a5e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a5e3 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[265, 65]
    (.letOp (n := 270) (.out 0x10a5e8 (movR64M64Effect 0x10a5e8 0 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 271) (.exec 0x10a5e8 (LoadPre 0x10a5e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10a5e8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a5e8 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 272) (.out 0x10a5f0 (movR64M64Effect 0x10a5f0 10 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 273) (.exec 0x10a5f0 (LoadPre 0x10a5f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10a5f0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a5f0 10 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 274) (.out 0x10a5f8 (mulR64Effect 0x10a5f8 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[272, 270]
    (.letOp (n := 275) (.out 0x10a5f8 (mulR64Effect 0x10a5f8 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[272, 270]
    (.letOp (n := 276) (.exec 0x10a5f8 (fun s => s.RIP = 0x10a5f8) (mulR64Effect 0x10a5f8 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[272, 270]
    (.letOp (n := 277) (.out 0x10a5fb (movR64R64Effect 0x10a5fb 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[275]
    (.letOp (n := 278) (.exec 0x10a5fb (fun s => s.RIP = 0x10a5fb) (movR64R64Effect 0x10a5fb 5 2) (Reg.operands [.gpr 2] [])) #v[275]
    (.letOp (n := 279) (.out 0x10a5fe (movR64R64Effect 0x10a5fe 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[274]
    (.letOp (n := 280) (.exec 0x10a5fe (fun s => s.RIP = 0x10a5fe) (movR64R64Effect 0x10a5fe 9 0) (Reg.operands [.gpr 0] [])) #v[274]
    (.letOp (n := 281) (.out 0x10a601 (movR64M64Effect 0x10a601 12 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 282) (.exec 0x10a601 (LoadPre 0x10a601 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10a601 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a601 12 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 283) (.out 0x10a609 (movR64R64Effect 0x10a609 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[281]
    (.letOp (n := 284) (.exec 0x10a609 (fun s => s.RIP = 0x10a609) (movR64R64Effect 0x10a609 0 12) (Reg.operands [.gpr 12] [])) #v[281]
    (.letOp (n := 285) (.out 0x10a60c (mulM64Effect 0x10a60c 8 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[283, 65]
    (.letOp (n := 286) (.out 0x10a60c (mulM64Effect 0x10a60c 8 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[283, 65]
    (.letOp (n := 287) (.exec 0x10a60c (LoadPre 0x10a60c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10a60c + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10a60c 8 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[283, 65]
    (.letOp (n := 288) (.out 0x10a614 (movR64R64Effect 0x10a614 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[285]
    (.letOp (n := 289) (.exec 0x10a614 (fun s => s.RIP = 0x10a614) (movR64R64Effect 0x10a614 3 0) (Reg.operands [.gpr 0] [])) #v[285]
    (.letOp (n := 290) (.out 0x10a617 (movR64R64Effect 0x10a617 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[286]
    (.letOp (n := 291) (.exec 0x10a617 (fun s => s.RIP = 0x10a617) (movR64R64Effect 0x10a617 14 2) (Reg.operands [.gpr 2] [])) #v[286]
    (.letOp (n := 292) (.out 0x10a61a (andR32Imm8Effect 0x10a61a 3 6 0xf) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[259]
    (.letOp (n := 293) (.exec 0x10a61a (fun s => s.RIP = 0x10a61a) (andR32Imm8Effect 0x10a61a 3 6 0xf) (Reg.operands [.gpr 6] [])) #v[259]
    (.letOp (n := 294) (.out 0x10a61d (movR64R64Effect 0x10a61d 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[186]
    (.letOp (n := 295) (.exec 0x10a61d (fun s => s.RIP = 0x10a61d) (movR64R64Effect 0x10a61d 0 11) (Reg.operands [.gpr 11] [])) #v[186]
    (b_l10a410_6)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_5 : List UInt8 :=
  [0x49, 0x83, 0xD0, 0x00, 0x49, 0x0F, 0xA4, 0xF0, 0x0C, 0x48, 0xC1, 0xEE, 0x30, 0x4C, 0x89, 0xC8,
    0x4C, 0x8B, 0xAC, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0x14, 0x24, 0x48,
    0x89, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x94, 0x24,
    0xF8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xD5, 0x49, 0x89, 0xC1, 0x4C, 0x8B, 0xA4,
    0x24, 0xC8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0xA4, 0x24, 0x58, 0x01, 0x00, 0x00,
    0x48, 0x89, 0xC3, 0x49, 0x89, 0xD6, 0x83, 0xE6, 0x0F, 0x4C, 0x89, 0xD8] ++ bytes_l10a410_6

theorem code_l10a410_5 : ∀ x ∈ codeRange 0x10a5c4 bytes_l10a410_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa5c4 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_6

def b_l10a410_4 : Block Op Label signature Reg.count 208 :=
  .letOp (n := 208) (.out 0x10a574 (movR64M64Effect 0x10a574 9 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 209) (.exec 0x10a574 (LoadPre 0x10a574 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10a574 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a574 9 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 210) (.out 0x10a57c (movR64R64Effect 0x10a57c 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[208]
    (.letOp (n := 211) (.exec 0x10a57c (fun s => s.RIP = 0x10a57c) (movR64R64Effect 0x10a57c 0 9) (Reg.operands [.gpr 9] [])) #v[208]
    (.letOp (n := 212) (.out 0x10a57f (mulR64Effect 0x10a57f 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[121, 210]
    (.letOp (n := 213) (.out 0x10a57f (mulR64Effect 0x10a57f 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[121, 210]
    (.letOp (n := 214) (.exec 0x10a57f (fun s => s.RIP = 0x10a57f) (mulR64Effect 0x10a57f 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[121, 210]
    (.letOp (n := 215) (.out 0x10a582 (movR64R64Effect 0x10a582 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[213]
    (.letOp (n := 216) (.exec 0x10a582 (fun s => s.RIP = 0x10a582) (movR64R64Effect 0x10a582 8 2) (Reg.operands [.gpr 2] [])) #v[213]
    (.letOp (n := 217) (.out 0x10a585 (movR64R64Effect 0x10a585 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[212]
    (.letOp (n := 218) (.exec 0x10a585 (fun s => s.RIP = 0x10a585) (movR64R64Effect 0x10a585 6 0) (Reg.operands [.gpr 0] [])) #v[212]
    (.letOp (n := 219) (.out 0x10a588 (movR64R64Effect 0x10a588 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[166]
    (.letOp (n := 220) (.exec 0x10a588 (fun s => s.RIP = 0x10a588) (movR64R64Effect 0x10a588 0 10) (Reg.operands [.gpr 10] [])) #v[166]
    (.letOp (n := 221) (.out 0x10a58b (movR64Imm64Effect 0x10a58b 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 222) (.exec 0x10a58b (fun s => s.RIP = 0x10a58b) (movR64Imm64Effect 0x10a58b 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 223) (.out 0x10a595 (mulR64Effect 0x10a595 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[221, 219]
    (.letOp (n := 224) (.out 0x10a595 (mulR64Effect 0x10a595 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[221, 219]
    (.letOp (n := 225) (.exec 0x10a595 (fun s => s.RIP = 0x10a595) (mulR64Effect 0x10a595 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[221, 219]
    (.letOp (n := 226) (.out 0x10a598 (addR64R64Effect 0x10a598 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[217, 206]
    (.letOp (n := 227) (.out 0x10a598 (addR64R64Effect 0x10a598 6 13) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 13] []) (.flag .CF)) #v[217, 206]
    (.letOp (n := 228) (.exec 0x10a598 (fun s => s.RIP = 0x10a598) (addR64R64Effect 0x10a598 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[217, 206]
    (.letOp (n := 229) (.out 0x10a59b (atFlags StatusFlags.CF (adcR64R64Effect 0x10a59b 8 12)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[215, 204, 227]
    (.letOp (n := 230) (.exec 0x10a59b (fun s => s.RIP = 0x10a59b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a59b 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[215, 204, 227]
    (.letOp (n := 231) (.out 0x10a59e (addR64R64Effect 0x10a59e 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[226, 195]
    (.letOp (n := 232) (.out 0x10a59e (addR64R64Effect 0x10a59e 6 15) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 15] []) (.flag .CF)) #v[226, 195]
    (.letOp (n := 233) (.exec 0x10a59e (fun s => s.RIP = 0x10a59e) (addR64R64Effect 0x10a59e 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[226, 195]
    (.letOp (n := 234) (.out 0x10a5a1 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a5a1 8 14)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[229, 193, 232]
    (.letOp (n := 235) (.exec 0x10a5a1 (fun s => s.RIP = 0x10a5a1) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a5a1 8 14)) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[229, 193, 232]
    (.letOp (n := 236) (.out 0x10a5a4 (addR64R64Effect 0x10a5a4 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[231, 184]
    (.letOp (n := 237) (.out 0x10a5a4 (addR64R64Effect 0x10a5a4 6 3) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 3] []) (.flag .CF)) #v[231, 184]
    (.letOp (n := 238) (.exec 0x10a5a4 (fun s => s.RIP = 0x10a5a4) (addR64R64Effect 0x10a5a4 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[231, 184]
    (.letOp (n := 239) (.out 0x10a5a7 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a5a7 8 5)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[234, 182, 237]
    (.letOp (n := 240) (.exec 0x10a5a7 (fun s => s.RIP = 0x10a5a7) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a5a7 8 5)) (Reg.operands [.gpr 8, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[234, 182, 237]
    (.letOp (n := 241) (.out 0x10a5aa (addR64M64Effect 0x10a5aa 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[236, 65]
    (.letOp (n := 242) (.out 0x10a5aa (addR64M64Effect 0x10a5aa 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[236, 65]
    (.letOp (n := 243) (.exec 0x10a5aa (LoadPre 0x10a5aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a5aa + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10a5aa 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[236, 65]
    (.letOp (n := 244) (.out 0x10a5af (atFlags StatusFlags.CF (adcR64M64Effect 0x10a5af 8 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[239, 65, 242]
    (.letOp (n := 245) (.exec 0x10a5af (LoadPre 0x10a5af (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a5af + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10a5af 8 (.sib 4 none 0 .none))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[239, 65, 242]
    (.letOp (n := 246) (.out 0x10a5b3 (addR64R64Effect 0x10a5b3 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[241, 223]
    (.letOp (n := 247) (.out 0x10a5b3 (addR64R64Effect 0x10a5b3 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[241, 223]
    (.letOp (n := 248) (.exec 0x10a5b3 (fun s => s.RIP = 0x10a5b3) (addR64R64Effect 0x10a5b3 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[241, 223]
    (.letOp (n := 249) (.out 0x10a5b6 (atFlags StatusFlags.CF (adcR64R64Effect 0x10a5b6 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[244, 224, 247]
    (.letOp (n := 250) (.exec 0x10a5b6 (fun s => s.RIP = 0x10a5b6) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a5b6 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[244, 224, 247]
    (.letOp (n := 251) (.out 0x10a5b9 (addR64R64Effect 0x10a5b9 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[246, 168]
    (.letOp (n := 252) (.out 0x10a5b9 (addR64R64Effect 0x10a5b9 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[246, 168]
    (.letOp (n := 253) (.exec 0x10a5b9 (fun s => s.RIP = 0x10a5b9) (addR64R64Effect 0x10a5b9 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[246, 168]
    (.letOp (n := 254) (.exec 0x10a5bc (StorePre 0x10a5bc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x10a5bc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a5bc 6 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[251, 65]
    (b_l10a410_5)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_4 : List UInt8 :=
  [0x4C, 0x8B, 0x8C, 0x24, 0x40, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xC8, 0x49, 0xF7, 0xE0, 0x49, 0x89,
    0xD0, 0x48, 0x89, 0xC6, 0x4C, 0x89, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00,
    0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x01, 0xEE, 0x4D, 0x11, 0xE0, 0x4C, 0x01, 0xFE, 0x4D, 0x11, 0xF0,
    0x48, 0x01, 0xDE, 0x49, 0x11, 0xE8, 0x48, 0x03, 0x74, 0x24, 0x10, 0x4C, 0x13, 0x04, 0x24, 0x48,
    0x01, 0xC6, 0x49, 0x11, 0xD0, 0x48, 0x01, 0xCE, 0x48, 0x89, 0xB4, 0x24, 0x90, 0x01, 0x00, 0x00] ++ bytes_l10a410_5

theorem code_l10a410_4 : ∀ x ∈ codeRange 0x10a574 bytes_l10a410_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa574 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_5

def b_l10a410_3 : Block Op Label signature Reg.count 166 :=
  .letOp (n := 166) (.out 0x10a522 (shldR64R64Effect 0x10a522 5 10 3 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[134, 132]
    (.letOp (n := 167) (.exec 0x10a522 (fun s => s.RIP = 0x10a522) (shldR64R64Effect 0x10a522 5 10 3 12) (Reg.operands [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[134, 132]
    (.letOp (n := 168) (.out 0x10a527 (shldR64R64Effect 0x10a527 5 1 5 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[164, 160]
    (.letOp (n := 169) (.exec 0x10a527 (fun s => s.RIP = 0x10a527) (shldR64R64Effect 0x10a527 5 1 5 12) (Reg.operands [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[164, 160]
    (.letOp (n := 170) (.out 0x10a52c (movR64R64Effect 0x10a52c 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[123]
    (.letOp (n := 171) (.exec 0x10a52c (fun s => s.RIP = 0x10a52c) (movR64R64Effect 0x10a52c 0 7) (Reg.operands [.gpr 7] [])) #v[123]
    (.letOp (n := 172) (.out 0x10a52f (mulR64Effect 0x10a52f 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[67, 170]
    (.letOp (n := 173) (.out 0x10a52f (mulR64Effect 0x10a52f 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[67, 170]
    (.letOp (n := 174) (.exec 0x10a52f (fun s => s.RIP = 0x10a52f) (mulR64Effect 0x10a52f 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[67, 170]
    (.letOp (n := 175) (.exec 0x10a532 (StorePre 0x10a532 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a532 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a532 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[173, 65]
    (.letOp (n := 176) (.exec 0x10a536 (StorePre 0x10a536 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a536 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a536 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[172, 65]
    (.letOp (n := 177) (.out 0x10a53b (movR64R64Effect 0x10a53b 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[80]
    (.letOp (n := 178) (.exec 0x10a53b (fun s => s.RIP = 0x10a53b) (movR64R64Effect 0x10a53b 0 11) (Reg.operands [.gpr 11] [])) #v[80]
    (.letOp (n := 179) (.out 0x10a53e (mulR64Effect 0x10a53e 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[69, 177]
    (.letOp (n := 180) (.out 0x10a53e (mulR64Effect 0x10a53e 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[69, 177]
    (.letOp (n := 181) (.exec 0x10a53e (fun s => s.RIP = 0x10a53e) (mulR64Effect 0x10a53e 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[69, 177]
    (.letOp (n := 182) (.out 0x10a541 (movR64R64Effect 0x10a541 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[180]
    (.letOp (n := 183) (.exec 0x10a541 (fun s => s.RIP = 0x10a541) (movR64R64Effect 0x10a541 5 2) (Reg.operands [.gpr 2] [])) #v[180]
    (.letOp (n := 184) (.out 0x10a544 (movR64R64Effect 0x10a544 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[179]
    (.letOp (n := 185) (.exec 0x10a544 (fun s => s.RIP = 0x10a544) (movR64R64Effect 0x10a544 3 0) (Reg.operands [.gpr 0] [])) #v[179]
    (.letOp (n := 186) (.out 0x10a547 (movR64M64Effect 0x10a547 11 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 187) (.exec 0x10a547 (LoadPre 0x10a547 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10a547 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a547 11 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 188) (.out 0x10a54f (movR64R64Effect 0x10a54f 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[186]
    (.letOp (n := 189) (.exec 0x10a54f (fun s => s.RIP = 0x10a54f) (movR64R64Effect 0x10a54f 0 11) (Reg.operands [.gpr 11] [])) #v[186]
    (.letOp (n := 190) (.out 0x10a552 (mulR64Effect 0x10a552 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[71, 188]
    (.letOp (n := 191) (.out 0x10a552 (mulR64Effect 0x10a552 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[71, 188]
    (.letOp (n := 192) (.exec 0x10a552 (fun s => s.RIP = 0x10a552) (mulR64Effect 0x10a552 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[71, 188]
    (.letOp (n := 193) (.out 0x10a555 (movR64R64Effect 0x10a555 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[191]
    (.letOp (n := 194) (.exec 0x10a555 (fun s => s.RIP = 0x10a555) (movR64R64Effect 0x10a555 14 2) (Reg.operands [.gpr 2] [])) #v[191]
    (.letOp (n := 195) (.out 0x10a558 (movR64R64Effect 0x10a558 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[190]
    (.letOp (n := 196) (.exec 0x10a558 (fun s => s.RIP = 0x10a558) (movR64R64Effect 0x10a558 15 0) (Reg.operands [.gpr 0] [])) #v[190]
    (.letOp (n := 197) (.out 0x10a55b (movR64M64Effect 0x10a55b 0 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 198) (.exec 0x10a55b (LoadPre 0x10a55b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x10a55b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a55b 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 199) (.out 0x10a563 (movR64M64Effect 0x10a563 7 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 200) (.exec 0x10a563 (LoadPre 0x10a563 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10a563 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10a563 7 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 201) (.out 0x10a56b (mulR64Effect 0x10a56b 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[199, 197]
    (.letOp (n := 202) (.out 0x10a56b (mulR64Effect 0x10a56b 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[199, 197]
    (.letOp (n := 203) (.exec 0x10a56b (fun s => s.RIP = 0x10a56b) (mulR64Effect 0x10a56b 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[199, 197]
    (.letOp (n := 204) (.out 0x10a56e (movR64R64Effect 0x10a56e 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[202]
    (.letOp (n := 205) (.exec 0x10a56e (fun s => s.RIP = 0x10a56e) (movR64R64Effect 0x10a56e 12 2) (Reg.operands [.gpr 2] [])) #v[202]
    (.letOp (n := 206) (.out 0x10a571 (movR64R64Effect 0x10a571 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[201]
    (.letOp (n := 207) (.exec 0x10a571 (fun s => s.RIP = 0x10a571) (movR64R64Effect 0x10a571 13 0) (Reg.operands [.gpr 0] [])) #v[201]
    (b_l10a410_4))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_3 : List UInt8 :=
  [0x49, 0x0F, 0xA4, 0xDA, 0x0C, 0x48, 0x0F, 0xA4, 0xE9, 0x0C, 0x48, 0x89, 0xF8, 0x49, 0xF7, 0xE1,
    0x48, 0x89, 0x14, 0x24, 0x48, 0x89, 0x44, 0x24, 0x10, 0x4C, 0x89, 0xD8, 0x49, 0xF7, 0xE4, 0x48,
    0x89, 0xD5, 0x48, 0x89, 0xC3, 0x4C, 0x8B, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xD8,
    0x49, 0xF7, 0xE5, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x84, 0x24, 0x48, 0x01, 0x00,
    0x00, 0x48, 0x8B, 0xBC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xD4, 0x49,
    0x89, 0xC5] ++ bytes_l10a410_4

theorem code_l10a410_3 : ∀ x ∈ codeRange 0x10a522 bytes_l10a410_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa522 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_4

def b_l10a410_2 : Block Op Label signature Reg.count 123 :=
  .letOp (n := 123) (.out 0x10a4c1 (movR64M64Effect 0x10a4c1 7 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 124) (.exec 0x10a4c1 (LoadPre 0x10a4c1 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x10a4c1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a4c1 7 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 125) (.out 0x10a4c5 (movR64R64Effect 0x10a4c5 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[123]
    (.letOp (n := 126) (.exec 0x10a4c5 (fun s => s.RIP = 0x10a4c5) (movR64R64Effect 0x10a4c5 0 7) (Reg.operands [.gpr 7] [])) #v[123]
    (.letOp (n := 127) (.exec 0x10a4c8 (StorePre 0x10a4c8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10a4c8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a4c8 7 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[123, 65]
    (.letOp (n := 128) (.out 0x10a4d0 (mulR64Effect 0x10a4d0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[121, 125]
    (.letOp (n := 129) (.out 0x10a4d0 (mulR64Effect 0x10a4d0 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[121, 125]
    (.letOp (n := 130) (.exec 0x10a4d0 (fun s => s.RIP = 0x10a4d0) (mulR64Effect 0x10a4d0 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[121, 125]
    (.letOp (n := 131) (.exec 0x10a4d3 (StorePre 0x10a4d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x10a4d3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a4d3 8 (.sib 4 none 0 (.d32 0x1c0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[121, 65]
    (.letOp (n := 132) (.out 0x10a4db (movR64R64Effect 0x10a4db 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[128]
    (.letOp (n := 133) (.exec 0x10a4db (fun s => s.RIP = 0x10a4db) (movR64R64Effect 0x10a4db 3 0) (Reg.operands [.gpr 0] [])) #v[128]
    (.letOp (n := 134) (.out 0x10a4de (movR64R64Effect 0x10a4de 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[129]
    (.letOp (n := 135) (.exec 0x10a4de (fun s => s.RIP = 0x10a4de) (movR64R64Effect 0x10a4de 10 2) (Reg.operands [.gpr 2] [])) #v[129]
    (.letOp (n := 136) (.out 0x10a4e1 (movR64Imm64Effect 0x10a4e1 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 137) (.exec 0x10a4e1 (fun s => s.RIP = 0x10a4e1) (movR64Imm64Effect 0x10a4e1 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 138) (.out 0x10a4eb (andR64R64Effect 0x10a4eb 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[128, 136]
    (.letOp (n := 139) (.exec 0x10a4eb (fun s => s.RIP = 0x10a4eb) (andR64R64Effect 0x10a4eb 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[128, 136]
    (.letOp (n := 140) (.out 0x10a4ee (movR64Imm64Effect 0x10a4ee 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 141) (.exec 0x10a4ee (fun s => s.RIP = 0x10a4ee) (movR64Imm64Effect 0x10a4ee 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 142) (.out 0x10a4f8 (mulR64Effect 0x10a4f8 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[140, 138]
    (.letOp (n := 143) (.out 0x10a4f8 (mulR64Effect 0x10a4f8 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[140, 138]
    (.letOp (n := 144) (.exec 0x10a4f8 (fun s => s.RIP = 0x10a4f8) (mulR64Effect 0x10a4f8 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[140, 138]
    (.letOp (n := 145) (.out 0x10a4fb (addR64R64Effect 0x10a4fb 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[117, 106]
    (.letOp (n := 146) (.out 0x10a4fb (addR64R64Effect 0x10a4fb 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[117, 106]
    (.letOp (n := 147) (.exec 0x10a4fb (fun s => s.RIP = 0x10a4fb) (addR64R64Effect 0x10a4fb 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[117, 106]
    (.letOp (n := 148) (.out 0x10a4fe (atFlags StatusFlags.CF (adcR64R64Effect 0x10a4fe 1 14)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[119, 108, 146]
    (.letOp (n := 149) (.exec 0x10a4fe (fun s => s.RIP = 0x10a4fe) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a4fe 1 14)) (Reg.operands [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[119, 108, 146]
    (.letOp (n := 150) (.out 0x10a501 (addR64M64Effect 0x10a501 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[145, 65]
    (.letOp (n := 151) (.out 0x10a501 (addR64M64Effect 0x10a501 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[145, 65]
    (.letOp (n := 152) (.exec 0x10a501 (LoadPre 0x10a501 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10a501 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10a501 5 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[145, 65]
    (.letOp (n := 153) (.out 0x10a506 (atFlags StatusFlags.CF (adcR64M64Effect 0x10a506 1 (.sib 4 none 0 (.d8 0x20)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[148, 65, 151]
    (.letOp (n := 154) (.exec 0x10a506 (LoadPre 0x10a506 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10a506 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10a506 1 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[148, 65, 151]
    (.letOp (n := 155) (.out 0x10a50b (addR64M64Effect 0x10a50b 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[150, 65]
    (.letOp (n := 156) (.out 0x10a50b (addR64M64Effect 0x10a50b 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[150, 65]
    (.letOp (n := 157) (.exec 0x10a50b (LoadPre 0x10a50b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a50b + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10a50b 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[150, 65]
    (.letOp (n := 158) (.out 0x10a510 (atFlags StatusFlags.CF (adcR64M64Effect 0x10a510 1 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[153, 65, 156]
    (.letOp (n := 159) (.exec 0x10a510 (LoadPre 0x10a510 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a510 + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10a510 1 (.sib 4 none 0 .none))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[153, 65, 156]
    (.letOp (n := 160) (.out 0x10a514 (addR64R64Effect 0x10a514 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[155, 142]
    (.letOp (n := 161) (.out 0x10a514 (addR64R64Effect 0x10a514 5 0) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 0] []) (.flag .CF)) #v[155, 142]
    (.letOp (n := 162) (.exec 0x10a514 (fun s => s.RIP = 0x10a514) (addR64R64Effect 0x10a514 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[155, 142]
    (.letOp (n := 163) (.exec 0x10a517 (StorePre 0x10a517 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x10a517 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a517 5 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[160, 65]
    (.letOp (n := 164) (.out 0x10a51f (atFlags StatusFlags.CF (adcR64R64Effect 0x10a51f 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[158, 143, 161]
    (.letOp (n := 165) (.exec 0x10a51f (fun s => s.RIP = 0x10a51f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10a51f 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[158, 143, 161]
    (b_l10a410_3)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_2 : List UInt8 :=
  [0x48, 0x8B, 0x7E, 0x20, 0x48, 0x89, 0xF8, 0x48, 0x89, 0xBC, 0x24, 0x10, 0x01, 0x00, 0x00, 0x49,
    0xF7, 0xE0, 0x4C, 0x89, 0x84, 0x24, 0xC0, 0x01, 0x00, 0x00, 0x48, 0x89, 0xC3, 0x49, 0x89, 0xD2,
    0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10,
    0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x01, 0xFD, 0x4C, 0x11, 0xF1,
    0x48, 0x03, 0x6C, 0x24, 0x18, 0x48, 0x13, 0x4C, 0x24, 0x20, 0x48, 0x03, 0x6C, 0x24, 0x10, 0x48,
    0x13, 0x0C, 0x24, 0x48, 0x01, 0xC5, 0x48, 0x89, 0xAC, 0x24, 0x78, 0x01, 0x00, 0x00, 0x48, 0x11,
    0xD1] ++ bytes_l10a410_3

theorem code_l10a410_2 : ∀ x ∈ codeRange 0x10a4c1 bytes_l10a410_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa4c1 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_3

def b_l10a410_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.exec 0x10a466 (StorePre 0x10a466 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a466 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a466 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[86, 65]
    (.letOp (n := 90) (.exec 0x10a46a (StorePre 0x10a46a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a46a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a46a 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[85, 65]
    (.letOp (n := 91) (.out 0x10a46f (movR64R64Effect 0x10a46f 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[77]
    (.letOp (n := 92) (.exec 0x10a46f (fun s => s.RIP = 0x10a46f) (movR64R64Effect 0x10a46f 0 1) (Reg.operands [.gpr 1] [])) #v[77]
    (.letOp (n := 93) (.out 0x10a472 (mulR64Effect 0x10a472 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[69, 91]
    (.letOp (n := 94) (.out 0x10a472 (mulR64Effect 0x10a472 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[69, 91]
    (.letOp (n := 95) (.exec 0x10a472 (fun s => s.RIP = 0x10a472) (mulR64Effect 0x10a472 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[69, 91]
    (.letOp (n := 96) (.exec 0x10a475 (StorePre 0x10a475 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10a475 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a475 12 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[69, 65]
    (.letOp (n := 97) (.exec 0x10a47d (StorePre 0x10a47d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10a47d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a47d 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[93, 65]
    (.letOp (n := 98) (.exec 0x10a482 (StorePre 0x10a482 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10a482 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a482 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[94, 65]
    (.letOp (n := 99) (.out 0x10a487 (movR64M64Effect 0x10a487 0 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 100) (.exec 0x10a487 (LoadPre 0x10a487 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10a487 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a487 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 101) (.exec 0x10a48b (StorePre 0x10a48b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x10a48b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a48b 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[99, 65]
    (.letOp (n := 102) (.out 0x10a493 (mulR64Effect 0x10a493 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[71, 99]
    (.letOp (n := 103) (.out 0x10a493 (mulR64Effect 0x10a493 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[71, 99]
    (.letOp (n := 104) (.exec 0x10a493 (fun s => s.RIP = 0x10a493) (mulR64Effect 0x10a493 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[71, 99]
    (.letOp (n := 105) (.exec 0x10a496 (StorePre 0x10a496 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10a496 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a496 13 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[71, 65]
    (.letOp (n := 106) (.out 0x10a49e (movR64R64Effect 0x10a49e 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[102]
    (.letOp (n := 107) (.exec 0x10a49e (fun s => s.RIP = 0x10a49e) (movR64R64Effect 0x10a49e 15 0) (Reg.operands [.gpr 0] [])) #v[102]
    (.letOp (n := 108) (.out 0x10a4a1 (movR64R64Effect 0x10a4a1 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[103]
    (.letOp (n := 109) (.exec 0x10a4a1 (fun s => s.RIP = 0x10a4a1) (movR64R64Effect 0x10a4a1 14 2) (Reg.operands [.gpr 2] [])) #v[103]
    (.letOp (n := 110) (.out 0x10a4a4 (movR64M64Effect 0x10a4a4 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 111) (.exec 0x10a4a4 (LoadPre 0x10a4a4 (fun s => AddrMode.addr (.base 6 .none) s (0x10a4a4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a4a4 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 112) (.exec 0x10a4a7 (StorePre 0x10a4a7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10a4a7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a4a7 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[110, 65]
    (.letOp (n := 113) (.exec 0x10a4af (StorePre 0x10a4af 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10a4af + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a4af 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 65]
    (.letOp (n := 114) (.out 0x10a4b4 (mulR64Effect 0x10a4b4 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[73, 110]
    (.letOp (n := 115) (.out 0x10a4b4 (mulR64Effect 0x10a4b4 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[73, 110]
    (.letOp (n := 116) (.exec 0x10a4b4 (fun s => s.RIP = 0x10a4b4) (mulR64Effect 0x10a4b4 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[73, 110]
    (.letOp (n := 117) (.out 0x10a4b7 (movR64R64Effect 0x10a4b7 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[114]
    (.letOp (n := 118) (.exec 0x10a4b7 (fun s => s.RIP = 0x10a4b7) (movR64R64Effect 0x10a4b7 5 0) (Reg.operands [.gpr 0] [])) #v[114]
    (.letOp (n := 119) (.out 0x10a4ba (movR64R64Effect 0x10a4ba 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[115]
    (.letOp (n := 120) (.exec 0x10a4ba (fun s => s.RIP = 0x10a4ba) (movR64R64Effect 0x10a4ba 1 2) (Reg.operands [.gpr 2] [])) #v[115]
    (.letOp (n := 121) (.out 0x10a4bd (movR64M64Effect 0x10a4bd 8 (.base 7 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 122) (.exec 0x10a4bd (LoadPre 0x10a4bd (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x10a4bd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a4bd 8 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 7] [])) #v[7]
    (b_l10a410_2))))))))))))))))))))))))))))))))))

def bytes_l10a410_1 : List UInt8 :=
  [0x48, 0x89, 0x14, 0x24, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE4, 0x4C,
    0x89, 0xA4, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x89, 0x54, 0x24,
    0x20, 0x48, 0x8B, 0x46, 0x08, 0x48, 0x89, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE5,
    0x4C, 0x89, 0xAC, 0x24, 0x58, 0x01, 0x00, 0x00, 0x49, 0x89, 0xC7, 0x49, 0x89, 0xD6, 0x48, 0x8B,
    0x06, 0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x48, 0x89, 0x74, 0x24, 0x60, 0x48, 0xF7,
    0xE5, 0x48, 0x89, 0xC5, 0x48, 0x89, 0xD1, 0x4C, 0x8B, 0x47, 0x20] ++ bytes_l10a410_2

theorem code_l10a410_1 : ∀ x ∈ codeRange 0x10a466 bytes_l10a410_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa466 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_2

def b_l10a410 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a410 (pushR64Effect 0x10a410 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x10a410 (PushPre 0x10a410 1) (pushR64Effect 0x10a410 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x10a411 (pushR64Effect 0x10a411 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x10a411 (PushPre 0x10a411 2) (pushR64Effect 0x10a411 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x10a413 (pushR64Effect 0x10a413 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x10a413 (PushPre 0x10a413 2) (pushR64Effect 0x10a413 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x10a415 (pushR64Effect 0x10a415 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x10a415 (PushPre 0x10a415 2) (pushR64Effect 0x10a415 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x10a417 (pushR64Effect 0x10a417 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x10a417 (PushPre 0x10a417 2) (pushR64Effect 0x10a417 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x10a419 (pushR64Effect 0x10a419 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x10a419 (PushPre 0x10a419 1) (pushR64Effect 0x10a419 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10a41a (subR64Imm32Effect 0x10a41a 4 0x1e8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10a41a (fun s => s.RIP = 0x10a41a) (subR64Imm32Effect 0x10a41a 4 0x1e8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10a421 (movR64M64Effect 0x10a421 9 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[7]
    (.letOp (n := 68) (.exec 0x10a421 (LoadPre 0x10a421 (fun s => AddrMode.addr (.base 7 .none) s (0x10a421 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a421 9 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x10a424 (movR64M64Effect 0x10a424 12 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[7]
    (.letOp (n := 70) (.exec 0x10a424 (LoadPre 0x10a424 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10a424 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a424 12 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x10a428 (movR64M64Effect 0x10a428 13 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 7] []) (.reg (.gpr 13))) #v[7]
    (.letOp (n := 72) (.exec 0x10a428 (LoadPre 0x10a428 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10a428 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a428 13 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.out 0x10a42c (movR64M64Effect 0x10a42c 5 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 7] []) (.reg (.gpr 5))) #v[7]
    (.letOp (n := 74) (.exec 0x10a42c (LoadPre 0x10a42c (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10a42c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a42c 5 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 75) (.exec 0x10a430 (StorePre 0x10a430 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10a430 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a430 5 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[73, 65]
    (.letOp (n := 76) (.exec 0x10a438 (StorePre 0x10a438 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x10a438 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a438 7 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 77) (.out 0x10a440 (movR64M64Effect 0x10a440 1 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 78) (.exec 0x10a440 (LoadPre 0x10a440 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10a440 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a440 1 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 79) (.exec 0x10a444 (StorePre 0x10a444 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10a444 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a444 1 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[77, 65]
    (.letOp (n := 80) (.out 0x10a44c (movR64M64Effect 0x10a44c 11 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[6]
    (.letOp (n := 81) (.exec 0x10a44c (LoadPre 0x10a44c (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10a44c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a44c 11 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 82) (.out 0x10a450 (movR64R64Effect 0x10a450 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[80]
    (.letOp (n := 83) (.exec 0x10a450 (fun s => s.RIP = 0x10a450) (movR64R64Effect 0x10a450 0 11) (Reg.operands [.gpr 11] [])) #v[80]
    (.letOp (n := 84) (.exec 0x10a453 (StorePre 0x10a453 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10a453 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a453 11 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[80, 65]
    (.letOp (n := 85) (.out 0x10a45b (mulR64Effect 0x10a45b 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[67, 82]
    (.letOp (n := 86) (.out 0x10a45b (mulR64Effect 0x10a45b 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[67, 82]
    (.letOp (n := 87) (.exec 0x10a45b (fun s => s.RIP = 0x10a45b) (mulR64Effect 0x10a45b 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[67, 82]
    (.letOp (n := 88) (.exec 0x10a45e (StorePre 0x10a45e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10a45e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10a45e 9 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[67, 65]
    (b_l10a410_1))))))))))))))))))))))))))))))))))))

def bytes_l10a410 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xE8, 0x01, 0x00,
    0x00, 0x4C, 0x8B, 0x0F, 0x4C, 0x8B, 0x67, 0x08, 0x4C, 0x8B, 0x6F, 0x10, 0x48, 0x8B, 0x6F, 0x18,
    0x48, 0x89, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24, 0x80, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x4E, 0x10, 0x48, 0x89, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x5E, 0x18,
    0x4C, 0x89, 0xD8, 0x4C, 0x89, 0x9C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE1, 0x4C, 0x89,
    0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] ++ bytes_l10a410_1

theorem code_l10a410 : ∀ x ∈ codeRange 0x10a410 bytes_l10a410, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa410 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_1

end K256.Proofs.Ecdh.LIR
