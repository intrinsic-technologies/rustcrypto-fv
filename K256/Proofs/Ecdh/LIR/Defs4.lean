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

def b_l10a410_171 : Block Op Label signature Reg.count 7260 :=
  .letOp (n := 7260) (.out 0x10dffb (popR64Effect 0x10dffb 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[7258]
    (.letOp (n := 7261) (.out 0x10dffb (popR64Effect 0x10dffb 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[7258]
    (.letOp (n := 7262) (.exec 0x10dffb (PopPre 0x10dffb) (popR64Effect 0x10dffb 1 3) (Reg.operands [.gpr 4] [])) #v[7258]
    (.letOp (n := 7263) (.out 0x10dffc (popR64Effect 0x10dffc 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[7261]
    (.letOp (n := 7264) (.out 0x10dffc (popR64Effect 0x10dffc 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[7261]
    (.letOp (n := 7265) (.exec 0x10dffc (PopPre 0x10dffc) (popR64Effect 0x10dffc 2 12) (Reg.operands [.gpr 4] [])) #v[7261]
    (.letOp (n := 7266) (.out 0x10dffe (popR64Effect 0x10dffe 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[7264]
    (.letOp (n := 7267) (.out 0x10dffe (popR64Effect 0x10dffe 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[7264]
    (.letOp (n := 7268) (.exec 0x10dffe (PopPre 0x10dffe) (popR64Effect 0x10dffe 2 13) (Reg.operands [.gpr 4] [])) #v[7264]
    (.letOp (n := 7269) (.out 0x10e000 (popR64Effect 0x10e000 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[7267]
    (.letOp (n := 7270) (.out 0x10e000 (popR64Effect 0x10e000 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[7267]
    (.letOp (n := 7271) (.exec 0x10e000 (PopPre 0x10e000) (popR64Effect 0x10e000 2 14) (Reg.operands [.gpr 4] [])) #v[7267]
    (.letOp (n := 7272) (.out 0x10e002 (popR64Effect 0x10e002 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[7270]
    (.letOp (n := 7273) (.out 0x10e002 (popR64Effect 0x10e002 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[7270]
    (.letOp (n := 7274) (.exec 0x10e002 (PopPre 0x10e002) (popR64Effect 0x10e002 2 15) (Reg.operands [.gpr 4] [])) #v[7270]
    (.letOp (n := 7275) (.out 0x10e004 (popR64Effect 0x10e004 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[7273]
    (.letOp (n := 7276) (.out 0x10e004 (popR64Effect 0x10e004 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[7273]
    (.letOp (n := 7277) (.exec 0x10e004 (PopPre 0x10e004) (popR64Effect 0x10e004 1 5) (Reg.operands [.gpr 4] [])) #v[7273]
    (.letOp (n := 7278) (.out 0x10e005 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[7276]
    (.letOp (n := 7279) (.out 0x10e005 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[7276]
    (.letOp (n := 7280) (.exec 0x10e005 (RetPre 0x10e005) (retEffect) (Reg.operands [.gpr 4] [])) #v[7276]
    (.terminate (.ret (RegMap.args [(0, 7245), (1, 7247), (2, 7249), (3, 7260), (4, 7279), (5, 7275), (6, 7251), (7, 7243), (8, 7151), (9, 7159), (10, 7205), (11, 7149), (12, 7263), (13, 7266), (14, 7269), (15, 7272), (22, 22), (39, 39), (50, 50), (51, 51)] 7281) (some ⟨7278, by decide⟩)))))))))))))))))))))))

def bytes_l10a410_171 : List UInt8 :=
  [0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10a410_171 : ∀ x ∈ codeRange 0x10dffb bytes_l10a410_171, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xdffb 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l10a410_170 : Block Op Label signature Reg.count 7225 :=
  .letOp (n := 7225) (.out 0x10dfb3 (addR64R64Effect 0x10dfb3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[7223, 7205]
    (.letOp (n := 7226) (.exec 0x10dfb3 (fun s => s.RIP = 0x10dfb3) (addR64R64Effect 0x10dfb3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[7223, 7205]
    (.letOp (n := 7227) (.out 0x10dfb6 (movR64R64Effect 0x10dfb6 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[7225]
    (.letOp (n := 7228) (.exec 0x10dfb6 (fun s => s.RIP = 0x10dfb6) (movR64R64Effect 0x10dfb6 2 1) (Reg.operands [.gpr 1] [])) #v[7225]
    (.letOp (n := 7229) (.out 0x10dfb9 (shrR64Effect 0x10dfb9 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[7227]
    (.letOp (n := 7230) (.exec 0x10dfb9 (fun s => s.RIP = 0x10dfb9) (shrR64Effect 0x10dfb9 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7227]
    (.letOp (n := 7231) (.out 0x10dfbd (addR64R64Effect 0x10dfbd 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[7229, 7207]
    (.letOp (n := 7232) (.exec 0x10dfbd (fun s => s.RIP = 0x10dfbd) (addR64R64Effect 0x10dfbd 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[7229, 7207]
    (.letOp (n := 7233) (.out 0x10dfc0 (movR64R64Effect 0x10dfc0 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[7231]
    (.letOp (n := 7234) (.exec 0x10dfc0 (fun s => s.RIP = 0x10dfc0) (movR64R64Effect 0x10dfc0 6 2) (Reg.operands [.gpr 2] [])) #v[7231]
    (.letOp (n := 7235) (.out 0x10dfc3 (shrR64Effect 0x10dfc3 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[7233]
    (.letOp (n := 7236) (.exec 0x10dfc3 (fun s => s.RIP = 0x10dfc3) (shrR64Effect 0x10dfc3 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7233]
    (.letOp (n := 7237) (.out 0x10dfc7 (addR64R64Effect 0x10dfc7 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[7235, 7189]
    (.letOp (n := 7238) (.exec 0x10dfc7 (fun s => s.RIP = 0x10dfc7) (addR64R64Effect 0x10dfc7 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[7235, 7189]
    (.letOp (n := 7239) (.out 0x10dfca (movR64R64Effect 0x10dfca 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[7237]
    (.letOp (n := 7240) (.exec 0x10dfca (fun s => s.RIP = 0x10dfca) (movR64R64Effect 0x10dfca 7 6) (Reg.operands [.gpr 6] [])) #v[7237]
    (.letOp (n := 7241) (.out 0x10dfcd (shrR64Effect 0x10dfcd 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[7239]
    (.letOp (n := 7242) (.exec 0x10dfcd (fun s => s.RIP = 0x10dfcd) (shrR64Effect 0x10dfcd 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7239]
    (.letOp (n := 7243) (.out 0x10dfd1 (addR64R64Effect 0x10dfd1 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[7241, 7211]
    (.letOp (n := 7244) (.exec 0x10dfd1 (fun s => s.RIP = 0x10dfd1) (addR64R64Effect 0x10dfd1 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[7241, 7211]
    (.letOp (n := 7245) (.out 0x10dfd4 (andR64R64Effect 0x10dfd4 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[7219, 7109]
    (.letOp (n := 7246) (.exec 0x10dfd4 (fun s => s.RIP = 0x10dfd4) (andR64R64Effect 0x10dfd4 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[7219, 7109]
    (.letOp (n := 7247) (.out 0x10dfd7 (andR64R64Effect 0x10dfd7 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[7225, 7109]
    (.letOp (n := 7248) (.exec 0x10dfd7 (fun s => s.RIP = 0x10dfd7) (andR64R64Effect 0x10dfd7 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[7225, 7109]
    (.letOp (n := 7249) (.out 0x10dfda (andR64R64Effect 0x10dfda 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[7231, 7109]
    (.letOp (n := 7250) (.exec 0x10dfda (fun s => s.RIP = 0x10dfda) (andR64R64Effect 0x10dfda 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[7231, 7109]
    (.letOp (n := 7251) (.out 0x10dfdd (andR64R64Effect 0x10dfdd 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[7237, 7109]
    (.letOp (n := 7252) (.exec 0x10dfdd (fun s => s.RIP = 0x10dfdd) (andR64R64Effect 0x10dfdd 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[7237, 7109]
    (.letOp (n := 7253) (.exec 0x10dfe0 (StorePre 0x10dfe0 4 (fun s => AddrMode.addr (.base 11 (.d8 0x50)) s (0x10dfe0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10dfe0 0 (.base 11 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 11] [])) #v[7245, 7149]
    (.letOp (n := 7254) (.exec 0x10dfe4 (StorePre 0x10dfe4 4 (fun s => AddrMode.addr (.base 11 (.d8 0x58)) s (0x10dfe4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10dfe4 1 (.base 11 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 11] [])) #v[7247, 7149]
    (.letOp (n := 7255) (.exec 0x10dfe8 (StorePre 0x10dfe8 4 (fun s => AddrMode.addr (.base 11 (.d8 0x60)) s (0x10dfe8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10dfe8 2 (.base 11 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 11] [])) #v[7249, 7149]
    (.letOp (n := 7256) (.exec 0x10dfec (StorePre 0x10dfec 4 (fun s => AddrMode.addr (.base 11 (.d8 0x68)) s (0x10dfec + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10dfec 6 (.base 11 (.d8 0x68))) (Reg.operands [.gpr 6, .gpr 11] [])) #v[7251, 7149]
    (.letOp (n := 7257) (.exec 0x10dff0 (StorePre 0x10dff0 4 (fun s => AddrMode.addr (.base 11 (.d8 0x70)) s (0x10dff0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10dff0 7 (.base 11 (.d8 0x70))) (Reg.operands [.gpr 7, .gpr 11] [])) #v[7243, 7149]
    (.letOp (n := 7258) (.out 0x10dff4 (addR64Imm32Effect 0x10dff4 4 0x1e8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 7259) (.exec 0x10dff4 (fun s => s.RIP = 0x10dff4) (addR64Imm32Effect 0x10dff4 4 0x1e8) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_171)))))))))))))))))))))))))))))))))))

def bytes_l10a410_170 : List UInt8 :=
  [0x4C, 0x01, 0xD1, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x34, 0x4C, 0x01, 0xEA, 0x48, 0x89, 0xD6,
    0x48, 0xC1, 0xEE, 0x34, 0x4C, 0x01, 0xF6, 0x48, 0x89, 0xF7, 0x48, 0xC1, 0xEF, 0x34, 0x4C, 0x01,
    0xFF, 0x48, 0x21, 0xE8, 0x48, 0x21, 0xE9, 0x48, 0x21, 0xEA, 0x48, 0x21, 0xEE, 0x49, 0x89, 0x43,
    0x50, 0x49, 0x89, 0x4B, 0x58, 0x49, 0x89, 0x53, 0x60, 0x49, 0x89, 0x73, 0x68, 0x49, 0x89, 0x7B,
    0x70, 0x48, 0x81, 0xC4, 0xE8, 0x01, 0x00, 0x00] ++ bytes_l10a410_171

theorem code_l10a410_170 : ∀ x ∈ codeRange 0x10dfb3 bytes_l10a410_170, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xdfb3 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_171

def b_l10a410_169 : Block Op Label signature Reg.count 7186 :=
  .letOp (n := 7186) (.exec 0x10df4b (StorePre 0x10df4b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x48)) s (0x10df4b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10df4b 0 (.base 7 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[7184, 7120]
    (.letOp (n := 7187) (.out 0x10df4f (andR64R64Effect 0x10df4f 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[7177, 7109]
    (.letOp (n := 7188) (.exec 0x10df4f (fun s => s.RIP = 0x10df4f) (andR64R64Effect 0x10df4f 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[7177, 7109]
    (.letOp (n := 7189) (.out 0x10df52 (addR64M64Effect 0x10df52 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[7187, 65]
    (.letOp (n := 7190) (.exec 0x10df52 (LoadPre 0x10df52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10df52 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10df52 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[7187, 65]
    (.letOp (n := 7191) (.out 0x10df57 (movR64Imm64Effect 0x10df57 1 0xffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 7192) (.exec 0x10df57 (fun s => s.RIP = 0x10df57) (movR64Imm64Effect 0x10df57 1 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 7193) (.out 0x10df61 (andR64R64Effect 0x10df61 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[6821, 7191]
    (.letOp (n := 7194) (.exec 0x10df61 (fun s => s.RIP = 0x10df61) (andR64R64Effect 0x10df61 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[6821, 7191]
    (.letOp (n := 7195) (.out 0x10df64 (addR64R64Effect 0x10df64 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[7193, 7182]
    (.letOp (n := 7196) (.exec 0x10df64 (fun s => s.RIP = 0x10df64) (addR64R64Effect 0x10df64 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[7193, 7182]
    (.letOp (n := 7197) (.out 0x10df67 (addR64M64Effect 0x10df67 15 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[7195, 65]
    (.letOp (n := 7198) (.exec 0x10df67 (LoadPre 0x10df67 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10df67 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10df67 15 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[7195, 65]
    (.letOp (n := 7199) (.out 0x10df6c (addR64M64Effect 0x10df6c 15 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[7197, 65]
    (.letOp (n := 7200) (.exec 0x10df6c (LoadPre 0x10df6c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10df6c + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10df6c 15 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[7197, 65]
    (.letOp (n := 7201) (.out 0x10df74 (movR64M64Effect 0x10df74 2 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 7202) (.exec 0x10df74 (LoadPre 0x10df74 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10df74 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10df74 2 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 7203) (.out 0x10df7c (addR64M64Effect 0x10df7c 2 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[7201, 65]
    (.letOp (n := 7204) (.exec 0x10df7c (LoadPre 0x10df7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10df7c + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10df7c 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[7201, 65]
    (.letOp (n := 7205) (.out 0x10df81 (addR64M64Effect 0x10df81 10 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[7077, 65]
    (.letOp (n := 7206) (.exec 0x10df81 (LoadPre 0x10df81 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10df81 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10df81 10 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[7077, 65]
    (.letOp (n := 7207) (.out 0x10df89 (addR64M64Effect 0x10df89 13 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[7168, 65]
    (.letOp (n := 7208) (.exec 0x10df89 (LoadPre 0x10df89 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10df89 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10df89 13 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[7168, 65]
    (.letOp (n := 7209) (.out 0x10df91 (movR64R64Effect 0x10df91 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[7199]
    (.letOp (n := 7210) (.exec 0x10df91 (fun s => s.RIP = 0x10df91) (movR64R64Effect 0x10df91 0 15) (Reg.operands [.gpr 15] [])) #v[7199]
    (.letOp (n := 7211) (.out 0x10df94 (andR64R64Effect 0x10df94 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[7199, 7191]
    (.letOp (n := 7212) (.exec 0x10df94 (fun s => s.RIP = 0x10df94) (andR64R64Effect 0x10df94 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[7199, 7191]
    (.letOp (n := 7213) (.out 0x10df97 (shrR64Effect 0x10df97 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[7209]
    (.letOp (n := 7214) (.exec 0x10df97 (fun s => s.RIP = 0x10df97) (shrR64Effect 0x10df97 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7209]
    (.letOp (n := 7215) (.out 0x10df9b (movR64Imm64Effect 0x10df9b 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 7216) (.exec 0x10df9b (fun s => s.RIP = 0x10df9b) (movR64Imm64Effect 0x10df9b 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 7217) (.out 0x10dfa5 (imulR64R64Effect 0x10dfa5 4 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[7213, 7215]
    (.letOp (n := 7218) (.exec 0x10dfa5 (fun s => s.RIP = 0x10dfa5) (imulR64R64Effect 0x10dfa5 4 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[7213, 7215]
    (.letOp (n := 7219) (.out 0x10dfa9 (addR64R64Effect 0x10dfa9 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[7217, 7203]
    (.letOp (n := 7220) (.exec 0x10dfa9 (fun s => s.RIP = 0x10dfa9) (addR64R64Effect 0x10dfa9 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[7217, 7203]
    (.letOp (n := 7221) (.out 0x10dfac (movR64R64Effect 0x10dfac 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[7219]
    (.letOp (n := 7222) (.exec 0x10dfac (fun s => s.RIP = 0x10dfac) (movR64R64Effect 0x10dfac 1 0) (Reg.operands [.gpr 0] [])) #v[7219]
    (.letOp (n := 7223) (.out 0x10dfaf (shrR64Effect 0x10dfaf 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[7221]
    (.letOp (n := 7224) (.exec 0x10dfaf (fun s => s.RIP = 0x10dfaf) (shrR64Effect 0x10dfaf 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7221]
    (b_l10a410_170)))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_169 : List UInt8 :=
  [0x48, 0x89, 0x47, 0x48, 0x49, 0x21, 0xEE, 0x4C, 0x03, 0x74, 0x24, 0x10, 0x48, 0xB9, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x49, 0x21, 0xCF, 0x49, 0x01, 0xD7, 0x4C, 0x03, 0x7C, 0x24,
    0x58, 0x4C, 0x03, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0xB8, 0x00, 0x00,
    0x00, 0x48, 0x03, 0x54, 0x24, 0x48, 0x4C, 0x03, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x03,
    0xAC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF8, 0x49, 0x21, 0xCF, 0x48, 0xC1, 0xE8, 0x30,
    0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xC1, 0x48, 0x01,
    0xD0, 0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x34] ++ bytes_l10a410_170

theorem code_l10a410_169 : ∀ x ∈ codeRange 0x10df4b bytes_l10a410_169, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xdf4b 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_170

def b_l10a410_168 : Block Op Label signature Reg.count 7144 :=
  .letOp (n := 7144) (.out 0x10defe (atFlags StatusFlags.CF (adcR64R64Effect 0x10defe 9 11)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[7136, 7050, 7142]
    (.letOp (n := 7145) (.exec 0x10defe (fun s => s.RIP = 0x10defe) (atFlags StatusFlags.CF (adcR64R64Effect 0x10defe 9 11)) (Reg.operands [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[7136, 7050, 7142]
    (.letOp (n := 7146) (.out 0x10df01 (movR64M64Effect 0x10df01 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 7147) (.exec 0x10df01 (LoadPre 0x10df01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10df01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10df01 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 7148) (.exec 0x10df06 (StorePre 0x10df06 4 (fun s => AddrMode.addr (.base 7 (.d8 0x40)) s (0x10df06 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10df06 0 (.base 7 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[7146, 7120]
    (.letOp (n := 7149) (.out 0x10df0a (movR64R64Effect 0x10df0a 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[7120]
    (.letOp (n := 7150) (.exec 0x10df0a (fun s => s.RIP = 0x10df0a) (movR64R64Effect 0x10df0a 11 7) (Reg.operands [.gpr 7] [])) #v[7120]
    (.letOp (n := 7151) (.out 0x10df0d (shrdR64R64Effect 0x10df0d 5 8 3 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[7102, 7105]
    (.letOp (n := 7152) (.exec 0x10df0d (fun s => s.RIP = 0x10df0d) (shrdR64R64Effect 0x10df0d 5 8 3 52) (Reg.operands [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7102, 7105]
    (.letOp (n := 7153) (.out 0x10df12 (shrR64Effect 0x10df12 4 3 52) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[7105]
    (.letOp (n := 7154) (.exec 0x10df12 (fun s => s.RIP = 0x10df12) (shrR64Effect 0x10df12 4 3 52) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7105]
    (.letOp (n := 7155) (.out 0x10df16 (movR64R64Effect 0x10df16 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[7144]
    (.letOp (n := 7156) (.exec 0x10df16 (fun s => s.RIP = 0x10df16) (movR64R64Effect 0x10df16 1 9) (Reg.operands [.gpr 9] [])) #v[7144]
    (.letOp (n := 7157) (.out 0x10df19 (shrR64Effect 0x10df19 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[7155]
    (.letOp (n := 7158) (.exec 0x10df19 (fun s => s.RIP = 0x10df19) (shrR64Effect 0x10df19 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7155]
    (.letOp (n := 7159) (.out 0x10df1d (shldR64R64Effect 0x10df1d 5 9 13 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[7144, 7141]
    (.letOp (n := 7160) (.exec 0x10df1d (fun s => s.RIP = 0x10df1d) (shldR64R64Effect 0x10df1d 5 9 13 12) (Reg.operands [.gpr 9, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7144, 7141]
    (.letOp (n := 7161) (.out 0x10df22 (imulR64R64Effect 0x10df22 4 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[7153, 7113]
    (.letOp (n := 7162) (.exec 0x10df22 (fun s => s.RIP = 0x10df22) (imulR64R64Effect 0x10df22 4 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[7153, 7113]
    (.letOp (n := 7163) (.out 0x10df26 (movR64R64Effect 0x10df26 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[7151]
    (.letOp (n := 7164) (.exec 0x10df26 (fun s => s.RIP = 0x10df26) (movR64R64Effect 0x10df26 0 8) (Reg.operands [.gpr 8] [])) #v[7151]
    (.letOp (n := 7165) (.out 0x10df29 (mulR64Effect 0x10df29 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[7113, 7163]
    (.letOp (n := 7166) (.out 0x10df29 (mulR64Effect 0x10df29 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[7113, 7163]
    (.letOp (n := 7167) (.exec 0x10df29 (fun s => s.RIP = 0x10df29) (mulR64Effect 0x10df29 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[7113, 7163]
    (.letOp (n := 7168) (.out 0x10df2c (andR64R64Effect 0x10df2c 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[7141, 7109]
    (.letOp (n := 7169) (.exec 0x10df2c (fun s => s.RIP = 0x10df2c) (andR64R64Effect 0x10df2c 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[7141, 7109]
    (.letOp (n := 7170) (.out 0x10df2f (andR64R64Effect 0x10df2f 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[6717, 7109]
    (.letOp (n := 7171) (.exec 0x10df2f (fun s => s.RIP = 0x10df2f) (andR64R64Effect 0x10df2f 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[6717, 7109]
    (.letOp (n := 7172) (.out 0x10df32 (addR64R64Effect 0x10df32 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[7170, 7165]
    (.letOp (n := 7173) (.out 0x10df32 (addR64R64Effect 0x10df32 14 0) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 0] []) (.flag .CF)) #v[7170, 7165]
    (.letOp (n := 7174) (.exec 0x10df32 (fun s => s.RIP = 0x10df32) (addR64R64Effect 0x10df32 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[7170, 7165]
    (.letOp (n := 7175) (.out 0x10df35 (atFlags StatusFlags.CF (adcR64R64Effect 0x10df35 2 3)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[7166, 7161, 7173]
    (.letOp (n := 7176) (.exec 0x10df35 (fun s => s.RIP = 0x10df35) (atFlags StatusFlags.CF (adcR64R64Effect 0x10df35 2 3)) (Reg.operands [.gpr 2, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[7166, 7161, 7173]
    (.letOp (n := 7177) (.out 0x10df38 (addR64R64Effect 0x10df38 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[7172, 7159]
    (.letOp (n := 7178) (.out 0x10df38 (addR64R64Effect 0x10df38 14 9) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 9] []) (.flag .CF)) #v[7172, 7159]
    (.letOp (n := 7179) (.exec 0x10df38 (fun s => s.RIP = 0x10df38) (addR64R64Effect 0x10df38 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[7172, 7159]
    (.letOp (n := 7180) (.out 0x10df3b (atFlags StatusFlags.CF (adcR64R64Effect 0x10df3b 2 1)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[7175, 7157, 7178]
    (.letOp (n := 7181) (.exec 0x10df3b (fun s => s.RIP = 0x10df3b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10df3b 2 1)) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[7175, 7157, 7178]
    (.letOp (n := 7182) (.out 0x10df3e (shldR64R64Effect 0x10df3e 5 2 14 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[7180, 7177]
    (.letOp (n := 7183) (.exec 0x10df3e (fun s => s.RIP = 0x10df3e) (shldR64R64Effect 0x10df3e 5 2 14 12) (Reg.operands [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7180, 7177]
    (.letOp (n := 7184) (.out 0x10df43 (movR64M64Effect 0x10df43 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 7185) (.exec 0x10df43 (LoadPre 0x10df43 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10df43 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10df43 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_169))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_168 : List UInt8 :=
  [0x4D, 0x11, 0xD9, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x47, 0x40, 0x49, 0x89, 0xFB, 0x49,
    0x0F, 0xAC, 0xD8, 0x34, 0x48, 0xC1, 0xEB, 0x34, 0x4C, 0x89, 0xC9, 0x48, 0xC1, 0xE9, 0x34, 0x4D,
    0x0F, 0xA4, 0xE9, 0x0C, 0x48, 0x0F, 0xAF, 0xDE, 0x4C, 0x89, 0xC0, 0x48, 0xF7, 0xE6, 0x49, 0x21,
    0xED, 0x49, 0x21, 0xEE, 0x49, 0x01, 0xC6, 0x48, 0x11, 0xDA, 0x4D, 0x01, 0xCE, 0x48, 0x11, 0xCA,
    0x4C, 0x0F, 0xA4, 0xF2, 0x0C, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] ++ bytes_l10a410_169

theorem code_l10a410_168 : ∀ x ∈ codeRange 0x10defe bytes_l10a410_168, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xdefe 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_169

def b_l10a410_167 : Block Op Label signature Reg.count 7100 :=
  .letOp (n := 7100) (.out 0x10de9b (atFlags StatusFlags.CF (adcR64R64Effect 0x10de9b 3 6)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[7093, 7084, 7098]
    (.letOp (n := 7101) (.exec 0x10de9b (fun s => s.RIP = 0x10de9b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10de9b 3 6)) (Reg.operands [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[7093, 7084, 7098]
    (.letOp (n := 7102) (.out 0x10de9e (addR64R64Effect 0x10de9e 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[7097, 7044]
    (.letOp (n := 7103) (.out 0x10de9e (addR64R64Effect 0x10de9e 8 5) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 5] []) (.flag .CF)) #v[7097, 7044]
    (.letOp (n := 7104) (.exec 0x10de9e (fun s => s.RIP = 0x10de9e) (addR64R64Effect 0x10de9e 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[7097, 7044]
    (.letOp (n := 7105) (.out 0x10dea1 (atFlags StatusFlags.CF (adcR64R64Effect 0x10dea1 3 1)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[7100, 7046, 7103]
    (.letOp (n := 7106) (.exec 0x10dea1 (fun s => s.RIP = 0x10dea1) (atFlags StatusFlags.CF (adcR64R64Effect 0x10dea1 3 1)) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[7100, 7046, 7103]
    (.letOp (n := 7107) (.out 0x10dea4 (movR64R64Effect 0x10dea4 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[7102]
    (.letOp (n := 7108) (.exec 0x10dea4 (fun s => s.RIP = 0x10dea4) (movR64R64Effect 0x10dea4 0 8) (Reg.operands [.gpr 8] [])) #v[7102]
    (.letOp (n := 7109) (.out 0x10dea7 (movR64Imm64Effect 0x10dea7 5 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 7110) (.exec 0x10dea7 (fun s => s.RIP = 0x10dea7) (movR64Imm64Effect 0x10dea7 5 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 7111) (.out 0x10deb1 (andR64R64Effect 0x10deb1 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[7107, 7109]
    (.letOp (n := 7112) (.exec 0x10deb1 (fun s => s.RIP = 0x10deb1) (andR64R64Effect 0x10deb1 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[7107, 7109]
    (.letOp (n := 7113) (.out 0x10deb4 (movR64Imm64Effect 0x10deb4 6 0x1000003d10) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 7114) (.exec 0x10deb4 (fun s => s.RIP = 0x10deb4) (movR64Imm64Effect 0x10deb4 6 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 7115) (.out 0x10debe (mulR64Effect 0x10debe 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[7113, 7111]
    (.letOp (n := 7116) (.out 0x10debe (mulR64Effect 0x10debe 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[7113, 7111]
    (.letOp (n := 7117) (.exec 0x10debe (fun s => s.RIP = 0x10debe) (mulR64Effect 0x10debe 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[7113, 7111]
    (.letOp (n := 7118) (.out 0x10dec1 (movR64M64Effect 0x10dec1 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 7119) (.exec 0x10dec1 (LoadPre 0x10dec1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10dec1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10dec1 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 7120) (.out 0x10dec6 (movR64M64Effect 0x10dec6 7 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 7121) (.exec 0x10dec6 (LoadPre 0x10dec6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x10dec6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dec6 7 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 7122) (.exec 0x10dece (StorePre 0x10dece 4 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x10dece + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10dece 1 (.base 7 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[7118, 7120]
    (.letOp (n := 7123) (.out 0x10ded2 (addR64M64Effect 0x10ded2 13 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[7073, 65]
    (.letOp (n := 7124) (.out 0x10ded2 (addR64M64Effect 0x10ded2 13 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[7073, 65]
    (.letOp (n := 7125) (.exec 0x10ded2 (LoadPre 0x10ded2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10ded2 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10ded2 13 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[7073, 65]
    (.letOp (n := 7126) (.out 0x10deda (atFlags StatusFlags.CF (adcR64M64Effect 0x10deda 9 (.sib 4 none 0 (.d8 0x20)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[7075, 65, 7124]
    (.letOp (n := 7127) (.exec 0x10deda (LoadPre 0x10deda (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10deda + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10deda 9 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[7075, 65, 7124]
    (.letOp (n := 7128) (.out 0x10dedf (addR64M64Effect 0x10dedf 13 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[7123, 65]
    (.letOp (n := 7129) (.out 0x10dedf (addR64M64Effect 0x10dedf 13 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[7123, 65]
    (.letOp (n := 7130) (.exec 0x10dedf (LoadPre 0x10dedf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10dedf + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10dedf 13 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[7123, 65]
    (.letOp (n := 7131) (.out 0x10dee7 (atFlags StatusFlags.CF (adcR64M64Effect 0x10dee7 9 (.sib 4 none 0 (.d8 0x40)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[7126, 65, 7129]
    (.letOp (n := 7132) (.exec 0x10dee7 (LoadPre 0x10dee7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10dee7 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10dee7 9 (.sib 4 none 0 (.d8 0x40)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[7126, 65, 7129]
    (.letOp (n := 7133) (.out 0x10deec (addR64R64Effect 0x10deec 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[7128, 7115]
    (.letOp (n := 7134) (.out 0x10deec (addR64R64Effect 0x10deec 13 0) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 0] []) (.flag .CF)) #v[7128, 7115]
    (.letOp (n := 7135) (.exec 0x10deec (fun s => s.RIP = 0x10deec) (addR64R64Effect 0x10deec 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[7128, 7115]
    (.letOp (n := 7136) (.out 0x10deef (atFlags StatusFlags.CF (adcR64R64Effect 0x10deef 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[7131, 7116, 7134]
    (.letOp (n := 7137) (.exec 0x10deef (fun s => s.RIP = 0x10deef) (atFlags StatusFlags.CF (adcR64R64Effect 0x10deef 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[7131, 7116, 7134]
    (.letOp (n := 7138) (.out 0x10def2 (movR64M64Effect 0x10def2 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 7139) (.exec 0x10def2 (LoadPre 0x10def2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10def2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10def2 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 7140) (.exec 0x10def7 (StorePre 0x10def7 4 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x10def7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10def7 0 (.base 7 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[7138, 7120]
    (.letOp (n := 7141) (.out 0x10defb (addR64R64Effect 0x10defb 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[7133, 7052]
    (.letOp (n := 7142) (.out 0x10defb (addR64R64Effect 0x10defb 13 12) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 12] []) (.flag .CF)) #v[7133, 7052]
    (.letOp (n := 7143) (.exec 0x10defb (fun s => s.RIP = 0x10defb) (addR64R64Effect 0x10defb 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[7133, 7052]
    (b_l10a410_168))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_167 : List UInt8 :=
  [0x48, 0x11, 0xF3, 0x49, 0x01, 0xE8, 0x48, 0x11, 0xCB, 0x4C, 0x89, 0xC0, 0x48, 0xBD, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xE8, 0x48, 0xBE, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE6, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x8B, 0xBC, 0x24, 0x80,
    0x01, 0x00, 0x00, 0x48, 0x89, 0x4F, 0x30, 0x4C, 0x03, 0xAC, 0x24, 0x20, 0x01, 0x00, 0x00, 0x4C,
    0x13, 0x4C, 0x24, 0x20, 0x4C, 0x03, 0xAC, 0x24, 0x18, 0x01, 0x00, 0x00, 0x4C, 0x13, 0x4C, 0x24,
    0x40, 0x49, 0x01, 0xC5, 0x49, 0x11, 0xD1, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0x89, 0x47, 0x38,
    0x4D, 0x01, 0xE5] ++ bytes_l10a410_168

theorem code_l10a410_167 : ∀ x ∈ codeRange 0x10de9b bytes_l10a410_167, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xde9b 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_168

def b_l10a410_166 : Block Op Label signature Reg.count 7059 :=
  .letOp (n := 7059) (.exec 0x10de39 (StorePre 0x10de39 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10de39 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10de39 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[7057, 65]
    (.letOp (n := 7060) (.exec 0x10de3e (StorePre 0x10de3e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10de3e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10de3e 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[7056, 65]
    (.letOp (n := 7061) (.out 0x10de46 (movR64M64Effect 0x10de46 0 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 7062) (.exec 0x10de46 (LoadPre 0x10de46 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10de46 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10de46 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 7063) (.out 0x10de4e (mulM64Effect 0x10de4e 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[7061, 65]
    (.letOp (n := 7064) (.out 0x10de4e (mulM64Effect 0x10de4e 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[7061, 65]
    (.letOp (n := 7065) (.exec 0x10de4e (LoadPre 0x10de4e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10de4e + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10de4e 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[7061, 65]
    (.letOp (n := 7066) (.exec 0x10de53 (StorePre 0x10de53 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10de53 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10de53 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[7064, 65]
    (.letOp (n := 7067) (.exec 0x10de58 (StorePre 0x10de58 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10de58 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10de58 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[7063, 65]
    (.letOp (n := 7068) (.out 0x10de60 (movR64M64Effect 0x10de60 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 7069) (.exec 0x10de60 (LoadPre 0x10de60 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10de60 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10de60 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 7070) (.out 0x10de65 (mulM64Effect 0x10de65 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[7068, 65]
    (.letOp (n := 7071) (.out 0x10de65 (mulM64Effect 0x10de65 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[7068, 65]
    (.letOp (n := 7072) (.exec 0x10de65 (LoadPre 0x10de65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10de65 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10de65 5 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[7068, 65]
    (.letOp (n := 7073) (.out 0x10de6a (movR64R64Effect 0x10de6a 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[7070]
    (.letOp (n := 7074) (.exec 0x10de6a (fun s => s.RIP = 0x10de6a) (movR64R64Effect 0x10de6a 13 0) (Reg.operands [.gpr 0] [])) #v[7070]
    (.letOp (n := 7075) (.out 0x10de6d (movR64R64Effect 0x10de6d 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[7071]
    (.letOp (n := 7076) (.exec 0x10de6d (fun s => s.RIP = 0x10de6d) (movR64R64Effect 0x10de6d 9 2) (Reg.operands [.gpr 2] [])) #v[7071]
    (.letOp (n := 7077) (.out 0x10de70 (andR64R64Effect 0x10de70 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[7037, 7018]
    (.letOp (n := 7078) (.exec 0x10de70 (fun s => s.RIP = 0x10de70) (andR64R64Effect 0x10de70 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[7037, 7018]
    (.letOp (n := 7079) (.out 0x10de73 (movR64M64Effect 0x10de73 0 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 7080) (.exec 0x10de73 (LoadPre 0x10de73 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10de73 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10de73 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 7081) (.out 0x10de7b (mulM64Effect 0x10de7b 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[7079, 65]
    (.letOp (n := 7082) (.out 0x10de7b (mulM64Effect 0x10de7b 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[7079, 65]
    (.letOp (n := 7083) (.exec 0x10de7b (LoadPre 0x10de7b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10de7b + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10de7b 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[7079, 65]
    (.letOp (n := 7084) (.out 0x10de80 (movR64R64Effect 0x10de80 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[7082]
    (.letOp (n := 7085) (.exec 0x10de80 (fun s => s.RIP = 0x10de80) (movR64R64Effect 0x10de80 6 2) (Reg.operands [.gpr 2] [])) #v[7082]
    (.letOp (n := 7086) (.out 0x10de83 (movR64R64Effect 0x10de83 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[7081]
    (.letOp (n := 7087) (.exec 0x10de83 (fun s => s.RIP = 0x10de83) (movR64R64Effect 0x10de83 7 0) (Reg.operands [.gpr 0] [])) #v[7081]
    (.letOp (n := 7088) (.out 0x10de86 (movR64M64Effect 0x10de86 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 7089) (.exec 0x10de86 (LoadPre 0x10de86 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10de86 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10de86 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 7090) (.out 0x10de8e (mulM64Effect 0x10de8e 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[7088, 65]
    (.letOp (n := 7091) (.out 0x10de8e (mulM64Effect 0x10de8e 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[7088, 65]
    (.letOp (n := 7092) (.exec 0x10de8e (LoadPre 0x10de8e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10de8e + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x10de8e 4 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[7088, 65]
    (.letOp (n := 7093) (.out 0x10de92 (movR64R64Effect 0x10de92 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[7091]
    (.letOp (n := 7094) (.exec 0x10de92 (fun s => s.RIP = 0x10de92) (movR64R64Effect 0x10de92 3 2) (Reg.operands [.gpr 2] [])) #v[7091]
    (.letOp (n := 7095) (.out 0x10de95 (movR64R64Effect 0x10de95 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[7090]
    (.letOp (n := 7096) (.exec 0x10de95 (fun s => s.RIP = 0x10de95) (movR64R64Effect 0x10de95 8 0) (Reg.operands [.gpr 0] [])) #v[7090]
    (.letOp (n := 7097) (.out 0x10de98 (addR64R64Effect 0x10de98 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[7095, 7086]
    (.letOp (n := 7098) (.out 0x10de98 (addR64R64Effect 0x10de98 8 7) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 7] []) (.flag .CF)) #v[7095, 7086]
    (.letOp (n := 7099) (.exec 0x10de98 (fun s => s.RIP = 0x10de98) (addR64R64Effect 0x10de98 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[7095, 7086]
    (b_l10a410_167)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_166 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84,
    0x24, 0x20, 0x01, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x20, 0x48, 0x89, 0x54, 0x24, 0x20, 0x48,
    0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x60, 0x48, 0xF7, 0x64, 0x24,
    0x18, 0x49, 0x89, 0xC5, 0x49, 0x89, 0xD1, 0x49, 0x21, 0xFA, 0x48, 0x8B, 0x84, 0x24, 0xE8, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x08, 0x48, 0x89, 0xD6, 0x48, 0x89, 0xC7, 0x48, 0x8B, 0x84,
    0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0xF7, 0x24, 0x24, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC0, 0x49,
    0x01, 0xF8] ++ bytes_l10a410_167

theorem code_l10a410_166 : ∀ x ∈ codeRange 0x10de39 bytes_l10a410_166, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xde39 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_167

def b_l10a410_165 : Block Op Label signature Reg.count 7014 :=
  .letOp (n := 7014) (.out 0x10ddde (atFlags StatusFlags.CF (adcR64R64Effect 0x10ddde 5 8)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[7009, 6928, 7012]
    (.letOp (n := 7015) (.exec 0x10ddde (fun s => s.RIP = 0x10ddde) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ddde 5 8)) (Reg.operands [.gpr 5, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[7009, 6928, 7012]
    (.letOp (n := 7016) (.out 0x10dde1 (movR64R64Effect 0x10dde1 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[7011]
    (.letOp (n := 7017) (.exec 0x10dde1 (fun s => s.RIP = 0x10dde1) (movR64R64Effect 0x10dde1 0 6) (Reg.operands [.gpr 6] [])) #v[7011]
    (.letOp (n := 7018) (.out 0x10dde4 (movR64Imm64Effect 0x10dde4 7 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 7019) (.exec 0x10dde4 (fun s => s.RIP = 0x10dde4) (movR64Imm64Effect 0x10dde4 7 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 7020) (.out 0x10ddee (andR64R64Effect 0x10ddee 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[7016, 7018]
    (.letOp (n := 7021) (.exec 0x10ddee (fun s => s.RIP = 0x10ddee) (andR64R64Effect 0x10ddee 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[7016, 7018]
    (.letOp (n := 7022) (.out 0x10ddf1 (movR64Imm64Effect 0x10ddf1 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 7023) (.exec 0x10ddf1 (fun s => s.RIP = 0x10ddf1) (movR64Imm64Effect 0x10ddf1 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 7024) (.out 0x10ddfb (mulR64Effect 0x10ddfb 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[7022, 7020]
    (.letOp (n := 7025) (.out 0x10ddfb (mulR64Effect 0x10ddfb 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[7022, 7020]
    (.letOp (n := 7026) (.exec 0x10ddfb (fun s => s.RIP = 0x10ddfb) (mulR64Effect 0x10ddfb 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[7022, 7020]
    (.letOp (n := 7027) (.out 0x10ddfe (addR64M64Effect 0x10ddfe 10 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[6964, 65]
    (.letOp (n := 7028) (.out 0x10ddfe (addR64M64Effect 0x10ddfe 10 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[6964, 65]
    (.letOp (n := 7029) (.exec 0x10ddfe (LoadPre 0x10ddfe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10ddfe + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10ddfe 10 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[6964, 65]
    (.letOp (n := 7030) (.out 0x10de03 (atFlags StatusFlags.CF (adcR64M64Effect 0x10de03 12 (.sib 4 none 0 (.d8 0x78)))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 12))) #v[6962, 65, 7028]
    (.letOp (n := 7031) (.exec 0x10de03 (LoadPre 0x10de03 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10de03 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10de03 12 (.sib 4 none 0 (.d8 0x78)))) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6962, 65, 7028]
    (.letOp (n := 7032) (.out 0x10de08 (addR64R64Effect 0x10de08 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[7027, 7024]
    (.letOp (n := 7033) (.out 0x10de08 (addR64R64Effect 0x10de08 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[7027, 7024]
    (.letOp (n := 7034) (.exec 0x10de08 (fun s => s.RIP = 0x10de08) (addR64R64Effect 0x10de08 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[7027, 7024]
    (.letOp (n := 7035) (.out 0x10de0b (atFlags StatusFlags.CF (adcR64R64Effect 0x10de0b 12 2)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[7030, 7025, 7033]
    (.letOp (n := 7036) (.exec 0x10de0b (fun s => s.RIP = 0x10de0b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10de0b 12 2)) (Reg.operands [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[7030, 7025, 7033]
    (.letOp (n := 7037) (.out 0x10de0e (addR64R64Effect 0x10de0e 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[7032, 6946]
    (.letOp (n := 7038) (.out 0x10de0e (addR64R64Effect 0x10de0e 10 9) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 9] []) (.flag .CF)) #v[7032, 6946]
    (.letOp (n := 7039) (.exec 0x10de0e (fun s => s.RIP = 0x10de0e) (addR64R64Effect 0x10de0e 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[7032, 6946]
    (.letOp (n := 7040) (.out 0x10de11 (atFlags StatusFlags.CF (adcR64R64Effect 0x10de11 12 11)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[7035, 6944, 7038]
    (.letOp (n := 7041) (.exec 0x10de11 (fun s => s.RIP = 0x10de11) (atFlags StatusFlags.CF (adcR64R64Effect 0x10de11 12 11)) (Reg.operands [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[7035, 6944, 7038]
    (.letOp (n := 7042) (.out 0x10de14 (movR64R64Effect 0x10de14 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[7014]
    (.letOp (n := 7043) (.exec 0x10de14 (fun s => s.RIP = 0x10de14) (movR64R64Effect 0x10de14 1 5) (Reg.operands [.gpr 5] [])) #v[7014]
    (.letOp (n := 7044) (.out 0x10de17 (shldR64R64Effect 0x10de17 5 5 6 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[7014, 7011]
    (.letOp (n := 7045) (.exec 0x10de17 (fun s => s.RIP = 0x10de17) (shldR64R64Effect 0x10de17 5 5 6 12) (Reg.operands [.gpr 5, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7014, 7011]
    (.letOp (n := 7046) (.out 0x10de1c (shrR64Effect 0x10de1c 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[7042]
    (.letOp (n := 7047) (.exec 0x10de1c (fun s => s.RIP = 0x10de1c) (shrR64Effect 0x10de1c 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7042]
    (.letOp (n := 7048) (.out 0x10de20 (movR64R64Effect 0x10de20 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 12] []) (.reg (.gpr 11))) #v[7040]
    (.letOp (n := 7049) (.exec 0x10de20 (fun s => s.RIP = 0x10de20) (movR64R64Effect 0x10de20 11 12) (Reg.operands [.gpr 12] [])) #v[7040]
    (.letOp (n := 7050) (.out 0x10de23 (shrR64Effect 0x10de23 4 11 52) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[7048]
    (.letOp (n := 7051) (.exec 0x10de23 (fun s => s.RIP = 0x10de23) (shrR64Effect 0x10de23 4 11 52) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7048]
    (.letOp (n := 7052) (.out 0x10de27 (shldR64R64Effect 0x10de27 5 12 10 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[7040, 7037]
    (.letOp (n := 7053) (.exec 0x10de27 (fun s => s.RIP = 0x10de27) (shldR64R64Effect 0x10de27 5 12 10 12) (Reg.operands [.gpr 12, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7040, 7037]
    (.letOp (n := 7054) (.out 0x10de2c (movR64M64Effect 0x10de2c 0 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 7055) (.exec 0x10de2c (LoadPre 0x10de2c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10de2c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10de2c 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 7056) (.out 0x10de34 (mulM64Effect 0x10de34 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[7054, 65]
    (.letOp (n := 7057) (.out 0x10de34 (mulM64Effect 0x10de34 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[7054, 65]
    (.letOp (n := 7058) (.exec 0x10de34 (LoadPre 0x10de34 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10de34 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10de34 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[7054, 65]
    (b_l10a410_166)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_165 : List UInt8 :=
  [0x4C, 0x11, 0xC5, 0x48, 0x89, 0xF0, 0x48, 0xBF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x48, 0x21, 0xF8, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1,
    0x4C, 0x03, 0x54, 0x24, 0x70, 0x4C, 0x13, 0x64, 0x24, 0x78, 0x49, 0x01, 0xC2, 0x49, 0x11, 0xD4,
    0x4D, 0x01, 0xCA, 0x4D, 0x11, 0xDC, 0x48, 0x89, 0xE9, 0x48, 0x0F, 0xA4, 0xF5, 0x0C, 0x48, 0xC1,
    0xE9, 0x34, 0x4D, 0x89, 0xE3, 0x49, 0xC1, 0xEB, 0x34, 0x4D, 0x0F, 0xA4, 0xD4, 0x0C, 0x48, 0x8B,
    0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x40] ++ bytes_l10a410_166

theorem code_l10a410_165 : ∀ x ∈ codeRange 0x10ddde bytes_l10a410_165, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xddde 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_166

def b_l10a410_164 : Block Op Label signature Reg.count 6971 :=
  .letOp (n := 6971) (.out 0x10dd83 (movR64R64Effect 0x10dd83 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[6968]
    (.letOp (n := 6972) (.exec 0x10dd83 (fun s => s.RIP = 0x10dd83) (movR64R64Effect 0x10dd83 7 0) (Reg.operands [.gpr 0] [])) #v[6968]
    (.letOp (n := 6973) (.out 0x10dd86 (movR64R64Effect 0x10dd86 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[6969]
    (.letOp (n := 6974) (.exec 0x10dd86 (fun s => s.RIP = 0x10dd86) (movR64R64Effect 0x10dd86 1 2) (Reg.operands [.gpr 2] [])) #v[6969]
    (.letOp (n := 6975) (.out 0x10dd89 (movR64Imm64Effect 0x10dd89 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 6976) (.exec 0x10dd89 (fun s => s.RIP = 0x10dd89) (movR64Imm64Effect 0x10dd89 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 6977) (.out 0x10dd93 (andR64R64Effect 0x10dd93 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[6948, 6975]
    (.letOp (n := 6978) (.exec 0x10dd93 (fun s => s.RIP = 0x10dd93) (andR64R64Effect 0x10dd93 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[6948, 6975]
    (.letOp (n := 6979) (.exec 0x10dd96 (StorePre 0x10dd96 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10dd96 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10dd96 6 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6977, 65]
    (.letOp (n := 6980) (.out 0x10dd9e (movR64M64Effect 0x10dd9e 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6981) (.exec 0x10dd9e (LoadPre 0x10dd9e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10dd9e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dd9e 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6982) (.out 0x10dda6 (mulR64Effect 0x10dda6 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[6869, 6980]
    (.letOp (n := 6983) (.out 0x10dda6 (mulR64Effect 0x10dda6 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[6869, 6980]
    (.letOp (n := 6984) (.exec 0x10dda6 (fun s => s.RIP = 0x10dda6) (mulR64Effect 0x10dda6 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[6869, 6980]
    (.letOp (n := 6985) (.out 0x10dda9 (movR64R64Effect 0x10dda9 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[6983]
    (.letOp (n := 6986) (.exec 0x10dda9 (fun s => s.RIP = 0x10dda9) (movR64R64Effect 0x10dda9 5 2) (Reg.operands [.gpr 2] [])) #v[6983]
    (.letOp (n := 6987) (.out 0x10ddac (movR64R64Effect 0x10ddac 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[6982]
    (.letOp (n := 6988) (.exec 0x10ddac (fun s => s.RIP = 0x10ddac) (movR64R64Effect 0x10ddac 3 0) (Reg.operands [.gpr 0] [])) #v[6982]
    (.letOp (n := 6989) (.out 0x10ddaf (movR64M64Effect 0x10ddaf 0 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6990) (.exec 0x10ddaf (LoadPre 0x10ddaf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10ddaf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ddaf 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6991) (.out 0x10ddb7 (mulM64Effect 0x10ddb7 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6989, 65]
    (.letOp (n := 6992) (.out 0x10ddb7 (mulM64Effect 0x10ddb7 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6989, 65]
    (.letOp (n := 6993) (.exec 0x10ddb7 (LoadPre 0x10ddb7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10ddb7 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x10ddb7 4 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6989, 65]
    (.letOp (n := 6994) (.out 0x10ddbb (movR64R64Effect 0x10ddbb 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[6991]
    (.letOp (n := 6995) (.exec 0x10ddbb (fun s => s.RIP = 0x10ddbb) (movR64R64Effect 0x10ddbb 6 0) (Reg.operands [.gpr 0] [])) #v[6991]
    (.letOp (n := 6996) (.out 0x10ddbe (addR64R64Effect 0x10ddbe 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[6994, 6987]
    (.letOp (n := 6997) (.out 0x10ddbe (addR64R64Effect 0x10ddbe 6 3) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 3] []) (.flag .CF)) #v[6994, 6987]
    (.letOp (n := 6998) (.exec 0x10ddbe (fun s => s.RIP = 0x10ddbe) (addR64R64Effect 0x10ddbe 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6994, 6987]
    (.letOp (n := 6999) (.out 0x10ddc1 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ddc1 5 2)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[6985, 6992, 6997]
    (.letOp (n := 7000) (.exec 0x10ddc1 (fun s => s.RIP = 0x10ddc1) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ddc1 5 2)) (Reg.operands [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6985, 6992, 6997]
    (.letOp (n := 7001) (.out 0x10ddc4 (movR64M64Effect 0x10ddc4 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 7002) (.exec 0x10ddc4 (LoadPre 0x10ddc4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10ddc4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ddc4 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 7003) (.out 0x10ddc9 (movR64M64Effect 0x10ddc9 2 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 7004) (.exec 0x10ddc9 (LoadPre 0x10ddc9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x10ddc9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ddc9 2 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 7005) (.exec 0x10ddd1 (StorePre 0x10ddd1 4 (fun s => AddrMode.addr (.base 2 (.d8 0x28)) s (0x10ddd1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10ddd1 0 (.base 2 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 2] [])) #v[7001, 7003]
    (.letOp (n := 7006) (.out 0x10ddd5 (addR64R64Effect 0x10ddd5 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[6996, 6971]
    (.letOp (n := 7007) (.out 0x10ddd5 (addR64R64Effect 0x10ddd5 6 7) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 7] []) (.flag .CF)) #v[6996, 6971]
    (.letOp (n := 7008) (.exec 0x10ddd5 (fun s => s.RIP = 0x10ddd5) (addR64R64Effect 0x10ddd5 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[6996, 6971]
    (.letOp (n := 7009) (.out 0x10ddd8 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ddd8 5 1)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[6999, 6973, 7007]
    (.letOp (n := 7010) (.exec 0x10ddd8 (fun s => s.RIP = 0x10ddd8) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ddd8 5 1)) (Reg.operands [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6999, 6973, 7007]
    (.letOp (n := 7011) (.out 0x10dddb (addR64R64Effect 0x10dddb 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[7006, 6918]
    (.letOp (n := 7012) (.out 0x10dddb (addR64R64Effect 0x10dddb 6 13) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 13] []) (.flag .CF)) #v[7006, 6918]
    (.letOp (n := 7013) (.exec 0x10dddb (fun s => s.RIP = 0x10dddb) (addR64R64Effect 0x10dddb 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[7006, 6918]
    (b_l10a410_165)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_164 : List UInt8 :=
  [0x48, 0x89, 0xC7, 0x48, 0x89, 0xD1, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x48, 0x21, 0xC6, 0x48, 0x89, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x08,
    0x01, 0x00, 0x00, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0xD5, 0x48, 0x89, 0xC3, 0x48, 0x8B, 0x84, 0x24,
    0x18, 0x01, 0x00, 0x00, 0x48, 0xF7, 0x24, 0x24, 0x48, 0x89, 0xC6, 0x48, 0x01, 0xDE, 0x48, 0x11,
    0xD5, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x94, 0x24, 0x80, 0x01, 0x00, 0x00, 0x48, 0x89,
    0x42, 0x28, 0x48, 0x01, 0xFE, 0x48, 0x11, 0xCD, 0x4C, 0x01, 0xEE] ++ bytes_l10a410_165

theorem code_l10a410_164 : ∀ x ∈ codeRange 0x10dd83 bytes_l10a410_164, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xdd83 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_165

def b_l10a410_163 : Block Op Label signature Reg.count 6928 :=
  .letOp (n := 6928) (.out 0x10dd29 (shrR64Effect 0x10dd29 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[6916]
    (.letOp (n := 6929) (.exec 0x10dd29 (fun s => s.RIP = 0x10dd29) (shrR64Effect 0x10dd29 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6916]
    (.letOp (n := 6930) (.out 0x10dd2d (movR64Imm64Effect 0x10dd2d 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 6931) (.exec 0x10dd2d (fun s => s.RIP = 0x10dd2d) (movR64Imm64Effect 0x10dd2d 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 6932) (.out 0x10dd37 (mulR64Effect 0x10dd37 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[6930, 6926]
    (.letOp (n := 6933) (.out 0x10dd37 (mulR64Effect 0x10dd37 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[6930, 6926]
    (.letOp (n := 6934) (.exec 0x10dd37 (fun s => s.RIP = 0x10dd37) (mulR64Effect 0x10dd37 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[6930, 6926]
    (.letOp (n := 6935) (.out 0x10dd3a (movR64R64Effect 0x10dd3a 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[6933]
    (.letOp (n := 6936) (.exec 0x10dd3a (fun s => s.RIP = 0x10dd3a) (movR64R64Effect 0x10dd3a 9 2) (Reg.operands [.gpr 2] [])) #v[6933]
    (.letOp (n := 6937) (.out 0x10dd3d (addR64M64Effect 0x10dd3d 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6932, 65]
    (.letOp (n := 6938) (.out 0x10dd3d (addR64M64Effect 0x10dd3d 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[6932, 65]
    (.letOp (n := 6939) (.exec 0x10dd3d (LoadPre 0x10dd3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10dd3d + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10dd3d 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6932, 65]
    (.letOp (n := 6940) (.out 0x10dd42 (atFlags StatusFlags.CF (adcR64M64Effect 0x10dd42 9 (.sib 4 none 0 (.d8 0x78)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[6935, 65, 6938]
    (.letOp (n := 6941) (.exec 0x10dd42 (LoadPre 0x10dd42 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10dd42 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10dd42 9 (.sib 4 none 0 (.d8 0x78)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6935, 65, 6938]
    (.letOp (n := 6942) (.out 0x10dd47 (movR64R64Effect 0x10dd47 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[6940]
    (.letOp (n := 6943) (.exec 0x10dd47 (fun s => s.RIP = 0x10dd47) (movR64R64Effect 0x10dd47 11 9) (Reg.operands [.gpr 9] [])) #v[6940]
    (.letOp (n := 6944) (.out 0x10dd4a (shrR64Effect 0x10dd4a 4 11 52) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[6942]
    (.letOp (n := 6945) (.exec 0x10dd4a (fun s => s.RIP = 0x10dd4a) (shrR64Effect 0x10dd4a 4 11 52) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6942]
    (.letOp (n := 6946) (.out 0x10dd4e (shldR64R64Effect 0x10dd4e 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[6940, 6937]
    (.letOp (n := 6947) (.exec 0x10dd4e (fun s => s.RIP = 0x10dd4e) (shldR64R64Effect 0x10dd4e 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6940, 6937]
    (.letOp (n := 6948) (.out 0x10dd53 (movR64R64Effect 0x10dd53 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[6937]
    (.letOp (n := 6949) (.exec 0x10dd53 (fun s => s.RIP = 0x10dd53) (movR64R64Effect 0x10dd53 6 0) (Reg.operands [.gpr 0] [])) #v[6937]
    (.letOp (n := 6950) (.out 0x10dd56 (movR64R64Effect 0x10dd56 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[6878]
    (.letOp (n := 6951) (.exec 0x10dd56 (fun s => s.RIP = 0x10dd56) (movR64R64Effect 0x10dd56 0 1) (Reg.operands [.gpr 1] [])) #v[6878]
    (.letOp (n := 6952) (.out 0x10dd59 (mulR64Effect 0x10dd59 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[6841, 6950]
    (.letOp (n := 6953) (.out 0x10dd59 (mulR64Effect 0x10dd59 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[6841, 6950]
    (.letOp (n := 6954) (.exec 0x10dd59 (fun s => s.RIP = 0x10dd59) (mulR64Effect 0x10dd59 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[6841, 6950]
    (.letOp (n := 6955) (.exec 0x10dd5c (StorePre 0x10dd5c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10dd5c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10dd5c 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6953, 65]
    (.letOp (n := 6956) (.exec 0x10dd61 (StorePre 0x10dd61 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10dd61 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10dd61 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6952, 65]
    (.letOp (n := 6957) (.out 0x10dd66 (movR64M64Effect 0x10dd66 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6958) (.exec 0x10dd66 (LoadPre 0x10dd66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10dd66 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10dd66 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6959) (.out 0x10dd6b (mulM64Effect 0x10dd6b 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6957, 65]
    (.letOp (n := 6960) (.out 0x10dd6b (mulM64Effect 0x10dd6b 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6957, 65]
    (.letOp (n := 6961) (.exec 0x10dd6b (LoadPre 0x10dd6b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10dd6b + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10dd6b 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6957, 65]
    (.letOp (n := 6962) (.out 0x10dd70 (movR64R64Effect 0x10dd70 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[6960]
    (.letOp (n := 6963) (.exec 0x10dd70 (fun s => s.RIP = 0x10dd70) (movR64R64Effect 0x10dd70 12 2) (Reg.operands [.gpr 2] [])) #v[6960]
    (.letOp (n := 6964) (.out 0x10dd73 (movR64R64Effect 0x10dd73 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[6959]
    (.letOp (n := 6965) (.exec 0x10dd73 (fun s => s.RIP = 0x10dd73) (movR64R64Effect 0x10dd73 10 0) (Reg.operands [.gpr 0] [])) #v[6959]
    (.letOp (n := 6966) (.out 0x10dd76 (movR64M64Effect 0x10dd76 0 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6967) (.exec 0x10dd76 (LoadPre 0x10dd76 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10dd76 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dd76 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6968) (.out 0x10dd7e (mulM64Effect 0x10dd7e 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6966, 65]
    (.letOp (n := 6969) (.out 0x10dd7e (mulM64Effect 0x10dd7e 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6966, 65]
    (.letOp (n := 6970) (.exec 0x10dd7e (LoadPre 0x10dd7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10dd7e + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10dd7e 5 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6966, 65]
    (b_l10a410_164)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_163 : List UInt8 :=
  [0x49, 0xC1, 0xE8, 0x34, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xE2, 0x49, 0x89, 0xD1, 0x48, 0x03, 0x44, 0x24, 0x70, 0x4C, 0x13, 0x4C, 0x24, 0x78, 0x4D, 0x89,
    0xCB, 0x49, 0xC1, 0xEB, 0x34, 0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xC6, 0x48, 0x89, 0xC8,
    0x49, 0xF7, 0xE2, 0x48, 0x89, 0x54, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x70, 0x48, 0x8B, 0x44,
    0x24, 0x60, 0x48, 0xF7, 0x64, 0x24, 0x20, 0x49, 0x89, 0xD4, 0x49, 0x89, 0xC2, 0x48, 0x8B, 0x84,
    0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x18] ++ bytes_l10a410_164

theorem code_l10a410_163 : ∀ x ∈ codeRange 0x10dd29 bytes_l10a410_163, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xdd29 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_164

def b_l10a410_162 : Block Op Label signature Reg.count 6888 :=
  .letOp (n := 6888) (.out 0x10dcc7 (atFlags StatusFlags.CF (adcR64R64Effect 0x10dcc7 13 2)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[6874, 6883, 6886]
    (.letOp (n := 6889) (.exec 0x10dcc7 (fun s => s.RIP = 0x10dcc7) (atFlags StatusFlags.CF (adcR64R64Effect 0x10dcc7 13 2)) (Reg.operands [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6874, 6883, 6886]
    (.letOp (n := 6890) (.out 0x10dcca (movR64M64Effect 0x10dcca 2 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 6891) (.exec 0x10dcca (LoadPre 0x10dcca (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x10dcca + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dcca 2 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6892) (.out 0x10dcd2 (movR64M64Effect 0x10dcd2 9 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 6893) (.exec 0x10dcd2 (LoadPre 0x10dcd2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10dcd2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dcd2 9 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6894) (.exec 0x10dcda (StorePre 0x10dcda 4 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x10dcda + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10dcda 9 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 2] [])) #v[6892, 6890]
    (.letOp (n := 6895) (.out 0x10dcde (addR64R64Effect 0x10dcde 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[6885, 6861]
    (.letOp (n := 6896) (.out 0x10dcde (addR64R64Effect 0x10dcde 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[6885, 6861]
    (.letOp (n := 6897) (.exec 0x10dcde (fun s => s.RIP = 0x10dcde) (addR64R64Effect 0x10dcde 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[6885, 6861]
    (.letOp (n := 6898) (.out 0x10dce1 (atFlags StatusFlags.CF (adcR64R64Effect 0x10dce1 13 8)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[6888, 6863, 6896]
    (.letOp (n := 6899) (.exec 0x10dce1 (fun s => s.RIP = 0x10dce1) (atFlags StatusFlags.CF (adcR64R64Effect 0x10dce1 13 8)) (Reg.operands [.gpr 13, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6888, 6863, 6896]
    (.letOp (n := 6900) (.out 0x10dce4 (movR64M64Effect 0x10dce4 7 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 6901) (.exec 0x10dce4 (LoadPre 0x10dce4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10dce4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dce4 7 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6902) (.exec 0x10dcec (StorePre 0x10dcec 4 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x10dcec + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10dcec 7 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[6900, 6890]
    (.letOp (n := 6903) (.out 0x10dcf0 (addR64R64Effect 0x10dcf0 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[6895, 6854]
    (.letOp (n := 6904) (.out 0x10dcf0 (addR64R64Effect 0x10dcf0 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[6895, 6854]
    (.letOp (n := 6905) (.exec 0x10dcf0 (fun s => s.RIP = 0x10dcf0) (addR64R64Effect 0x10dcf0 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[6895, 6854]
    (.letOp (n := 6906) (.out 0x10dcf3 (atFlags StatusFlags.CF (adcR64M64Effect 0x10dcf3 13 (.sib 4 none 0 (.d32 0xb0)))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 13))) #v[6898, 65, 6904]
    (.letOp (n := 6907) (.exec 0x10dcf3 (LoadPre 0x10dcf3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10dcf3 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10dcf3 13 (.sib 4 none 0 (.d32 0xb0)))) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6898, 65, 6904]
    (.letOp (n := 6908) (.out 0x10dcfb (movR64M64Effect 0x10dcfb 6 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 6909) (.exec 0x10dcfb (LoadPre 0x10dcfb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10dcfb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dcfb 6 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6910) (.exec 0x10dd03 (StorePre 0x10dd03 4 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x10dd03 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10dd03 6 (.base 2 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6908, 6890]
    (.letOp (n := 6911) (.out 0x10dd07 (addR64R64Effect 0x10dd07 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[6903, 6831]
    (.letOp (n := 6912) (.out 0x10dd07 (addR64R64Effect 0x10dd07 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[6903, 6831]
    (.letOp (n := 6913) (.exec 0x10dd07 (fun s => s.RIP = 0x10dd07) (addR64R64Effect 0x10dd07 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[6903, 6831]
    (.letOp (n := 6914) (.out 0x10dd0a (atFlags StatusFlags.CF (adcR64R64Effect 0x10dd0a 13 5)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[6906, 6833, 6912]
    (.letOp (n := 6915) (.exec 0x10dd0a (fun s => s.RIP = 0x10dd0a) (atFlags StatusFlags.CF (adcR64R64Effect 0x10dd0a 13 5)) (Reg.operands [.gpr 13, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6906, 6833, 6912]
    (.letOp (n := 6916) (.out 0x10dd0d (movR64R64Effect 0x10dd0d 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 13] []) (.reg (.gpr 8))) #v[6914]
    (.letOp (n := 6917) (.exec 0x10dd0d (fun s => s.RIP = 0x10dd0d) (movR64R64Effect 0x10dd0d 8 13) (Reg.operands [.gpr 13] [])) #v[6914]
    (.letOp (n := 6918) (.out 0x10dd10 (shldR64R64Effect 0x10dd10 5 13 0 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[6914, 6911]
    (.letOp (n := 6919) (.exec 0x10dd10 (fun s => s.RIP = 0x10dd10) (shldR64R64Effect 0x10dd10 5 13 0 12) (Reg.operands [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6914, 6911]
    (.letOp (n := 6920) (.out 0x10dd15 (shlR64Effect 0x10dd15 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[6911]
    (.letOp (n := 6921) (.exec 0x10dd15 (fun s => s.RIP = 0x10dd15) (shlR64Effect 0x10dd15 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6911]
    (.letOp (n := 6922) (.out 0x10dd19 (movR64Imm64Effect 0x10dd19 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 6923) (.exec 0x10dd19 (fun s => s.RIP = 0x10dd19) (movR64Imm64Effect 0x10dd19 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 6924) (.out 0x10dd23 (andR64R64Effect 0x10dd23 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[6920, 6922]
    (.letOp (n := 6925) (.exec 0x10dd23 (fun s => s.RIP = 0x10dd23) (andR64R64Effect 0x10dd23 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[6920, 6922]
    (.letOp (n := 6926) (.out 0x10dd26 (orR64R64Effect 0x10dd26 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[6924, 6865]
    (.letOp (n := 6927) (.exec 0x10dd26 (fun s => s.RIP = 0x10dd26) (orR64R64Effect 0x10dd26 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[6924, 6865]
    (b_l10a410_163))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_162 : List UInt8 :=
  [0x49, 0x11, 0xD5, 0x48, 0x8B, 0x94, 0x24, 0x80, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x8C, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x4C, 0x89, 0x4A, 0x10, 0x48, 0x01, 0xF8, 0x4D, 0x11, 0xC5, 0x48, 0x8B, 0xBC,
    0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x7A, 0x18, 0x48, 0x01, 0xF0, 0x4C, 0x13, 0xAC, 0x24,
    0xB0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xB4, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x72, 0x20,
    0x4C, 0x01, 0xE0, 0x49, 0x11, 0xED, 0x4D, 0x89, 0xE8, 0x49, 0x0F, 0xA4, 0xC5, 0x0C, 0x48, 0xC1,
    0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x4C,
    0x09, 0xD8] ++ bytes_l10a410_163

theorem code_l10a410_162 : ∀ x ∈ codeRange 0x10dcc7 bytes_l10a410_162, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xdcc7 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_163

def b_l10a410_161 : Block Op Label signature Reg.count 6846 :=
  .letOp (n := 6846) (.exec 0x10dc6a (StorePre 0x10dc6a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10dc6a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10dc6a 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6844, 65]
    (.letOp (n := 6847) (.exec 0x10dc6f (StorePre 0x10dc6f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10dc6f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10dc6f 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6843, 65]
    (.letOp (n := 6848) (.out 0x10dc74 (movR64M64Effect 0x10dc74 0 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6849) (.exec 0x10dc74 (LoadPre 0x10dc74 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10dc74 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dc74 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6850) (.out 0x10dc7c (mulR64Effect 0x10dc7c 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[6735, 6848]
    (.letOp (n := 6851) (.out 0x10dc7c (mulR64Effect 0x10dc7c 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[6735, 6848]
    (.letOp (n := 6852) (.exec 0x10dc7c (fun s => s.RIP = 0x10dc7c) (mulR64Effect 0x10dc7c 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[6735, 6848]
    (.letOp (n := 6853) (.exec 0x10dc7f (StorePre 0x10dc7f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10dc7f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10dc7f 2 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6851, 65]
    (.letOp (n := 6854) (.out 0x10dc87 (movR64R64Effect 0x10dc87 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[6850]
    (.letOp (n := 6855) (.exec 0x10dc87 (fun s => s.RIP = 0x10dc87) (movR64R64Effect 0x10dc87 6 0) (Reg.operands [.gpr 0] [])) #v[6850]
    (.letOp (n := 6856) (.out 0x10dc8a (movR64M64Effect 0x10dc8a 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6857) (.exec 0x10dc8a (LoadPre 0x10dc8a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10dc8a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dc8a 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6858) (.out 0x10dc92 (mulR64Effect 0x10dc92 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[6744, 6856]
    (.letOp (n := 6859) (.out 0x10dc92 (mulR64Effect 0x10dc92 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[6744, 6856]
    (.letOp (n := 6860) (.exec 0x10dc92 (fun s => s.RIP = 0x10dc92) (mulR64Effect 0x10dc92 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[6744, 6856]
    (.letOp (n := 6861) (.out 0x10dc95 (movR64R64Effect 0x10dc95 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[6858]
    (.letOp (n := 6862) (.exec 0x10dc95 (fun s => s.RIP = 0x10dc95) (movR64R64Effect 0x10dc95 7 0) (Reg.operands [.gpr 0] [])) #v[6858]
    (.letOp (n := 6863) (.out 0x10dc98 (movR64R64Effect 0x10dc98 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[6859]
    (.letOp (n := 6864) (.exec 0x10dc98 (fun s => s.RIP = 0x10dc98) (movR64R64Effect 0x10dc98 8 2) (Reg.operands [.gpr 2] [])) #v[6859]
    (.letOp (n := 6865) (.out 0x10dc9b (andR32Imm8Effect 0x10dc9b 4 11 0xf) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[6837]
    (.letOp (n := 6866) (.exec 0x10dc9b (fun s => s.RIP = 0x10dc9b) (andR32Imm8Effect 0x10dc9b 4 11 0xf) (Reg.operands [.gpr 11] [])) #v[6837]
    (.letOp (n := 6867) (.out 0x10dc9f (movR64M64Effect 0x10dc9f 0 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6868) (.exec 0x10dc9f (LoadPre 0x10dc9f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10dc9f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dc9f 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6869) (.out 0x10dca7 (movR64M64Effect 0x10dca7 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 6870) (.exec 0x10dca7 (LoadPre 0x10dca7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10dca7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10dca7 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6871) (.out 0x10dcac (mulR64Effect 0x10dcac 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[6869, 6867]
    (.letOp (n := 6872) (.out 0x10dcac (mulR64Effect 0x10dcac 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[6869, 6867]
    (.letOp (n := 6873) (.exec 0x10dcac (fun s => s.RIP = 0x10dcac) (mulR64Effect 0x10dcac 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[6869, 6867]
    (.letOp (n := 6874) (.out 0x10dcaf (movR64R64Effect 0x10dcaf 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[6872]
    (.letOp (n := 6875) (.exec 0x10dcaf (fun s => s.RIP = 0x10dcaf) (movR64R64Effect 0x10dcaf 13 2) (Reg.operands [.gpr 2] [])) #v[6872]
    (.letOp (n := 6876) (.out 0x10dcb2 (movR64R64Effect 0x10dcb2 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[6871]
    (.letOp (n := 6877) (.exec 0x10dcb2 (fun s => s.RIP = 0x10dcb2) (movR64R64Effect 0x10dcb2 9 0) (Reg.operands [.gpr 0] [])) #v[6871]
    (.letOp (n := 6878) (.out 0x10dcb5 (movR64M64Effect 0x10dcb5 1 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 6879) (.exec 0x10dcb5 (LoadPre 0x10dcb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10dcb5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dcb5 1 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6880) (.out 0x10dcbd (movR64R64Effect 0x10dcbd 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[6878]
    (.letOp (n := 6881) (.exec 0x10dcbd (fun s => s.RIP = 0x10dcbd) (movR64R64Effect 0x10dcbd 0 1) (Reg.operands [.gpr 1] [])) #v[6878]
    (.letOp (n := 6882) (.out 0x10dcc0 (mulM64Effect 0x10dcc0 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6880, 65]
    (.letOp (n := 6883) (.out 0x10dcc0 (mulM64Effect 0x10dcc0 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6880, 65]
    (.letOp (n := 6884) (.exec 0x10dcc0 (LoadPre 0x10dcc0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10dcc0 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x10dcc0 4 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6880, 65]
    (.letOp (n := 6885) (.out 0x10dcc4 (addR64R64Effect 0x10dcc4 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[6882, 6876]
    (.letOp (n := 6886) (.out 0x10dcc4 (addR64R64Effect 0x10dcc4 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[6882, 6876]
    (.letOp (n := 6887) (.exec 0x10dcc4 (fun s => s.RIP = 0x10dcc4) (addR64R64Effect 0x10dcc4 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[6882, 6876]
    (b_l10a410_162))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_161 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x70, 0x48, 0x8B, 0x84, 0x24, 0xE8, 0x00,
    0x00, 0x00, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC6,
    0x48, 0x8B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xC7, 0x49, 0x89,
    0xD0, 0x41, 0x83, 0xE3, 0x0F, 0x48, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x5C,
    0x24, 0x08, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD5, 0x49, 0x89, 0xC1, 0x48, 0x8B, 0x8C, 0x24, 0x20,
    0x01, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0x24, 0x24, 0x4C, 0x01, 0xC8] ++ bytes_l10a410_162

theorem code_l10a410_161 : ∀ x ∈ codeRange 0x10dc6a bytes_l10a410_161, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xdc6a 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_162

def b_l10a410_160 : Block Op Label signature Reg.count 6804 :=
  .letOp (n := 6804) (.out 0x10dc11 (atFlags StatusFlags.CF (adcR64M64Effect 0x10dc11 12 (.sib 4 none 0 (.d32 0xb0)))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 12))) #v[6799, 65, 6802]
    (.letOp (n := 6805) (.exec 0x10dc11 (LoadPre 0x10dc11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10dc11 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10dc11 12 (.sib 4 none 0 (.d32 0xb0)))) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6799, 65, 6802]
    (.letOp (n := 6806) (.out 0x10dc19 (addR64M64Effect 0x10dc19 15 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[6801, 65]
    (.letOp (n := 6807) (.out 0x10dc19 (addR64M64Effect 0x10dc19 15 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[6801, 65]
    (.letOp (n := 6808) (.exec 0x10dc19 (LoadPre 0x10dc19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10dc19 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10dc19 15 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[6801, 65]
    (.letOp (n := 6809) (.out 0x10dc1e (atFlags StatusFlags.CF (adcR64M64Effect 0x10dc1e 12 (.sib 4 none 0 (.d8 0x78)))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 12))) #v[6804, 65, 6807]
    (.letOp (n := 6810) (.exec 0x10dc1e (LoadPre 0x10dc1e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10dc1e + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10dc1e 12 (.sib 4 none 0 (.d8 0x78)))) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6804, 65, 6807]
    (.letOp (n := 6811) (.out 0x10dc23 (addR64R64Effect 0x10dc23 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[6806, 6780]
    (.letOp (n := 6812) (.out 0x10dc23 (addR64R64Effect 0x10dc23 15 0) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 0] []) (.flag .CF)) #v[6806, 6780]
    (.letOp (n := 6813) (.exec 0x10dc23 (fun s => s.RIP = 0x10dc23) (addR64R64Effect 0x10dc23 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[6806, 6780]
    (.letOp (n := 6814) (.out 0x10dc26 (atFlags StatusFlags.CF (adcR64R64Effect 0x10dc26 12 10)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[6809, 6783, 6812]
    (.letOp (n := 6815) (.exec 0x10dc26 (fun s => s.RIP = 0x10dc26) (atFlags StatusFlags.CF (adcR64R64Effect 0x10dc26 12 10)) (Reg.operands [.gpr 12, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6809, 6783, 6812]
    (.letOp (n := 6816) (.out 0x10dc29 (movR64M64Effect 0x10dc29 9 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 6817) (.exec 0x10dc29 (LoadPre 0x10dc29 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x10dc29 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dc29 9 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6818) (.out 0x10dc31 (movR64M64Effect 0x10dc31 0 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6819) (.exec 0x10dc31 (LoadPre 0x10dc31 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10dc31 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dc31 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6820) (.exec 0x10dc39 (StorePre 0x10dc39 3 (fun s => AddrMode.addr (.base 9 .none) s (0x10dc39 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10dc39 0 (.base 9 .none)) (Reg.operands [.gpr 0, .gpr 9] [])) #v[6818, 6816]
    (.letOp (n := 6821) (.out 0x10dc3c (addR64R64Effect 0x10dc3c 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[6811, 6787]
    (.letOp (n := 6822) (.out 0x10dc3c (addR64R64Effect 0x10dc3c 15 2) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 2] []) (.flag .CF)) #v[6811, 6787]
    (.letOp (n := 6823) (.exec 0x10dc3c (fun s => s.RIP = 0x10dc3c) (addR64R64Effect 0x10dc3c 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[6811, 6787]
    (.letOp (n := 6824) (.out 0x10dc3f (atFlags StatusFlags.CF (adcR64R64Effect 0x10dc3f 12 1)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[6814, 6789, 6822]
    (.letOp (n := 6825) (.exec 0x10dc3f (fun s => s.RIP = 0x10dc3f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10dc3f 12 1)) (Reg.operands [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6814, 6789, 6822]
    (.letOp (n := 6826) (.out 0x10dc42 (movR64M64Effect 0x10dc42 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6827) (.exec 0x10dc42 (LoadPre 0x10dc42 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10dc42 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dc42 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6828) (.exec 0x10dc4a (StorePre 0x10dc4a 4 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x10dc4a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10dc4a 0 (.base 9 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 9] [])) #v[6826, 6816]
    (.letOp (n := 6829) (.out 0x10dc4e (movR64R64Effect 0x10dc4e 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 12] []) (.reg (.gpr 5))) #v[6824]
    (.letOp (n := 6830) (.exec 0x10dc4e (fun s => s.RIP = 0x10dc4e) (movR64R64Effect 0x10dc4e 5 12) (Reg.operands [.gpr 12] [])) #v[6824]
    (.letOp (n := 6831) (.out 0x10dc51 (shldR64R64Effect 0x10dc51 5 12 15 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[6824, 6821]
    (.letOp (n := 6832) (.exec 0x10dc51 (fun s => s.RIP = 0x10dc51) (shldR64R64Effect 0x10dc51 5 12 15 12) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6824, 6821]
    (.letOp (n := 6833) (.out 0x10dc56 (shrR64Effect 0x10dc56 4 5 52) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[6829]
    (.letOp (n := 6834) (.exec 0x10dc56 (fun s => s.RIP = 0x10dc56) (shrR64Effect 0x10dc56 4 5 52) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6829]
    (.letOp (n := 6835) (.out 0x10dc5a (movR64R64Effect 0x10dc5a 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 15] []) (.reg (.gpr 11))) #v[6821]
    (.letOp (n := 6836) (.exec 0x10dc5a (fun s => s.RIP = 0x10dc5a) (movR64R64Effect 0x10dc5a 11 15) (Reg.operands [.gpr 15] [])) #v[6821]
    (.letOp (n := 6837) (.out 0x10dc5d (shrR64Effect 0x10dc5d 4 11 48) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[6835]
    (.letOp (n := 6838) (.exec 0x10dc5d (fun s => s.RIP = 0x10dc5d) (shrR64Effect 0x10dc5d 4 11 48) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6835]
    (.letOp (n := 6839) (.out 0x10dc61 (movR64R64Effect 0x10dc61 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6761]
    (.letOp (n := 6840) (.exec 0x10dc61 (fun s => s.RIP = 0x10dc61) (movR64R64Effect 0x10dc61 0 6) (Reg.operands [.gpr 6] [])) #v[6761]
    (.letOp (n := 6841) (.out 0x10dc64 (movR64R64Effect 0x10dc64 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 13] []) (.reg (.gpr 10))) #v[6726]
    (.letOp (n := 6842) (.exec 0x10dc64 (fun s => s.RIP = 0x10dc64) (movR64R64Effect 0x10dc64 10 13) (Reg.operands [.gpr 13] [])) #v[6726]
    (.letOp (n := 6843) (.out 0x10dc67 (mulR64Effect 0x10dc67 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[6726, 6839]
    (.letOp (n := 6844) (.out 0x10dc67 (mulR64Effect 0x10dc67 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[6726, 6839]
    (.letOp (n := 6845) (.exec 0x10dc67 (fun s => s.RIP = 0x10dc67) (mulR64Effect 0x10dc67 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[6726, 6839]
    (b_l10a410_161))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_160 : List UInt8 :=
  [0x4C, 0x13, 0xA4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x03, 0x7C, 0x24, 0x70, 0x4C, 0x13, 0x64,
    0x24, 0x78, 0x49, 0x01, 0xC7, 0x4D, 0x11, 0xD4, 0x4C, 0x8B, 0x8C, 0x24, 0x80, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x49, 0x89, 0x01, 0x49, 0x01, 0xD7, 0x49, 0x11,
    0xCC, 0x48, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0x89, 0x41, 0x08, 0x4C, 0x89, 0xE5,
    0x4D, 0x0F, 0xA4, 0xFC, 0x0C, 0x48, 0xC1, 0xED, 0x34, 0x4D, 0x89, 0xFB, 0x49, 0xC1, 0xEB, 0x30,
    0x48, 0x89, 0xF0, 0x4D, 0x89, 0xEA, 0x49, 0xF7, 0xE5] ++ bytes_l10a410_161

theorem code_l10a410_160 : ∀ x ∈ codeRange 0x10dc11 bytes_l10a410_160, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xdc11 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_161

def b_l10a410_159 : Block Op Label signature Reg.count 6759 :=
  .letOp (n := 6759) (.out 0x10dbbc (movR64R64Effect 0x10dbbc 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[6754]
    (.letOp (n := 6760) (.exec 0x10dbbc (fun s => s.RIP = 0x10dbbc) (movR64R64Effect 0x10dbbc 3 0) (Reg.operands [.gpr 0] [])) #v[6754]
    (.letOp (n := 6761) (.out 0x10dbbf (movR64M64Effect 0x10dbbf 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 6762) (.exec 0x10dbbf (LoadPre 0x10dbbf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10dbbf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10dbbf 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6763) (.out 0x10dbc4 (movR64R64Effect 0x10dbc4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6761]
    (.letOp (n := 6764) (.exec 0x10dbc4 (fun s => s.RIP = 0x10dbc4) (movR64R64Effect 0x10dbc4 0 6) (Reg.operands [.gpr 6] [])) #v[6761]
    (.letOp (n := 6765) (.out 0x10dbc7 (mulM64Effect 0x10dbc7 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6763, 65]
    (.letOp (n := 6766) (.out 0x10dbc7 (mulM64Effect 0x10dbc7 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6763, 65]
    (.letOp (n := 6767) (.exec 0x10dbc7 (LoadPre 0x10dbc7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10dbc7 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x10dbc7 4 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6763, 65]
    (.letOp (n := 6768) (.out 0x10dbcb (movR64R64Effect 0x10dbcb 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[6765]
    (.letOp (n := 6769) (.exec 0x10dbcb (fun s => s.RIP = 0x10dbcb) (movR64R64Effect 0x10dbcb 15 0) (Reg.operands [.gpr 0] [])) #v[6765]
    (.letOp (n := 6770) (.out 0x10dbce (movR64R64Effect 0x10dbce 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[6766]
    (.letOp (n := 6771) (.exec 0x10dbce (fun s => s.RIP = 0x10dbce) (movR64R64Effect 0x10dbce 12 2) (Reg.operands [.gpr 2] [])) #v[6766]
    (.letOp (n := 6772) (.out 0x10dbd1 (shrR64Effect 0x10dbd1 4 10 52) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[6685]
    (.letOp (n := 6773) (.exec 0x10dbd1 (fun s => s.RIP = 0x10dbd1) (shrR64Effect 0x10dbd1 4 10 52) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6685]
    (.letOp (n := 6774) (.out 0x10dbd5 (movR64Imm64Effect 0x10dbd5 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 6775) (.exec 0x10dbd5 (fun s => s.RIP = 0x10dbd5) (movR64Imm64Effect 0x10dbd5 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 6776) (.out 0x10dbdf (imulR64R64Effect 0x10dbdf 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[6772, 6774]
    (.letOp (n := 6777) (.exec 0x10dbdf (fun s => s.RIP = 0x10dbdf) (imulR64R64Effect 0x10dbdf 4 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[6772, 6774]
    (.letOp (n := 6778) (.out 0x10dbe3 (movR64R64Effect 0x10dbe3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[6722]
    (.letOp (n := 6779) (.exec 0x10dbe3 (fun s => s.RIP = 0x10dbe3) (movR64R64Effect 0x10dbe3 0 9) (Reg.operands [.gpr 9] [])) #v[6722]
    (.letOp (n := 6780) (.out 0x10dbe6 (mulR64Effect 0x10dbe6 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[6774, 6778]
    (.letOp (n := 6781) (.out 0x10dbe6 (mulR64Effect 0x10dbe6 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[6774, 6778]
    (.letOp (n := 6782) (.exec 0x10dbe6 (fun s => s.RIP = 0x10dbe6) (mulR64Effect 0x10dbe6 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[6774, 6778]
    (.letOp (n := 6783) (.out 0x10dbe9 (addR64R64Effect 0x10dbe9 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[6776, 6781]
    (.letOp (n := 6784) (.exec 0x10dbe9 (fun s => s.RIP = 0x10dbe9) (addR64R64Effect 0x10dbe9 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[6776, 6781]
    (.letOp (n := 6785) (.out 0x10dbec (movR64R64Effect 0x10dbec 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[6720]
    (.letOp (n := 6786) (.exec 0x10dbec (fun s => s.RIP = 0x10dbec) (movR64R64Effect 0x10dbec 2 1) (Reg.operands [.gpr 1] [])) #v[6720]
    (.letOp (n := 6787) (.out 0x10dbef (shldR64R64Effect 0x10dbef 5 2 14 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[6785, 6717]
    (.letOp (n := 6788) (.exec 0x10dbef (fun s => s.RIP = 0x10dbef) (shldR64R64Effect 0x10dbef 5 2 14 12) (Reg.operands [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6785, 6717]
    (.letOp (n := 6789) (.out 0x10dbf4 (shrR64Effect 0x10dbf4 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[6720]
    (.letOp (n := 6790) (.exec 0x10dbf4 (fun s => s.RIP = 0x10dbf4) (shrR64Effect 0x10dbf4 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6720]
    (.letOp (n := 6791) (.out 0x10dbf8 (addR64R64Effect 0x10dbf8 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[6768, 6759]
    (.letOp (n := 6792) (.out 0x10dbf8 (addR64R64Effect 0x10dbf8 15 3) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 3] []) (.flag .CF)) #v[6768, 6759]
    (.letOp (n := 6793) (.exec 0x10dbf8 (fun s => s.RIP = 0x10dbf8) (addR64R64Effect 0x10dbf8 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[6768, 6759]
    (.letOp (n := 6794) (.out 0x10dbfb (atFlags StatusFlags.CF (adcR64R64Effect 0x10dbfb 12 5)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[6770, 6757, 6792]
    (.letOp (n := 6795) (.exec 0x10dbfb (fun s => s.RIP = 0x10dbfb) (atFlags StatusFlags.CF (adcR64R64Effect 0x10dbfb 12 5)) (Reg.operands [.gpr 12, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6770, 6757, 6792]
    (.letOp (n := 6796) (.out 0x10dbfe (addR64R64Effect 0x10dbfe 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[6791, 6750]
    (.letOp (n := 6797) (.out 0x10dbfe (addR64R64Effect 0x10dbfe 15 11) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 11] []) (.flag .CF)) #v[6791, 6750]
    (.letOp (n := 6798) (.exec 0x10dbfe (fun s => s.RIP = 0x10dbfe) (addR64R64Effect 0x10dbfe 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[6791, 6750]
    (.letOp (n := 6799) (.out 0x10dc01 (atFlags StatusFlags.CF (adcR64M64Effect 0x10dc01 12 (.sib 4 none 0 (.d32 0x160)))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 12))) #v[6794, 65, 6797]
    (.letOp (n := 6800) (.exec 0x10dc01 (LoadPre 0x10dc01 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x10dc01 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10dc01 12 (.sib 4 none 0 (.d32 0x160)))) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6794, 65, 6797]
    (.letOp (n := 6801) (.out 0x10dc09 (addR64M64Effect 0x10dc09 15 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[6796, 65]
    (.letOp (n := 6802) (.out 0x10dc09 (addR64M64Effect 0x10dc09 15 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[6796, 65]
    (.letOp (n := 6803) (.exec 0x10dc09 (LoadPre 0x10dc09 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10dc09 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10dc09 15 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[6796, 65]
    (b_l10a410_160)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_159 : List UInt8 :=
  [0x48, 0x89, 0xC3, 0x48, 0x8B, 0x74, 0x24, 0x60, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0x24, 0x24, 0x49,
    0x89, 0xC7, 0x49, 0x89, 0xD4, 0x49, 0xC1, 0xEA, 0x34, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xD2, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0xE2, 0x49, 0x01, 0xD2,
    0x48, 0x89, 0xCA, 0x4C, 0x0F, 0xA4, 0xF2, 0x0C, 0x48, 0xC1, 0xE9, 0x34, 0x49, 0x01, 0xDF, 0x49,
    0x11, 0xEC, 0x4D, 0x01, 0xDF, 0x4C, 0x13, 0xA4, 0x24, 0x60, 0x01, 0x00, 0x00, 0x4C, 0x03, 0xBC,
    0x24, 0xF0, 0x00, 0x00, 0x00] ++ bytes_l10a410_160

theorem code_l10a410_159 : ∀ x ∈ codeRange 0x10dbbc bytes_l10a410_159, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xdbbc 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_160

def b_l10a410_158 : Block Op Label signature Reg.count 6720 :=
  .letOp (n := 6720) (.out 0x10db63 (atFlags StatusFlags.CF (adcR64R64Effect 0x10db63 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[6715, 6697, 6718]
    (.letOp (n := 6721) (.exec 0x10db63 (fun s => s.RIP = 0x10db63) (atFlags StatusFlags.CF (adcR64R64Effect 0x10db63 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6715, 6697, 6718]
    (.letOp (n := 6722) (.out 0x10db66 (shrdR64R64Effect 0x10db66 5 9 10 52) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[6683, 6685]
    (.letOp (n := 6723) (.exec 0x10db66 (fun s => s.RIP = 0x10db66) (shrdR64R64Effect 0x10db66 5 9 10 52) (Reg.operands [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6683, 6685]
    (.letOp (n := 6724) (.out 0x10db6b (movR64R64Effect 0x10db6b 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[6676]
    (.letOp (n := 6725) (.exec 0x10db6b (fun s => s.RIP = 0x10db6b) (movR64R64Effect 0x10db6b 0 12) (Reg.operands [.gpr 12] [])) #v[6676]
    (.letOp (n := 6726) (.out 0x10db6e (movR64M64Effect 0x10db6e 13 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 6727) (.exec 0x10db6e (LoadPre 0x10db6e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10db6e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10db6e 13 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6728) (.out 0x10db73 (mulR64Effect 0x10db73 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[6726, 6724]
    (.letOp (n := 6729) (.out 0x10db73 (mulR64Effect 0x10db73 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[6726, 6724]
    (.letOp (n := 6730) (.exec 0x10db73 (fun s => s.RIP = 0x10db73) (mulR64Effect 0x10db73 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[6726, 6724]
    (.letOp (n := 6731) (.exec 0x10db76 (StorePre 0x10db76 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10db76 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10db76 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6729, 65]
    (.letOp (n := 6732) (.exec 0x10db7b (StorePre 0x10db7b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10db7b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10db7b 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6728, 65]
    (.letOp (n := 6733) (.out 0x10db80 (movR64R64Effect 0x10db80 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[6631]
    (.letOp (n := 6734) (.exec 0x10db80 (fun s => s.RIP = 0x10db80) (movR64R64Effect 0x10db80 0 5) (Reg.operands [.gpr 5] [])) #v[6631]
    (.letOp (n := 6735) (.out 0x10db83 (movR64M64Effect 0x10db83 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 6736) (.exec 0x10db83 (LoadPre 0x10db83 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10db83 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10db83 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6737) (.out 0x10db88 (mulR64Effect 0x10db88 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[6735, 6733]
    (.letOp (n := 6738) (.out 0x10db88 (mulR64Effect 0x10db88 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[6735, 6733]
    (.letOp (n := 6739) (.exec 0x10db88 (fun s => s.RIP = 0x10db88) (mulR64Effect 0x10db88 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[6735, 6733]
    (.letOp (n := 6740) (.exec 0x10db8b (StorePre 0x10db8b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10db8b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10db8b 2 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6738, 65]
    (.letOp (n := 6741) (.exec 0x10db93 (StorePre 0x10db93 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10db93 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10db93 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6737, 65]
    (.letOp (n := 6742) (.out 0x10db9b (movR64R64Effect 0x10db9b 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[6640]
    (.letOp (n := 6743) (.exec 0x10db9b (fun s => s.RIP = 0x10db9b) (movR64R64Effect 0x10db9b 0 7) (Reg.operands [.gpr 7] [])) #v[6640]
    (.letOp (n := 6744) (.out 0x10db9e (movR64M64Effect 0x10db9e 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 6745) (.exec 0x10db9e (LoadPre 0x10db9e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10db9e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10db9e 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6746) (.out 0x10dba3 (mulR64Effect 0x10dba3 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[6744, 6742]
    (.letOp (n := 6747) (.out 0x10dba3 (mulR64Effect 0x10dba3 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[6744, 6742]
    (.letOp (n := 6748) (.exec 0x10dba3 (fun s => s.RIP = 0x10dba3) (mulR64Effect 0x10dba3 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[6744, 6742]
    (.letOp (n := 6749) (.exec 0x10dba6 (StorePre 0x10dba6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x10dba6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10dba6 2 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6747, 65]
    (.letOp (n := 6750) (.out 0x10dbae (movR64R64Effect 0x10dbae 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[6746]
    (.letOp (n := 6751) (.exec 0x10dbae (fun s => s.RIP = 0x10dbae) (movR64R64Effect 0x10dbae 11 0) (Reg.operands [.gpr 0] [])) #v[6746]
    (.letOp (n := 6752) (.out 0x10dbb1 (movR64R64Effect 0x10dbb1 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6656]
    (.letOp (n := 6753) (.exec 0x10dbb1 (fun s => s.RIP = 0x10dbb1) (movR64R64Effect 0x10dbb1 0 6) (Reg.operands [.gpr 6] [])) #v[6656]
    (.letOp (n := 6754) (.out 0x10dbb4 (mulM64Effect 0x10dbb4 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6752, 65]
    (.letOp (n := 6755) (.out 0x10dbb4 (mulM64Effect 0x10dbb4 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6752, 65]
    (.letOp (n := 6756) (.exec 0x10dbb4 (LoadPre 0x10dbb4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10dbb4 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10dbb4 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6752, 65]
    (.letOp (n := 6757) (.out 0x10dbb9 (movR64R64Effect 0x10dbb9 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[6755]
    (.letOp (n := 6758) (.exec 0x10dbb9 (fun s => s.RIP = 0x10dbb9) (movR64R64Effect 0x10dbb9 5 2) (Reg.operands [.gpr 2] [])) #v[6755]
    (b_l10a410_159)))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_158 : List UInt8 :=
  [0x48, 0x11, 0xD1, 0x4D, 0x0F, 0xAC, 0xD1, 0x34, 0x4C, 0x89, 0xE0, 0x4C, 0x8B, 0x6C, 0x24, 0x40,
    0x49, 0xF7, 0xE5, 0x48, 0x89, 0x54, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x70, 0x48, 0x89, 0xE8,
    0x4C, 0x8B, 0x44, 0x24, 0x20, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x48, 0x8B, 0x7C, 0x24, 0x18,
    0x48, 0xF7, 0xE7, 0x48, 0x89, 0x94, 0x24, 0x60, 0x01, 0x00, 0x00, 0x49, 0x89, 0xC3, 0x48, 0x89,
    0xF0, 0x48, 0xF7, 0x64, 0x24, 0x08, 0x48, 0x89, 0xD5] ++ bytes_l10a410_159

theorem code_l10a410_158 : ∀ x ∈ codeRange 0x10db63 bytes_l10a410_158, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xdb63 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_159

def b_l10a410_157 : Block Op Label signature Reg.count 6676 :=
  .letOp (n := 6676) (.out 0x10db05 (movR64M64Effect 0x10db05 12 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 6677) (.exec 0x10db05 (LoadPre 0x10db05 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10db05 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10db05 12 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6678) (.out 0x10db0d (movR64R64Effect 0x10db0d 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[6676]
    (.letOp (n := 6679) (.exec 0x10db0d (fun s => s.RIP = 0x10db0d) (movR64R64Effect 0x10db0d 0 12) (Reg.operands [.gpr 12] [])) #v[6676]
    (.letOp (n := 6680) (.out 0x10db10 (mulR64Effect 0x10db10 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[6653, 6678]
    (.letOp (n := 6681) (.out 0x10db10 (mulR64Effect 0x10db10 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[6653, 6678]
    (.letOp (n := 6682) (.exec 0x10db10 (fun s => s.RIP = 0x10db10) (mulR64Effect 0x10db10 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[6653, 6678]
    (.letOp (n := 6683) (.out 0x10db13 (movR64R64Effect 0x10db13 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[6680]
    (.letOp (n := 6684) (.exec 0x10db13 (fun s => s.RIP = 0x10db13) (movR64R64Effect 0x10db13 9 0) (Reg.operands [.gpr 0] [])) #v[6680]
    (.letOp (n := 6685) (.out 0x10db16 (movR64R64Effect 0x10db16 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[6681]
    (.letOp (n := 6686) (.exec 0x10db16 (fun s => s.RIP = 0x10db16) (movR64R64Effect 0x10db16 10 2) (Reg.operands [.gpr 2] [])) #v[6681]
    (.letOp (n := 6687) (.out 0x10db19 (movR64Imm64Effect 0x10db19 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 6688) (.exec 0x10db19 (fun s => s.RIP = 0x10db19) (movR64Imm64Effect 0x10db19 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 6689) (.out 0x10db23 (andR64R64Effect 0x10db23 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[6629, 6687]
    (.letOp (n := 6690) (.exec 0x10db23 (fun s => s.RIP = 0x10db23) (andR64R64Effect 0x10db23 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[6629, 6687]
    (.letOp (n := 6691) (.exec 0x10db26 (StorePre 0x10db26 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10db26 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10db26 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[6689, 65]
    (.letOp (n := 6692) (.out 0x10db2b (andR64R64Effect 0x10db2b 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[6680, 6687]
    (.letOp (n := 6693) (.exec 0x10db2b (fun s => s.RIP = 0x10db2b) (andR64R64Effect 0x10db2b 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[6680, 6687]
    (.letOp (n := 6694) (.out 0x10db2e (movR64Imm64Effect 0x10db2e 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 6695) (.exec 0x10db2e (fun s => s.RIP = 0x10db2e) (movR64Imm64Effect 0x10db2e 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 6696) (.out 0x10db38 (mulR64Effect 0x10db38 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[6694, 6692]
    (.letOp (n := 6697) (.out 0x10db38 (mulR64Effect 0x10db38 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[6694, 6692]
    (.letOp (n := 6698) (.exec 0x10db38 (fun s => s.RIP = 0x10db38) (mulR64Effect 0x10db38 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[6694, 6692]
    (.letOp (n := 6699) (.out 0x10db3b (movR64Imm64Effect 0x10db3b 13 0xffffffffffff) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 6700) (.exec 0x10db3b (fun s => s.RIP = 0x10db3b) (movR64Imm64Effect 0x10db3b 13 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 6701) (.exec 0x10db45 (StorePre 0x10db45 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10db45 + BitVec.ofNat 64 5)) 8) (andMREffect 0x10db45 5 64 13 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[6699, 65]
    (.letOp (n := 6702) (.out 0x10db4a (addR64R64Effect 0x10db4a 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[6674, 6665]
    (.letOp (n := 6703) (.out 0x10db4a (addR64R64Effect 0x10db4a 14 15) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 15] []) (.flag .CF)) #v[6674, 6665]
    (.letOp (n := 6704) (.exec 0x10db4a (fun s => s.RIP = 0x10db4a) (addR64R64Effect 0x10db4a 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[6674, 6665]
    (.letOp (n := 6705) (.out 0x10db4d (atFlags StatusFlags.CF (adcR64R64Effect 0x10db4d 1 3)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[6672, 6663, 6703]
    (.letOp (n := 6706) (.exec 0x10db4d (fun s => s.RIP = 0x10db4d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10db4d 1 3)) (Reg.operands [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6672, 6663, 6703]
    (.letOp (n := 6707) (.out 0x10db50 (addR64R64Effect 0x10db50 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[6702, 6647]
    (.letOp (n := 6708) (.out 0x10db50 (addR64R64Effect 0x10db50 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[6702, 6647]
    (.letOp (n := 6709) (.exec 0x10db50 (fun s => s.RIP = 0x10db50) (addR64R64Effect 0x10db50 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[6702, 6647]
    (.letOp (n := 6710) (.out 0x10db53 (atFlags StatusFlags.CF (adcR64R64Effect 0x10db53 1 8)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[6705, 6649, 6708]
    (.letOp (n := 6711) (.exec 0x10db53 (fun s => s.RIP = 0x10db53) (atFlags StatusFlags.CF (adcR64R64Effect 0x10db53 1 8)) (Reg.operands [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6705, 6649, 6708]
    (.letOp (n := 6712) (.out 0x10db56 (addR64M64Effect 0x10db56 14 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[6707, 65]
    (.letOp (n := 6713) (.out 0x10db56 (addR64M64Effect 0x10db56 14 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 4] []) (.flag .CF)) #v[6707, 65]
    (.letOp (n := 6714) (.exec 0x10db56 (LoadPre 0x10db56 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10db56 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10db56 14 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[6707, 65]
    (.letOp (n := 6715) (.out 0x10db5b (atFlags StatusFlags.CF (adcR64M64Effect 0x10db5b 1 (.sib 4 none 0 (.d8 0x78)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[6710, 65, 6713]
    (.letOp (n := 6716) (.exec 0x10db5b (LoadPre 0x10db5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10db5b + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10db5b 1 (.sib 4 none 0 (.d8 0x78)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6710, 65, 6713]
    (.letOp (n := 6717) (.out 0x10db60 (addR64R64Effect 0x10db60 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[6712, 6696]
    (.letOp (n := 6718) (.out 0x10db60 (addR64R64Effect 0x10db60 14 0) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 0] []) (.flag .CF)) #v[6712, 6696]
    (.letOp (n := 6719) (.exec 0x10db60 (fun s => s.RIP = 0x10db60) (addR64R64Effect 0x10db60 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[6712, 6696]
    (b_l10a410_158))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_157 : List UInt8 :=
  [0x4C, 0x8B, 0xA4, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE2, 0x49, 0x89,
    0xC1, 0x49, 0x89, 0xD2, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21,
    0xD5, 0x4C, 0x89, 0x6C, 0x24, 0x10, 0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00,
    0x4C, 0x21, 0x6C, 0x24, 0x58, 0x4D, 0x01, 0xFE, 0x48, 0x11, 0xD9, 0x4D, 0x01, 0xDE, 0x4C, 0x11,
    0xC1, 0x4C, 0x03, 0x74, 0x24, 0x70, 0x48, 0x13, 0x4C, 0x24, 0x78, 0x49, 0x01, 0xC6] ++ bytes_l10a410_158

theorem code_l10a410_157 : ∀ x ∈ codeRange 0x10db05 bytes_l10a410_157, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xdb05 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_158

def b_l10a410_156 : Block Op Label signature Reg.count 6635 :=
  .letOp (n := 6635) (.out 0x10dab2 (mulR64Effect 0x10dab2 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[6608, 6633]
    (.letOp (n := 6636) (.out 0x10dab2 (mulR64Effect 0x10dab2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[6608, 6633]
    (.letOp (n := 6637) (.exec 0x10dab2 (fun s => s.RIP = 0x10dab2) (mulR64Effect 0x10dab2 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[6608, 6633]
    (.letOp (n := 6638) (.exec 0x10dab5 (StorePre 0x10dab5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10dab5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10dab5 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6636, 65]
    (.letOp (n := 6639) (.exec 0x10daba (StorePre 0x10daba 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10daba + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10daba 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6635, 65]
    (.letOp (n := 6640) (.out 0x10dabf (movR64M64Effect 0x10dabf 7 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 6641) (.exec 0x10dabf (LoadPre 0x10dabf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x10dabf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dabf 7 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6642) (.out 0x10dac7 (movR64R64Effect 0x10dac7 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[6640]
    (.letOp (n := 6643) (.exec 0x10dac7 (fun s => s.RIP = 0x10dac7) (movR64R64Effect 0x10dac7 0 7) (Reg.operands [.gpr 7] [])) #v[6640]
    (.letOp (n := 6644) (.out 0x10daca (mulR64Effect 0x10daca 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[6613, 6642]
    (.letOp (n := 6645) (.out 0x10daca (mulR64Effect 0x10daca 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[6613, 6642]
    (.letOp (n := 6646) (.exec 0x10daca (fun s => s.RIP = 0x10daca) (mulR64Effect 0x10daca 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[6613, 6642]
    (.letOp (n := 6647) (.out 0x10dacd (movR64R64Effect 0x10dacd 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[6644]
    (.letOp (n := 6648) (.exec 0x10dacd (fun s => s.RIP = 0x10dacd) (movR64R64Effect 0x10dacd 11 0) (Reg.operands [.gpr 0] [])) #v[6644]
    (.letOp (n := 6649) (.out 0x10dad0 (movR64R64Effect 0x10dad0 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[6645]
    (.letOp (n := 6650) (.exec 0x10dad0 (fun s => s.RIP = 0x10dad0) (movR64R64Effect 0x10dad0 8 2) (Reg.operands [.gpr 2] [])) #v[6645]
    (.letOp (n := 6651) (.out 0x10dad3 (movR64M64Effect 0x10dad3 0 (.sib 4 none 0 (.d32 0x190))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6652) (.exec 0x10dad3 (LoadPre 0x10dad3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x10dad3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dad3 0 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6653) (.out 0x10dadb (leaR64Effect 0x10dadb 10 (.sib 0 (some 0) 1 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0, .gpr 0] []) (.reg (.gpr 10))) #v[6651, 6651]
    (.letOp (n := 6654) (.exec 0x10dadb (fun s => s.RIP = 0x10dadb) (leaR64Effect 0x10dadb 10 (.sib 0 (some 0) 1 .none)) (Reg.operands [.gpr 0, .gpr 0] [])) #v[6651, 6651]
    (.letOp (n := 6655) (.exec 0x10dadf (StorePre 0x10dadf 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10dadf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10dadf 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[6653, 65]
    (.letOp (n := 6656) (.out 0x10dae3 (movR64M64Effect 0x10dae3 6 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 6657) (.exec 0x10dae3 (LoadPre 0x10dae3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10dae3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10dae3 6 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6658) (.out 0x10daeb (movR64R64Effect 0x10daeb 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6656]
    (.letOp (n := 6659) (.exec 0x10daeb (fun s => s.RIP = 0x10daeb) (movR64R64Effect 0x10daeb 0 6) (Reg.operands [.gpr 6] [])) #v[6656]
    (.letOp (n := 6660) (.out 0x10daee (mulR64Effect 0x10daee 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[6618, 6658]
    (.letOp (n := 6661) (.out 0x10daee (mulR64Effect 0x10daee 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[6618, 6658]
    (.letOp (n := 6662) (.exec 0x10daee (fun s => s.RIP = 0x10daee) (mulR64Effect 0x10daee 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[6618, 6658]
    (.letOp (n := 6663) (.out 0x10daf1 (movR64R64Effect 0x10daf1 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[6661]
    (.letOp (n := 6664) (.exec 0x10daf1 (fun s => s.RIP = 0x10daf1) (movR64R64Effect 0x10daf1 3 2) (Reg.operands [.gpr 2] [])) #v[6661]
    (.letOp (n := 6665) (.out 0x10daf4 (movR64R64Effect 0x10daf4 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[6660]
    (.letOp (n := 6666) (.exec 0x10daf4 (fun s => s.RIP = 0x10daf4) (movR64R64Effect 0x10daf4 15 0) (Reg.operands [.gpr 0] [])) #v[6660]
    (.letOp (n := 6667) (.out 0x10daf7 (movR64M64Effect 0x10daf7 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6668) (.exec 0x10daf7 (LoadPre 0x10daf7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10daf7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10daf7 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6669) (.out 0x10dafc (mulR64Effect 0x10dafc 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[6623, 6667]
    (.letOp (n := 6670) (.out 0x10dafc (mulR64Effect 0x10dafc 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[6623, 6667]
    (.letOp (n := 6671) (.exec 0x10dafc (fun s => s.RIP = 0x10dafc) (mulR64Effect 0x10dafc 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[6623, 6667]
    (.letOp (n := 6672) (.out 0x10daff (movR64R64Effect 0x10daff 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[6670]
    (.letOp (n := 6673) (.exec 0x10daff (fun s => s.RIP = 0x10daff) (movR64R64Effect 0x10daff 1 2) (Reg.operands [.gpr 2] [])) #v[6670]
    (.letOp (n := 6674) (.out 0x10db02 (movR64R64Effect 0x10db02 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[6669]
    (.letOp (n := 6675) (.exec 0x10db02 (fun s => s.RIP = 0x10db02) (movR64R64Effect 0x10db02 14 0) (Reg.operands [.gpr 0] [])) #v[6669]
    (b_l10a410_157)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_156 : List UInt8 :=
  [0x48, 0xF7, 0xE7, 0x48, 0x89, 0x54, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x70, 0x48, 0x8B, 0xBC,
    0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xC3, 0x49, 0x89,
    0xD0, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00, 0x4C, 0x8D, 0x14, 0x40, 0x4C, 0x89, 0x14,
    0x24, 0x48, 0x8B, 0xB4, 0x24, 0x20, 0x01, 0x00, 0x00, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE1, 0x48,
    0x89, 0xD3, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x44, 0x24, 0x60, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD1,
    0x49, 0x89, 0xC6] ++ bytes_l10a410_157

theorem code_l10a410_156 : ∀ x ∈ codeRange 0x10dab2 bytes_l10a410_156, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xdab2 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_157

def b_l10a410_155 : Block Op Label signature Reg.count 6599 :=
  .letOp (n := 6599) (.out 0x10da4a (atFlags StatusFlags.CF (adcR64R64Effect 0x10da4a 2 3)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[6588, 6590, 6597]
    (.letOp (n := 6600) (.exec 0x10da4a (fun s => s.RIP = 0x10da4a) (atFlags StatusFlags.CF (adcR64R64Effect 0x10da4a 2 3)) (Reg.operands [.gpr 2, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6588, 6590, 6597]
    (.letOp (n := 6601) (.out 0x10da4d (addR64R64Effect 0x10da4d 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[6596, 6580]
    (.letOp (n := 6602) (.out 0x10da4d (addR64R64Effect 0x10da4d 6 9) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 9] []) (.flag .CF)) #v[6596, 6580]
    (.letOp (n := 6603) (.exec 0x10da4d (fun s => s.RIP = 0x10da4d) (addR64R64Effect 0x10da4d 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6596, 6580]
    (.letOp (n := 6604) (.out 0x10da50 (atFlags StatusFlags.CF (adcR64R64Effect 0x10da50 2 1)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[6599, 6578, 6602]
    (.letOp (n := 6605) (.exec 0x10da50 (fun s => s.RIP = 0x10da50) (atFlags StatusFlags.CF (adcR64R64Effect 0x10da50 2 1)) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6599, 6578, 6602]
    (.letOp (n := 6606) (.out 0x10da53 (movR64M64Effect 0x10da53 0 (.sib 4 none 0 (.d32 0x1a8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6607) (.exec 0x10da53 (LoadPre 0x10da53 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x10da53 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10da53 0 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6608) (.out 0x10da5b (leaR64Effect 0x10da5b 7 (.sib 0 (some 0) 1 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0, .gpr 0] []) (.reg (.gpr 7))) #v[6606, 6606]
    (.letOp (n := 6609) (.exec 0x10da5b (fun s => s.RIP = 0x10da5b) (leaR64Effect 0x10da5b 7 (.sib 0 (some 0) 1 .none)) (Reg.operands [.gpr 0, .gpr 0] [])) #v[6606, 6606]
    (.letOp (n := 6610) (.exec 0x10da5f (StorePre 0x10da5f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10da5f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10da5f 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[6608, 65]
    (.letOp (n := 6611) (.out 0x10da64 (movR64M64Effect 0x10da64 0 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6612) (.exec 0x10da64 (LoadPre 0x10da64 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x10da64 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10da64 0 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6613) (.out 0x10da6c (leaR64Effect 0x10da6c 8 (.sib 0 (some 0) 1 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0, .gpr 0] []) (.reg (.gpr 8))) #v[6611, 6611]
    (.letOp (n := 6614) (.exec 0x10da6c (fun s => s.RIP = 0x10da6c) (leaR64Effect 0x10da6c 8 (.sib 0 (some 0) 1 .none)) (Reg.operands [.gpr 0, .gpr 0] [])) #v[6611, 6611]
    (.letOp (n := 6615) (.exec 0x10da70 (StorePre 0x10da70 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10da70 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10da70 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[6613, 65]
    (.letOp (n := 6616) (.out 0x10da75 (movR64M64Effect 0x10da75 0 (.sib 4 none 0 (.d32 0x1a0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6617) (.exec 0x10da75 (LoadPre 0x10da75 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x10da75 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10da75 0 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6618) (.out 0x10da7d (leaR64Effect 0x10da7d 9 (.sib 0 (some 0) 1 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0, .gpr 0] []) (.reg (.gpr 9))) #v[6616, 6616]
    (.letOp (n := 6619) (.exec 0x10da7d (fun s => s.RIP = 0x10da7d) (leaR64Effect 0x10da7d 9 (.sib 0 (some 0) 1 .none)) (Reg.operands [.gpr 0, .gpr 0] [])) #v[6616, 6616]
    (.letOp (n := 6620) (.exec 0x10da81 (StorePre 0x10da81 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10da81 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10da81 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[6618, 65]
    (.letOp (n := 6621) (.out 0x10da86 (movR64M64Effect 0x10da86 0 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6622) (.exec 0x10da86 (LoadPre 0x10da86 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x10da86 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10da86 0 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6623) (.out 0x10da8e (leaR64Effect 0x10da8e 1 (.sib 0 (some 0) 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0, .gpr 0] []) (.reg (.gpr 1))) #v[6621, 6621]
    (.letOp (n := 6624) (.exec 0x10da8e (fun s => s.RIP = 0x10da8e) (leaR64Effect 0x10da8e 1 (.sib 0 (some 0) 1 .none)) (Reg.operands [.gpr 0, .gpr 0] [])) #v[6621, 6621]
    (.letOp (n := 6625) (.exec 0x10da92 (StorePre 0x10da92 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10da92 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10da92 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[6623, 65]
    (.letOp (n := 6626) (.out 0x10da97 (shldR64R64Effect 0x10da97 5 2 6 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[6604, 6601]
    (.letOp (n := 6627) (.exec 0x10da97 (fun s => s.RIP = 0x10da97) (shldR64R64Effect 0x10da97 5 2 6 12) (Reg.operands [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6604, 6601]
    (.letOp (n := 6628) (.exec 0x10da9c (StorePre 0x10da9c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10da9c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10da9c 2 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6626, 65]
    (.letOp (n := 6629) (.out 0x10daa4 (movR64R64Effect 0x10daa4 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6601]
    (.letOp (n := 6630) (.exec 0x10daa4 (fun s => s.RIP = 0x10daa4) (movR64R64Effect 0x10daa4 13 6) (Reg.operands [.gpr 6] [])) #v[6601]
    (.letOp (n := 6631) (.out 0x10daa7 (movR64M64Effect 0x10daa7 5 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 6632) (.exec 0x10daa7 (LoadPre 0x10daa7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10daa7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10daa7 5 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6633) (.out 0x10daaf (movR64R64Effect 0x10daaf 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[6631]
    (.letOp (n := 6634) (.exec 0x10daaf (fun s => s.RIP = 0x10daaf) (movR64R64Effect 0x10daaf 0 5) (Reg.operands [.gpr 5] [])) #v[6631]
    (b_l10a410_156))))))))))))))))))))))))))))))))))))

def bytes_l10a410_155 : List UInt8 :=
  [0x48, 0x11, 0xDA, 0x4C, 0x01, 0xCE, 0x48, 0x11, 0xCA, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x01, 0x00,
    0x00, 0x48, 0x8D, 0x3C, 0x40, 0x48, 0x89, 0x7C, 0x24, 0x40, 0x48, 0x8B, 0x84, 0x24, 0x60, 0x01,
    0x00, 0x00, 0x4C, 0x8D, 0x04, 0x40, 0x4C, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84, 0x24, 0xA0,
    0x01, 0x00, 0x00, 0x4C, 0x8D, 0x0C, 0x40, 0x4C, 0x89, 0x4C, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24,
    0x78, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x0C, 0x40, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x0F, 0xA4,
    0xF2, 0x0C, 0x48, 0x89, 0x94, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x49, 0x89, 0xF5, 0x48, 0x8B, 0xAC,
    0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0x89, 0xE8] ++ bytes_l10a410_156

theorem code_l10a410_155 : ∀ x ∈ codeRange 0x10da4a bytes_l10a410_155, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xda4a 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_156

def b_l10a410_154 : Block Op Label signature Reg.count 6555 :=
  .letOp (n := 6555) (.out 0x10d9ff (atFlags StatusFlags.CF (adcR64R64Effect 0x10d9ff 9 7)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[6508, 6497, 6553]
    (.letOp (n := 6556) (.exec 0x10d9ff (fun s => s.RIP = 0x10d9ff) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d9ff 9 7)) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6508, 6497, 6553]
    (.letOp (n := 6557) (.out 0x10da02 (addR64R64Effect 0x10da02 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[6552, 6490]
    (.letOp (n := 6558) (.out 0x10da02 (addR64R64Effect 0x10da02 6 11) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 11] []) (.flag .CF)) #v[6552, 6490]
    (.letOp (n := 6559) (.exec 0x10da02 (fun s => s.RIP = 0x10da02) (addR64R64Effect 0x10da02 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[6552, 6490]
    (.letOp (n := 6560) (.out 0x10da05 (atFlags StatusFlags.CF (adcR64M64Effect 0x10da05 9 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[6555, 65, 6558]
    (.letOp (n := 6561) (.exec 0x10da05 (LoadPre 0x10da05 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10da05 + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10da05 9 (.sib 4 none 0 .none))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6555, 65, 6558]
    (.letOp (n := 6562) (.out 0x10da09 (addR64R64Effect 0x10da09 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[6557, 6549]
    (.letOp (n := 6563) (.out 0x10da09 (addR64R64Effect 0x10da09 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[6557, 6549]
    (.letOp (n := 6564) (.exec 0x10da09 (fun s => s.RIP = 0x10da09) (addR64R64Effect 0x10da09 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[6557, 6549]
    (.letOp (n := 6565) (.out 0x10da0c (atFlags StatusFlags.CF (adcR64R64Effect 0x10da0c 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[6560, 6550, 6563]
    (.letOp (n := 6566) (.exec 0x10da0c (fun s => s.RIP = 0x10da0c) (atFlags StatusFlags.CF (adcR64R64Effect 0x10da0c 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6560, 6550, 6563]
    (.letOp (n := 6567) (.out 0x10da0f (addR64R64Effect 0x10da0f 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[6562, 6482]
    (.letOp (n := 6568) (.out 0x10da0f (addR64R64Effect 0x10da0f 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[6562, 6482]
    (.letOp (n := 6569) (.exec 0x10da0f (fun s => s.RIP = 0x10da0f) (addR64R64Effect 0x10da0f 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[6562, 6482]
    (.letOp (n := 6570) (.out 0x10da12 (atFlags StatusFlags.CF (adcR64R64Effect 0x10da12 9 13)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[6565, 6480, 6568]
    (.letOp (n := 6571) (.exec 0x10da12 (fun s => s.RIP = 0x10da12) (atFlags StatusFlags.CF (adcR64R64Effect 0x10da12 9 13)) (Reg.operands [.gpr 9, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6565, 6480, 6568]
    (.letOp (n := 6572) (.out 0x10da15 (shrdR64R64Effect 0x10da15 5 8 3 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[6536, 6539]
    (.letOp (n := 6573) (.exec 0x10da15 (fun s => s.RIP = 0x10da15) (shrdR64R64Effect 0x10da15 5 8 3 52) (Reg.operands [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6536, 6539]
    (.letOp (n := 6574) (.out 0x10da1a (shrR64Effect 0x10da1a 4 3 52) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6539]
    (.letOp (n := 6575) (.exec 0x10da1a (fun s => s.RIP = 0x10da1a) (shrR64Effect 0x10da1a 4 3 52) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6539]
    (.letOp (n := 6576) (.out 0x10da1e (movR64R64Effect 0x10da1e 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[6570]
    (.letOp (n := 6577) (.exec 0x10da1e (fun s => s.RIP = 0x10da1e) (movR64R64Effect 0x10da1e 1 9) (Reg.operands [.gpr 9] [])) #v[6570]
    (.letOp (n := 6578) (.out 0x10da21 (shrR64Effect 0x10da21 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[6576]
    (.letOp (n := 6579) (.exec 0x10da21 (fun s => s.RIP = 0x10da21) (shrR64Effect 0x10da21 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6576]
    (.letOp (n := 6580) (.out 0x10da25 (shldR64R64Effect 0x10da25 5 9 6 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[6570, 6567]
    (.letOp (n := 6581) (.exec 0x10da25 (fun s => s.RIP = 0x10da25) (shldR64R64Effect 0x10da25 5 9 6 12) (Reg.operands [.gpr 9, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6570, 6567]
    (.letOp (n := 6582) (.out 0x10da2a (andR64R64Effect 0x10da2a 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[6567, 6543]
    (.letOp (n := 6583) (.exec 0x10da2a (fun s => s.RIP = 0x10da2a) (andR64R64Effect 0x10da2a 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[6567, 6543]
    (.letOp (n := 6584) (.exec 0x10da2d (StorePre 0x10da2d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10da2d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10da2d 6 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6582, 65]
    (.letOp (n := 6585) (.out 0x10da35 (movR64R64Effect 0x10da35 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[6572]
    (.letOp (n := 6586) (.exec 0x10da35 (fun s => s.RIP = 0x10da35) (movR64R64Effect 0x10da35 0 8) (Reg.operands [.gpr 8] [])) #v[6572]
    (.letOp (n := 6587) (.out 0x10da38 (mulR64Effect 0x10da38 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[6547, 6585]
    (.letOp (n := 6588) (.out 0x10da38 (mulR64Effect 0x10da38 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[6547, 6585]
    (.letOp (n := 6589) (.exec 0x10da38 (fun s => s.RIP = 0x10da38) (mulR64Effect 0x10da38 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[6547, 6585]
    (.letOp (n := 6590) (.out 0x10da3b (imulR64R64Effect 0x10da3b 4 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[6574, 6547]
    (.letOp (n := 6591) (.exec 0x10da3b (fun s => s.RIP = 0x10da3b) (imulR64R64Effect 0x10da3b 4 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[6574, 6547]
    (.letOp (n := 6592) (.out 0x10da3f (movR64M64Effect 0x10da3f 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 6593) (.exec 0x10da3f (LoadPre 0x10da3f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10da3f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10da3f 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6594) (.out 0x10da44 (andR64R64Effect 0x10da44 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[6592, 6543]
    (.letOp (n := 6595) (.exec 0x10da44 (fun s => s.RIP = 0x10da44) (andR64R64Effect 0x10da44 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[6592, 6543]
    (.letOp (n := 6596) (.out 0x10da47 (addR64R64Effect 0x10da47 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[6594, 6587]
    (.letOp (n := 6597) (.out 0x10da47 (addR64R64Effect 0x10da47 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[6594, 6587]
    (.letOp (n := 6598) (.exec 0x10da47 (fun s => s.RIP = 0x10da47) (addR64R64Effect 0x10da47 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[6594, 6587]
    (b_l10a410_155))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_154 : List UInt8 :=
  [0x49, 0x11, 0xF9, 0x4C, 0x01, 0xDE, 0x4C, 0x13, 0x0C, 0x24, 0x48, 0x01, 0xC6, 0x49, 0x11, 0xD1,
    0x48, 0x01, 0xCE, 0x4D, 0x11, 0xE9, 0x49, 0x0F, 0xAC, 0xD8, 0x34, 0x48, 0xC1, 0xEB, 0x34, 0x4C,
    0x89, 0xC9, 0x48, 0xC1, 0xE9, 0x34, 0x49, 0x0F, 0xA4, 0xF1, 0x0C, 0x4C, 0x21, 0xD6, 0x48, 0x89,
    0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE7, 0x49, 0x0F, 0xAF, 0xDF,
    0x48, 0x8B, 0x74, 0x24, 0x10, 0x4C, 0x21, 0xD6, 0x48, 0x01, 0xC6] ++ bytes_l10a410_155

theorem code_l10a410_154 : ∀ x ∈ codeRange 0x10d9ff bytes_l10a410_154, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd9ff 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_155

def b_l10a410_153 : Block Op Label signature Reg.count 6510 :=
  .letOp (n := 6510) (.out 0x10d9a5 (andR64R64Effect 0x10d9a5 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[6468, 6446]
    (.letOp (n := 6511) (.exec 0x10d9a5 (fun s => s.RIP = 0x10d9a5) (andR64R64Effect 0x10d9a5 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[6468, 6446]
    (.letOp (n := 6512) (.exec 0x10d9a8 (StorePre 0x10d9a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10d9a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10d9a8 8 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[6510, 65]
    (.letOp (n := 6513) (.out 0x10d9b0 (movR64M64Effect 0x10d9b0 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6514) (.exec 0x10d9b0 (LoadPre 0x10d9b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10d9b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d9b0 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6515) (.out 0x10d9b5 (mulM64Effect 0x10d9b5 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6513, 65]
    (.letOp (n := 6516) (.out 0x10d9b5 (mulM64Effect 0x10d9b5 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6513, 65]
    (.letOp (n := 6517) (.exec 0x10d9b5 (LoadPre 0x10d9b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10d9b5 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d9b5 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6513, 65]
    (.letOp (n := 6518) (.out 0x10d9ba (movR64R64Effect 0x10d9ba 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[6516]
    (.letOp (n := 6519) (.exec 0x10d9ba (fun s => s.RIP = 0x10d9ba) (movR64R64Effect 0x10d9ba 15 2) (Reg.operands [.gpr 2] [])) #v[6516]
    (.letOp (n := 6520) (.out 0x10d9bd (movR64R64Effect 0x10d9bd 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[6515]
    (.letOp (n := 6521) (.exec 0x10d9bd (fun s => s.RIP = 0x10d9bd) (movR64R64Effect 0x10d9bd 12 0) (Reg.operands [.gpr 0] [])) #v[6515]
    (.letOp (n := 6522) (.out 0x10d9c0 (movR64M64Effect 0x10d9c0 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6523) (.exec 0x10d9c0 (LoadPre 0x10d9c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10d9c0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d9c0 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6524) (.out 0x10d9c8 (mulM64Effect 0x10d9c8 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6522, 65]
    (.letOp (n := 6525) (.out 0x10d9c8 (mulM64Effect 0x10d9c8 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6522, 65]
    (.letOp (n := 6526) (.exec 0x10d9c8 (LoadPre 0x10d9c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10d9c8 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d9c8 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6522, 65]
    (.letOp (n := 6527) (.out 0x10d9cd (movR64R64Effect 0x10d9cd 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[6525]
    (.letOp (n := 6528) (.exec 0x10d9cd (fun s => s.RIP = 0x10d9cd) (movR64R64Effect 0x10d9cd 3 2) (Reg.operands [.gpr 2] [])) #v[6525]
    (.letOp (n := 6529) (.out 0x10d9d0 (movR64R64Effect 0x10d9d0 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[6524]
    (.letOp (n := 6530) (.exec 0x10d9d0 (fun s => s.RIP = 0x10d9d0) (movR64R64Effect 0x10d9d0 8 0) (Reg.operands [.gpr 0] [])) #v[6524]
    (.letOp (n := 6531) (.out 0x10d9d3 (addR64R64Effect 0x10d9d3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[6529, 6520]
    (.letOp (n := 6532) (.out 0x10d9d3 (addR64R64Effect 0x10d9d3 8 12) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 12] []) (.flag .CF)) #v[6529, 6520]
    (.letOp (n := 6533) (.exec 0x10d9d3 (fun s => s.RIP = 0x10d9d3) (addR64R64Effect 0x10d9d3 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[6529, 6520]
    (.letOp (n := 6534) (.out 0x10d9d6 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d9d6 3 15)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[6527, 6518, 6532]
    (.letOp (n := 6535) (.exec 0x10d9d6 (fun s => s.RIP = 0x10d9d6) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d9d6 3 15)) (Reg.operands [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6527, 6518, 6532]
    (.letOp (n := 6536) (.out 0x10d9d9 (addR64R64Effect 0x10d9d9 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[6531, 6474]
    (.letOp (n := 6537) (.out 0x10d9d9 (addR64R64Effect 0x10d9d9 8 10) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 10] []) (.flag .CF)) #v[6531, 6474]
    (.letOp (n := 6538) (.exec 0x10d9d9 (fun s => s.RIP = 0x10d9d9) (addR64R64Effect 0x10d9d9 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[6531, 6474]
    (.letOp (n := 6539) (.out 0x10d9dc (atFlags StatusFlags.CF (adcR64R64Effect 0x10d9dc 3 5)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[6534, 6476, 6537]
    (.letOp (n := 6540) (.exec 0x10d9dc (fun s => s.RIP = 0x10d9dc) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d9dc 3 5)) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6534, 6476, 6537]
    (.letOp (n := 6541) (.out 0x10d9df (movR64R64Effect 0x10d9df 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[6536]
    (.letOp (n := 6542) (.exec 0x10d9df (fun s => s.RIP = 0x10d9df) (movR64R64Effect 0x10d9df 0 8) (Reg.operands [.gpr 8] [])) #v[6536]
    (.letOp (n := 6543) (.out 0x10d9e2 (movR64Imm64Effect 0x10d9e2 10 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 6544) (.exec 0x10d9e2 (fun s => s.RIP = 0x10d9e2) (movR64Imm64Effect 0x10d9e2 10 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 6545) (.out 0x10d9ec (andR64R64Effect 0x10d9ec 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[6541, 6543]
    (.letOp (n := 6546) (.exec 0x10d9ec (fun s => s.RIP = 0x10d9ec) (andR64R64Effect 0x10d9ec 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[6541, 6543]
    (.letOp (n := 6547) (.out 0x10d9ef (movR64Imm64Effect 0x10d9ef 15 0x1000003d10) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 6548) (.exec 0x10d9ef (fun s => s.RIP = 0x10d9ef) (movR64Imm64Effect 0x10d9ef 15 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 6549) (.out 0x10d9f9 (mulR64Effect 0x10d9f9 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[6547, 6545]
    (.letOp (n := 6550) (.out 0x10d9f9 (mulR64Effect 0x10d9f9 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[6547, 6545]
    (.letOp (n := 6551) (.exec 0x10d9f9 (fun s => s.RIP = 0x10d9f9) (mulR64Effect 0x10d9f9 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[6547, 6545]
    (.letOp (n := 6552) (.out 0x10d9fc (addR64R64Effect 0x10d9fc 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[6506, 6499]
    (.letOp (n := 6553) (.out 0x10d9fc (addR64R64Effect 0x10d9fc 6 14) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 14] []) (.flag .CF)) #v[6506, 6499]
    (.letOp (n := 6554) (.exec 0x10d9fc (fun s => s.RIP = 0x10d9fc) (addR64R64Effect 0x10d9fc 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[6506, 6499]
    (b_l10a410_154)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_153 : List UInt8 :=
  [0x49, 0x21, 0xD8, 0x4C, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x18,
    0x48, 0xF7, 0x64, 0x24, 0x20, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x84, 0x24, 0xC0,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x40, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC0, 0x4D, 0x01,
    0xE0, 0x4C, 0x11, 0xFB, 0x4D, 0x01, 0xD0, 0x48, 0x11, 0xEB, 0x4C, 0x89, 0xC0, 0x49, 0xBA, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xD0, 0x49, 0xBF, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE7, 0x4C, 0x01, 0xF6] ++ bytes_l10a410_154

theorem code_l10a410_153 : ∀ x ∈ codeRange 0x10d9a5 bytes_l10a410_153, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd9a5 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_154

def b_l10a410_152 : Block Op Label signature Reg.count 6468 :=
  .letOp (n := 6468) (.out 0x10d94c (movR64R64Effect 0x10d94c 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[6465]
    (.letOp (n := 6469) (.exec 0x10d94c (fun s => s.RIP = 0x10d94c) (movR64R64Effect 0x10d94c 8 5) (Reg.operands [.gpr 5] [])) #v[6465]
    (.letOp (n := 6470) (.out 0x10d94f (atFlags StatusFlags.CF (adcR64R64Effect 0x10d94f 1 13)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[6463, 6375, 6466]
    (.letOp (n := 6471) (.exec 0x10d94f (fun s => s.RIP = 0x10d94f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d94f 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6463, 6375, 6466]
    (.letOp (n := 6472) (.out 0x10d952 (movR64R64Effect 0x10d952 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 10] []) (.reg (.gpr 5))) #v[6442]
    (.letOp (n := 6473) (.exec 0x10d952 (fun s => s.RIP = 0x10d952) (movR64R64Effect 0x10d952 5 10) (Reg.operands [.gpr 10] [])) #v[6442]
    (.letOp (n := 6474) (.out 0x10d955 (shldR64R64Effect 0x10d955 5 10 7 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[6442, 6439]
    (.letOp (n := 6475) (.exec 0x10d955 (fun s => s.RIP = 0x10d955) (shldR64R64Effect 0x10d955 5 10 7 12) (Reg.operands [.gpr 10, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6442, 6439]
    (.letOp (n := 6476) (.out 0x10d95a (shrR64Effect 0x10d95a 4 5 52) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[6472]
    (.letOp (n := 6477) (.exec 0x10d95a (fun s => s.RIP = 0x10d95a) (shrR64Effect 0x10d95a 4 5 52) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6472]
    (.letOp (n := 6478) (.out 0x10d95e (movR64R64Effect 0x10d95e 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[6470]
    (.letOp (n := 6479) (.exec 0x10d95e (fun s => s.RIP = 0x10d95e) (movR64R64Effect 0x10d95e 13 1) (Reg.operands [.gpr 1] [])) #v[6470]
    (.letOp (n := 6480) (.out 0x10d961 (shrR64Effect 0x10d961 4 13 52) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[6478]
    (.letOp (n := 6481) (.exec 0x10d961 (fun s => s.RIP = 0x10d961) (shrR64Effect 0x10d961 4 13 52) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6478]
    (.letOp (n := 6482) (.out 0x10d965 (shldR64R64Effect 0x10d965 5 1 8 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[6470, 6468]
    (.letOp (n := 6483) (.exec 0x10d965 (fun s => s.RIP = 0x10d965) (shldR64R64Effect 0x10d965 5 1 8 12) (Reg.operands [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6470, 6468]
    (.letOp (n := 6484) (.out 0x10d96a (movR64R64Effect 0x10d96a 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[6420]
    (.letOp (n := 6485) (.exec 0x10d96a (fun s => s.RIP = 0x10d96a) (movR64R64Effect 0x10d96a 0 11) (Reg.operands [.gpr 11] [])) #v[6420]
    (.letOp (n := 6486) (.out 0x10d96d (mulM64Effect 0x10d96d 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6484, 65]
    (.letOp (n := 6487) (.out 0x10d96d (mulM64Effect 0x10d96d 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6484, 65]
    (.letOp (n := 6488) (.exec 0x10d96d (LoadPre 0x10d96d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10d96d + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10d96d 8 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6484, 65]
    (.letOp (n := 6489) (.exec 0x10d975 (StorePre 0x10d975 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d975 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10d975 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6487, 65]
    (.letOp (n := 6490) (.out 0x10d979 (movR64R64Effect 0x10d979 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[6486]
    (.letOp (n := 6491) (.exec 0x10d979 (fun s => s.RIP = 0x10d979) (movR64R64Effect 0x10d979 11 0) (Reg.operands [.gpr 0] [])) #v[6486]
    (.letOp (n := 6492) (.out 0x10d97c (movR64M64Effect 0x10d97c 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6493) (.exec 0x10d97c (LoadPre 0x10d97c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10d97c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d97c 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6494) (.out 0x10d984 (mulM64Effect 0x10d984 5 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6492, 65]
    (.letOp (n := 6495) (.out 0x10d984 (mulM64Effect 0x10d984 5 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6492, 65]
    (.letOp (n := 6496) (.exec 0x10d984 (LoadPre 0x10d984 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10d984 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d984 5 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6492, 65]
    (.letOp (n := 6497) (.out 0x10d989 (movR64R64Effect 0x10d989 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[6495]
    (.letOp (n := 6498) (.exec 0x10d989 (fun s => s.RIP = 0x10d989) (movR64R64Effect 0x10d989 7 2) (Reg.operands [.gpr 2] [])) #v[6495]
    (.letOp (n := 6499) (.out 0x10d98c (movR64R64Effect 0x10d98c 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[6494]
    (.letOp (n := 6500) (.exec 0x10d98c (fun s => s.RIP = 0x10d98c) (movR64R64Effect 0x10d98c 14 0) (Reg.operands [.gpr 0] [])) #v[6494]
    (.letOp (n := 6501) (.out 0x10d98f (movR64M64Effect 0x10d98f 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6502) (.exec 0x10d98f (LoadPre 0x10d98f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10d98f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d98f 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6503) (.out 0x10d997 (mulM64Effect 0x10d997 8 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6501, 65]
    (.letOp (n := 6504) (.out 0x10d997 (mulM64Effect 0x10d997 8 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6501, 65]
    (.letOp (n := 6505) (.exec 0x10d997 (LoadPre 0x10d997 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10d997 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10d997 8 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6501, 65]
    (.letOp (n := 6506) (.out 0x10d99f (movR64R64Effect 0x10d99f 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[6503]
    (.letOp (n := 6507) (.exec 0x10d99f (fun s => s.RIP = 0x10d99f) (movR64R64Effect 0x10d99f 6 0) (Reg.operands [.gpr 0] [])) #v[6503]
    (.letOp (n := 6508) (.out 0x10d9a2 (movR64R64Effect 0x10d9a2 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[6504]
    (.letOp (n := 6509) (.exec 0x10d9a2 (fun s => s.RIP = 0x10d9a2) (movR64R64Effect 0x10d9a2 9 2) (Reg.operands [.gpr 2] [])) #v[6504]
    (b_l10a410_153))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_152 : List UInt8 :=
  [0x49, 0x89, 0xE8, 0x4C, 0x11, 0xE9, 0x4C, 0x89, 0xD5, 0x49, 0x0F, 0xA4, 0xFA, 0x0C, 0x48, 0xC1,
    0xED, 0x34, 0x49, 0x89, 0xCD, 0x49, 0xC1, 0xED, 0x34, 0x4C, 0x0F, 0xA4, 0xC1, 0x0C, 0x4C, 0x89,
    0xD8, 0x48, 0xF7, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x14, 0x24, 0x49, 0x89, 0xC3,
    0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x78, 0x48, 0x89, 0xD7,
    0x49, 0x89, 0xC6, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0xF0,
    0x00, 0x00, 0x00, 0x48, 0x89, 0xC6, 0x49, 0x89, 0xD1] ++ bytes_l10a410_153

theorem code_l10a410_152 : ∀ x ∈ codeRange 0x10d94c bytes_l10a410_152, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd94c 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_153

def b_l10a410_151 : Block Op Label signature Reg.count 6420 :=
  .letOp (n := 6420) (.out 0x10d8fd (movR64M64Effect 0x10d8fd 11 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 6421) (.exec 0x10d8fd (LoadPre 0x10d8fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10d8fd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d8fd 11 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6422) (.out 0x10d902 (movR64R64Effect 0x10d902 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[6420]
    (.letOp (n := 6423) (.exec 0x10d902 (fun s => s.RIP = 0x10d902) (movR64R64Effect 0x10d902 0 11) (Reg.operands [.gpr 11] [])) #v[6420]
    (.letOp (n := 6424) (.out 0x10d905 (mulR64Effect 0x10d905 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[6322, 6422]
    (.letOp (n := 6425) (.out 0x10d905 (mulR64Effect 0x10d905 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[6322, 6422]
    (.letOp (n := 6426) (.exec 0x10d905 (fun s => s.RIP = 0x10d905) (mulR64Effect 0x10d905 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[6322, 6422]
    (.letOp (n := 6427) (.out 0x10d908 (movR64R64Effect 0x10d908 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[6424]
    (.letOp (n := 6428) (.exec 0x10d908 (fun s => s.RIP = 0x10d908) (movR64R64Effect 0x10d908 7 0) (Reg.operands [.gpr 0] [])) #v[6424]
    (.letOp (n := 6429) (.out 0x10d90b (addR64R64Effect 0x10d90b 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[6427, 6418]
    (.letOp (n := 6430) (.out 0x10d90b (addR64R64Effect 0x10d90b 7 15) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 15] []) (.flag .CF)) #v[6427, 6418]
    (.letOp (n := 6431) (.exec 0x10d90b (fun s => s.RIP = 0x10d90b) (addR64R64Effect 0x10d90b 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[6427, 6418]
    (.letOp (n := 6432) (.out 0x10d90e (atFlags StatusFlags.CF (adcR64R64Effect 0x10d90e 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[6416, 6425, 6430]
    (.letOp (n := 6433) (.exec 0x10d90e (fun s => s.RIP = 0x10d90e) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d90e 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6416, 6425, 6430]
    (.letOp (n := 6434) (.out 0x10d911 (addR64R64Effect 0x10d911 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[6429, 6402]
    (.letOp (n := 6435) (.out 0x10d911 (addR64R64Effect 0x10d911 7 3) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 3] []) (.flag .CF)) #v[6429, 6402]
    (.letOp (n := 6436) (.exec 0x10d911 (fun s => s.RIP = 0x10d911) (addR64R64Effect 0x10d911 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[6429, 6402]
    (.letOp (n := 6437) (.out 0x10d914 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d914 10 14)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[6432, 6404, 6435]
    (.letOp (n := 6438) (.exec 0x10d914 (fun s => s.RIP = 0x10d914) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d914 10 14)) (Reg.operands [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6432, 6404, 6435]
    (.letOp (n := 6439) (.out 0x10d917 (addR64R64Effect 0x10d917 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[6434, 6349]
    (.letOp (n := 6440) (.out 0x10d917 (addR64R64Effect 0x10d917 7 6) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 6] []) (.flag .CF)) #v[6434, 6349]
    (.letOp (n := 6441) (.exec 0x10d917 (fun s => s.RIP = 0x10d917) (addR64R64Effect 0x10d917 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[6434, 6349]
    (.letOp (n := 6442) (.out 0x10d91a (atFlags StatusFlags.CF (adcR64R64Effect 0x10d91a 10 12)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[6437, 6359, 6440]
    (.letOp (n := 6443) (.exec 0x10d91a (fun s => s.RIP = 0x10d91a) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d91a 10 12)) (Reg.operands [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6437, 6359, 6440]
    (.letOp (n := 6444) (.out 0x10d91d (movR64R64Effect 0x10d91d 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[6439]
    (.letOp (n := 6445) (.exec 0x10d91d (fun s => s.RIP = 0x10d91d) (movR64R64Effect 0x10d91d 0 7) (Reg.operands [.gpr 7] [])) #v[6439]
    (.letOp (n := 6446) (.out 0x10d920 (movR64Imm64Effect 0x10d920 3 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 6447) (.exec 0x10d920 (fun s => s.RIP = 0x10d920) (movR64Imm64Effect 0x10d920 3 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 6448) (.out 0x10d92a (andR64R64Effect 0x10d92a 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[6444, 6446]
    (.letOp (n := 6449) (.exec 0x10d92a (fun s => s.RIP = 0x10d92a) (andR64R64Effect 0x10d92a 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[6444, 6446]
    (.letOp (n := 6450) (.out 0x10d92d (movR64Imm64Effect 0x10d92d 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 6451) (.exec 0x10d92d (fun s => s.RIP = 0x10d92d) (movR64Imm64Effect 0x10d92d 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 6452) (.out 0x10d937 (mulR64Effect 0x10d937 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[6450, 6448]
    (.letOp (n := 6453) (.out 0x10d937 (mulR64Effect 0x10d937 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[6450, 6448]
    (.letOp (n := 6454) (.exec 0x10d937 (fun s => s.RIP = 0x10d937) (mulR64Effect 0x10d937 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[6450, 6448]
    (.letOp (n := 6455) (.out 0x10d93a (addR64M64Effect 0x10d93a 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[6395, 65]
    (.letOp (n := 6456) (.out 0x10d93a (addR64M64Effect 0x10d93a 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[6395, 65]
    (.letOp (n := 6457) (.exec 0x10d93a (LoadPre 0x10d93a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10d93a + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d93a 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[6395, 65]
    (.letOp (n := 6458) (.out 0x10d93f (atFlags StatusFlags.CF (adcR64M64Effect 0x10d93f 1 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[6393, 65, 6456]
    (.letOp (n := 6459) (.exec 0x10d93f (LoadPre 0x10d93f (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d93f + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d93f 1 (.sib 4 none 0 .none))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6393, 65, 6456]
    (.letOp (n := 6460) (.out 0x10d943 (addR64R64Effect 0x10d943 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[6455, 6452]
    (.letOp (n := 6461) (.out 0x10d943 (addR64R64Effect 0x10d943 5 0) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 0] []) (.flag .CF)) #v[6455, 6452]
    (.letOp (n := 6462) (.exec 0x10d943 (fun s => s.RIP = 0x10d943) (addR64R64Effect 0x10d943 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[6455, 6452]
    (.letOp (n := 6463) (.out 0x10d946 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d946 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[6458, 6453, 6461]
    (.letOp (n := 6464) (.exec 0x10d946 (fun s => s.RIP = 0x10d946) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d946 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6458, 6453, 6461]
    (.letOp (n := 6465) (.out 0x10d949 (addR64R64Effect 0x10d949 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[6460, 6377]
    (.letOp (n := 6466) (.out 0x10d949 (addR64R64Effect 0x10d949 5 9) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 9] []) (.flag .CF)) #v[6460, 6377]
    (.letOp (n := 6467) (.exec 0x10d949 (fun s => s.RIP = 0x10d949) (addR64R64Effect 0x10d949 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[6460, 6377]
    (b_l10a410_152))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_151 : List UInt8 :=
  [0x4C, 0x8B, 0x5C, 0x24, 0x70, 0x4C, 0x89, 0xD8, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0xC7, 0x4C, 0x01,
    0xFF, 0x49, 0x11, 0xD2, 0x48, 0x01, 0xDF, 0x4D, 0x11, 0xF2, 0x48, 0x01, 0xF7, 0x4D, 0x11, 0xE2,
    0x48, 0x89, 0xF8, 0x48, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD8,
    0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x03, 0x6C,
    0x24, 0x08, 0x48, 0x13, 0x0C, 0x24, 0x48, 0x01, 0xC5, 0x48, 0x11, 0xD1, 0x4C, 0x01, 0xCD] ++ bytes_l10a410_152

theorem code_l10a410_151 : ∀ x ∈ codeRange 0x10d8fd bytes_l10a410_151, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd8fd 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_152

def b_l10a410_150 : Block Op Label signature Reg.count 6379 :=
  .letOp (n := 6379) (.out 0x10d8a2 (movR64R64Effect 0x10d8a2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[6368]
    (.letOp (n := 6380) (.exec 0x10d8a2 (fun s => s.RIP = 0x10d8a2) (movR64R64Effect 0x10d8a2 7 0) (Reg.operands [.gpr 0] [])) #v[6368]
    (.letOp (n := 6381) (.out 0x10d8a5 (movR64R64Effect 0x10d8a5 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[6318]
    (.letOp (n := 6382) (.exec 0x10d8a5 (fun s => s.RIP = 0x10d8a5) (movR64R64Effect 0x10d8a5 0 5) (Reg.operands [.gpr 5] [])) #v[6318]
    (.letOp (n := 6383) (.out 0x10d8a8 (mulM64Effect 0x10d8a8 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6381, 65]
    (.letOp (n := 6384) (.out 0x10d8a8 (mulM64Effect 0x10d8a8 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6381, 65]
    (.letOp (n := 6385) (.exec 0x10d8a8 (LoadPre 0x10d8a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10d8a8 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10d8a8 8 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6381, 65]
    (.letOp (n := 6386) (.exec 0x10d8b0 (StorePre 0x10d8b0 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d8b0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10d8b0 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6384, 65]
    (.letOp (n := 6387) (.exec 0x10d8b4 (StorePre 0x10d8b4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10d8b4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d8b4 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6383, 65]
    (.letOp (n := 6388) (.out 0x10d8b9 (movR64M64Effect 0x10d8b9 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6389) (.exec 0x10d8b9 (LoadPre 0x10d8b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10d8b9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d8b9 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6390) (.out 0x10d8c1 (mulR64Effect 0x10d8c1 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[6287, 6388]
    (.letOp (n := 6391) (.out 0x10d8c1 (mulR64Effect 0x10d8c1 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[6287, 6388]
    (.letOp (n := 6392) (.exec 0x10d8c1 (fun s => s.RIP = 0x10d8c1) (mulR64Effect 0x10d8c1 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[6287, 6388]
    (.letOp (n := 6393) (.out 0x10d8c4 (movR64R64Effect 0x10d8c4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[6391]
    (.letOp (n := 6394) (.exec 0x10d8c4 (fun s => s.RIP = 0x10d8c4) (movR64R64Effect 0x10d8c4 1 2) (Reg.operands [.gpr 2] [])) #v[6391]
    (.letOp (n := 6395) (.out 0x10d8c7 (movR64R64Effect 0x10d8c7 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[6390]
    (.letOp (n := 6396) (.exec 0x10d8c7 (fun s => s.RIP = 0x10d8c7) (movR64R64Effect 0x10d8c7 5 0) (Reg.operands [.gpr 0] [])) #v[6390]
    (.letOp (n := 6397) (.out 0x10d8ca (movR64M64Effect 0x10d8ca 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6398) (.exec 0x10d8ca (LoadPre 0x10d8ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10d8ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d8ca 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6399) (.out 0x10d8cf (mulR64Effect 0x10d8cf 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[6298, 6397]
    (.letOp (n := 6400) (.out 0x10d8cf (mulR64Effect 0x10d8cf 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[6298, 6397]
    (.letOp (n := 6401) (.exec 0x10d8cf (fun s => s.RIP = 0x10d8cf) (mulR64Effect 0x10d8cf 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[6298, 6397]
    (.letOp (n := 6402) (.out 0x10d8d2 (movR64R64Effect 0x10d8d2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[6399]
    (.letOp (n := 6403) (.exec 0x10d8d2 (fun s => s.RIP = 0x10d8d2) (movR64R64Effect 0x10d8d2 3 0) (Reg.operands [.gpr 0] [])) #v[6399]
    (.letOp (n := 6404) (.out 0x10d8d5 (movR64R64Effect 0x10d8d5 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[6400]
    (.letOp (n := 6405) (.exec 0x10d8d5 (fun s => s.RIP = 0x10d8d5) (movR64R64Effect 0x10d8d5 14 2) (Reg.operands [.gpr 2] [])) #v[6400]
    (.letOp (n := 6406) (.out 0x10d8d8 (movR64Imm64Effect 0x10d8d8 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 6407) (.exec 0x10d8d8 (fun s => s.RIP = 0x10d8d8) (movR64Imm64Effect 0x10d8d8 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 6408) (.out 0x10d8e2 (andR64R64Effect 0x10d8e2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[6379, 6406]
    (.letOp (n := 6409) (.exec 0x10d8e2 (fun s => s.RIP = 0x10d8e2) (andR64R64Effect 0x10d8e2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[6379, 6406]
    (.letOp (n := 6410) (.exec 0x10d8e5 (StorePre 0x10d8e5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10d8e5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d8e5 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[6408, 65]
    (.letOp (n := 6411) (.out 0x10d8ea (movR64M64Effect 0x10d8ea 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6412) (.exec 0x10d8ea (LoadPre 0x10d8ea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10d8ea + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d8ea 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6413) (.out 0x10d8f2 (mulM64Effect 0x10d8f2 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6411, 65]
    (.letOp (n := 6414) (.out 0x10d8f2 (mulM64Effect 0x10d8f2 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6411, 65]
    (.letOp (n := 6415) (.exec 0x10d8f2 (LoadPre 0x10d8f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10d8f2 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d8f2 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6411, 65]
    (.letOp (n := 6416) (.out 0x10d8f7 (movR64R64Effect 0x10d8f7 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[6414]
    (.letOp (n := 6417) (.exec 0x10d8f7 (fun s => s.RIP = 0x10d8f7) (movR64R64Effect 0x10d8f7 10 2) (Reg.operands [.gpr 2] [])) #v[6414]
    (.letOp (n := 6418) (.out 0x10d8fa (movR64R64Effect 0x10d8fa 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[6413]
    (.letOp (n := 6419) (.exec 0x10d8fa (fun s => s.RIP = 0x10d8fa) (movR64R64Effect 0x10d8fa 15 0) (Reg.operands [.gpr 0] [])) #v[6413]
    (b_l10a410_151)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_150 : List UInt8 :=
  [0x48, 0x89, 0xC7, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89,
    0x14, 0x24, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE1, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x49, 0xF7, 0xE2,
    0x48, 0x89, 0xC3, 0x49, 0x89, 0xD6, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x48, 0x21, 0xC7, 0x48, 0x89, 0x7C, 0x24, 0x48, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0x64, 0x24, 0x20, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC7] ++ bytes_l10a410_151

theorem code_l10a410_150 : ∀ x ∈ codeRange 0x10d8a2 bytes_l10a410_150, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd8a2 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_151

def b_l10a410_149 : Block Op Label signature Reg.count 6335 :=
  .letOp (n := 6335) (.out 0x10d84e (atFlags StatusFlags.CF (adcR64R64Effect 0x10d84e 6 3)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[6330, 6305, 6333]
    (.letOp (n := 6336) (.exec 0x10d84e (fun s => s.RIP = 0x10d84e) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d84e 6 3)) (Reg.operands [.gpr 6, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6330, 6305, 6333]
    (.letOp (n := 6337) (.out 0x10d851 (addR64R64Effect 0x10d851 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[6332, 6294]
    (.letOp (n := 6338) (.out 0x10d851 (addR64R64Effect 0x10d851 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[6332, 6294]
    (.letOp (n := 6339) (.exec 0x10d851 (fun s => s.RIP = 0x10d851) (addR64R64Effect 0x10d851 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[6332, 6294]
    (.letOp (n := 6340) (.out 0x10d854 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d854 6 13)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[6335, 6292, 6338]
    (.letOp (n := 6341) (.exec 0x10d854 (fun s => s.RIP = 0x10d854) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d854 6 13)) (Reg.operands [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6335, 6292, 6338]
    (.letOp (n := 6342) (.out 0x10d857 (addR64R64Effect 0x10d857 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[6337, 6270]
    (.letOp (n := 6343) (.out 0x10d857 (addR64R64Effect 0x10d857 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[6337, 6270]
    (.letOp (n := 6344) (.exec 0x10d857 (fun s => s.RIP = 0x10d857) (addR64R64Effect 0x10d857 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[6337, 6270]
    (.letOp (n := 6345) (.out 0x10d85a (atFlags StatusFlags.CF (adcR64R64Effect 0x10d85a 6 12)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[6340, 6272, 6343]
    (.letOp (n := 6346) (.exec 0x10d85a (fun s => s.RIP = 0x10d85a) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d85a 6 12)) (Reg.operands [.gpr 6, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6340, 6272, 6343]
    (.letOp (n := 6347) (.out 0x10d85d (movR64R64Effect 0x10d85d 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6345]
    (.letOp (n := 6348) (.exec 0x10d85d (fun s => s.RIP = 0x10d85d) (movR64R64Effect 0x10d85d 12 6) (Reg.operands [.gpr 6] [])) #v[6345]
    (.letOp (n := 6349) (.out 0x10d860 (shldR64R64Effect 0x10d860 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[6345, 6342]
    (.letOp (n := 6350) (.exec 0x10d860 (fun s => s.RIP = 0x10d860) (shldR64R64Effect 0x10d860 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6345, 6342]
    (.letOp (n := 6351) (.out 0x10d865 (shlR64Effect 0x10d865 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[6342]
    (.letOp (n := 6352) (.exec 0x10d865 (fun s => s.RIP = 0x10d865) (shlR64Effect 0x10d865 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6342]
    (.letOp (n := 6353) (.out 0x10d869 (movR64Imm64Effect 0x10d869 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 6354) (.exec 0x10d869 (fun s => s.RIP = 0x10d869) (movR64Imm64Effect 0x10d869 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 6355) (.out 0x10d873 (andR64R64Effect 0x10d873 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[6351, 6353]
    (.letOp (n := 6356) (.exec 0x10d873 (fun s => s.RIP = 0x10d873) (andR64R64Effect 0x10d873 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[6351, 6353]
    (.letOp (n := 6357) (.out 0x10d876 (orR64R64Effect 0x10d876 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[6355, 6307]
    (.letOp (n := 6358) (.exec 0x10d876 (fun s => s.RIP = 0x10d876) (orR64R64Effect 0x10d876 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[6355, 6307]
    (.letOp (n := 6359) (.out 0x10d879 (shrR64Effect 0x10d879 4 12 52) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[6347]
    (.letOp (n := 6360) (.exec 0x10d879 (fun s => s.RIP = 0x10d879) (shrR64Effect 0x10d879 4 12 52) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6347]
    (.letOp (n := 6361) (.out 0x10d87d (movR64Imm64Effect 0x10d87d 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 6362) (.exec 0x10d87d (fun s => s.RIP = 0x10d87d) (movR64Imm64Effect 0x10d87d 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 6363) (.out 0x10d887 (mulR64Effect 0x10d887 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[6361, 6357]
    (.letOp (n := 6364) (.out 0x10d887 (mulR64Effect 0x10d887 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[6361, 6357]
    (.letOp (n := 6365) (.exec 0x10d887 (fun s => s.RIP = 0x10d887) (mulR64Effect 0x10d887 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[6361, 6357]
    (.letOp (n := 6366) (.out 0x10d88a (movR64R64Effect 0x10d88a 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[6364]
    (.letOp (n := 6367) (.exec 0x10d88a (fun s => s.RIP = 0x10d88a) (movR64R64Effect 0x10d88a 9 2) (Reg.operands [.gpr 2] [])) #v[6364]
    (.letOp (n := 6368) (.out 0x10d88d (addR64M64Effect 0x10d88d 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6363, 65]
    (.letOp (n := 6369) (.out 0x10d88d (addR64M64Effect 0x10d88d 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[6363, 65]
    (.letOp (n := 6370) (.exec 0x10d88d (LoadPre 0x10d88d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10d88d + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d88d 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6363, 65]
    (.letOp (n := 6371) (.out 0x10d892 (atFlags StatusFlags.CF (adcR64M64Effect 0x10d892 9 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[6366, 65, 6369]
    (.letOp (n := 6372) (.exec 0x10d892 (LoadPre 0x10d892 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d892 + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d892 9 (.sib 4 none 0 .none))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6366, 65, 6369]
    (.letOp (n := 6373) (.out 0x10d896 (movR64R64Effect 0x10d896 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[6371]
    (.letOp (n := 6374) (.exec 0x10d896 (fun s => s.RIP = 0x10d896) (movR64R64Effect 0x10d896 13 9) (Reg.operands [.gpr 9] [])) #v[6371]
    (.letOp (n := 6375) (.out 0x10d899 (shrR64Effect 0x10d899 4 13 52) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[6373]
    (.letOp (n := 6376) (.exec 0x10d899 (fun s => s.RIP = 0x10d899) (shrR64Effect 0x10d899 4 13 52) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6373]
    (.letOp (n := 6377) (.out 0x10d89d (shldR64R64Effect 0x10d89d 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[6371, 6368]
    (.letOp (n := 6378) (.exec 0x10d89d (fun s => s.RIP = 0x10d89d) (shldR64R64Effect 0x10d89d 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6371, 6368]
    (b_l10a410_150))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_149 : List UInt8 :=
  [0x48, 0x11, 0xDE, 0x48, 0x01, 0xF8, 0x4C, 0x11, 0xEE, 0x4C, 0x01, 0xC8, 0x4C, 0x11, 0xE6, 0x49,
    0x89, 0xF4, 0x48, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x4C, 0x09, 0xF8, 0x49, 0xC1, 0xEC, 0x34, 0x48,
    0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xD1, 0x48,
    0x03, 0x44, 0x24, 0x08, 0x4C, 0x13, 0x0C, 0x24, 0x4D, 0x89, 0xCD, 0x49, 0xC1, 0xED, 0x34, 0x49,
    0x0F, 0xA4, 0xC1, 0x0C] ++ bytes_l10a410_150

theorem code_l10a410_149 : ∀ x ∈ codeRange 0x10d84e bytes_l10a410_149, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd84e 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_150

def b_l10a410_148 : Block Op Label signature Reg.count 6289 :=
  .letOp (n := 6289) (.out 0x10d7fc (mulR64Effect 0x10d7fc 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[6287, 6285]
    (.letOp (n := 6290) (.out 0x10d7fc (mulR64Effect 0x10d7fc 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[6287, 6285]
    (.letOp (n := 6291) (.exec 0x10d7fc (fun s => s.RIP = 0x10d7fc) (mulR64Effect 0x10d7fc 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[6287, 6285]
    (.letOp (n := 6292) (.out 0x10d7ff (movR64R64Effect 0x10d7ff 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[6290]
    (.letOp (n := 6293) (.exec 0x10d7ff (fun s => s.RIP = 0x10d7ff) (movR64R64Effect 0x10d7ff 13 2) (Reg.operands [.gpr 2] [])) #v[6290]
    (.letOp (n := 6294) (.out 0x10d802 (movR64R64Effect 0x10d802 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[6289]
    (.letOp (n := 6295) (.exec 0x10d802 (fun s => s.RIP = 0x10d802) (movR64R64Effect 0x10d802 7 0) (Reg.operands [.gpr 0] [])) #v[6289]
    (.letOp (n := 6296) (.out 0x10d805 (movR64M64Effect 0x10d805 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6297) (.exec 0x10d805 (LoadPre 0x10d805 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10d805 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d805 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6298) (.out 0x10d80d (movR64M64Effect 0x10d80d 10 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 6299) (.exec 0x10d80d (LoadPre 0x10d80d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10d80d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d80d 10 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6300) (.out 0x10d815 (mulR64Effect 0x10d815 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[6298, 6296]
    (.letOp (n := 6301) (.out 0x10d815 (mulR64Effect 0x10d815 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[6298, 6296]
    (.letOp (n := 6302) (.exec 0x10d815 (fun s => s.RIP = 0x10d815) (mulR64Effect 0x10d815 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[6298, 6296]
    (.letOp (n := 6303) (.out 0x10d818 (movR64R64Effect 0x10d818 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[6300]
    (.letOp (n := 6304) (.exec 0x10d818 (fun s => s.RIP = 0x10d818) (movR64R64Effect 0x10d818 11 0) (Reg.operands [.gpr 0] [])) #v[6300]
    (.letOp (n := 6305) (.out 0x10d81b (movR64R64Effect 0x10d81b 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[6301]
    (.letOp (n := 6306) (.exec 0x10d81b (fun s => s.RIP = 0x10d81b) (movR64R64Effect 0x10d81b 3 2) (Reg.operands [.gpr 2] [])) #v[6301]
    (.letOp (n := 6307) (.out 0x10d81e (andR32Imm8Effect 0x10d81e 4 15 0xf) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[6276]
    (.letOp (n := 6308) (.exec 0x10d81e (fun s => s.RIP = 0x10d81e) (andR32Imm8Effect 0x10d81e 4 15 0xf) (Reg.operands [.gpr 15] [])) #v[6276]
    (.letOp (n := 6309) (.out 0x10d822 (movR64M64Effect 0x10d822 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6310) (.exec 0x10d822 (LoadPre 0x10d822 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10d822 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d822 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6311) (.out 0x10d827 (mulM64Effect 0x10d827 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6309, 65]
    (.letOp (n := 6312) (.out 0x10d827 (mulM64Effect 0x10d827 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6309, 65]
    (.letOp (n := 6313) (.exec 0x10d827 (LoadPre 0x10d827 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10d827 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d827 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6309, 65]
    (.letOp (n := 6314) (.out 0x10d82c (movR64R64Effect 0x10d82c 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[6312]
    (.letOp (n := 6315) (.exec 0x10d82c (fun s => s.RIP = 0x10d82c) (movR64R64Effect 0x10d82c 6 2) (Reg.operands [.gpr 2] [])) #v[6312]
    (.letOp (n := 6316) (.out 0x10d82f (movR64R64Effect 0x10d82f 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[6311]
    (.letOp (n := 6317) (.exec 0x10d82f (fun s => s.RIP = 0x10d82f) (movR64R64Effect 0x10d82f 14 0) (Reg.operands [.gpr 0] [])) #v[6311]
    (.letOp (n := 6318) (.out 0x10d832 (movR64M64Effect 0x10d832 5 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 6319) (.exec 0x10d832 (LoadPre 0x10d832 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10d832 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d832 5 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6320) (.out 0x10d83a (movR64R64Effect 0x10d83a 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[6318]
    (.letOp (n := 6321) (.exec 0x10d83a (fun s => s.RIP = 0x10d83a) (movR64R64Effect 0x10d83a 0 5) (Reg.operands [.gpr 5] [])) #v[6318]
    (.letOp (n := 6322) (.out 0x10d83d (movR64M64Effect 0x10d83d 8 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 6323) (.exec 0x10d83d (LoadPre 0x10d83d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10d83d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d83d 8 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6324) (.out 0x10d842 (mulR64Effect 0x10d842 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[6322, 6320]
    (.letOp (n := 6325) (.out 0x10d842 (mulR64Effect 0x10d842 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[6322, 6320]
    (.letOp (n := 6326) (.exec 0x10d842 (fun s => s.RIP = 0x10d842) (mulR64Effect 0x10d842 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[6322, 6320]
    (.letOp (n := 6327) (.out 0x10d845 (addR64R64Effect 0x10d845 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[6324, 6316]
    (.letOp (n := 6328) (.out 0x10d845 (addR64R64Effect 0x10d845 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[6324, 6316]
    (.letOp (n := 6329) (.exec 0x10d845 (fun s => s.RIP = 0x10d845) (addR64R64Effect 0x10d845 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[6324, 6316]
    (.letOp (n := 6330) (.out 0x10d848 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d848 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[6314, 6325, 6328]
    (.letOp (n := 6331) (.exec 0x10d848 (fun s => s.RIP = 0x10d848) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d848 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6314, 6325, 6328]
    (.letOp (n := 6332) (.out 0x10d84b (addR64R64Effect 0x10d84b 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[6327, 6303]
    (.letOp (n := 6333) (.out 0x10d84b (addR64R64Effect 0x10d84b 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[6327, 6303]
    (.letOp (n := 6334) (.exec 0x10d84b (fun s => s.RIP = 0x10d84b) (addR64R64Effect 0x10d84b 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[6327, 6303]
    (b_l10a410_149))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_148 : List UInt8 :=
  [0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD5, 0x48, 0x89, 0xC7, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00,
    0x00, 0x4C, 0x8B, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xC3, 0x48,
    0x89, 0xD3, 0x41, 0x83, 0xE7, 0x0F, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x48, 0xF7, 0x64, 0x24, 0x20,
    0x48, 0x89, 0xD6, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0xAC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89,
    0xE8, 0x4C, 0x8B, 0x44, 0x24, 0x40, 0x49, 0xF7, 0xE0, 0x4C, 0x01, 0xF0, 0x48, 0x11, 0xD6, 0x4C,
    0x01, 0xD8] ++ bytes_l10a410_149

theorem code_l10a410_148 : ∀ x ∈ codeRange 0x10d7fc bytes_l10a410_148, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd7fc 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_149

def b_l10a410_147 : Block Op Label signature Reg.count 6247 :=
  .letOp (n := 6247) (.out 0x10d7a7 (addR64M64Effect 0x10d7a7 11 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4] []) (.reg (.gpr 11))) #v[6242, 65]
    (.letOp (n := 6248) (.out 0x10d7a7 (addR64M64Effect 0x10d7a7 11 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 4] []) (.flag .CF)) #v[6242, 65]
    (.letOp (n := 6249) (.exec 0x10d7a7 (LoadPre 0x10d7a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10d7a7 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d7a7 11 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[6242, 65]
    (.letOp (n := 6250) (.out 0x10d7ac (atFlags StatusFlags.CF (adcR64M64Effect 0x10d7ac 9 (.sib 4 none 0 (.d8 0x58)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[6245, 65, 6248]
    (.letOp (n := 6251) (.exec 0x10d7ac (LoadPre 0x10d7ac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10d7ac + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d7ac 9 (.sib 4 none 0 (.d8 0x58)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6245, 65, 6248]
    (.letOp (n := 6252) (.out 0x10d7b1 (addR64M64Effect 0x10d7b1 11 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4] []) (.reg (.gpr 11))) #v[6247, 65]
    (.letOp (n := 6253) (.out 0x10d7b1 (addR64M64Effect 0x10d7b1 11 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 4] []) (.flag .CF)) #v[6247, 65]
    (.letOp (n := 6254) (.exec 0x10d7b1 (LoadPre 0x10d7b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10d7b1 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d7b1 11 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[6247, 65]
    (.letOp (n := 6255) (.out 0x10d7b6 (atFlags StatusFlags.CF (adcR64M64Effect 0x10d7b6 9 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[6250, 65, 6253]
    (.letOp (n := 6256) (.exec 0x10d7b6 (LoadPre 0x10d7b6 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d7b6 + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d7b6 9 (.sib 4 none 0 .none))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6250, 65, 6253]
    (.letOp (n := 6257) (.out 0x10d7ba (addR64R64Effect 0x10d7ba 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[6252, 6226]
    (.letOp (n := 6258) (.out 0x10d7ba (addR64R64Effect 0x10d7ba 11 0) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 0] []) (.flag .CF)) #v[6252, 6226]
    (.letOp (n := 6259) (.exec 0x10d7ba (fun s => s.RIP = 0x10d7ba) (addR64R64Effect 0x10d7ba 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[6252, 6226]
    (.letOp (n := 6260) (.out 0x10d7bd (atFlags StatusFlags.CF (adcR64R64Effect 0x10d7bd 9 6)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[6255, 6229, 6258]
    (.letOp (n := 6261) (.exec 0x10d7bd (fun s => s.RIP = 0x10d7bd) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d7bd 9 6)) (Reg.operands [.gpr 9, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6255, 6229, 6258]
    (.letOp (n := 6262) (.out 0x10d7c0 (addR64R64Effect 0x10d7c0 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[6257, 6233]
    (.letOp (n := 6263) (.out 0x10d7c0 (addR64R64Effect 0x10d7c0 11 1) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 1] []) (.flag .CF)) #v[6257, 6233]
    (.letOp (n := 6264) (.exec 0x10d7c0 (fun s => s.RIP = 0x10d7c0) (addR64R64Effect 0x10d7c0 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[6257, 6233]
    (.letOp (n := 6265) (.exec 0x10d7c3 (StorePre 0x10d7c3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10d7c3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d7c3 11 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[6262, 65]
    (.letOp (n := 6266) (.out 0x10d7c8 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d7c8 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[6260, 6235, 6263]
    (.letOp (n := 6267) (.exec 0x10d7c8 (fun s => s.RIP = 0x10d7c8) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d7c8 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6260, 6235, 6263]
    (.letOp (n := 6268) (.out 0x10d7cb (movR64R64Effect 0x10d7cb 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[6266]
    (.letOp (n := 6269) (.exec 0x10d7cb (fun s => s.RIP = 0x10d7cb) (movR64R64Effect 0x10d7cb 12 9) (Reg.operands [.gpr 9] [])) #v[6266]
    (.letOp (n := 6270) (.out 0x10d7ce (shldR64R64Effect 0x10d7ce 5 9 11 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[6266, 6262]
    (.letOp (n := 6271) (.exec 0x10d7ce (fun s => s.RIP = 0x10d7ce) (shldR64R64Effect 0x10d7ce 5 9 11 12) (Reg.operands [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6266, 6262]
    (.letOp (n := 6272) (.out 0x10d7d3 (shrR64Effect 0x10d7d3 4 12 52) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[6268]
    (.letOp (n := 6273) (.exec 0x10d7d3 (fun s => s.RIP = 0x10d7d3) (shrR64Effect 0x10d7d3 4 12 52) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6268]
    (.letOp (n := 6274) (.out 0x10d7d7 (movR64R64Effect 0x10d7d7 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 11] []) (.reg (.gpr 15))) #v[6262]
    (.letOp (n := 6275) (.exec 0x10d7d7 (fun s => s.RIP = 0x10d7d7) (movR64R64Effect 0x10d7d7 15 11) (Reg.operands [.gpr 11] [])) #v[6262]
    (.letOp (n := 6276) (.out 0x10d7da (shrR64Effect 0x10d7da 4 15 48) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[6274]
    (.letOp (n := 6277) (.exec 0x10d7da (fun s => s.RIP = 0x10d7da) (shrR64Effect 0x10d7da 4 15 48) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6274]
    (.letOp (n := 6278) (.out 0x10d7de (movR64R64Effect 0x10d7de 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[6207]
    (.letOp (n := 6279) (.exec 0x10d7de (fun s => s.RIP = 0x10d7de) (movR64R64Effect 0x10d7de 0 7) (Reg.operands [.gpr 7] [])) #v[6207]
    (.letOp (n := 6280) (.out 0x10d7e1 (mulM64Effect 0x10d7e1 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6278, 65]
    (.letOp (n := 6281) (.out 0x10d7e1 (mulM64Effect 0x10d7e1 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[6278, 65]
    (.letOp (n := 6282) (.exec 0x10d7e1 (LoadPre 0x10d7e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10d7e1 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10d7e1 8 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6278, 65]
    (.letOp (n := 6283) (.exec 0x10d7e9 (StorePre 0x10d7e9 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d7e9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10d7e9 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6281, 65]
    (.letOp (n := 6284) (.exec 0x10d7ed (StorePre 0x10d7ed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10d7ed + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d7ed 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6280, 65]
    (.letOp (n := 6285) (.out 0x10d7f2 (movR64M64Effect 0x10d7f2 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6286) (.exec 0x10d7f2 (LoadPre 0x10d7f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10d7f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d7f2 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6287) (.out 0x10d7f7 (movR64M64Effect 0x10d7f7 1 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 6288) (.exec 0x10d7f7 (LoadPre 0x10d7f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10d7f7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d7f7 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_148))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_147 : List UInt8 :=
  [0x4C, 0x03, 0x5C, 0x24, 0x48, 0x4C, 0x13, 0x4C, 0x24, 0x58, 0x4C, 0x03, 0x5C, 0x24, 0x08, 0x4C,
    0x13, 0x0C, 0x24, 0x49, 0x01, 0xC3, 0x49, 0x11, 0xF1, 0x49, 0x01, 0xCB, 0x4C, 0x89, 0x5C, 0x24,
    0x58, 0x49, 0x11, 0xD1, 0x4D, 0x89, 0xCC, 0x4D, 0x0F, 0xA4, 0xD9, 0x0C, 0x49, 0xC1, 0xEC, 0x34,
    0x4D, 0x89, 0xDF, 0x49, 0xC1, 0xEF, 0x30, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0xA4, 0x24, 0x90, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x14, 0x24, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x44, 0x24, 0x18,
    0x48, 0x8B, 0x4C, 0x24, 0x78] ++ bytes_l10a410_148

theorem code_l10a410_147 : ∀ x ∈ codeRange 0x10d7a7 bytes_l10a410_147, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd7a7 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_148

def b_l10a410_146 : Block Op Label signature Reg.count 6203 :=
  .letOp (n := 6203) (.out 0x10d75a (movR64R64Effect 0x10d75a 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[6201]
    (.letOp (n := 6204) (.exec 0x10d75a (fun s => s.RIP = 0x10d75a) (movR64R64Effect 0x10d75a 12 2) (Reg.operands [.gpr 2] [])) #v[6201]
    (.letOp (n := 6205) (.out 0x10d75d (movR64R64Effect 0x10d75d 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[6200]
    (.letOp (n := 6206) (.exec 0x10d75d (fun s => s.RIP = 0x10d75d) (movR64R64Effect 0x10d75d 13 0) (Reg.operands [.gpr 0] [])) #v[6200]
    (.letOp (n := 6207) (.out 0x10d760 (movR64M64Effect 0x10d760 7 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 6208) (.exec 0x10d760 (LoadPre 0x10d760 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10d760 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d760 7 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6209) (.out 0x10d768 (movR64R64Effect 0x10d768 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[6207]
    (.letOp (n := 6210) (.exec 0x10d768 (fun s => s.RIP = 0x10d768) (movR64R64Effect 0x10d768 0 7) (Reg.operands [.gpr 7] [])) #v[6207]
    (.letOp (n := 6211) (.out 0x10d76b (mulR64Effect 0x10d76b 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[6128, 6209]
    (.letOp (n := 6212) (.out 0x10d76b (mulR64Effect 0x10d76b 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[6128, 6209]
    (.letOp (n := 6213) (.exec 0x10d76b (fun s => s.RIP = 0x10d76b) (mulR64Effect 0x10d76b 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[6128, 6209]
    (.letOp (n := 6214) (.out 0x10d76e (movR64R64Effect 0x10d76e 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[6211]
    (.letOp (n := 6215) (.exec 0x10d76e (fun s => s.RIP = 0x10d76e) (movR64R64Effect 0x10d76e 11 0) (Reg.operands [.gpr 0] [])) #v[6211]
    (.letOp (n := 6216) (.out 0x10d771 (movR64R64Effect 0x10d771 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[6212]
    (.letOp (n := 6217) (.exec 0x10d771 (fun s => s.RIP = 0x10d771) (movR64R64Effect 0x10d771 9 2) (Reg.operands [.gpr 2] [])) #v[6212]
    (.letOp (n := 6218) (.out 0x10d774 (shrR64Effect 0x10d774 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[6135]
    (.letOp (n := 6219) (.exec 0x10d774 (fun s => s.RIP = 0x10d774) (shrR64Effect 0x10d774 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6135]
    (.letOp (n := 6220) (.out 0x10d778 (movR64Imm64Effect 0x10d778 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 6221) (.exec 0x10d778 (fun s => s.RIP = 0x10d778) (movR64Imm64Effect 0x10d778 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 6222) (.out 0x10d782 (imulR64R64Effect 0x10d782 4 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[6218, 6220]
    (.letOp (n := 6223) (.exec 0x10d782 (fun s => s.RIP = 0x10d782) (imulR64R64Effect 0x10d782 4 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6218, 6220]
    (.letOp (n := 6224) (.out 0x10d786 (movR64R64Effect 0x10d786 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[6173]
    (.letOp (n := 6225) (.exec 0x10d786 (fun s => s.RIP = 0x10d786) (movR64R64Effect 0x10d786 0 10) (Reg.operands [.gpr 10] [])) #v[6173]
    (.letOp (n := 6226) (.out 0x10d789 (mulR64Effect 0x10d789 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[6220, 6224]
    (.letOp (n := 6227) (.out 0x10d789 (mulR64Effect 0x10d789 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[6220, 6224]
    (.letOp (n := 6228) (.exec 0x10d789 (fun s => s.RIP = 0x10d789) (mulR64Effect 0x10d789 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[6220, 6224]
    (.letOp (n := 6229) (.out 0x10d78c (addR64R64Effect 0x10d78c 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[6222, 6227]
    (.letOp (n := 6230) (.exec 0x10d78c (fun s => s.RIP = 0x10d78c) (addR64R64Effect 0x10d78c 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6222, 6227]
    (.letOp (n := 6231) (.out 0x10d78f (movR64R64Effect 0x10d78f 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[6171]
    (.letOp (n := 6232) (.exec 0x10d78f (fun s => s.RIP = 0x10d78f) (movR64R64Effect 0x10d78f 2 1) (Reg.operands [.gpr 1] [])) #v[6171]
    (.letOp (n := 6233) (.out 0x10d792 (shldR64R64Effect 0x10d792 5 1 8 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[6171, 6167]
    (.letOp (n := 6234) (.exec 0x10d792 (fun s => s.RIP = 0x10d792) (shldR64R64Effect 0x10d792 5 1 8 12) (Reg.operands [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6171, 6167]
    (.letOp (n := 6235) (.out 0x10d797 (shrR64Effect 0x10d797 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[6231]
    (.letOp (n := 6236) (.exec 0x10d797 (fun s => s.RIP = 0x10d797) (shrR64Effect 0x10d797 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6231]
    (.letOp (n := 6237) (.out 0x10d79b (addR64R64Effect 0x10d79b 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13] []) (.reg (.gpr 11))) #v[6214, 6205]
    (.letOp (n := 6238) (.out 0x10d79b (addR64R64Effect 0x10d79b 11 13) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 13] []) (.flag .CF)) #v[6214, 6205]
    (.letOp (n := 6239) (.exec 0x10d79b (fun s => s.RIP = 0x10d79b) (addR64R64Effect 0x10d79b 11 13) (Reg.operands [.gpr 11, .gpr 13] [])) #v[6214, 6205]
    (.letOp (n := 6240) (.out 0x10d79e (atFlags StatusFlags.CF (adcR64R64Effect 0x10d79e 9 12)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[6216, 6203, 6238]
    (.letOp (n := 6241) (.exec 0x10d79e (fun s => s.RIP = 0x10d79e) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d79e 9 12)) (Reg.operands [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6216, 6203, 6238]
    (.letOp (n := 6242) (.out 0x10d7a1 (addR64R64Effect 0x10d7a1 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[6237, 6196]
    (.letOp (n := 6243) (.out 0x10d7a1 (addR64R64Effect 0x10d7a1 11 15) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 15] []) (.flag .CF)) #v[6237, 6196]
    (.letOp (n := 6244) (.exec 0x10d7a1 (fun s => s.RIP = 0x10d7a1) (addR64R64Effect 0x10d7a1 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[6237, 6196]
    (.letOp (n := 6245) (.out 0x10d7a4 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d7a4 9 14)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[6240, 6194, 6243]
    (.letOp (n := 6246) (.exec 0x10d7a4 (fun s => s.RIP = 0x10d7a4) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d7a4 9 14)) (Reg.operands [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6240, 6194, 6243]
    (b_l10a410_147))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_146 : List UInt8 :=
  [0x49, 0x89, 0xD4, 0x49, 0x89, 0xC5, 0x48, 0x8B, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89,
    0xF8, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xC3, 0x49, 0x89, 0xD1, 0x48, 0xC1, 0xEE, 0x34, 0x48, 0xBA,
    0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xF2, 0x4C, 0x89, 0xD0, 0x48,
    0xF7, 0xE2, 0x48, 0x01, 0xD6, 0x48, 0x89, 0xCA, 0x4C, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0xC1, 0xEA,
    0x34, 0x4D, 0x01, 0xEB, 0x4D, 0x11, 0xE1, 0x4D, 0x01, 0xFB, 0x4D, 0x11, 0xF1] ++ bytes_l10a410_147

theorem code_l10a410_146 : ∀ x ∈ codeRange 0x10d75a bytes_l10a410_146, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd75a 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_147

def b_l10a410_145 : Block Op Label signature Reg.count 6162 :=
  .letOp (n := 6162) (.out 0x10d70b (addR64M64Effect 0x10d70b 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[6157, 65]
    (.letOp (n := 6163) (.out 0x10d70b (addR64M64Effect 0x10d70b 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[6157, 65]
    (.letOp (n := 6164) (.exec 0x10d70b (LoadPre 0x10d70b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10d70b + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d70b 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[6157, 65]
    (.letOp (n := 6165) (.out 0x10d710 (atFlags StatusFlags.CF (adcR64M64Effect 0x10d710 1 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[6160, 65, 6163]
    (.letOp (n := 6166) (.exec 0x10d710 (LoadPre 0x10d710 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d710 + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d710 1 (.sib 4 none 0 .none))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6160, 65, 6163]
    (.letOp (n := 6167) (.out 0x10d714 (addR64R64Effect 0x10d714 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[6162, 6148]
    (.letOp (n := 6168) (.out 0x10d714 (addR64R64Effect 0x10d714 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[6162, 6148]
    (.letOp (n := 6169) (.exec 0x10d714 (fun s => s.RIP = 0x10d714) (addR64R64Effect 0x10d714 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[6162, 6148]
    (.letOp (n := 6170) (.exec 0x10d717 (StorePre 0x10d717 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10d717 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d717 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[6167, 65]
    (.letOp (n := 6171) (.out 0x10d71c (atFlags StatusFlags.CF (adcR64R64Effect 0x10d71c 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[6165, 6149, 6168]
    (.letOp (n := 6172) (.exec 0x10d71c (fun s => s.RIP = 0x10d71c) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d71c 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6165, 6149, 6168]
    (.letOp (n := 6173) (.out 0x10d71f (shrdR64R64Effect 0x10d71f 5 10 6 52) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[6133, 6135]
    (.letOp (n := 6174) (.exec 0x10d71f (fun s => s.RIP = 0x10d71f) (shrdR64R64Effect 0x10d71f 5 10 6 52) (Reg.operands [.gpr 10, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6133, 6135]
    (.letOp (n := 6175) (.out 0x10d724 (movR64R64Effect 0x10d724 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[6124]
    (.letOp (n := 6176) (.exec 0x10d724 (fun s => s.RIP = 0x10d724) (movR64R64Effect 0x10d724 0 15) (Reg.operands [.gpr 15] [])) #v[6124]
    (.letOp (n := 6177) (.out 0x10d727 (mulR64Effect 0x10d727 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[6081, 6175]
    (.letOp (n := 6178) (.out 0x10d727 (mulR64Effect 0x10d727 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[6081, 6175]
    (.letOp (n := 6179) (.exec 0x10d727 (fun s => s.RIP = 0x10d727) (mulR64Effect 0x10d727 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[6081, 6175]
    (.letOp (n := 6180) (.exec 0x10d72a (StorePre 0x10d72a 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d72a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10d72a 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6178, 65]
    (.letOp (n := 6181) (.exec 0x10d72e (StorePre 0x10d72e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10d72e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d72e 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6177, 65]
    (.letOp (n := 6182) (.out 0x10d733 (movR64M64Effect 0x10d733 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6183) (.exec 0x10d733 (LoadPre 0x10d733 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10d733 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d733 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6184) (.out 0x10d73b (mulR64Effect 0x10d73b 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[6092, 6182]
    (.letOp (n := 6185) (.out 0x10d73b (mulR64Effect 0x10d73b 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[6092, 6182]
    (.letOp (n := 6186) (.exec 0x10d73b (fun s => s.RIP = 0x10d73b) (mulR64Effect 0x10d73b 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[6092, 6182]
    (.letOp (n := 6187) (.exec 0x10d73e (StorePre 0x10d73e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10d73e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d73e 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6185, 65]
    (.letOp (n := 6188) (.exec 0x10d743 (StorePre 0x10d743 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10d743 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d743 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6184, 65]
    (.letOp (n := 6189) (.out 0x10d748 (movR64R64Effect 0x10d748 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[6088]
    (.letOp (n := 6190) (.exec 0x10d748 (fun s => s.RIP = 0x10d748) (movR64R64Effect 0x10d748 0 14) (Reg.operands [.gpr 14] [])) #v[6088]
    (.letOp (n := 6191) (.out 0x10d74b (mulR64Effect 0x10d74b 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[6106, 6189]
    (.letOp (n := 6192) (.out 0x10d74b (mulR64Effect 0x10d74b 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[6106, 6189]
    (.letOp (n := 6193) (.exec 0x10d74b (fun s => s.RIP = 0x10d74b) (mulR64Effect 0x10d74b 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[6106, 6189]
    (.letOp (n := 6194) (.out 0x10d74e (movR64R64Effect 0x10d74e 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[6192]
    (.letOp (n := 6195) (.exec 0x10d74e (fun s => s.RIP = 0x10d74e) (movR64R64Effect 0x10d74e 14 2) (Reg.operands [.gpr 2] [])) #v[6192]
    (.letOp (n := 6196) (.out 0x10d751 (movR64R64Effect 0x10d751 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[6191]
    (.letOp (n := 6197) (.exec 0x10d751 (fun s => s.RIP = 0x10d751) (movR64R64Effect 0x10d751 15 0) (Reg.operands [.gpr 0] [])) #v[6191]
    (.letOp (n := 6198) (.out 0x10d754 (movR64R64Effect 0x10d754 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[6102]
    (.letOp (n := 6199) (.exec 0x10d754 (fun s => s.RIP = 0x10d754) (movR64R64Effect 0x10d754 0 3) (Reg.operands [.gpr 3] [])) #v[6102]
    (.letOp (n := 6200) (.out 0x10d757 (mulR64Effect 0x10d757 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[6115, 6198]
    (.letOp (n := 6201) (.out 0x10d757 (mulR64Effect 0x10d757 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[6115, 6198]
    (.letOp (n := 6202) (.exec 0x10d757 (fun s => s.RIP = 0x10d757) (mulR64Effect 0x10d757 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[6115, 6198]
    (b_l10a410_146)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_145 : List UInt8 :=
  [0x4C, 0x03, 0x44, 0x24, 0x10, 0x48, 0x13, 0x0C, 0x24, 0x49, 0x01, 0xC0, 0x4C, 0x89, 0x44, 0x24,
    0x10, 0x48, 0x11, 0xD1, 0x49, 0x0F, 0xAC, 0xF2, 0x34, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE5, 0x48,
    0x89, 0x14, 0x24, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00,
    0x49, 0xF7, 0xE4, 0x48, 0x89, 0x54, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x48, 0x4C, 0x89, 0xF0,
    0x49, 0xF7, 0xE3, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC7, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE1] ++ bytes_l10a410_146

theorem code_l10a410_145 : ∀ x ∈ codeRange 0x10d70b bytes_l10a410_145, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd70b 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_146

def b_l10a410_144 : Block Op Label signature Reg.count 6120 :=
  .letOp (n := 6120) (.out 0x10d6ae (movR64R64Effect 0x10d6ae 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[6118]
    (.letOp (n := 6121) (.exec 0x10d6ae (fun s => s.RIP = 0x10d6ae) (movR64R64Effect 0x10d6ae 1 2) (Reg.operands [.gpr 2] [])) #v[6118]
    (.letOp (n := 6122) (.out 0x10d6b1 (movR64R64Effect 0x10d6b1 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[6117]
    (.letOp (n := 6123) (.exec 0x10d6b1 (fun s => s.RIP = 0x10d6b1) (movR64R64Effect 0x10d6b1 8 0) (Reg.operands [.gpr 0] [])) #v[6117]
    (.letOp (n := 6124) (.out 0x10d6b4 (movR64M64Effect 0x10d6b4 15 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 6125) (.exec 0x10d6b4 (LoadPre 0x10d6b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10d6b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d6b4 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6126) (.out 0x10d6b9 (movR64R64Effect 0x10d6b9 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[6124]
    (.letOp (n := 6127) (.exec 0x10d6b9 (fun s => s.RIP = 0x10d6b9) (movR64R64Effect 0x10d6b9 0 15) (Reg.operands [.gpr 15] [])) #v[6124]
    (.letOp (n := 6128) (.out 0x10d6bc (movR64M64Effect 0x10d6bc 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 6129) (.exec 0x10d6bc (LoadPre 0x10d6bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10d6bc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d6bc 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6130) (.out 0x10d6c1 (mulR64Effect 0x10d6c1 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[6128, 6126]
    (.letOp (n := 6131) (.out 0x10d6c1 (mulR64Effect 0x10d6c1 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[6128, 6126]
    (.letOp (n := 6132) (.exec 0x10d6c1 (fun s => s.RIP = 0x10d6c1) (mulR64Effect 0x10d6c1 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[6128, 6126]
    (.letOp (n := 6133) (.out 0x10d6c4 (movR64R64Effect 0x10d6c4 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[6130]
    (.letOp (n := 6134) (.exec 0x10d6c4 (fun s => s.RIP = 0x10d6c4) (movR64R64Effect 0x10d6c4 10 0) (Reg.operands [.gpr 0] [])) #v[6130]
    (.letOp (n := 6135) (.out 0x10d6c7 (movR64R64Effect 0x10d6c7 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[6131]
    (.letOp (n := 6136) (.exec 0x10d6c7 (fun s => s.RIP = 0x10d6c7) (movR64R64Effect 0x10d6c7 6 2) (Reg.operands [.gpr 2] [])) #v[6131]
    (.letOp (n := 6137) (.out 0x10d6ca (movR64Imm64Effect 0x10d6ca 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 6138) (.exec 0x10d6ca (fun s => s.RIP = 0x10d6ca) (movR64Imm64Effect 0x10d6ca 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 6139) (.out 0x10d6d4 (andR64R64Effect 0x10d6d4 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[6058, 6137]
    (.letOp (n := 6140) (.exec 0x10d6d4 (fun s => s.RIP = 0x10d6d4) (andR64R64Effect 0x10d6d4 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[6058, 6137]
    (.letOp (n := 6141) (.exec 0x10d6d7 (StorePre 0x10d6d7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10d6d7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d6d7 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[6139, 65]
    (.letOp (n := 6142) (.out 0x10d6dc (andR64R64Effect 0x10d6dc 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[6130, 6137]
    (.letOp (n := 6143) (.exec 0x10d6dc (fun s => s.RIP = 0x10d6dc) (andR64R64Effect 0x10d6dc 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[6130, 6137]
    (.letOp (n := 6144) (.out 0x10d6df (movR64R64Effect 0x10d6df 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[6137]
    (.letOp (n := 6145) (.exec 0x10d6df (fun s => s.RIP = 0x10d6df) (movR64R64Effect 0x10d6df 7 2) (Reg.operands [.gpr 2] [])) #v[6137]
    (.letOp (n := 6146) (.out 0x10d6e2 (movR64Imm64Effect 0x10d6e2 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 6147) (.exec 0x10d6e2 (fun s => s.RIP = 0x10d6e2) (movR64Imm64Effect 0x10d6e2 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 6148) (.out 0x10d6ec (mulR64Effect 0x10d6ec 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[6146, 6142]
    (.letOp (n := 6149) (.out 0x10d6ec (mulR64Effect 0x10d6ec 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[6146, 6142]
    (.letOp (n := 6150) (.exec 0x10d6ec (fun s => s.RIP = 0x10d6ec) (mulR64Effect 0x10d6ec 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[6146, 6142]
    (.letOp (n := 6151) (.exec 0x10d6ef (StorePre 0x10d6ef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10d6ef + BitVec.ofNat 64 5)) 8) (andMREffect 0x10d6ef 5 64 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[6144, 65]
    (.letOp (n := 6152) (.out 0x10d6f4 (addR64M64Effect 0x10d6f4 8 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[6122, 65]
    (.letOp (n := 6153) (.out 0x10d6f4 (addR64M64Effect 0x10d6f4 8 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[6122, 65]
    (.letOp (n := 6154) (.exec 0x10d6f4 (LoadPre 0x10d6f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10d6f4 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10d6f4 8 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[6122, 65]
    (.letOp (n := 6155) (.out 0x10d6fc (atFlags StatusFlags.CF (adcR64M64Effect 0x10d6fc 1 (.sib 4 none 0 (.d8 0x48)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[6120, 65, 6153]
    (.letOp (n := 6156) (.exec 0x10d6fc (LoadPre 0x10d6fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10d6fc + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d6fc 1 (.sib 4 none 0 (.d8 0x48)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6120, 65, 6153]
    (.letOp (n := 6157) (.out 0x10d701 (addR64M64Effect 0x10d701 8 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[6152, 65]
    (.letOp (n := 6158) (.out 0x10d701 (addR64M64Effect 0x10d701 8 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[6152, 65]
    (.letOp (n := 6159) (.exec 0x10d701 (LoadPre 0x10d701 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10d701 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d701 8 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[6152, 65]
    (.letOp (n := 6160) (.out 0x10d706 (atFlags StatusFlags.CF (adcR64M64Effect 0x10d706 1 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[6155, 65, 6158]
    (.letOp (n := 6161) (.exec 0x10d706 (LoadPre 0x10d706 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10d706 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d706 1 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[6155, 65, 6158]
    (b_l10a410_145))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_144 : List UInt8 :=
  [0x48, 0x89, 0xD1, 0x49, 0x89, 0xC0, 0x4C, 0x8B, 0x7C, 0x24, 0x18, 0x4C, 0x89, 0xF8, 0x48, 0x8B,
    0x6C, 0x24, 0x40, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xC2, 0x48, 0x89, 0xD6, 0x48, 0xBA, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD7, 0x48, 0x89, 0x7C, 0x24, 0x50, 0x48, 0x21,
    0xD0, 0x48, 0x89, 0xD7, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xE2, 0x48, 0x21, 0x7C, 0x24, 0x38, 0x4C, 0x03, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x13,
    0x4C, 0x24, 0x48, 0x4C, 0x03, 0x44, 0x24, 0x58, 0x48, 0x13, 0x4C, 0x24, 0x08] ++ bytes_l10a410_145

theorem code_l10a410_144 : ∀ x ∈ codeRange 0x10d6ae bytes_l10a410_144, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd6ae 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_145

def b_l10a410_143 : Block Op Label signature Reg.count 6083 :=
  .letOp (n := 6083) (.out 0x10d64d (mulR64Effect 0x10d64d 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[6081, 6079]
    (.letOp (n := 6084) (.out 0x10d64d (mulR64Effect 0x10d64d 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[6081, 6079]
    (.letOp (n := 6085) (.exec 0x10d64d (fun s => s.RIP = 0x10d64d) (mulR64Effect 0x10d64d 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[6081, 6079]
    (.letOp (n := 6086) (.exec 0x10d650 (StorePre 0x10d650 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d650 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10d650 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6084, 65]
    (.letOp (n := 6087) (.exec 0x10d654 (StorePre 0x10d654 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10d654 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d654 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6083, 65]
    (.letOp (n := 6088) (.out 0x10d659 (movR64M64Effect 0x10d659 14 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 6089) (.exec 0x10d659 (LoadPre 0x10d659 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10d659 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d659 14 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6090) (.out 0x10d65e (movR64R64Effect 0x10d65e 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[6088]
    (.letOp (n := 6091) (.exec 0x10d65e (fun s => s.RIP = 0x10d65e) (movR64R64Effect 0x10d65e 0 14) (Reg.operands [.gpr 14] [])) #v[6088]
    (.letOp (n := 6092) (.out 0x10d661 (movR64M64Effect 0x10d661 12 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 6093) (.exec 0x10d661 (LoadPre 0x10d661 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10d661 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d661 12 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6094) (.out 0x10d666 (mulR64Effect 0x10d666 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[6092, 6090]
    (.letOp (n := 6095) (.out 0x10d666 (mulR64Effect 0x10d666 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[6092, 6090]
    (.letOp (n := 6096) (.exec 0x10d666 (fun s => s.RIP = 0x10d666) (mulR64Effect 0x10d666 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[6092, 6090]
    (.letOp (n := 6097) (.exec 0x10d669 (StorePre 0x10d669 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10d669 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d669 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6094, 65]
    (.letOp (n := 6098) (.exec 0x10d66e (StorePre 0x10d66e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10d66e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d66e 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6095, 65]
    (.letOp (n := 6099) (.out 0x10d673 (andR64R64Effect 0x10d673 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[6054, 6014]
    (.letOp (n := 6100) (.exec 0x10d673 (fun s => s.RIP = 0x10d673) (andR64R64Effect 0x10d673 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[6054, 6014]
    (.letOp (n := 6101) (.exec 0x10d676 (StorePre 0x10d676 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10d676 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d676 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[6099, 65]
    (.letOp (n := 6102) (.out 0x10d67b (movR64M64Effect 0x10d67b 3 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 6103) (.exec 0x10d67b (LoadPre 0x10d67b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10d67b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d67b 3 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6104) (.out 0x10d683 (movR64R64Effect 0x10d683 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[6102]
    (.letOp (n := 6105) (.exec 0x10d683 (fun s => s.RIP = 0x10d683) (movR64R64Effect 0x10d683 0 3) (Reg.operands [.gpr 3] [])) #v[6102]
    (.letOp (n := 6106) (.out 0x10d686 (movR64M64Effect 0x10d686 11 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 6107) (.exec 0x10d686 (LoadPre 0x10d686 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10d686 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d686 11 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6108) (.out 0x10d68e (mulR64Effect 0x10d68e 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[6106, 6104]
    (.letOp (n := 6109) (.out 0x10d68e (mulR64Effect 0x10d68e 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[6106, 6104]
    (.letOp (n := 6110) (.exec 0x10d68e (fun s => s.RIP = 0x10d68e) (mulR64Effect 0x10d68e 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[6106, 6104]
    (.letOp (n := 6111) (.exec 0x10d691 (StorePre 0x10d691 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10d691 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d691 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6109, 65]
    (.letOp (n := 6112) (.exec 0x10d696 (StorePre 0x10d696 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10d696 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10d696 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6108, 65]
    (.letOp (n := 6113) (.out 0x10d69e (movR64M64Effect 0x10d69e 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6114) (.exec 0x10d69e (LoadPre 0x10d69e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10d69e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d69e 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6115) (.out 0x10d6a6 (movR64M64Effect 0x10d6a6 9 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 6116) (.exec 0x10d6a6 (LoadPre 0x10d6a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10d6a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d6a6 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6117) (.out 0x10d6ab (mulR64Effect 0x10d6ab 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[6115, 6113]
    (.letOp (n := 6118) (.out 0x10d6ab (mulR64Effect 0x10d6ab 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[6115, 6113]
    (.letOp (n := 6119) (.exec 0x10d6ab (fun s => s.RIP = 0x10d6ab) (mulR64Effect 0x10d6ab 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[6115, 6113]
    (b_l10a410_144)))))))))))))))))))))))))))))))))))))

def bytes_l10a410_143 : List UInt8 :=
  [0x49, 0xF7, 0xE5, 0x48, 0x89, 0x14, 0x24, 0x48, 0x89, 0x44, 0x24, 0x10, 0x4C, 0x8B, 0x74, 0x24,
    0x70, 0x4C, 0x89, 0xF0, 0x4C, 0x8B, 0x64, 0x24, 0x78, 0x49, 0xF7, 0xE4, 0x48, 0x89, 0x44, 0x24,
    0x58, 0x48, 0x89, 0x54, 0x24, 0x08, 0x4D, 0x21, 0xD0, 0x4C, 0x89, 0x44, 0x24, 0x30, 0x48, 0x8B,
    0x9C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD8, 0x4C, 0x8B, 0x9C, 0x24, 0xF0, 0x00, 0x00,
    0x00, 0x49, 0xF7, 0xE3, 0x48, 0x89, 0x54, 0x24, 0x48, 0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00,
    0x00, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x4C, 0x24, 0x20, 0x49, 0xF7,
    0xE1] ++ bytes_l10a410_144

theorem code_l10a410_143 : ∀ x ∈ codeRange 0x10d64d bytes_l10a410_143, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd64d 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_144

def b_l10a410_142 : Block Op Label signature Reg.count 6046 :=
  .letOp (n := 6046) (.out 0x10d5fa (movR64R64Effect 0x10d5fa 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[6042]
    (.letOp (n := 6047) (.exec 0x10d5fa (fun s => s.RIP = 0x10d5fa) (movR64R64Effect 0x10d5fa 9 7) (Reg.operands [.gpr 7] [])) #v[6042]
    (.letOp (n := 6048) (.out 0x10d5fd (shrR64Effect 0x10d5fd 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[6044]
    (.letOp (n := 6049) (.exec 0x10d5fd (fun s => s.RIP = 0x10d5fd) (shrR64Effect 0x10d5fd 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6044]
    (.letOp (n := 6050) (.out 0x10d601 (addR64R64Effect 0x10d601 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[6048, 6030]
    (.letOp (n := 6051) (.exec 0x10d601 (fun s => s.RIP = 0x10d601) (addR64R64Effect 0x10d601 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[6048, 6030]
    (.letOp (n := 6052) (.out 0x10d604 (movR64R64Effect 0x10d604 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[6050]
    (.letOp (n := 6053) (.exec 0x10d604 (fun s => s.RIP = 0x10d604) (movR64R64Effect 0x10d604 7 2) (Reg.operands [.gpr 2] [])) #v[6050]
    (.letOp (n := 6054) (.out 0x10d607 (movR64R64Effect 0x10d607 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[6050]
    (.letOp (n := 6055) (.exec 0x10d607 (fun s => s.RIP = 0x10d607) (movR64R64Effect 0x10d607 8 2) (Reg.operands [.gpr 2] [])) #v[6050]
    (.letOp (n := 6056) (.out 0x10d60a (shrR64Effect 0x10d60a 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6052]
    (.letOp (n := 6057) (.exec 0x10d60a (fun s => s.RIP = 0x10d60a) (shrR64Effect 0x10d60a 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6052]
    (.letOp (n := 6058) (.out 0x10d60e (addR64R64Effect 0x10d60e 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[6056, 6032]
    (.letOp (n := 6059) (.exec 0x10d60e (fun s => s.RIP = 0x10d60e) (addR64R64Effect 0x10d60e 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[6056, 6032]
    (.letOp (n := 6060) (.out 0x10d611 (movR64R64Effect 0x10d611 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[6058]
    (.letOp (n := 6061) (.exec 0x10d611 (fun s => s.RIP = 0x10d611) (movR64R64Effect 0x10d611 2 7) (Reg.operands [.gpr 7] [])) #v[6058]
    (.letOp (n := 6062) (.out 0x10d614 (shrR64Effect 0x10d614 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[6060]
    (.letOp (n := 6063) (.exec 0x10d614 (fun s => s.RIP = 0x10d614) (shrR64Effect 0x10d614 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6060]
    (.letOp (n := 6064) (.out 0x10d618 (addR64R64Effect 0x10d618 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[6062, 6016]
    (.letOp (n := 6065) (.exec 0x10d618 (fun s => s.RIP = 0x10d618) (addR64R64Effect 0x10d618 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[6062, 6016]
    (.letOp (n := 6066) (.exec 0x10d61b (StorePre 0x10d61b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10d61b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d61b 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6064, 65]
    (.letOp (n := 6067) (.out 0x10d620 (andR64R64Effect 0x10d620 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[6024, 6018]
    (.letOp (n := 6068) (.exec 0x10d620 (fun s => s.RIP = 0x10d620) (andR64R64Effect 0x10d620 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[6024, 6018]
    (.letOp (n := 6069) (.out 0x10d623 (movR64R64Effect 0x10d623 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[6064]
    (.letOp (n := 6070) (.exec 0x10d623 (fun s => s.RIP = 0x10d623) (movR64R64Effect 0x10d623 0 2) (Reg.operands [.gpr 2] [])) #v[6064]
    (.letOp (n := 6071) (.out 0x10d626 (shrR64Effect 0x10d626 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[6069]
    (.letOp (n := 6072) (.exec 0x10d626 (fun s => s.RIP = 0x10d626) (shrR64Effect 0x10d626 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6069]
    (.letOp (n := 6073) (.out 0x10d62a (addR64R64Effect 0x10d62a 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[6071, 6067]
    (.letOp (n := 6074) (.exec 0x10d62a (fun s => s.RIP = 0x10d62a) (addR64R64Effect 0x10d62a 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[6071, 6067]
    (.letOp (n := 6075) (.exec 0x10d62d (StorePre 0x10d62d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10d62d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10d62d 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6073, 65]
    (.letOp (n := 6076) (.out 0x10d635 (andR64R64Effect 0x10d635 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[6046, 6014]
    (.letOp (n := 6077) (.exec 0x10d635 (fun s => s.RIP = 0x10d635) (andR64R64Effect 0x10d635 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[6046, 6014]
    (.letOp (n := 6078) (.exec 0x10d638 (StorePre 0x10d638 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10d638 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d638 9 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[6076, 65]
    (.letOp (n := 6079) (.out 0x10d63d (movR64M64Effect 0x10d63d 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 6080) (.exec 0x10d63d (LoadPre 0x10d63d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10d63d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d63d 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6081) (.out 0x10d645 (movR64M64Effect 0x10d645 13 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 6082) (.exec 0x10d645 (LoadPre 0x10d645 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10d645 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d645 13 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_143)))))))))))))))))))))))))))))))))))))

def bytes_l10a410_142 : List UInt8 :=
  [0x49, 0x89, 0xF9, 0x48, 0xC1, 0xEA, 0x34, 0x4C, 0x01, 0xF2, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xD0,
    0x48, 0xC1, 0xEF, 0x34, 0x48, 0x01, 0xDF, 0x48, 0x89, 0xFA, 0x48, 0xC1, 0xEA, 0x34, 0x48, 0x01,
    0xEA, 0x48, 0x89, 0x54, 0x24, 0x38, 0x48, 0x21, 0xC6, 0x48, 0x89, 0xD0, 0x48, 0xC1, 0xE8, 0x34,
    0x48, 0x01, 0xF0, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4D, 0x21, 0xD1, 0x4C, 0x89,
    0x4C, 0x24, 0x28, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0xAC, 0x24, 0x90,
    0x00, 0x00, 0x00] ++ bytes_l10a410_143

theorem code_l10a410_142 : ∀ x ∈ codeRange 0x10d5fa bytes_l10a410_142, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd5fa 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_143

def b_l10a410_141 : Block Op Label signature Reg.count 6005 :=
  .letOp (n := 6005) (.out 0x10d597 (addR64R64Effect 0x10d597 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[6000, 5985]
    (.letOp (n := 6006) (.out 0x10d597 (addR64R64Effect 0x10d597 5 9) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 9] []) (.flag .CF)) #v[6000, 5985]
    (.letOp (n := 6007) (.exec 0x10d597 (fun s => s.RIP = 0x10d597) (addR64R64Effect 0x10d597 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[6000, 5985]
    (.letOp (n := 6008) (.out 0x10d59a (atFlags StatusFlags.CF (adcR64R64Effect 0x10d59a 2 1)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[6003, 5987, 6006]
    (.letOp (n := 6009) (.exec 0x10d59a (fun s => s.RIP = 0x10d59a) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d59a 2 1)) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6003, 5987, 6006]
    (.letOp (n := 6010) (.out 0x10d59d (shldR64R64Effect 0x10d59d 5 2 5 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[6008, 6005]
    (.letOp (n := 6011) (.exec 0x10d59d (fun s => s.RIP = 0x10d59d) (shldR64R64Effect 0x10d59d 5 2 5 12) (Reg.operands [.gpr 2, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6008, 6005]
    (.letOp (n := 6012) (.out 0x10d5a2 (andR64R64Effect 0x10d5a2 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[6005, 5950]
    (.letOp (n := 6013) (.exec 0x10d5a2 (fun s => s.RIP = 0x10d5a2) (andR64R64Effect 0x10d5a2 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[6005, 5950]
    (.letOp (n := 6014) (.out 0x10d5a5 (movR64R64Effect 0x10d5a5 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[5950]
    (.letOp (n := 6015) (.exec 0x10d5a5 (fun s => s.RIP = 0x10d5a5) (movR64R64Effect 0x10d5a5 10 8) (Reg.operands [.gpr 8] [])) #v[5950]
    (.letOp (n := 6016) (.out 0x10d5a8 (addR64M64Effect 0x10d5a8 5 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[6012, 65]
    (.letOp (n := 6017) (.exec 0x10d5a8 (LoadPre 0x10d5a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10d5a8 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10d5a8 5 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[6012, 65]
    (.letOp (n := 6018) (.out 0x10d5b0 (movR64Imm64Effect 0x10d5b0 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 6019) (.exec 0x10d5b0 (fun s => s.RIP = 0x10d5b0) (movR64Imm64Effect 0x10d5b0 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 6020) (.out 0x10d5ba (andR64R64Effect 0x10d5ba 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[5682, 6018]
    (.letOp (n := 6021) (.exec 0x10d5ba (fun s => s.RIP = 0x10d5ba) (andR64R64Effect 0x10d5ba 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[5682, 6018]
    (.letOp (n := 6022) (.out 0x10d5bd (addR64R64Effect 0x10d5bd 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[6020, 6010]
    (.letOp (n := 6023) (.exec 0x10d5bd (fun s => s.RIP = 0x10d5bd) (addR64R64Effect 0x10d5bd 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6020, 6010]
    (.letOp (n := 6024) (.out 0x10d5c0 (addR64M64Effect 0x10d5c0 6 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[6022, 65]
    (.letOp (n := 6025) (.exec 0x10d5c0 (LoadPre 0x10d5c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10d5c0 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10d5c0 6 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6022, 65]
    (.letOp (n := 6026) (.out 0x10d5c8 (movR64M64Effect 0x10d5c8 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 6027) (.exec 0x10d5c8 (LoadPre 0x10d5c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10d5c8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d5c8 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 6028) (.out 0x10d5cd (addR64M64Effect 0x10d5cd 2 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[6026, 65]
    (.letOp (n := 6029) (.exec 0x10d5cd (LoadPre 0x10d5cd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10d5cd + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10d5cd 2 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6026, 65]
    (.letOp (n := 6030) (.out 0x10d5d5 (addR64M64Effect 0x10d5d5 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[5918, 65]
    (.letOp (n := 6031) (.exec 0x10d5d5 (LoadPre 0x10d5d5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10d5d5 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d5d5 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[5918, 65]
    (.letOp (n := 6032) (.out 0x10d5da (addR64M64Effect 0x10d5da 3 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[5989, 65]
    (.letOp (n := 6033) (.exec 0x10d5da (LoadPre 0x10d5da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10d5da + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d5da 3 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[5989, 65]
    (.letOp (n := 6034) (.out 0x10d5df (movR64R64Effect 0x10d5df 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6024]
    (.letOp (n := 6035) (.exec 0x10d5df (fun s => s.RIP = 0x10d5df) (movR64R64Effect 0x10d5df 7 6) (Reg.operands [.gpr 6] [])) #v[6024]
    (.letOp (n := 6036) (.out 0x10d5e2 (shrR64Effect 0x10d5e2 4 7 48) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6034]
    (.letOp (n := 6037) (.exec 0x10d5e2 (fun s => s.RIP = 0x10d5e2) (shrR64Effect 0x10d5e2 4 7 48) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6034]
    (.letOp (n := 6038) (.out 0x10d5e6 (movR64Imm64Effect 0x10d5e6 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 6039) (.exec 0x10d5e6 (fun s => s.RIP = 0x10d5e6) (movR64Imm64Effect 0x10d5e6 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 6040) (.out 0x10d5f0 (imulR64R64Effect 0x10d5f0 4 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[6036, 6038]
    (.letOp (n := 6041) (.exec 0x10d5f0 (fun s => s.RIP = 0x10d5f0) (imulR64R64Effect 0x10d5f0 4 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[6036, 6038]
    (.letOp (n := 6042) (.out 0x10d5f4 (addR64R64Effect 0x10d5f4 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[6040, 6028]
    (.letOp (n := 6043) (.exec 0x10d5f4 (fun s => s.RIP = 0x10d5f4) (addR64R64Effect 0x10d5f4 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[6040, 6028]
    (.letOp (n := 6044) (.out 0x10d5f7 (movR64R64Effect 0x10d5f7 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[6042]
    (.letOp (n := 6045) (.exec 0x10d5f7 (fun s => s.RIP = 0x10d5f7) (movR64R64Effect 0x10d5f7 2 7) (Reg.operands [.gpr 7] [])) #v[6042]
    (b_l10a410_142)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_141 : List UInt8 :=
  [0x4C, 0x01, 0xCD, 0x48, 0x11, 0xCA, 0x48, 0x0F, 0xA4, 0xEA, 0x0C, 0x4C, 0x21, 0xC5, 0x4D, 0x89,
    0xC2, 0x48, 0x03, 0xAC, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x00, 0x00, 0x48, 0x21, 0xC6, 0x48, 0x01, 0xD6, 0x48, 0x03, 0xB4, 0x24, 0xC8, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x54, 0x24, 0x30, 0x48, 0x03, 0x94, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x4C, 0x03,
    0x74, 0x24, 0x08, 0x48, 0x03, 0x5C, 0x24, 0x58, 0x48, 0x89, 0xF7, 0x48, 0xC1, 0xEF, 0x30, 0x48,
    0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xF9, 0x48, 0x01, 0xD7,
    0x48, 0x89, 0xFA] ++ bytes_l10a410_142

theorem code_l10a410_141 : ∀ x ∈ codeRange 0x10d597 bytes_l10a410_141, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd597 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_142

def b_l10a410_140 : Block Op Label signature Reg.count 5959 :=
  .letOp (n := 5959) (.out 0x10d549 (addR64M64Effect 0x10d549 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[5909, 65]
    (.letOp (n := 5960) (.out 0x10d549 (addR64M64Effect 0x10d549 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[5909, 65]
    (.letOp (n := 5961) (.exec 0x10d549 (LoadPre 0x10d549 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10d549 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d549 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[5909, 65]
    (.letOp (n := 5962) (.out 0x10d54e (atFlags StatusFlags.CF (adcR64M64Effect 0x10d54e 9 (.sib 4 none 0 (.d32 0x80)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[5907, 65, 5960]
    (.letOp (n := 5963) (.exec 0x10d54e (LoadPre 0x10d54e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10d54e + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d54e 9 (.sib 4 none 0 (.d32 0x80)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5907, 65, 5960]
    (.letOp (n := 5964) (.out 0x10d556 (addR64M64Effect 0x10d556 3 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[5959, 65]
    (.letOp (n := 5965) (.out 0x10d556 (addR64M64Effect 0x10d556 3 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[5959, 65]
    (.letOp (n := 5966) (.exec 0x10d556 (LoadPre 0x10d556 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10d556 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d556 3 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[5959, 65]
    (.letOp (n := 5967) (.out 0x10d55b (atFlags StatusFlags.CF (adcR64M64Effect 0x10d55b 9 (.sib 4 none 0 (.d8 0x38)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[5962, 65, 5965]
    (.letOp (n := 5968) (.exec 0x10d55b (LoadPre 0x10d55b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10d55b + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d55b 9 (.sib 4 none 0 (.d8 0x38)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5962, 65, 5965]
    (.letOp (n := 5969) (.out 0x10d560 (addR64R64Effect 0x10d560 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[5964, 5956]
    (.letOp (n := 5970) (.out 0x10d560 (addR64R64Effect 0x10d560 3 0) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 0] []) (.flag .CF)) #v[5964, 5956]
    (.letOp (n := 5971) (.exec 0x10d560 (fun s => s.RIP = 0x10d560) (addR64R64Effect 0x10d560 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[5964, 5956]
    (.letOp (n := 5972) (.out 0x10d563 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d563 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[5967, 5957, 5970]
    (.letOp (n := 5973) (.exec 0x10d563 (fun s => s.RIP = 0x10d563) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d563 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5967, 5957, 5970]
    (.letOp (n := 5974) (.out 0x10d566 (addR64R64Effect 0x10d566 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[5969, 5893]
    (.letOp (n := 5975) (.out 0x10d566 (addR64R64Effect 0x10d566 3 1) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 1] []) (.flag .CF)) #v[5969, 5893]
    (.letOp (n := 5976) (.exec 0x10d566 (fun s => s.RIP = 0x10d566) (addR64R64Effect 0x10d566 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[5969, 5893]
    (.letOp (n := 5977) (.out 0x10d569 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d569 9 13)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[5972, 5891, 5975]
    (.letOp (n := 5978) (.exec 0x10d569 (fun s => s.RIP = 0x10d569) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d569 9 13)) (Reg.operands [.gpr 9, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5972, 5891, 5975]
    (.letOp (n := 5979) (.out 0x10d56c (shrdR64R64Effect 0x10d56c 5 11 12 52) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[5943, 5946]
    (.letOp (n := 5980) (.exec 0x10d56c (fun s => s.RIP = 0x10d56c) (shrdR64R64Effect 0x10d56c 5 11 12 52) (Reg.operands [.gpr 11, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5943, 5946]
    (.letOp (n := 5981) (.out 0x10d571 (shrR64Effect 0x10d571 4 12 52) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[5946]
    (.letOp (n := 5982) (.exec 0x10d571 (fun s => s.RIP = 0x10d571) (shrR64Effect 0x10d571 4 12 52) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5946]
    (.letOp (n := 5983) (.out 0x10d575 (movR64R64Effect 0x10d575 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[5977]
    (.letOp (n := 5984) (.exec 0x10d575 (fun s => s.RIP = 0x10d575) (movR64R64Effect 0x10d575 1 9) (Reg.operands [.gpr 9] [])) #v[5977]
    (.letOp (n := 5985) (.out 0x10d578 (shldR64R64Effect 0x10d578 5 9 3 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[5977, 5974]
    (.letOp (n := 5986) (.exec 0x10d578 (fun s => s.RIP = 0x10d578) (shldR64R64Effect 0x10d578 5 9 3 12) (Reg.operands [.gpr 9, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5977, 5974]
    (.letOp (n := 5987) (.out 0x10d57d (shrR64Effect 0x10d57d 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5983]
    (.letOp (n := 5988) (.exec 0x10d57d (fun s => s.RIP = 0x10d57d) (shrR64Effect 0x10d57d 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5983]
    (.letOp (n := 5989) (.out 0x10d581 (andR64R64Effect 0x10d581 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[5974, 5950]
    (.letOp (n := 5990) (.exec 0x10d581 (fun s => s.RIP = 0x10d581) (andR64R64Effect 0x10d581 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[5974, 5950]
    (.letOp (n := 5991) (.out 0x10d584 (imulR64R64Effect 0x10d584 4 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[5981, 5954]
    (.letOp (n := 5992) (.exec 0x10d584 (fun s => s.RIP = 0x10d584) (imulR64R64Effect 0x10d584 4 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[5981, 5954]
    (.letOp (n := 5993) (.out 0x10d588 (movR64R64Effect 0x10d588 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[5979]
    (.letOp (n := 5994) (.exec 0x10d588 (fun s => s.RIP = 0x10d588) (movR64R64Effect 0x10d588 0 11) (Reg.operands [.gpr 11] [])) #v[5979]
    (.letOp (n := 5995) (.out 0x10d58b (mulR64Effect 0x10d58b 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[5954, 5993]
    (.letOp (n := 5996) (.out 0x10d58b (mulR64Effect 0x10d58b 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[5954, 5993]
    (.letOp (n := 5997) (.exec 0x10d58b (fun s => s.RIP = 0x10d58b) (mulR64Effect 0x10d58b 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[5954, 5993]
    (.letOp (n := 5998) (.out 0x10d58e (andR64R64Effect 0x10d58e 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[5593, 5950]
    (.letOp (n := 5999) (.exec 0x10d58e (fun s => s.RIP = 0x10d58e) (andR64R64Effect 0x10d58e 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[5593, 5950]
    (.letOp (n := 6000) (.out 0x10d591 (addR64R64Effect 0x10d591 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[5998, 5995]
    (.letOp (n := 6001) (.out 0x10d591 (addR64R64Effect 0x10d591 5 0) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 0] []) (.flag .CF)) #v[5998, 5995]
    (.letOp (n := 6002) (.exec 0x10d591 (fun s => s.RIP = 0x10d591) (addR64R64Effect 0x10d591 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[5998, 5995]
    (.letOp (n := 6003) (.out 0x10d594 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d594 2 12)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[5996, 5991, 6001]
    (.letOp (n := 6004) (.exec 0x10d594 (fun s => s.RIP = 0x10d594) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d594 2 12)) (Reg.operands [.gpr 2, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5996, 5991, 6001]
    (b_l10a410_141))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_140 : List UInt8 :=
  [0x48, 0x03, 0x5C, 0x24, 0x28, 0x4C, 0x13, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x03, 0x5C,
    0x24, 0x50, 0x4C, 0x13, 0x4C, 0x24, 0x38, 0x48, 0x01, 0xC3, 0x49, 0x11, 0xD1, 0x48, 0x01, 0xCB,
    0x4D, 0x11, 0xE9, 0x4D, 0x0F, 0xAC, 0xE3, 0x34, 0x49, 0xC1, 0xEC, 0x34, 0x4C, 0x89, 0xC9, 0x49,
    0x0F, 0xA4, 0xD9, 0x0C, 0x48, 0xC1, 0xE9, 0x34, 0x4C, 0x21, 0xC3, 0x4C, 0x0F, 0xAF, 0xE7, 0x4C,
    0x89, 0xD8, 0x48, 0xF7, 0xE7, 0x4C, 0x21, 0xC5, 0x48, 0x01, 0xC5, 0x4C, 0x11, 0xE2] ++ bytes_l10a410_141

theorem code_l10a410_140 : ∀ x ∈ codeRange 0x10d549 bytes_l10a410_140, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd549 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_141

def b_l10a410_139 : Block Op Label signature Reg.count 5916 :=
  .letOp (n := 5916) (.exec 0x10d4ee (StorePre 0x10d4ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10d4ee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d4ee 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5913, 65]
    (.letOp (n := 5917) (.exec 0x10d4f3 (StorePre 0x10d4f3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10d4f3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d4f3 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5914, 65]
    (.letOp (n := 5918) (.out 0x10d4f8 (andR64R64Effect 0x10d4f8 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[5878, 5859]
    (.letOp (n := 5919) (.exec 0x10d4f8 (fun s => s.RIP = 0x10d4f8) (andR64R64Effect 0x10d4f8 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[5878, 5859]
    (.letOp (n := 5920) (.out 0x10d4fb (movR64M64Effect 0x10d4fb 0 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5921) (.exec 0x10d4fb (LoadPre 0x10d4fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10d4fb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d4fb 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5922) (.out 0x10d503 (mulM64Effect 0x10d503 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5920, 65]
    (.letOp (n := 5923) (.out 0x10d503 (mulM64Effect 0x10d503 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5920, 65]
    (.letOp (n := 5924) (.exec 0x10d503 (LoadPre 0x10d503 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10d503 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d503 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5920, 65]
    (.letOp (n := 5925) (.out 0x10d508 (movR64R64Effect 0x10d508 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[5923]
    (.letOp (n := 5926) (.exec 0x10d508 (fun s => s.RIP = 0x10d508) (movR64R64Effect 0x10d508 7 2) (Reg.operands [.gpr 2] [])) #v[5923]
    (.letOp (n := 5927) (.out 0x10d50b (movR64R64Effect 0x10d50b 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[5922]
    (.letOp (n := 5928) (.exec 0x10d50b (fun s => s.RIP = 0x10d50b) (movR64R64Effect 0x10d50b 8 0) (Reg.operands [.gpr 0] [])) #v[5922]
    (.letOp (n := 5929) (.out 0x10d50e (movR64M64Effect 0x10d50e 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5930) (.exec 0x10d50e (LoadPre 0x10d50e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10d50e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d50e 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5931) (.out 0x10d516 (mulM64Effect 0x10d516 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5929, 65]
    (.letOp (n := 5932) (.out 0x10d516 (mulM64Effect 0x10d516 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5929, 65]
    (.letOp (n := 5933) (.exec 0x10d516 (LoadPre 0x10d516 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d516 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x10d516 4 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5929, 65]
    (.letOp (n := 5934) (.out 0x10d51a (movR64R64Effect 0x10d51a 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[5932]
    (.letOp (n := 5935) (.exec 0x10d51a (fun s => s.RIP = 0x10d51a) (movR64R64Effect 0x10d51a 12 2) (Reg.operands [.gpr 2] [])) #v[5932]
    (.letOp (n := 5936) (.out 0x10d51d (movR64R64Effect 0x10d51d 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[5931]
    (.letOp (n := 5937) (.exec 0x10d51d (fun s => s.RIP = 0x10d51d) (movR64R64Effect 0x10d51d 11 0) (Reg.operands [.gpr 0] [])) #v[5931]
    (.letOp (n := 5938) (.out 0x10d520 (addR64R64Effect 0x10d520 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[5936, 5927]
    (.letOp (n := 5939) (.out 0x10d520 (addR64R64Effect 0x10d520 11 8) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 8] []) (.flag .CF)) #v[5936, 5927]
    (.letOp (n := 5940) (.exec 0x10d520 (fun s => s.RIP = 0x10d520) (addR64R64Effect 0x10d520 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[5936, 5927]
    (.letOp (n := 5941) (.out 0x10d523 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d523 12 7)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[5934, 5925, 5939]
    (.letOp (n := 5942) (.exec 0x10d523 (fun s => s.RIP = 0x10d523) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d523 12 7)) (Reg.operands [.gpr 12, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5934, 5925, 5939]
    (.letOp (n := 5943) (.out 0x10d526 (addR64R64Effect 0x10d526 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[5938, 5885]
    (.letOp (n := 5944) (.out 0x10d526 (addR64R64Effect 0x10d526 11 15) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 15] []) (.flag .CF)) #v[5938, 5885]
    (.letOp (n := 5945) (.exec 0x10d526 (fun s => s.RIP = 0x10d526) (addR64R64Effect 0x10d526 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[5938, 5885]
    (.letOp (n := 5946) (.out 0x10d529 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d529 12 10)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[5941, 5887, 5944]
    (.letOp (n := 5947) (.exec 0x10d529 (fun s => s.RIP = 0x10d529) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d529 12 10)) (Reg.operands [.gpr 12, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5941, 5887, 5944]
    (.letOp (n := 5948) (.out 0x10d52c (movR64R64Effect 0x10d52c 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[5943]
    (.letOp (n := 5949) (.exec 0x10d52c (fun s => s.RIP = 0x10d52c) (movR64R64Effect 0x10d52c 0 11) (Reg.operands [.gpr 11] [])) #v[5943]
    (.letOp (n := 5950) (.out 0x10d52f (movR64Imm64Effect 0x10d52f 8 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 5951) (.exec 0x10d52f (fun s => s.RIP = 0x10d52f) (movR64Imm64Effect 0x10d52f 8 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 5952) (.out 0x10d539 (andR64R64Effect 0x10d539 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[5948, 5950]
    (.letOp (n := 5953) (.exec 0x10d539 (fun s => s.RIP = 0x10d539) (andR64R64Effect 0x10d539 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[5948, 5950]
    (.letOp (n := 5954) (.out 0x10d53c (movR64Imm64Effect 0x10d53c 7 0x1000003d10) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 5955) (.exec 0x10d53c (fun s => s.RIP = 0x10d53c) (movR64Imm64Effect 0x10d53c 7 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 5956) (.out 0x10d546 (mulR64Effect 0x10d546 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[5954, 5952]
    (.letOp (n := 5957) (.out 0x10d546 (mulR64Effect 0x10d546 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[5954, 5952]
    (.letOp (n := 5958) (.exec 0x10d546 (fun s => s.RIP = 0x10d546) (mulR64Effect 0x10d546 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[5954, 5952]
    (b_l10a410_140)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_139 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0x89, 0x54, 0x24, 0x38, 0x4D, 0x21, 0xC6, 0x48, 0x8B, 0x84,
    0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x10, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0,
    0x48, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0xF7, 0x24, 0x24, 0x49, 0x89, 0xD4, 0x49,
    0x89, 0xC3, 0x4D, 0x01, 0xC3, 0x49, 0x11, 0xFC, 0x4D, 0x01, 0xFB, 0x4D, 0x11, 0xD4, 0x4C, 0x89,
    0xD8, 0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xC0, 0x48, 0xBF,
    0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7] ++ bytes_l10a410_140

theorem code_l10a410_139 : ∀ x ∈ codeRange 0x10d4ee bytes_l10a410_139, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd4ee 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_140

def b_l10a410_138 : Block Op Label signature Reg.count 5873 :=
  .letOp (n := 5873) (.out 0x10d48d (addR64R64Effect 0x10d48d 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[5868, 5865]
    (.letOp (n := 5874) (.out 0x10d48d (addR64R64Effect 0x10d48d 14 0) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 0] []) (.flag .CF)) #v[5868, 5865]
    (.letOp (n := 5875) (.exec 0x10d48d (fun s => s.RIP = 0x10d48d) (addR64R64Effect 0x10d48d 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[5868, 5865]
    (.letOp (n := 5876) (.out 0x10d490 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d490 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[5871, 5866, 5874]
    (.letOp (n := 5877) (.exec 0x10d490 (fun s => s.RIP = 0x10d490) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d490 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5871, 5866, 5874]
    (.letOp (n := 5878) (.out 0x10d493 (addR64R64Effect 0x10d493 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[5873, 5792]
    (.letOp (n := 5879) (.out 0x10d493 (addR64R64Effect 0x10d493 14 9) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 9] []) (.flag .CF)) #v[5873, 5792]
    (.letOp (n := 5880) (.exec 0x10d493 (fun s => s.RIP = 0x10d493) (addR64R64Effect 0x10d493 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[5873, 5792]
    (.letOp (n := 5881) (.out 0x10d496 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d496 1 11)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[5876, 5790, 5879]
    (.letOp (n := 5882) (.exec 0x10d496 (fun s => s.RIP = 0x10d496) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d496 1 11)) (Reg.operands [.gpr 1, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5876, 5790, 5879]
    (.letOp (n := 5883) (.out 0x10d499 (movR64R64Effect 0x10d499 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 15] []) (.reg (.gpr 10))) #v[5855]
    (.letOp (n := 5884) (.exec 0x10d499 (fun s => s.RIP = 0x10d499) (movR64R64Effect 0x10d499 10 15) (Reg.operands [.gpr 15] [])) #v[5855]
    (.letOp (n := 5885) (.out 0x10d49c (shldR64R64Effect 0x10d49c 5 15 7 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[5855, 5852]
    (.letOp (n := 5886) (.exec 0x10d49c (fun s => s.RIP = 0x10d49c) (shldR64R64Effect 0x10d49c 5 15 7 12) (Reg.operands [.gpr 15, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5855, 5852]
    (.letOp (n := 5887) (.out 0x10d4a1 (shrR64Effect 0x10d4a1 4 10 52) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[5883]
    (.letOp (n := 5888) (.exec 0x10d4a1 (fun s => s.RIP = 0x10d4a1) (shrR64Effect 0x10d4a1 4 10 52) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5883]
    (.letOp (n := 5889) (.out 0x10d4a5 (movR64R64Effect 0x10d4a5 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[5881]
    (.letOp (n := 5890) (.exec 0x10d4a5 (fun s => s.RIP = 0x10d4a5) (movR64R64Effect 0x10d4a5 13 1) (Reg.operands [.gpr 1] [])) #v[5881]
    (.letOp (n := 5891) (.out 0x10d4a8 (shrR64Effect 0x10d4a8 4 13 52) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[5889]
    (.letOp (n := 5892) (.exec 0x10d4a8 (fun s => s.RIP = 0x10d4a8) (shrR64Effect 0x10d4a8 4 13 52) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5889]
    (.letOp (n := 5893) (.out 0x10d4ac (shldR64R64Effect 0x10d4ac 5 1 14 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5881, 5878]
    (.letOp (n := 5894) (.exec 0x10d4ac (fun s => s.RIP = 0x10d4ac) (shldR64R64Effect 0x10d4ac 5 1 14 12) (Reg.operands [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5881, 5878]
    (.letOp (n := 5895) (.out 0x10d4b1 (movR64M64Effect 0x10d4b1 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5896) (.exec 0x10d4b1 (LoadPre 0x10d4b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10d4b1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d4b1 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5897) (.out 0x10d4b9 (mulM64Effect 0x10d4b9 8 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5895, 65]
    (.letOp (n := 5898) (.out 0x10d4b9 (mulM64Effect 0x10d4b9 8 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5895, 65]
    (.letOp (n := 5899) (.exec 0x10d4b9 (LoadPre 0x10d4b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x10d4b9 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10d4b9 8 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5895, 65]
    (.letOp (n := 5900) (.exec 0x10d4c1 (StorePre 0x10d4c1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10d4c1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10d4c1 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5898, 65]
    (.letOp (n := 5901) (.exec 0x10d4c9 (StorePre 0x10d4c9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10d4c9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d4c9 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5897, 65]
    (.letOp (n := 5902) (.out 0x10d4ce (movR64M64Effect 0x10d4ce 0 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5903) (.exec 0x10d4ce (LoadPre 0x10d4ce (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10d4ce + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d4ce 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5904) (.out 0x10d4d6 (mulM64Effect 0x10d4d6 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5902, 65]
    (.letOp (n := 5905) (.out 0x10d4d6 (mulM64Effect 0x10d4d6 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5902, 65]
    (.letOp (n := 5906) (.exec 0x10d4d6 (LoadPre 0x10d4d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10d4d6 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d4d6 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5902, 65]
    (.letOp (n := 5907) (.out 0x10d4db (movR64R64Effect 0x10d4db 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[5905]
    (.letOp (n := 5908) (.exec 0x10d4db (fun s => s.RIP = 0x10d4db) (movR64R64Effect 0x10d4db 9 2) (Reg.operands [.gpr 2] [])) #v[5905]
    (.letOp (n := 5909) (.out 0x10d4de (movR64R64Effect 0x10d4de 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[5904]
    (.letOp (n := 5910) (.exec 0x10d4de (fun s => s.RIP = 0x10d4de) (movR64R64Effect 0x10d4de 3 0) (Reg.operands [.gpr 0] [])) #v[5904]
    (.letOp (n := 5911) (.out 0x10d4e1 (movR64M64Effect 0x10d4e1 0 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5912) (.exec 0x10d4e1 (LoadPre 0x10d4e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10d4e1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d4e1 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5913) (.out 0x10d4e9 (mulM64Effect 0x10d4e9 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5911, 65]
    (.letOp (n := 5914) (.out 0x10d4e9 (mulM64Effect 0x10d4e9 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5911, 65]
    (.letOp (n := 5915) (.exec 0x10d4e9 (LoadPre 0x10d4e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10d4e9 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d4e9 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5911, 65]
    (b_l10a410_139)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_138 : List UInt8 :=
  [0x49, 0x01, 0xC6, 0x48, 0x11, 0xD1, 0x4D, 0x01, 0xCE, 0x4C, 0x11, 0xD9, 0x4D, 0x89, 0xFA, 0x49,
    0x0F, 0xA4, 0xFF, 0x0C, 0x49, 0xC1, 0xEA, 0x34, 0x49, 0x89, 0xCD, 0x49, 0xC1, 0xED, 0x34, 0x4C,
    0x0F, 0xA4, 0xF1, 0x0C, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24,
    0x48, 0x01, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24,
    0x28, 0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x50, 0x49, 0x89,
    0xD1, 0x48, 0x89, 0xC3, 0x48, 0x8B, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24,
    0x38] ++ bytes_l10a410_139

theorem code_l10a410_138 : ∀ x ∈ codeRange 0x10d48d bytes_l10a410_138, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd48d 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_139

def b_l10a410_137 : Block Op Label signature Reg.count 5826 :=
  .letOp (n := 5826) (.out 0x10d42f (movR64M64Effect 0x10d42f 0 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5827) (.exec 0x10d42f (LoadPre 0x10d42f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10d42f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d42f 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5828) (.out 0x10d437 (mulM64Effect 0x10d437 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5826, 65]
    (.letOp (n := 5829) (.out 0x10d437 (mulM64Effect 0x10d437 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5826, 65]
    (.letOp (n := 5830) (.exec 0x10d437 (LoadPre 0x10d437 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d437 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x10d437 4 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5826, 65]
    (.letOp (n := 5831) (.out 0x10d43b (movR64R64Effect 0x10d43b 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[5829]
    (.letOp (n := 5832) (.exec 0x10d43b (fun s => s.RIP = 0x10d43b) (movR64R64Effect 0x10d43b 15 2) (Reg.operands [.gpr 2] [])) #v[5829]
    (.letOp (n := 5833) (.out 0x10d43e (movR64R64Effect 0x10d43e 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[5828]
    (.letOp (n := 5834) (.exec 0x10d43e (fun s => s.RIP = 0x10d43e) (movR64R64Effect 0x10d43e 12 0) (Reg.operands [.gpr 0] [])) #v[5828]
    (.letOp (n := 5835) (.out 0x10d441 (movR64M64Effect 0x10d441 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5836) (.exec 0x10d441 (LoadPre 0x10d441 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10d441 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d441 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5837) (.out 0x10d449 (mulM64Effect 0x10d449 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5835, 65]
    (.letOp (n := 5838) (.out 0x10d449 (mulM64Effect 0x10d449 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5835, 65]
    (.letOp (n := 5839) (.exec 0x10d449 (LoadPre 0x10d449 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10d449 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10d449 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5835, 65]
    (.letOp (n := 5840) (.out 0x10d451 (movR64R64Effect 0x10d451 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[5837]
    (.letOp (n := 5841) (.exec 0x10d451 (fun s => s.RIP = 0x10d451) (movR64R64Effect 0x10d451 7 0) (Reg.operands [.gpr 0] [])) #v[5837]
    (.letOp (n := 5842) (.out 0x10d454 (addR64R64Effect 0x10d454 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[5833, 5824]
    (.letOp (n := 5843) (.out 0x10d454 (addR64R64Effect 0x10d454 12 13) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 13] []) (.flag .CF)) #v[5833, 5824]
    (.letOp (n := 5844) (.exec 0x10d454 (fun s => s.RIP = 0x10d454) (addR64R64Effect 0x10d454 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[5833, 5824]
    (.letOp (n := 5845) (.out 0x10d457 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d457 15 8)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[5831, 5822, 5843]
    (.letOp (n := 5846) (.exec 0x10d457 (fun s => s.RIP = 0x10d457) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d457 15 8)) (Reg.operands [.gpr 15, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5831, 5822, 5843]
    (.letOp (n := 5847) (.out 0x10d45a (addR64R64Effect 0x10d45a 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[5840, 5842]
    (.letOp (n := 5848) (.out 0x10d45a (addR64R64Effect 0x10d45a 7 12) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 12] []) (.flag .CF)) #v[5840, 5842]
    (.letOp (n := 5849) (.exec 0x10d45a (fun s => s.RIP = 0x10d45a) (addR64R64Effect 0x10d45a 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[5840, 5842]
    (.letOp (n := 5850) (.out 0x10d45d (atFlags StatusFlags.CF (adcR64R64Effect 0x10d45d 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[5845, 5838, 5848]
    (.letOp (n := 5851) (.exec 0x10d45d (fun s => s.RIP = 0x10d45d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d45d 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5845, 5838, 5848]
    (.letOp (n := 5852) (.out 0x10d460 (addR64R64Effect 0x10d460 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[5847, 5764]
    (.letOp (n := 5853) (.out 0x10d460 (addR64R64Effect 0x10d460 7 3) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 3] []) (.flag .CF)) #v[5847, 5764]
    (.letOp (n := 5854) (.exec 0x10d460 (fun s => s.RIP = 0x10d460) (addR64R64Effect 0x10d460 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[5847, 5764]
    (.letOp (n := 5855) (.out 0x10d463 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d463 15 10)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[5850, 5774, 5853]
    (.letOp (n := 5856) (.exec 0x10d463 (fun s => s.RIP = 0x10d463) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d463 15 10)) (Reg.operands [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5850, 5774, 5853]
    (.letOp (n := 5857) (.out 0x10d466 (movR64R64Effect 0x10d466 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[5852]
    (.letOp (n := 5858) (.exec 0x10d466 (fun s => s.RIP = 0x10d466) (movR64R64Effect 0x10d466 0 7) (Reg.operands [.gpr 7] [])) #v[5852]
    (.letOp (n := 5859) (.out 0x10d469 (movR64Imm64Effect 0x10d469 8 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 5860) (.exec 0x10d469 (fun s => s.RIP = 0x10d469) (movR64Imm64Effect 0x10d469 8 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 5861) (.out 0x10d473 (andR64R64Effect 0x10d473 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[5857, 5859]
    (.letOp (n := 5862) (.exec 0x10d473 (fun s => s.RIP = 0x10d473) (andR64R64Effect 0x10d473 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[5857, 5859]
    (.letOp (n := 5863) (.out 0x10d476 (movR64Imm64Effect 0x10d476 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 5864) (.exec 0x10d476 (fun s => s.RIP = 0x10d476) (movR64Imm64Effect 0x10d476 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 5865) (.out 0x10d480 (mulR64Effect 0x10d480 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[5863, 5861]
    (.letOp (n := 5866) (.out 0x10d480 (mulR64Effect 0x10d480 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[5863, 5861]
    (.letOp (n := 5867) (.exec 0x10d480 (fun s => s.RIP = 0x10d480) (mulR64Effect 0x10d480 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[5863, 5861]
    (.letOp (n := 5868) (.out 0x10d483 (addR64M64Effect 0x10d483 14 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[5808, 65]
    (.letOp (n := 5869) (.out 0x10d483 (addR64M64Effect 0x10d483 14 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 4] []) (.flag .CF)) #v[5808, 65]
    (.letOp (n := 5870) (.exec 0x10d483 (LoadPre 0x10d483 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10d483 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d483 14 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[5808, 65]
    (.letOp (n := 5871) (.out 0x10d488 (atFlags StatusFlags.CF (adcR64M64Effect 0x10d488 1 (.sib 4 none 0 (.d8 0x28)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[5810, 65, 5869]
    (.letOp (n := 5872) (.exec 0x10d488 (LoadPre 0x10d488 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10d488 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d488 1 (.sib 4 none 0 (.d8 0x28)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5810, 65, 5869]
    (b_l10a410_138)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_137 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0xF7, 0x24, 0x24, 0x49, 0x89, 0xD7, 0x49,
    0x89, 0xC4, 0x48, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x48, 0x89, 0xC7, 0x4D, 0x01, 0xEC, 0x4D, 0x11, 0xC7, 0x4C, 0x01, 0xE7, 0x49, 0x11,
    0xD7, 0x48, 0x01, 0xDF, 0x4D, 0x11, 0xD7, 0x48, 0x89, 0xF8, 0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xC0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00,
    0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x03, 0x74, 0x24, 0x48, 0x48, 0x13, 0x4C, 0x24, 0x28] ++ bytes_l10a410_138

theorem code_l10a410_137 : ∀ x ∈ codeRange 0x10d42f bytes_l10a410_137, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd42f 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_138

def b_l10a410_136 : Block Op Label signature Reg.count 5786 :=
  .letOp (n := 5786) (.out 0x10d3d3 (atFlags StatusFlags.CF (adcR64M64Effect 0x10d3d3 9 (.sib 4 none 0 (.d8 0x30)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[5781, 65, 5784]
    (.letOp (n := 5787) (.exec 0x10d3d3 (LoadPre 0x10d3d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10d3d3 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d3d3 9 (.sib 4 none 0 (.d8 0x30)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5781, 65, 5784]
    (.letOp (n := 5788) (.out 0x10d3d8 (movR64R64Effect 0x10d3d8 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[5786]
    (.letOp (n := 5789) (.exec 0x10d3d8 (fun s => s.RIP = 0x10d3d8) (movR64R64Effect 0x10d3d8 11 9) (Reg.operands [.gpr 9] [])) #v[5786]
    (.letOp (n := 5790) (.out 0x10d3db (shrR64Effect 0x10d3db 4 11 52) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[5788]
    (.letOp (n := 5791) (.exec 0x10d3db (fun s => s.RIP = 0x10d3db) (shrR64Effect 0x10d3db 4 11 52) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5788]
    (.letOp (n := 5792) (.out 0x10d3df (shldR64R64Effect 0x10d3df 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[5786, 5783]
    (.letOp (n := 5793) (.exec 0x10d3df (fun s => s.RIP = 0x10d3df) (shldR64R64Effect 0x10d3df 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5786, 5783]
    (.letOp (n := 5794) (.out 0x10d3e4 (movR64R64Effect 0x10d3e4 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[5783]
    (.letOp (n := 5795) (.exec 0x10d3e4 (fun s => s.RIP = 0x10d3e4) (movR64R64Effect 0x10d3e4 7 0) (Reg.operands [.gpr 0] [])) #v[5783]
    (.letOp (n := 5796) (.out 0x10d3e7 (movR64M64Effect 0x10d3e7 0 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5797) (.exec 0x10d3e7 (LoadPre 0x10d3e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x10d3e7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d3e7 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5798) (.out 0x10d3ef (mulR64Effect 0x10d3ef 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[5735, 5796]
    (.letOp (n := 5799) (.out 0x10d3ef (mulR64Effect 0x10d3ef 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[5735, 5796]
    (.letOp (n := 5800) (.exec 0x10d3ef (fun s => s.RIP = 0x10d3ef) (mulR64Effect 0x10d3ef 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5735, 5796]
    (.letOp (n := 5801) (.exec 0x10d3f2 (StorePre 0x10d3f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10d3f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d3f2 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5799, 65]
    (.letOp (n := 5802) (.exec 0x10d3f7 (StorePre 0x10d3f7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10d3f7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d3f7 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5798, 65]
    (.letOp (n := 5803) (.out 0x10d3fc (movR64R64Effect 0x10d3fc 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[5702]
    (.letOp (n := 5804) (.exec 0x10d3fc (fun s => s.RIP = 0x10d3fc) (movR64R64Effect 0x10d3fc 0 14) (Reg.operands [.gpr 14] [])) #v[5702]
    (.letOp (n := 5805) (.out 0x10d3ff (mulM64Effect 0x10d3ff 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5803, 65]
    (.letOp (n := 5806) (.out 0x10d3ff (mulM64Effect 0x10d3ff 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5803, 65]
    (.letOp (n := 5807) (.exec 0x10d3ff (LoadPre 0x10d3ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10d3ff + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d3ff 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5803, 65]
    (.letOp (n := 5808) (.out 0x10d404 (movR64R64Effect 0x10d404 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[5805]
    (.letOp (n := 5809) (.exec 0x10d404 (fun s => s.RIP = 0x10d404) (movR64R64Effect 0x10d404 14 0) (Reg.operands [.gpr 0] [])) #v[5805]
    (.letOp (n := 5810) (.out 0x10d407 (movR64R64Effect 0x10d407 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[5806]
    (.letOp (n := 5811) (.exec 0x10d407 (fun s => s.RIP = 0x10d407) (movR64R64Effect 0x10d407 1 2) (Reg.operands [.gpr 2] [])) #v[5806]
    (.letOp (n := 5812) (.out 0x10d40a (movR64Imm64Effect 0x10d40a 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 5813) (.exec 0x10d40a (fun s => s.RIP = 0x10d40a) (movR64Imm64Effect 0x10d40a 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 5814) (.out 0x10d414 (andR64R64Effect 0x10d414 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[5794, 5812]
    (.letOp (n := 5815) (.exec 0x10d414 (fun s => s.RIP = 0x10d414) (andR64R64Effect 0x10d414 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[5794, 5812]
    (.letOp (n := 5816) (.exec 0x10d417 (StorePre 0x10d417 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10d417 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d417 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[5814, 65]
    (.letOp (n := 5817) (.out 0x10d41c (movR64M64Effect 0x10d41c 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5818) (.exec 0x10d41c (LoadPre 0x10d41c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10d41c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d41c 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5819) (.out 0x10d421 (mulM64Effect 0x10d421 8 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5817, 65]
    (.letOp (n := 5820) (.out 0x10d421 (mulM64Effect 0x10d421 8 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5817, 65]
    (.letOp (n := 5821) (.exec 0x10d421 (LoadPre 0x10d421 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10d421 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10d421 8 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5817, 65]
    (.letOp (n := 5822) (.out 0x10d429 (movR64R64Effect 0x10d429 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[5820]
    (.letOp (n := 5823) (.exec 0x10d429 (fun s => s.RIP = 0x10d429) (movR64R64Effect 0x10d429 8 2) (Reg.operands [.gpr 2] [])) #v[5820]
    (.letOp (n := 5824) (.out 0x10d42c (movR64R64Effect 0x10d42c 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[5819]
    (.letOp (n := 5825) (.exec 0x10d42c (fun s => s.RIP = 0x10d42c) (movR64R64Effect 0x10d42c 13 0) (Reg.operands [.gpr 0] [])) #v[5819]
    (b_l10a410_137))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_136 : List UInt8 :=
  [0x4C, 0x13, 0x4C, 0x24, 0x30, 0x4D, 0x89, 0xCB, 0x49, 0xC1, 0xEB, 0x34, 0x49, 0x0F, 0xA4, 0xC1,
    0x0C, 0x48, 0x89, 0xC7, 0x48, 0x8B, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48,
    0x89, 0x54, 0x24, 0x28, 0x48, 0x89, 0x44, 0x24, 0x48, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0x64, 0x24,
    0x38, 0x49, 0x89, 0xC6, 0x48, 0x89, 0xD1, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F,
    0x00, 0x48, 0x21, 0xC7, 0x48, 0x89, 0x7C, 0x24, 0x30, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0xF7,
    0xA4, 0x24, 0x40, 0x01, 0x00, 0x00, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC5] ++ bytes_l10a410_137

theorem code_l10a410_136 : ∀ x ∈ codeRange 0x10d3d3 bytes_l10a410_136, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd3d3 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_137

def b_l10a410_135 : Block Op Label signature Reg.count 5740 :=
  .letOp (n := 5740) (.out 0x10d382 (andR32Imm8Effect 0x10d382 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[5713]
    (.letOp (n := 5741) (.exec 0x10d382 (fun s => s.RIP = 0x10d382) (andR32Imm8Effect 0x10d382 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[5713]
    (.letOp (n := 5742) (.out 0x10d386 (addR64R64Effect 0x10d386 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[5722, 5707]
    (.letOp (n := 5743) (.out 0x10d386 (addR64R64Effect 0x10d386 9 7) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 7] []) (.flag .CF)) #v[5722, 5707]
    (.letOp (n := 5744) (.exec 0x10d386 (fun s => s.RIP = 0x10d386) (addR64R64Effect 0x10d386 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[5722, 5707]
    (.letOp (n := 5745) (.out 0x10d389 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d389 3 8)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[5720, 5709, 5743]
    (.letOp (n := 5746) (.exec 0x10d389 (fun s => s.RIP = 0x10d389) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d389 3 8)) (Reg.operands [.gpr 3, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5720, 5709, 5743]
    (.letOp (n := 5747) (.out 0x10d38c (addR64R64Effect 0x10d38c 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[5742, 5731]
    (.letOp (n := 5748) (.out 0x10d38c (addR64R64Effect 0x10d38c 9 15) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 15] []) (.flag .CF)) #v[5742, 5731]
    (.letOp (n := 5749) (.exec 0x10d38c (fun s => s.RIP = 0x10d38c) (addR64R64Effect 0x10d38c 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[5742, 5731]
    (.letOp (n := 5750) (.out 0x10d38f (atFlags StatusFlags.CF (adcR64R64Effect 0x10d38f 3 11)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[5745, 5729, 5748]
    (.letOp (n := 5751) (.exec 0x10d38f (fun s => s.RIP = 0x10d38f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d38f 3 11)) (Reg.operands [.gpr 3, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5745, 5729, 5748]
    (.letOp (n := 5752) (.out 0x10d392 (addR64R64Effect 0x10d392 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[5737, 5747]
    (.letOp (n := 5753) (.out 0x10d392 (addR64R64Effect 0x10d392 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[5737, 5747]
    (.letOp (n := 5754) (.exec 0x10d392 (fun s => s.RIP = 0x10d392) (addR64R64Effect 0x10d392 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[5737, 5747]
    (.letOp (n := 5755) (.out 0x10d395 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d395 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[5750, 5738, 5753]
    (.letOp (n := 5756) (.exec 0x10d395 (fun s => s.RIP = 0x10d395) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d395 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5750, 5738, 5753]
    (.letOp (n := 5757) (.out 0x10d398 (addR64R64Effect 0x10d398 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[5752, 5691]
    (.letOp (n := 5758) (.out 0x10d398 (addR64R64Effect 0x10d398 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[5752, 5691]
    (.letOp (n := 5759) (.exec 0x10d398 (fun s => s.RIP = 0x10d398) (addR64R64Effect 0x10d398 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[5752, 5691]
    (.letOp (n := 5760) (.out 0x10d39b (atFlags StatusFlags.CF (adcR64R64Effect 0x10d39b 3 12)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[5755, 5689, 5758]
    (.letOp (n := 5761) (.exec 0x10d39b (fun s => s.RIP = 0x10d39b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d39b 3 12)) (Reg.operands [.gpr 3, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5755, 5689, 5758]
    (.letOp (n := 5762) (.out 0x10d39e (movR64R64Effect 0x10d39e 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 3] []) (.reg (.gpr 10))) #v[5760]
    (.letOp (n := 5763) (.exec 0x10d39e (fun s => s.RIP = 0x10d39e) (movR64R64Effect 0x10d39e 10 3) (Reg.operands [.gpr 3] [])) #v[5760]
    (.letOp (n := 5764) (.out 0x10d3a1 (shldR64R64Effect 0x10d3a1 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[5760, 5757]
    (.letOp (n := 5765) (.exec 0x10d3a1 (fun s => s.RIP = 0x10d3a1) (shldR64R64Effect 0x10d3a1 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5760, 5757]
    (.letOp (n := 5766) (.out 0x10d3a6 (shlR64Effect 0x10d3a6 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5757]
    (.letOp (n := 5767) (.exec 0x10d3a6 (fun s => s.RIP = 0x10d3a6) (shlR64Effect 0x10d3a6 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5757]
    (.letOp (n := 5768) (.out 0x10d3aa (movR64Imm64Effect 0x10d3aa 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 5769) (.exec 0x10d3aa (fun s => s.RIP = 0x10d3aa) (movR64Imm64Effect 0x10d3aa 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 5770) (.out 0x10d3b4 (andR64R64Effect 0x10d3b4 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[5766, 5768]
    (.letOp (n := 5771) (.exec 0x10d3b4 (fun s => s.RIP = 0x10d3b4) (andR64R64Effect 0x10d3b4 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[5766, 5768]
    (.letOp (n := 5772) (.out 0x10d3b7 (orR64R64Effect 0x10d3b7 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[5770, 5740]
    (.letOp (n := 5773) (.exec 0x10d3b7 (fun s => s.RIP = 0x10d3b7) (orR64R64Effect 0x10d3b7 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[5770, 5740]
    (.letOp (n := 5774) (.out 0x10d3ba (shrR64Effect 0x10d3ba 4 10 52) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[5762]
    (.letOp (n := 5775) (.exec 0x10d3ba (fun s => s.RIP = 0x10d3ba) (shrR64Effect 0x10d3ba 4 10 52) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5762]
    (.letOp (n := 5776) (.out 0x10d3be (movR64Imm64Effect 0x10d3be 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 5777) (.exec 0x10d3be (fun s => s.RIP = 0x10d3be) (movR64Imm64Effect 0x10d3be 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 5778) (.out 0x10d3c8 (mulR64Effect 0x10d3c8 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[5776, 5772]
    (.letOp (n := 5779) (.out 0x10d3c8 (mulR64Effect 0x10d3c8 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[5776, 5772]
    (.letOp (n := 5780) (.exec 0x10d3c8 (fun s => s.RIP = 0x10d3c8) (mulR64Effect 0x10d3c8 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[5776, 5772]
    (.letOp (n := 5781) (.out 0x10d3cb (movR64R64Effect 0x10d3cb 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[5779]
    (.letOp (n := 5782) (.exec 0x10d3cb (fun s => s.RIP = 0x10d3cb) (movR64R64Effect 0x10d3cb 9 2) (Reg.operands [.gpr 2] [])) #v[5779]
    (.letOp (n := 5783) (.out 0x10d3ce (addR64M64Effect 0x10d3ce 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5778, 65]
    (.letOp (n := 5784) (.out 0x10d3ce (addR64M64Effect 0x10d3ce 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[5778, 65]
    (.letOp (n := 5785) (.exec 0x10d3ce (LoadPre 0x10d3ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10d3ce + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d3ce 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5778, 65]
    (b_l10a410_136))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_135 : List UInt8 :=
  [0x41, 0x83, 0xE5, 0x0F, 0x49, 0x01, 0xF9, 0x4C, 0x11, 0xC3, 0x4D, 0x01, 0xF9, 0x4C, 0x11, 0xDB,
    0x4C, 0x01, 0xC8, 0x48, 0x11, 0xD3, 0x4C, 0x01, 0xD0, 0x4C, 0x11, 0xE3, 0x49, 0x89, 0xDA, 0x48,
    0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x00, 0x48, 0x21, 0xD0, 0x4C, 0x09, 0xE8, 0x49, 0xC1, 0xEA, 0x34, 0x48, 0xBA, 0xD1, 0x03,
    0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xD1, 0x48, 0x03, 0x44, 0x24,
    0x28] ++ bytes_l10a410_136

theorem code_l10a410_135 : ∀ x ∈ codeRange 0x10d382 bytes_l10a410_135, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd382 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_136

def b_l10a410_134 : Block Op Label signature Reg.count 5698 :=
  .letOp (n := 5698) (.exec 0x10d323 (StorePre 0x10d323 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10d323 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d323 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5696, 65]
    (.letOp (n := 5699) (.exec 0x10d328 (StorePre 0x10d328 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10d328 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d328 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5695, 65]
    (.letOp (n := 5700) (.out 0x10d32d (movR64M64Effect 0x10d32d 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5701) (.exec 0x10d32d (LoadPre 0x10d32d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10d32d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d32d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5702) (.out 0x10d332 (movR64M64Effect 0x10d332 14 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 5703) (.exec 0x10d332 (LoadPre 0x10d332 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10d332 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d332 14 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5704) (.out 0x10d33a (mulR64Effect 0x10d33a 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[5702, 5700]
    (.letOp (n := 5705) (.out 0x10d33a (mulR64Effect 0x10d33a 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[5702, 5700]
    (.letOp (n := 5706) (.exec 0x10d33a (fun s => s.RIP = 0x10d33a) (mulR64Effect 0x10d33a 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[5702, 5700]
    (.letOp (n := 5707) (.out 0x10d33d (movR64R64Effect 0x10d33d 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[5704]
    (.letOp (n := 5708) (.exec 0x10d33d (fun s => s.RIP = 0x10d33d) (movR64R64Effect 0x10d33d 7 0) (Reg.operands [.gpr 0] [])) #v[5704]
    (.letOp (n := 5709) (.out 0x10d340 (movR64R64Effect 0x10d340 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[5705]
    (.letOp (n := 5710) (.exec 0x10d340 (fun s => s.RIP = 0x10d340) (movR64R64Effect 0x10d340 8 2) (Reg.operands [.gpr 2] [])) #v[5705]
    (.letOp (n := 5711) (.out 0x10d343 (movR64R64Effect 0x10d343 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[5682]
    (.letOp (n := 5712) (.exec 0x10d343 (fun s => s.RIP = 0x10d343) (movR64R64Effect 0x10d343 13 6) (Reg.operands [.gpr 6] [])) #v[5682]
    (.letOp (n := 5713) (.out 0x10d346 (shrR64Effect 0x10d346 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[5711]
    (.letOp (n := 5714) (.exec 0x10d346 (fun s => s.RIP = 0x10d346) (shrR64Effect 0x10d346 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5711]
    (.letOp (n := 5715) (.out 0x10d34a (movR64M64Effect 0x10d34a 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5716) (.exec 0x10d34a (LoadPre 0x10d34a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d34a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10d34a 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5717) (.out 0x10d34e (mulM64Effect 0x10d34e 8 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5715, 65]
    (.letOp (n := 5718) (.out 0x10d34e (mulM64Effect 0x10d34e 8 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5715, 65]
    (.letOp (n := 5719) (.exec 0x10d34e (LoadPre 0x10d34e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10d34e + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10d34e 8 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5715, 65]
    (.letOp (n := 5720) (.out 0x10d356 (movR64R64Effect 0x10d356 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[5718]
    (.letOp (n := 5721) (.exec 0x10d356 (fun s => s.RIP = 0x10d356) (movR64R64Effect 0x10d356 3 2) (Reg.operands [.gpr 2] [])) #v[5718]
    (.letOp (n := 5722) (.out 0x10d359 (movR64R64Effect 0x10d359 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[5717]
    (.letOp (n := 5723) (.exec 0x10d359 (fun s => s.RIP = 0x10d359) (movR64R64Effect 0x10d359 9 0) (Reg.operands [.gpr 0] [])) #v[5717]
    (.letOp (n := 5724) (.out 0x10d35c (movR64M64Effect 0x10d35c 0 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5725) (.exec 0x10d35c (LoadPre 0x10d35c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10d35c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d35c 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5726) (.out 0x10d364 (mulM64Effect 0x10d364 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5724, 65]
    (.letOp (n := 5727) (.out 0x10d364 (mulM64Effect 0x10d364 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5724, 65]
    (.letOp (n := 5728) (.exec 0x10d364 (LoadPre 0x10d364 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10d364 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10d364 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5724, 65]
    (.letOp (n := 5729) (.out 0x10d36c (movR64R64Effect 0x10d36c 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[5727]
    (.letOp (n := 5730) (.exec 0x10d36c (fun s => s.RIP = 0x10d36c) (movR64R64Effect 0x10d36c 11 2) (Reg.operands [.gpr 2] [])) #v[5727]
    (.letOp (n := 5731) (.out 0x10d36f (movR64R64Effect 0x10d36f 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[5726]
    (.letOp (n := 5732) (.exec 0x10d36f (fun s => s.RIP = 0x10d36f) (movR64R64Effect 0x10d36f 15 0) (Reg.operands [.gpr 0] [])) #v[5726]
    (.letOp (n := 5733) (.out 0x10d372 (movR64M64Effect 0x10d372 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5734) (.exec 0x10d372 (LoadPre 0x10d372 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10d372 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d372 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5735) (.out 0x10d37a (movR64M64Effect 0x10d37a 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 5736) (.exec 0x10d37a (LoadPre 0x10d37a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10d37a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d37a 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5737) (.out 0x10d37f (mulR64Effect 0x10d37f 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[5735, 5733]
    (.letOp (n := 5738) (.out 0x10d37f (mulR64Effect 0x10d37f 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[5735, 5733]
    (.letOp (n := 5739) (.exec 0x10d37f (fun s => s.RIP = 0x10d37f) (mulR64Effect 0x10d37f 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5735, 5733]
    (b_l10a410_135))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_134 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x30, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x4C,
    0x8B, 0xB4, 0x24, 0x58, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0xC7, 0x49, 0x89, 0xD0,
    0x49, 0x89, 0xF5, 0x49, 0xC1, 0xED, 0x30, 0x48, 0x8B, 0x04, 0x24, 0x48, 0xF7, 0xA4, 0x24, 0x40,
    0x01, 0x00, 0x00, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC1, 0x48, 0x8B, 0x84, 0x24, 0x38, 0x01, 0x00,
    0x00, 0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD3, 0x49, 0x89, 0xC7, 0x48,
    0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x50, 0x48, 0xF7, 0xE1] ++ bytes_l10a410_135

theorem code_l10a410_134 : ∀ x ∈ codeRange 0x10d323 bytes_l10a410_134, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd323 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_135

def b_l10a410_133 : Block Op Label signature Reg.count 5650 :=
  .letOp (n := 5650) (.out 0x10d2d1 (movR64Imm64Effect 0x10d2d1 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 5651) (.exec 0x10d2d1 (fun s => s.RIP = 0x10d2d1) (movR64Imm64Effect 0x10d2d1 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 5652) (.out 0x10d2db (mulR64Effect 0x10d2db 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[5650, 5648]
    (.letOp (n := 5653) (.out 0x10d2db (mulR64Effect 0x10d2db 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[5650, 5648]
    (.letOp (n := 5654) (.exec 0x10d2db (fun s => s.RIP = 0x10d2db) (mulR64Effect 0x10d2db 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[5650, 5648]
    (.letOp (n := 5655) (.out 0x10d2de (shrR64Effect 0x10d2de 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5600]
    (.letOp (n := 5656) (.exec 0x10d2de (fun s => s.RIP = 0x10d2de) (shrR64Effect 0x10d2de 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5600]
    (.letOp (n := 5657) (.out 0x10d2e2 (addR64R64Effect 0x10d2e2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[5626, 5617]
    (.letOp (n := 5658) (.out 0x10d2e2 (addR64R64Effect 0x10d2e2 6 7) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 7] []) (.flag .CF)) #v[5626, 5617]
    (.letOp (n := 5659) (.exec 0x10d2e2 (fun s => s.RIP = 0x10d2e2) (addR64R64Effect 0x10d2e2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[5626, 5617]
    (.letOp (n := 5660) (.out 0x10d2e5 (atFlags StatusFlags.CF (adcR64M64Effect 0x10d2e5 10 (.sib 4 none 0 (.d8 0x48)))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 10))) #v[5624, 65, 5658]
    (.letOp (n := 5661) (.exec 0x10d2e5 (LoadPre 0x10d2e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10d2e5 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d2e5 10 (.sib 4 none 0 (.d8 0x48)))) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5624, 65, 5658]
    (.letOp (n := 5662) (.out 0x10d2ea (addR64M64Effect 0x10d2ea 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[5657, 65]
    (.letOp (n := 5663) (.out 0x10d2ea (addR64M64Effect 0x10d2ea 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[5657, 65]
    (.letOp (n := 5664) (.exec 0x10d2ea (LoadPre 0x10d2ea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10d2ea + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d2ea 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[5657, 65]
    (.letOp (n := 5665) (.out 0x10d2ef (atFlags StatusFlags.CF (adcR64M64Effect 0x10d2ef 10 (.sib 4 none 0 (.d8 0x30)))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 10))) #v[5660, 65, 5663]
    (.letOp (n := 5666) (.exec 0x10d2ef (LoadPre 0x10d2ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10d2ef + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d2ef 10 (.sib 4 none 0 (.d8 0x30)))) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5660, 65, 5663]
    (.letOp (n := 5667) (.out 0x10d2f4 (addR64R64Effect 0x10d2f4 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[5662, 5635]
    (.letOp (n := 5668) (.out 0x10d2f4 (addR64R64Effect 0x10d2f4 6 15) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 15] []) (.flag .CF)) #v[5662, 5635]
    (.letOp (n := 5669) (.exec 0x10d2f4 (fun s => s.RIP = 0x10d2f4) (addR64R64Effect 0x10d2f4 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[5662, 5635]
    (.letOp (n := 5670) (.out 0x10d2f7 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d2f7 10 14)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[5665, 5633, 5668]
    (.letOp (n := 5671) (.exec 0x10d2f7 (fun s => s.RIP = 0x10d2f7) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d2f7 10 14)) (Reg.operands [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5665, 5633, 5668]
    (.letOp (n := 5672) (.out 0x10d2fa (addR64R64Effect 0x10d2fa 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[5667, 5646]
    (.letOp (n := 5673) (.out 0x10d2fa (addR64R64Effect 0x10d2fa 6 13) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 13] []) (.flag .CF)) #v[5667, 5646]
    (.letOp (n := 5674) (.exec 0x10d2fa (fun s => s.RIP = 0x10d2fa) (addR64R64Effect 0x10d2fa 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[5667, 5646]
    (.letOp (n := 5675) (.out 0x10d2fd (atFlags StatusFlags.CF (adcR64R64Effect 0x10d2fd 10 12)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[5670, 5644, 5673]
    (.letOp (n := 5676) (.exec 0x10d2fd (fun s => s.RIP = 0x10d2fd) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d2fd 10 12)) (Reg.operands [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5670, 5644, 5673]
    (.letOp (n := 5677) (.out 0x10d300 (addR64R64Effect 0x10d300 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[5672, 5652]
    (.letOp (n := 5678) (.out 0x10d300 (addR64R64Effect 0x10d300 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[5672, 5652]
    (.letOp (n := 5679) (.exec 0x10d300 (fun s => s.RIP = 0x10d300) (addR64R64Effect 0x10d300 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[5672, 5652]
    (.letOp (n := 5680) (.out 0x10d303 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d303 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[5675, 5653, 5678]
    (.letOp (n := 5681) (.exec 0x10d303 (fun s => s.RIP = 0x10d303) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d303 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5675, 5653, 5678]
    (.letOp (n := 5682) (.out 0x10d306 (addR64R64Effect 0x10d306 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[5677, 5602]
    (.letOp (n := 5683) (.out 0x10d306 (addR64R64Effect 0x10d306 6 3) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 3] []) (.flag .CF)) #v[5677, 5602]
    (.letOp (n := 5684) (.exec 0x10d306 (fun s => s.RIP = 0x10d306) (addR64R64Effect 0x10d306 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[5677, 5602]
    (.letOp (n := 5685) (.out 0x10d309 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d309 10 1)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[5680, 5655, 5683]
    (.letOp (n := 5686) (.exec 0x10d309 (fun s => s.RIP = 0x10d309) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d309 10 1)) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5680, 5655, 5683]
    (.letOp (n := 5687) (.out 0x10d30c (movR64R64Effect 0x10d30c 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 10] []) (.reg (.gpr 12))) #v[5685]
    (.letOp (n := 5688) (.exec 0x10d30c (fun s => s.RIP = 0x10d30c) (movR64R64Effect 0x10d30c 12 10) (Reg.operands [.gpr 10] [])) #v[5685]
    (.letOp (n := 5689) (.out 0x10d30f (shrR64Effect 0x10d30f 4 12 52) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[5687]
    (.letOp (n := 5690) (.exec 0x10d30f (fun s => s.RIP = 0x10d30f) (shrR64Effect 0x10d30f 4 12 52) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5687]
    (.letOp (n := 5691) (.out 0x10d313 (shldR64R64Effect 0x10d313 5 10 6 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[5685, 5682]
    (.letOp (n := 5692) (.exec 0x10d313 (fun s => s.RIP = 0x10d313) (shldR64R64Effect 0x10d313 5 10 6 12) (Reg.operands [.gpr 10, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5685, 5682]
    (.letOp (n := 5693) (.out 0x10d318 (movR64M64Effect 0x10d318 0 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5694) (.exec 0x10d318 (LoadPre 0x10d318 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x10d318 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d318 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5695) (.out 0x10d320 (mulR64Effect 0x10d320 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[5639, 5693]
    (.letOp (n := 5696) (.out 0x10d320 (mulR64Effect 0x10d320 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[5639, 5693]
    (.letOp (n := 5697) (.exec 0x10d320 (fun s => s.RIP = 0x10d320) (mulR64Effect 0x10d320 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[5639, 5693]
    (b_l10a410_134))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_133 : List UInt8 :=
  [0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0xC1, 0xE9,
    0x34, 0x48, 0x01, 0xFE, 0x4C, 0x13, 0x54, 0x24, 0x48, 0x48, 0x03, 0x74, 0x24, 0x28, 0x4C, 0x13,
    0x54, 0x24, 0x30, 0x4C, 0x01, 0xFE, 0x4D, 0x11, 0xF2, 0x4C, 0x01, 0xEE, 0x4D, 0x11, 0xE2, 0x48,
    0x01, 0xC6, 0x49, 0x11, 0xD2, 0x48, 0x01, 0xDE, 0x49, 0x11, 0xCA, 0x4D, 0x89, 0xD4, 0x49, 0xC1,
    0xEC, 0x34, 0x49, 0x0F, 0xA4, 0xF2, 0x0C, 0x48, 0x8B, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x49,
    0xF7, 0xE0] ++ bytes_l10a410_134

theorem code_l10a410_133 : ∀ x ∈ codeRange 0x10d2d1 bytes_l10a410_133, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd2d1 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_134

def b_l10a410_132 : Block Op Label signature Reg.count 5609 :=
  .letOp (n := 5609) (.exec 0x10d28a (StorePre 0x10d28a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10d28a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d28a 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5607, 65]
    (.letOp (n := 5610) (.exec 0x10d28f (StorePre 0x10d28f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10d28f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d28f 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5606, 65]
    (.letOp (n := 5611) (.out 0x10d294 (movR64M64Effect 0x10d294 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5612) (.exec 0x10d294 (LoadPre 0x10d294 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d294 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10d294 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5613) (.out 0x10d298 (mulR64Effect 0x10d298 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[5515, 5611]
    (.letOp (n := 5614) (.out 0x10d298 (mulR64Effect 0x10d298 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[5515, 5611]
    (.letOp (n := 5615) (.exec 0x10d298 (fun s => s.RIP = 0x10d298) (mulR64Effect 0x10d298 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[5515, 5611]
    (.letOp (n := 5616) (.exec 0x10d29b (StorePre 0x10d29b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10d29b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d29b 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5614, 65]
    (.letOp (n := 5617) (.out 0x10d2a0 (movR64R64Effect 0x10d2a0 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[5613]
    (.letOp (n := 5618) (.exec 0x10d2a0 (fun s => s.RIP = 0x10d2a0) (movR64R64Effect 0x10d2a0 7 0) (Reg.operands [.gpr 0] [])) #v[5613]
    (.letOp (n := 5619) (.out 0x10d2a3 (movR64R64Effect 0x10d2a3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[5532]
    (.letOp (n := 5620) (.exec 0x10d2a3 (fun s => s.RIP = 0x10d2a3) (movR64R64Effect 0x10d2a3 0 13) (Reg.operands [.gpr 13] [])) #v[5532]
    (.letOp (n := 5621) (.out 0x10d2a6 (mulR64Effect 0x10d2a6 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[5519, 5619]
    (.letOp (n := 5622) (.out 0x10d2a6 (mulR64Effect 0x10d2a6 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[5519, 5619]
    (.letOp (n := 5623) (.exec 0x10d2a6 (fun s => s.RIP = 0x10d2a6) (mulR64Effect 0x10d2a6 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[5519, 5619]
    (.letOp (n := 5624) (.out 0x10d2a9 (movR64R64Effect 0x10d2a9 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[5622]
    (.letOp (n := 5625) (.exec 0x10d2a9 (fun s => s.RIP = 0x10d2a9) (movR64R64Effect 0x10d2a9 10 2) (Reg.operands [.gpr 2] [])) #v[5622]
    (.letOp (n := 5626) (.out 0x10d2ac (movR64R64Effect 0x10d2ac 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[5621]
    (.letOp (n := 5627) (.exec 0x10d2ac (fun s => s.RIP = 0x10d2ac) (movR64R64Effect 0x10d2ac 6 0) (Reg.operands [.gpr 0] [])) #v[5621]
    (.letOp (n := 5628) (.out 0x10d2af (movR64R64Effect 0x10d2af 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[5543]
    (.letOp (n := 5629) (.exec 0x10d2af (fun s => s.RIP = 0x10d2af) (movR64R64Effect 0x10d2af 0 9) (Reg.operands [.gpr 9] [])) #v[5543]
    (.letOp (n := 5630) (.out 0x10d2b2 (mulM64Effect 0x10d2b2 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5628, 65]
    (.letOp (n := 5631) (.out 0x10d2b2 (mulM64Effect 0x10d2b2 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5628, 65]
    (.letOp (n := 5632) (.exec 0x10d2b2 (LoadPre 0x10d2b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10d2b2 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d2b2 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5628, 65]
    (.letOp (n := 5633) (.out 0x10d2b7 (movR64R64Effect 0x10d2b7 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[5631]
    (.letOp (n := 5634) (.exec 0x10d2b7 (fun s => s.RIP = 0x10d2b7) (movR64R64Effect 0x10d2b7 14 2) (Reg.operands [.gpr 2] [])) #v[5631]
    (.letOp (n := 5635) (.out 0x10d2ba (movR64R64Effect 0x10d2ba 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[5630]
    (.letOp (n := 5636) (.exec 0x10d2ba (fun s => s.RIP = 0x10d2ba) (movR64R64Effect 0x10d2ba 15 0) (Reg.operands [.gpr 0] [])) #v[5630]
    (.letOp (n := 5637) (.out 0x10d2bd (movR64R64Effect 0x10d2bd 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[5552]
    (.letOp (n := 5638) (.exec 0x10d2bd (fun s => s.RIP = 0x10d2bd) (movR64R64Effect 0x10d2bd 0 12) (Reg.operands [.gpr 12] [])) #v[5552]
    (.letOp (n := 5639) (.out 0x10d2c0 (movR64M64Effect 0x10d2c0 8 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 5640) (.exec 0x10d2c0 (LoadPre 0x10d2c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10d2c0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d2c0 8 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5641) (.out 0x10d2c5 (mulR64Effect 0x10d2c5 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[5639, 5637]
    (.letOp (n := 5642) (.out 0x10d2c5 (mulR64Effect 0x10d2c5 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[5639, 5637]
    (.letOp (n := 5643) (.exec 0x10d2c5 (fun s => s.RIP = 0x10d2c5) (mulR64Effect 0x10d2c5 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[5639, 5637]
    (.letOp (n := 5644) (.out 0x10d2c8 (movR64R64Effect 0x10d2c8 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[5642]
    (.letOp (n := 5645) (.exec 0x10d2c8 (fun s => s.RIP = 0x10d2c8) (movR64R64Effect 0x10d2c8 12 2) (Reg.operands [.gpr 2] [])) #v[5642]
    (.letOp (n := 5646) (.out 0x10d2cb (movR64R64Effect 0x10d2cb 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[5641]
    (.letOp (n := 5647) (.exec 0x10d2cb (fun s => s.RIP = 0x10d2cb) (movR64R64Effect 0x10d2cb 13 0) (Reg.operands [.gpr 0] [])) #v[5641]
    (.letOp (n := 5648) (.out 0x10d2ce (movR64R64Effect 0x10d2ce 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[5598]
    (.letOp (n := 5649) (.exec 0x10d2ce (fun s => s.RIP = 0x10d2ce) (movR64R64Effect 0x10d2ce 0 11) (Reg.operands [.gpr 11] [])) #v[5598]
    (b_l10a410_133)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_132 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x30, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x04, 0x24, 0x49, 0xF7,
    0xE6, 0x48, 0x89, 0x54, 0x24, 0x48, 0x48, 0x89, 0xC7, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE7, 0x49,
    0x89, 0xD2, 0x48, 0x89, 0xC6, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0x64, 0x24, 0x50, 0x49, 0x89, 0xD6,
    0x49, 0x89, 0xC7, 0x4C, 0x89, 0xE0, 0x4C, 0x8B, 0x44, 0x24, 0x38, 0x49, 0xF7, 0xE0, 0x49, 0x89,
    0xD4, 0x49, 0x89, 0xC5, 0x4C, 0x89, 0xD8] ++ bytes_l10a410_133

theorem code_l10a410_132 : ∀ x ∈ codeRange 0x10d28a bytes_l10a410_132, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd28a 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_133

def b_l10a410_131 : Block Op Label signature Reg.count 5565 :=
  .letOp (n := 5565) (.out 0x10d220 (addR64R64Effect 0x10d220 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[5530, 5504]
    (.letOp (n := 5566) (.exec 0x10d220 (fun s => s.RIP = 0x10d220) (addR64R64Effect 0x10d220 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[5530, 5504]
    (.letOp (n := 5567) (.exec 0x10d223 (StorePre 0x10d223 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10d223 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10d223 1 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[5565, 65]
    (.letOp (n := 5568) (.out 0x10d22b (movR64Imm64Effect 0x10d22b 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 5569) (.exec 0x10d22b (fun s => s.RIP = 0x10d22b) (movR64Imm64Effect 0x10d22b 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 5570) (.out 0x10d235 (andR64R64Effect 0x10d235 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[5558, 5568]
    (.letOp (n := 5571) (.exec 0x10d235 (fun s => s.RIP = 0x10d235) (andR64R64Effect 0x10d235 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[5558, 5568]
    (.letOp (n := 5572) (.out 0x10d238 (movR64Imm64Effect 0x10d238 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 5573) (.exec 0x10d238 (fun s => s.RIP = 0x10d238) (movR64Imm64Effect 0x10d238 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 5574) (.out 0x10d242 (mulR64Effect 0x10d242 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[5572, 5570]
    (.letOp (n := 5575) (.out 0x10d242 (mulR64Effect 0x10d242 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[5572, 5570]
    (.letOp (n := 5576) (.exec 0x10d242 (fun s => s.RIP = 0x10d242) (mulR64Effect 0x10d242 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[5572, 5570]
    (.letOp (n := 5577) (.exec 0x10d245 (StorePre 0x10d245 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10d245 + BitVec.ofNat 64 8)) 8) (andMREffect 0x10d245 8 64 1 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[5568, 65]
    (.letOp (n := 5578) (.out 0x10d24d (addR64M64Effect 0x10d24d 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[5541, 65]
    (.letOp (n := 5579) (.out 0x10d24d (addR64M64Effect 0x10d24d 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[5541, 65]
    (.letOp (n := 5580) (.exec 0x10d24d (LoadPre 0x10d24d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10d24d + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d24d 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5541, 65]
    (.letOp (n := 5581) (.out 0x10d252 (atFlags StatusFlags.CF (adcR64M64Effect 0x10d252 3 (.sib 4 none 0 (.d8 0x48)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[5539, 65, 5579]
    (.letOp (n := 5582) (.exec 0x10d252 (LoadPre 0x10d252 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10d252 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d252 3 (.sib 4 none 0 (.d8 0x48)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5539, 65, 5579]
    (.letOp (n := 5583) (.out 0x10d257 (addR64M64Effect 0x10d257 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[5578, 65]
    (.letOp (n := 5584) (.out 0x10d257 (addR64M64Effect 0x10d257 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[5578, 65]
    (.letOp (n := 5585) (.exec 0x10d257 (LoadPre 0x10d257 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10d257 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d257 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5578, 65]
    (.letOp (n := 5586) (.out 0x10d25c (atFlags StatusFlags.CF (adcR64M64Effect 0x10d25c 3 (.sib 4 none 0 (.d8 0x30)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[5581, 65, 5584]
    (.letOp (n := 5587) (.exec 0x10d25c (LoadPre 0x10d25c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10d25c + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d25c 3 (.sib 4 none 0 (.d8 0x30)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5581, 65, 5584]
    (.letOp (n := 5588) (.out 0x10d261 (addR64M64Effect 0x10d261 5 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[5583, 65]
    (.letOp (n := 5589) (.out 0x10d261 (addR64M64Effect 0x10d261 5 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[5583, 65]
    (.letOp (n := 5590) (.exec 0x10d261 (LoadPre 0x10d261 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10d261 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10d261 5 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5583, 65]
    (.letOp (n := 5591) (.out 0x10d269 (atFlags StatusFlags.CF (adcR64M64Effect 0x10d269 3 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[5586, 65, 5589]
    (.letOp (n := 5592) (.exec 0x10d269 (LoadPre 0x10d269 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10d269 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d269 3 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5586, 65, 5589]
    (.letOp (n := 5593) (.out 0x10d271 (addR64R64Effect 0x10d271 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[5588, 5574]
    (.letOp (n := 5594) (.out 0x10d271 (addR64R64Effect 0x10d271 5 0) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 0] []) (.flag .CF)) #v[5588, 5574]
    (.letOp (n := 5595) (.exec 0x10d271 (fun s => s.RIP = 0x10d271) (addR64R64Effect 0x10d271 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[5588, 5574]
    (.letOp (n := 5596) (.out 0x10d274 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d274 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[5591, 5575, 5594]
    (.letOp (n := 5597) (.exec 0x10d274 (fun s => s.RIP = 0x10d274) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d274 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5591, 5575, 5594]
    (.letOp (n := 5598) (.out 0x10d277 (shldR64R64Effect 0x10d277 5 11 8 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[5563, 5561]
    (.letOp (n := 5599) (.exec 0x10d277 (fun s => s.RIP = 0x10d277) (shldR64R64Effect 0x10d277 5 11 8 12) (Reg.operands [.gpr 11, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5563, 5561]
    (.letOp (n := 5600) (.out 0x10d27c (movR64R64Effect 0x10d27c 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[5596]
    (.letOp (n := 5601) (.exec 0x10d27c (fun s => s.RIP = 0x10d27c) (movR64R64Effect 0x10d27c 1 3) (Reg.operands [.gpr 3] [])) #v[5596]
    (.letOp (n := 5602) (.out 0x10d27f (shldR64R64Effect 0x10d27f 5 3 5 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[5596, 5593]
    (.letOp (n := 5603) (.exec 0x10d27f (fun s => s.RIP = 0x10d27f) (shldR64R64Effect 0x10d27f 5 3 5 12) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5596, 5593]
    (.letOp (n := 5604) (.out 0x10d284 (movR64R64Effect 0x10d284 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[5556]
    (.letOp (n := 5605) (.exec 0x10d284 (fun s => s.RIP = 0x10d284) (movR64R64Effect 0x10d284 0 7) (Reg.operands [.gpr 7] [])) #v[5556]
    (.letOp (n := 5606) (.out 0x10d287 (mulR64Effect 0x10d287 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[5508, 5604]
    (.letOp (n := 5607) (.out 0x10d287 (mulR64Effect 0x10d287 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[5508, 5604]
    (.letOp (n := 5608) (.exec 0x10d287 (fun s => s.RIP = 0x10d287) (mulR64Effect 0x10d287 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[5508, 5604]
    (b_l10a410_132))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_131 : List UInt8 :=
  [0x48, 0x01, 0xF1, 0x48, 0x89, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0xB9, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x21, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x03, 0x6C,
    0x24, 0x68, 0x48, 0x13, 0x5C, 0x24, 0x48, 0x48, 0x03, 0x6C, 0x24, 0x28, 0x48, 0x13, 0x5C, 0x24,
    0x30, 0x48, 0x03, 0xAC, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x13, 0x9C, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x48, 0x01, 0xC5, 0x48, 0x11, 0xD3, 0x4D, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0x89, 0xD9, 0x48,
    0x0F, 0xA4, 0xEB, 0x0C, 0x48, 0x89, 0xF8, 0x49, 0xF7, 0xE2] ++ bytes_l10a410_132

theorem code_l10a410_131 : ∀ x ∈ codeRange 0x10d220 bytes_l10a410_131, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd220 106 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_132

def b_l10a410_130 : Block Op Label signature Reg.count 5525 :=
  .letOp (n := 5525) (.exec 0x10d1b7 (StorePre 0x10d1b7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10d1b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d1b7 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5522, 65]
    (.letOp (n := 5526) (.out 0x10d1bc (movR64Imm64Effect 0x10d1bc 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 5527) (.exec 0x10d1bc (fun s => s.RIP = 0x10d1bc) (movR64Imm64Effect 0x10d1bc 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 5528) (.out 0x10d1c6 (movR64M64Effect 0x10d1c6 1 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 5529) (.exec 0x10d1c6 (LoadPre 0x10d1c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10d1c6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d1c6 1 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5530) (.out 0x10d1ce (andR64R64Effect 0x10d1ce 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[5528, 5526]
    (.letOp (n := 5531) (.exec 0x10d1ce (fun s => s.RIP = 0x10d1ce) (andR64R64Effect 0x10d1ce 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5528, 5526]
    (.letOp (n := 5532) (.out 0x10d1d1 (movR64M64Effect 0x10d1d1 13 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 5533) (.exec 0x10d1d1 (LoadPre 0x10d1d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10d1d1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d1d1 13 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5534) (.out 0x10d1d9 (movR64R64Effect 0x10d1d9 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[5532]
    (.letOp (n := 5535) (.exec 0x10d1d9 (fun s => s.RIP = 0x10d1d9) (movR64R64Effect 0x10d1d9 0 13) (Reg.operands [.gpr 13] [])) #v[5532]
    (.letOp (n := 5536) (.out 0x10d1dc (mulM64Effect 0x10d1dc 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5534, 65]
    (.letOp (n := 5537) (.out 0x10d1dc (mulM64Effect 0x10d1dc 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5534, 65]
    (.letOp (n := 5538) (.exec 0x10d1dc (LoadPre 0x10d1dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10d1dc + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d1dc 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5534, 65]
    (.letOp (n := 5539) (.out 0x10d1e1 (movR64R64Effect 0x10d1e1 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[5537]
    (.letOp (n := 5540) (.exec 0x10d1e1 (fun s => s.RIP = 0x10d1e1) (movR64R64Effect 0x10d1e1 3 2) (Reg.operands [.gpr 2] [])) #v[5537]
    (.letOp (n := 5541) (.out 0x10d1e4 (movR64R64Effect 0x10d1e4 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[5536]
    (.letOp (n := 5542) (.exec 0x10d1e4 (fun s => s.RIP = 0x10d1e4) (movR64R64Effect 0x10d1e4 5 0) (Reg.operands [.gpr 0] [])) #v[5536]
    (.letOp (n := 5543) (.out 0x10d1e7 (movR64M64Effect 0x10d1e7 9 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 5544) (.exec 0x10d1e7 (LoadPre 0x10d1e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10d1e7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d1e7 9 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5545) (.out 0x10d1ef (movR64R64Effect 0x10d1ef 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[5543]
    (.letOp (n := 5546) (.exec 0x10d1ef (fun s => s.RIP = 0x10d1ef) (movR64R64Effect 0x10d1ef 0 9) (Reg.operands [.gpr 9] [])) #v[5543]
    (.letOp (n := 5547) (.out 0x10d1f2 (mulM64Effect 0x10d1f2 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5545, 65]
    (.letOp (n := 5548) (.out 0x10d1f2 (mulM64Effect 0x10d1f2 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5545, 65]
    (.letOp (n := 5549) (.exec 0x10d1f2 (LoadPre 0x10d1f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10d1f2 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d1f2 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5545, 65]
    (.letOp (n := 5550) (.exec 0x10d1f7 (StorePre 0x10d1f7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10d1f7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10d1f7 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5548, 65]
    (.letOp (n := 5551) (.exec 0x10d1ff (StorePre 0x10d1ff 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10d1ff + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10d1ff 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5547, 65]
    (.letOp (n := 5552) (.out 0x10d207 (movR64M64Effect 0x10d207 12 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 5553) (.exec 0x10d207 (LoadPre 0x10d207 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10d207 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d207 12 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5554) (.out 0x10d20f (movR64R64Effect 0x10d20f 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[5552]
    (.letOp (n := 5555) (.exec 0x10d20f (fun s => s.RIP = 0x10d20f) (movR64R64Effect 0x10d20f 0 12) (Reg.operands [.gpr 12] [])) #v[5552]
    (.letOp (n := 5556) (.out 0x10d212 (movR64M64Effect 0x10d212 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 5557) (.exec 0x10d212 (LoadPre 0x10d212 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10d212 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d212 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5558) (.out 0x10d217 (mulR64Effect 0x10d217 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[5556, 5554]
    (.letOp (n := 5559) (.out 0x10d217 (mulR64Effect 0x10d217 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[5556, 5554]
    (.letOp (n := 5560) (.exec 0x10d217 (fun s => s.RIP = 0x10d217) (mulR64Effect 0x10d217 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[5556, 5554]
    (.letOp (n := 5561) (.out 0x10d21a (movR64R64Effect 0x10d21a 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[5558]
    (.letOp (n := 5562) (.exec 0x10d21a (fun s => s.RIP = 0x10d21a) (movR64R64Effect 0x10d21a 8 0) (Reg.operands [.gpr 0] [])) #v[5558]
    (.letOp (n := 5563) (.out 0x10d21d (movR64R64Effect 0x10d21d 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[5559]
    (.letOp (n := 5564) (.exec 0x10d21d (fun s => s.RIP = 0x10d21d) (movR64R64Effect 0x10d21d 11 2) (Reg.operands [.gpr 2] [])) #v[5559]
    (b_l10a410_131))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_130 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x48, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48,
    0x8B, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x21, 0xC1, 0x4C, 0x8B, 0xAC, 0x24, 0x40, 0x01,
    0x00, 0x00, 0x4C, 0x89, 0xE8, 0x48, 0xF7, 0x64, 0x24, 0x50, 0x48, 0x89, 0xD3, 0x48, 0x89, 0xC5,
    0x4C, 0x8B, 0x8C, 0x24, 0x38, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0x64, 0x24, 0x38,
    0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00,
    0x4C, 0x8B, 0xA4, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x48, 0x8B, 0x7C, 0x24, 0x10,
    0x48, 0xF7, 0xE7, 0x49, 0x89, 0xC0, 0x49, 0x89, 0xD3] ++ bytes_l10a410_131

theorem code_l10a410_130 : ∀ x ∈ codeRange 0x10d1b7 bytes_l10a410_130, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd1b7 105 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_131

def b_l10a410_129 : Block Op Label signature Reg.count 5485 :=
  .letOp (n := 5485) (.out 0x10d158 (movR64R64Effect 0x10d158 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[5483]
    (.letOp (n := 5486) (.exec 0x10d158 (fun s => s.RIP = 0x10d158) (movR64R64Effect 0x10d158 6 2) (Reg.operands [.gpr 2] [])) #v[5483]
    (.letOp (n := 5487) (.out 0x10d15b (imulR64R64Effect 0x10d15b 4 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[5467, 5480]
    (.letOp (n := 5488) (.exec 0x10d15b (fun s => s.RIP = 0x10d15b) (imulR64R64Effect 0x10d15b 4 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[5467, 5480]
    (.letOp (n := 5489) (.out 0x10d15f (movR64M64Effect 0x10d15f 2 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 5490) (.exec 0x10d15f (LoadPre 0x10d15f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10d15f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d15f 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5491) (.out 0x10d167 (andR64R64Effect 0x10d167 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[5489, 5436]
    (.letOp (n := 5492) (.exec 0x10d167 (fun s => s.RIP = 0x10d167) (andR64R64Effect 0x10d167 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[5489, 5436]
    (.letOp (n := 5493) (.out 0x10d16a (addR64R64Effect 0x10d16a 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[5491, 5482]
    (.letOp (n := 5494) (.out 0x10d16a (addR64R64Effect 0x10d16a 2 0) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 0] []) (.flag .CF)) #v[5491, 5482]
    (.letOp (n := 5495) (.exec 0x10d16a (fun s => s.RIP = 0x10d16a) (addR64R64Effect 0x10d16a 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[5491, 5482]
    (.letOp (n := 5496) (.out 0x10d16d (atFlags StatusFlags.CF (adcR64R64Effect 0x10d16d 6 9)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[5485, 5487, 5494]
    (.letOp (n := 5497) (.exec 0x10d16d (fun s => s.RIP = 0x10d16d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d16d 6 9)) (Reg.operands [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5485, 5487, 5494]
    (.letOp (n := 5498) (.out 0x10d170 (addR64R64Effect 0x10d170 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[5493, 5473]
    (.letOp (n := 5499) (.out 0x10d170 (addR64R64Effect 0x10d170 2 10) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 10] []) (.flag .CF)) #v[5493, 5473]
    (.letOp (n := 5500) (.exec 0x10d170 (fun s => s.RIP = 0x10d170) (addR64R64Effect 0x10d170 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[5493, 5473]
    (.letOp (n := 5501) (.exec 0x10d173 (StorePre 0x10d173 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10d173 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10d173 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5498, 65]
    (.letOp (n := 5502) (.out 0x10d17b (atFlags StatusFlags.CF (adcR64R64Effect 0x10d17b 6 1)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[5496, 5471, 5499]
    (.letOp (n := 5503) (.exec 0x10d17b (fun s => s.RIP = 0x10d17b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d17b 6 1)) (Reg.operands [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5496, 5471, 5499]
    (.letOp (n := 5504) (.out 0x10d17e (shldR64R64Effect 0x10d17e 5 6 2 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5502, 5498]
    (.letOp (n := 5505) (.exec 0x10d17e (fun s => s.RIP = 0x10d17e) (shldR64R64Effect 0x10d17e 5 6 2 12) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5502, 5498]
    (.letOp (n := 5506) (.out 0x10d183 (movR64M64Effect 0x10d183 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5507) (.exec 0x10d183 (LoadPre 0x10d183 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10d183 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10d183 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5508) (.out 0x10d187 (movR64M64Effect 0x10d187 10 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 5509) (.exec 0x10d187 (LoadPre 0x10d187 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x10d187 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d187 10 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5510) (.out 0x10d18f (mulR64Effect 0x10d18f 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[5508, 5506]
    (.letOp (n := 5511) (.out 0x10d18f (mulR64Effect 0x10d18f 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[5508, 5506]
    (.letOp (n := 5512) (.exec 0x10d18f (fun s => s.RIP = 0x10d18f) (mulR64Effect 0x10d18f 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[5508, 5506]
    (.letOp (n := 5513) (.exec 0x10d192 (StorePre 0x10d192 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10d192 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d192 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5511, 65]
    (.letOp (n := 5514) (.exec 0x10d197 (StorePre 0x10d197 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10d197 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d197 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5510, 65]
    (.letOp (n := 5515) (.out 0x10d19c (movR64M64Effect 0x10d19c 14 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 5516) (.exec 0x10d19c (LoadPre 0x10d19c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10d19c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d19c 14 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5517) (.out 0x10d1a4 (movR64R64Effect 0x10d1a4 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[5515]
    (.letOp (n := 5518) (.exec 0x10d1a4 (fun s => s.RIP = 0x10d1a4) (movR64R64Effect 0x10d1a4 0 14) (Reg.operands [.gpr 14] [])) #v[5515]
    (.letOp (n := 5519) (.out 0x10d1a7 (movR64M64Effect 0x10d1a7 15 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 5520) (.exec 0x10d1a7 (LoadPre 0x10d1a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10d1a7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d1a7 15 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5521) (.out 0x10d1af (mulR64Effect 0x10d1af 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[5519, 5517]
    (.letOp (n := 5522) (.out 0x10d1af (mulR64Effect 0x10d1af 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[5519, 5517]
    (.letOp (n := 5523) (.exec 0x10d1af (fun s => s.RIP = 0x10d1af) (mulR64Effect 0x10d1af 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[5519, 5517]
    (.letOp (n := 5524) (.exec 0x10d1b2 (StorePre 0x10d1b2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10d1b2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d1b2 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5521, 65]
    (b_l10a410_130))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_129 : List UInt8 :=
  [0x48, 0x89, 0xD6, 0x4C, 0x0F, 0xAF, 0xCF, 0x48, 0x8B, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48,
    0x21, 0xDA, 0x48, 0x01, 0xC2, 0x4C, 0x11, 0xCE, 0x4C, 0x01, 0xD2, 0x48, 0x89, 0x94, 0x24, 0xA8,
    0x00, 0x00, 0x00, 0x48, 0x11, 0xCE, 0x48, 0x0F, 0xA4, 0xD6, 0x0C, 0x48, 0x8B, 0x04, 0x24, 0x4C,
    0x8B, 0x94, 0x24, 0x48, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0x54, 0x24, 0x30, 0x48,
    0x89, 0x44, 0x24, 0x28, 0x4C, 0x8B, 0xB4, 0x24, 0x58, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF0, 0x4C,
    0x8B, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0x44, 0x24, 0x68] ++ bytes_l10a410_130

theorem code_l10a410_129 : ∀ x ∈ codeRange 0x10d158 bytes_l10a410_129, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd158 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_130

def b_l10a410_128 : Block Op Label signature Reg.count 5440 :=
  .letOp (n := 5440) (.out 0x10d109 (movR64Imm64Effect 0x10d109 6 0x1000003d10) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 5441) (.exec 0x10d109 (fun s => s.RIP = 0x10d109) (movR64Imm64Effect 0x10d109 6 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 5442) (.out 0x10d113 (mulR64Effect 0x10d113 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[5440, 5438]
    (.letOp (n := 5443) (.out 0x10d113 (mulR64Effect 0x10d113 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[5440, 5438]
    (.letOp (n := 5444) (.exec 0x10d113 (fun s => s.RIP = 0x10d113) (mulR64Effect 0x10d113 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[5440, 5438]
    (.letOp (n := 5445) (.out 0x10d116 (addR64M64Effect 0x10d116 7 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[5392, 65]
    (.letOp (n := 5446) (.out 0x10d116 (addR64M64Effect 0x10d116 7 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[5392, 65]
    (.letOp (n := 5447) (.exec 0x10d116 (LoadPre 0x10d116 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10d116 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10d116 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[5392, 65]
    (.letOp (n := 5448) (.out 0x10d11b (atFlags StatusFlags.CF (adcR64M64Effect 0x10d11b 10 (.sib 4 none 0 (.d8 0x30)))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 10))) #v[5390, 65, 5446]
    (.letOp (n := 5449) (.exec 0x10d11b (LoadPre 0x10d11b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10d11b + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d11b 10 (.sib 4 none 0 (.d8 0x30)))) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5390, 65, 5446]
    (.letOp (n := 5450) (.out 0x10d120 (addR64R64Effect 0x10d120 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[5445, 5399]
    (.letOp (n := 5451) (.out 0x10d120 (addR64R64Effect 0x10d120 7 8) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 8] []) (.flag .CF)) #v[5445, 5399]
    (.letOp (n := 5452) (.exec 0x10d120 (fun s => s.RIP = 0x10d120) (addR64R64Effect 0x10d120 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[5445, 5399]
    (.letOp (n := 5453) (.out 0x10d123 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d123 10 14)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[5448, 5401, 5451]
    (.letOp (n := 5454) (.exec 0x10d123 (fun s => s.RIP = 0x10d123) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d123 10 14)) (Reg.operands [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5448, 5401, 5451]
    (.letOp (n := 5455) (.out 0x10d126 (addR64R64Effect 0x10d126 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[5450, 5442]
    (.letOp (n := 5456) (.out 0x10d126 (addR64R64Effect 0x10d126 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[5450, 5442]
    (.letOp (n := 5457) (.exec 0x10d126 (fun s => s.RIP = 0x10d126) (addR64R64Effect 0x10d126 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[5450, 5442]
    (.letOp (n := 5458) (.out 0x10d129 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d129 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[5453, 5443, 5456]
    (.letOp (n := 5459) (.exec 0x10d129 (fun s => s.RIP = 0x10d129) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d129 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5453, 5443, 5456]
    (.letOp (n := 5460) (.out 0x10d12c (addR64R64Effect 0x10d12c 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[5455, 5374]
    (.letOp (n := 5461) (.out 0x10d12c (addR64R64Effect 0x10d12c 7 1) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 1] []) (.flag .CF)) #v[5455, 5374]
    (.letOp (n := 5462) (.exec 0x10d12c (fun s => s.RIP = 0x10d12c) (addR64R64Effect 0x10d12c 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[5455, 5374]
    (.letOp (n := 5463) (.out 0x10d12f (atFlags StatusFlags.CF (adcR64R64Effect 0x10d12f 10 13)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[5458, 5372, 5461]
    (.letOp (n := 5464) (.exec 0x10d12f (fun s => s.RIP = 0x10d12f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d12f 10 13)) (Reg.operands [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5458, 5372, 5461]
    (.letOp (n := 5465) (.out 0x10d132 (shrdR64R64Effect 0x10d132 5 11 9 52) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[5429, 5432]
    (.letOp (n := 5466) (.exec 0x10d132 (fun s => s.RIP = 0x10d132) (shrdR64R64Effect 0x10d132 5 11 9 52) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5429, 5432]
    (.letOp (n := 5467) (.out 0x10d137 (shrR64Effect 0x10d137 4 9 52) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[5432]
    (.letOp (n := 5468) (.exec 0x10d137 (fun s => s.RIP = 0x10d137) (shrR64Effect 0x10d137 4 9 52) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5432]
    (.letOp (n := 5469) (.out 0x10d13b (movR64R64Effect 0x10d13b 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[5463]
    (.letOp (n := 5470) (.exec 0x10d13b (fun s => s.RIP = 0x10d13b) (movR64R64Effect 0x10d13b 1 10) (Reg.operands [.gpr 10] [])) #v[5463]
    (.letOp (n := 5471) (.out 0x10d13e (shrR64Effect 0x10d13e 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5469]
    (.letOp (n := 5472) (.exec 0x10d13e (fun s => s.RIP = 0x10d13e) (shrR64Effect 0x10d13e 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5469]
    (.letOp (n := 5473) (.out 0x10d142 (shldR64R64Effect 0x10d142 5 10 7 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[5463, 5460]
    (.letOp (n := 5474) (.exec 0x10d142 (fun s => s.RIP = 0x10d142) (shldR64R64Effect 0x10d142 5 10 7 12) (Reg.operands [.gpr 10, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5463, 5460]
    (.letOp (n := 5475) (.out 0x10d147 (andR64R64Effect 0x10d147 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[5460, 5436]
    (.letOp (n := 5476) (.exec 0x10d147 (fun s => s.RIP = 0x10d147) (andR64R64Effect 0x10d147 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[5460, 5436]
    (.letOp (n := 5477) (.exec 0x10d14a (StorePre 0x10d14a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10d14a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d14a 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[5475, 65]
    (.letOp (n := 5478) (.out 0x10d14f (movR64R64Effect 0x10d14f 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[5465]
    (.letOp (n := 5479) (.exec 0x10d14f (fun s => s.RIP = 0x10d14f) (movR64R64Effect 0x10d14f 0 11) (Reg.operands [.gpr 11] [])) #v[5465]
    (.letOp (n := 5480) (.out 0x10d152 (movR64R64Effect 0x10d152 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[5440]
    (.letOp (n := 5481) (.exec 0x10d152 (fun s => s.RIP = 0x10d152) (movR64R64Effect 0x10d152 7 6) (Reg.operands [.gpr 6] [])) #v[5440]
    (.letOp (n := 5482) (.out 0x10d155 (mulR64Effect 0x10d155 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[5440, 5478]
    (.letOp (n := 5483) (.out 0x10d155 (mulR64Effect 0x10d155 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[5440, 5478]
    (.letOp (n := 5484) (.exec 0x10d155 (fun s => s.RIP = 0x10d155) (mulR64Effect 0x10d155 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[5440, 5478]
    (b_l10a410_129)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_128 : List UInt8 :=
  [0x48, 0xBE, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE6, 0x48, 0x03, 0x7C,
    0x24, 0x68, 0x4C, 0x13, 0x54, 0x24, 0x30, 0x4C, 0x01, 0xC7, 0x4D, 0x11, 0xF2, 0x48, 0x01, 0xC7,
    0x49, 0x11, 0xD2, 0x48, 0x01, 0xCF, 0x4D, 0x11, 0xEA, 0x4D, 0x0F, 0xAC, 0xCB, 0x34, 0x49, 0xC1,
    0xE9, 0x34, 0x4C, 0x89, 0xD1, 0x48, 0xC1, 0xE9, 0x34, 0x49, 0x0F, 0xA4, 0xFA, 0x0C, 0x48, 0x21,
    0xDF, 0x48, 0x89, 0x7C, 0x24, 0x58, 0x4C, 0x89, 0xD8, 0x48, 0x89, 0xF7, 0x48, 0xF7, 0xE6] ++ bytes_l10a410_129

theorem code_l10a410_128 : ∀ x ∈ codeRange 0x10d109 bytes_l10a410_128, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd109 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_129

def b_l10a410_127 : Block Op Label signature Reg.count 5396 :=
  .letOp (n := 5396) (.out 0x10d0bc (mulM64Effect 0x10d0bc 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5394, 65]
    (.letOp (n := 5397) (.out 0x10d0bc (mulM64Effect 0x10d0bc 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5394, 65]
    (.letOp (n := 5398) (.exec 0x10d0bc (LoadPre 0x10d0bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10d0bc + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d0bc 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5394, 65]
    (.letOp (n := 5399) (.out 0x10d0c1 (movR64R64Effect 0x10d0c1 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[5396]
    (.letOp (n := 5400) (.exec 0x10d0c1 (fun s => s.RIP = 0x10d0c1) (movR64R64Effect 0x10d0c1 8 0) (Reg.operands [.gpr 0] [])) #v[5396]
    (.letOp (n := 5401) (.out 0x10d0c4 (movR64R64Effect 0x10d0c4 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[5397]
    (.letOp (n := 5402) (.exec 0x10d0c4 (fun s => s.RIP = 0x10d0c4) (movR64R64Effect 0x10d0c4 14 2) (Reg.operands [.gpr 2] [])) #v[5397]
    (.letOp (n := 5403) (.out 0x10d0c7 (andR64R64Effect 0x10d0c7 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[5376, 5338]
    (.letOp (n := 5404) (.exec 0x10d0c7 (fun s => s.RIP = 0x10d0c7) (andR64R64Effect 0x10d0c7 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[5376, 5338]
    (.letOp (n := 5405) (.exec 0x10d0ca (StorePre 0x10d0ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10d0ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d0ca 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[5403, 65]
    (.letOp (n := 5406) (.out 0x10d0cf (movR64M64Effect 0x10d0cf 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5407) (.exec 0x10d0cf (LoadPre 0x10d0cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10d0cf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d0cf 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5408) (.out 0x10d0d4 (mulR64Effect 0x10d0d4 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[5303, 5406]
    (.letOp (n := 5409) (.out 0x10d0d4 (mulR64Effect 0x10d0d4 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[5303, 5406]
    (.letOp (n := 5410) (.exec 0x10d0d4 (fun s => s.RIP = 0x10d0d4) (mulR64Effect 0x10d0d4 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[5303, 5406]
    (.letOp (n := 5411) (.out 0x10d0d7 (movR64R64Effect 0x10d0d7 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[5409]
    (.letOp (n := 5412) (.exec 0x10d0d7 (fun s => s.RIP = 0x10d0d7) (movR64R64Effect 0x10d0d7 15 2) (Reg.operands [.gpr 2] [])) #v[5409]
    (.letOp (n := 5413) (.out 0x10d0da (movR64R64Effect 0x10d0da 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[5408]
    (.letOp (n := 5414) (.exec 0x10d0da (fun s => s.RIP = 0x10d0da) (movR64R64Effect 0x10d0da 12 0) (Reg.operands [.gpr 0] [])) #v[5408]
    (.letOp (n := 5415) (.out 0x10d0dd (movR64M64Effect 0x10d0dd 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5416) (.exec 0x10d0dd (LoadPre 0x10d0dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10d0dd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d0dd 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5417) (.out 0x10d0e2 (mulM64Effect 0x10d0e2 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5415, 65]
    (.letOp (n := 5418) (.out 0x10d0e2 (mulM64Effect 0x10d0e2 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5415, 65]
    (.letOp (n := 5419) (.exec 0x10d0e2 (LoadPre 0x10d0e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10d0e2 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d0e2 5 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5415, 65]
    (.letOp (n := 5420) (.out 0x10d0e7 (movR64R64Effect 0x10d0e7 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[5418]
    (.letOp (n := 5421) (.exec 0x10d0e7 (fun s => s.RIP = 0x10d0e7) (movR64R64Effect 0x10d0e7 9 2) (Reg.operands [.gpr 2] [])) #v[5418]
    (.letOp (n := 5422) (.out 0x10d0ea (movR64R64Effect 0x10d0ea 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[5417]
    (.letOp (n := 5423) (.exec 0x10d0ea (fun s => s.RIP = 0x10d0ea) (movR64R64Effect 0x10d0ea 11 0) (Reg.operands [.gpr 0] [])) #v[5417]
    (.letOp (n := 5424) (.out 0x10d0ed (addR64R64Effect 0x10d0ed 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 12] []) (.reg (.gpr 11))) #v[5422, 5413]
    (.letOp (n := 5425) (.out 0x10d0ed (addR64R64Effect 0x10d0ed 11 12) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 12] []) (.flag .CF)) #v[5422, 5413]
    (.letOp (n := 5426) (.exec 0x10d0ed (fun s => s.RIP = 0x10d0ed) (addR64R64Effect 0x10d0ed 11 12) (Reg.operands [.gpr 11, .gpr 12] [])) #v[5422, 5413]
    (.letOp (n := 5427) (.out 0x10d0f0 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d0f0 9 15)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[5420, 5411, 5425]
    (.letOp (n := 5428) (.exec 0x10d0f0 (fun s => s.RIP = 0x10d0f0) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d0f0 9 15)) (Reg.operands [.gpr 9, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5420, 5411, 5425]
    (.letOp (n := 5429) (.out 0x10d0f3 (addR64R64Effect 0x10d0f3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[5424, 5366]
    (.letOp (n := 5430) (.out 0x10d0f3 (addR64R64Effect 0x10d0f3 11 6) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 6] []) (.flag .CF)) #v[5424, 5366]
    (.letOp (n := 5431) (.exec 0x10d0f3 (fun s => s.RIP = 0x10d0f3) (addR64R64Effect 0x10d0f3 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[5424, 5366]
    (.letOp (n := 5432) (.out 0x10d0f6 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d0f6 9 5)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[5427, 5368, 5430]
    (.letOp (n := 5433) (.exec 0x10d0f6 (fun s => s.RIP = 0x10d0f6) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d0f6 9 5)) (Reg.operands [.gpr 9, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5427, 5368, 5430]
    (.letOp (n := 5434) (.out 0x10d0f9 (movR64R64Effect 0x10d0f9 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[5429]
    (.letOp (n := 5435) (.exec 0x10d0f9 (fun s => s.RIP = 0x10d0f9) (movR64R64Effect 0x10d0f9 0 11) (Reg.operands [.gpr 11] [])) #v[5429]
    (.letOp (n := 5436) (.out 0x10d0fc (movR64Imm64Effect 0x10d0fc 3 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 5437) (.exec 0x10d0fc (fun s => s.RIP = 0x10d0fc) (movR64Imm64Effect 0x10d0fc 3 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 5438) (.out 0x10d106 (andR64R64Effect 0x10d106 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[5434, 5436]
    (.letOp (n := 5439) (.exec 0x10d106 (fun s => s.RIP = 0x10d106) (andR64R64Effect 0x10d106 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[5434, 5436]
    (b_l10a410_128))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_127 : List UInt8 :=
  [0x48, 0xF7, 0x64, 0x24, 0x08, 0x49, 0x89, 0xC0, 0x49, 0x89, 0xD6, 0x4D, 0x21, 0xD9, 0x4C, 0x89,
    0x4C, 0x24, 0x08, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD7, 0x49, 0x89,
    0xC4, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0xF7, 0x64, 0x24, 0x58, 0x49, 0x89, 0xD1, 0x49, 0x89,
    0xC3, 0x4D, 0x01, 0xE3, 0x4D, 0x11, 0xF9, 0x49, 0x01, 0xF3, 0x49, 0x11, 0xE9, 0x4C, 0x89, 0xD8,
    0x48, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD8] ++ bytes_l10a410_128

theorem code_l10a410_127 : ∀ x ∈ codeRange 0x10d0bc bytes_l10a410_127, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd0bc 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_128

def b_l10a410_126 : Block Op Label signature Reg.count 5355 :=
  .letOp (n := 5355) (.out 0x10d06a (atFlags StatusFlags.CF (adcR64R64Effect 0x10d06a 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[5350, 5345, 5353]
    (.letOp (n := 5356) (.exec 0x10d06a (fun s => s.RIP = 0x10d06a) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d06a 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5350, 5345, 5353]
    (.letOp (n := 5357) (.out 0x10d06d (addR64R64Effect 0x10d06d 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[5352, 5266]
    (.letOp (n := 5358) (.out 0x10d06d (addR64R64Effect 0x10d06d 13 9) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 9] []) (.flag .CF)) #v[5352, 5266]
    (.letOp (n := 5359) (.exec 0x10d06d (fun s => s.RIP = 0x10d06d) (addR64R64Effect 0x10d06d 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[5352, 5266]
    (.letOp (n := 5360) (.out 0x10d070 (movR64R64Effect 0x10d070 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[5357]
    (.letOp (n := 5361) (.exec 0x10d070 (fun s => s.RIP = 0x10d070) (movR64R64Effect 0x10d070 0 13) (Reg.operands [.gpr 13] [])) #v[5357]
    (.letOp (n := 5362) (.out 0x10d073 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10d073 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[5355, 5358]
    (.letOp (n := 5363) (.exec 0x10d073 (fun s => s.RIP = 0x10d073) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10d073 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5355, 5358]
    (.letOp (n := 5364) (.out 0x10d077 (movR64R64Effect 0x10d077 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[5334]
    (.letOp (n := 5365) (.exec 0x10d077 (fun s => s.RIP = 0x10d077) (movR64R64Effect 0x10d077 5 6) (Reg.operands [.gpr 6] [])) #v[5334]
    (.letOp (n := 5366) (.out 0x10d07a (shldR64R64Effect 0x10d07a 5 6 7 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5334, 5331]
    (.letOp (n := 5367) (.exec 0x10d07a (fun s => s.RIP = 0x10d07a) (shldR64R64Effect 0x10d07a 5 6 7 12) (Reg.operands [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5334, 5331]
    (.letOp (n := 5368) (.out 0x10d07f (shrR64Effect 0x10d07f 4 5 52) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5364]
    (.letOp (n := 5369) (.exec 0x10d07f (fun s => s.RIP = 0x10d07f) (shrR64Effect 0x10d07f 4 5 52) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5364]
    (.letOp (n := 5370) (.out 0x10d083 (movR64R64Effect 0x10d083 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[5362]
    (.letOp (n := 5371) (.exec 0x10d083 (fun s => s.RIP = 0x10d083) (movR64R64Effect 0x10d083 13 1) (Reg.operands [.gpr 1] [])) #v[5362]
    (.letOp (n := 5372) (.out 0x10d086 (shrR64Effect 0x10d086 4 13 52) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[5370]
    (.letOp (n := 5373) (.exec 0x10d086 (fun s => s.RIP = 0x10d086) (shrR64Effect 0x10d086 4 13 52) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5370]
    (.letOp (n := 5374) (.out 0x10d08a (shldR64R64Effect 0x10d08a 5 1 0 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5362, 5360]
    (.letOp (n := 5375) (.exec 0x10d08a (fun s => s.RIP = 0x10d08a) (shldR64R64Effect 0x10d08a 5 1 0 12) (Reg.operands [.gpr 1, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5362, 5360]
    (.letOp (n := 5376) (.out 0x10d08f (movR64R64Effect 0x10d08f 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[5360]
    (.letOp (n := 5377) (.exec 0x10d08f (fun s => s.RIP = 0x10d08f) (movR64R64Effect 0x10d08f 9 0) (Reg.operands [.gpr 0] [])) #v[5360]
    (.letOp (n := 5378) (.out 0x10d092 (movR64M64Effect 0x10d092 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5379) (.exec 0x10d092 (LoadPre 0x10d092 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10d092 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d092 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5380) (.out 0x10d097 (mulR64Effect 0x10d097 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[5272, 5378]
    (.letOp (n := 5381) (.out 0x10d097 (mulR64Effect 0x10d097 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[5272, 5378]
    (.letOp (n := 5382) (.exec 0x10d097 (fun s => s.RIP = 0x10d097) (mulR64Effect 0x10d097 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[5272, 5378]
    (.letOp (n := 5383) (.exec 0x10d09a (StorePre 0x10d09a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10d09a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d09a 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5381, 65]
    (.letOp (n := 5384) (.exec 0x10d09f (StorePre 0x10d09f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10d09f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10d09f 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5380, 65]
    (.letOp (n := 5385) (.out 0x10d0a4 (movR64M64Effect 0x10d0a4 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5386) (.exec 0x10d0a4 (LoadPre 0x10d0a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10d0a4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d0a4 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5387) (.out 0x10d0ac (mulM64Effect 0x10d0ac 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5385, 65]
    (.letOp (n := 5388) (.out 0x10d0ac (mulM64Effect 0x10d0ac 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5385, 65]
    (.letOp (n := 5389) (.exec 0x10d0ac (LoadPre 0x10d0ac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10d0ac + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d0ac 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5385, 65]
    (.letOp (n := 5390) (.out 0x10d0b1 (movR64R64Effect 0x10d0b1 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[5388]
    (.letOp (n := 5391) (.exec 0x10d0b1 (fun s => s.RIP = 0x10d0b1) (movR64R64Effect 0x10d0b1 10 2) (Reg.operands [.gpr 2] [])) #v[5388]
    (.letOp (n := 5392) (.out 0x10d0b4 (movR64R64Effect 0x10d0b4 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[5387]
    (.letOp (n := 5393) (.exec 0x10d0b4 (fun s => s.RIP = 0x10d0b4) (movR64R64Effect 0x10d0b4 7 0) (Reg.operands [.gpr 0] [])) #v[5387]
    (.letOp (n := 5394) (.out 0x10d0b7 (movR64M64Effect 0x10d0b7 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5395) (.exec 0x10d0b7 (LoadPre 0x10d0b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10d0b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d0b7 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_127)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_126 : List UInt8 :=
  [0x48, 0x11, 0xD1, 0x4D, 0x01, 0xCD, 0x4C, 0x89, 0xE8, 0x48, 0x83, 0xD1, 0x00, 0x48, 0x89, 0xF5,
    0x48, 0x0F, 0xA4, 0xFE, 0x0C, 0x48, 0xC1, 0xED, 0x34, 0x49, 0x89, 0xCD, 0x49, 0xC1, 0xED, 0x34,
    0x48, 0x0F, 0xA4, 0xC1, 0x0C, 0x49, 0x89, 0xC1, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x49, 0xF7, 0xE6,
    0x48, 0x89, 0x54, 0x24, 0x30, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x28, 0x49, 0x89, 0xD2, 0x48, 0x89, 0xC7, 0x48, 0x8B, 0x44,
    0x24, 0x70] ++ bytes_l10a410_127

theorem code_l10a410_126 : ∀ x ∈ codeRange 0x10d06a bytes_l10a410_126, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd06a 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_127

def b_l10a410_125 : Block Op Label signature Reg.count 5307 :=
  .letOp (n := 5307) (.out 0x10d018 (mulM64Effect 0x10d018 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5305, 65]
    (.letOp (n := 5308) (.out 0x10d018 (mulM64Effect 0x10d018 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5305, 65]
    (.letOp (n := 5309) (.exec 0x10d018 (LoadPre 0x10d018 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10d018 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d018 5 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5305, 65]
    (.letOp (n := 5310) (.out 0x10d01d (movR64R64Effect 0x10d01d 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[5308]
    (.letOp (n := 5311) (.exec 0x10d01d (fun s => s.RIP = 0x10d01d) (movR64R64Effect 0x10d01d 6 2) (Reg.operands [.gpr 2] [])) #v[5308]
    (.letOp (n := 5312) (.out 0x10d020 (movR64R64Effect 0x10d020 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[5307]
    (.letOp (n := 5313) (.exec 0x10d020 (fun s => s.RIP = 0x10d020) (movR64R64Effect 0x10d020 15 0) (Reg.operands [.gpr 0] [])) #v[5307]
    (.letOp (n := 5314) (.out 0x10d023 (movR64M64Effect 0x10d023 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5315) (.exec 0x10d023 (LoadPre 0x10d023 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10d023 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10d023 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5316) (.out 0x10d028 (mulM64Effect 0x10d028 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5314, 65]
    (.letOp (n := 5317) (.out 0x10d028 (mulM64Effect 0x10d028 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5314, 65]
    (.letOp (n := 5318) (.exec 0x10d028 (LoadPre 0x10d028 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10d028 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10d028 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5314, 65]
    (.letOp (n := 5319) (.out 0x10d02d (movR64R64Effect 0x10d02d 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[5316]
    (.letOp (n := 5320) (.exec 0x10d02d (fun s => s.RIP = 0x10d02d) (movR64R64Effect 0x10d02d 7 0) (Reg.operands [.gpr 0] [])) #v[5316]
    (.letOp (n := 5321) (.out 0x10d030 (addR64R64Effect 0x10d030 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[5312, 5301]
    (.letOp (n := 5322) (.out 0x10d030 (addR64R64Effect 0x10d030 15 11) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 11] []) (.flag .CF)) #v[5312, 5301]
    (.letOp (n := 5323) (.exec 0x10d030 (fun s => s.RIP = 0x10d030) (addR64R64Effect 0x10d030 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[5312, 5301]
    (.letOp (n := 5324) (.out 0x10d033 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d033 6 8)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[5310, 5299, 5322]
    (.letOp (n := 5325) (.exec 0x10d033 (fun s => s.RIP = 0x10d033) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d033 6 8)) (Reg.operands [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5310, 5299, 5322]
    (.letOp (n := 5326) (.out 0x10d036 (addR64R64Effect 0x10d036 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[5319, 5321]
    (.letOp (n := 5327) (.out 0x10d036 (addR64R64Effect 0x10d036 7 15) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 15] []) (.flag .CF)) #v[5319, 5321]
    (.letOp (n := 5328) (.exec 0x10d036 (fun s => s.RIP = 0x10d036) (addR64R64Effect 0x10d036 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[5319, 5321]
    (.letOp (n := 5329) (.out 0x10d039 (atFlags StatusFlags.CF (adcR64R64Effect 0x10d039 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[5324, 5317, 5327]
    (.letOp (n := 5330) (.exec 0x10d039 (fun s => s.RIP = 0x10d039) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d039 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5324, 5317, 5327]
    (.letOp (n := 5331) (.out 0x10d03c (addR64R64Effect 0x10d03c 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[5326, 5242]
    (.letOp (n := 5332) (.out 0x10d03c (addR64R64Effect 0x10d03c 7 10) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 10] []) (.flag .CF)) #v[5326, 5242]
    (.letOp (n := 5333) (.exec 0x10d03c (fun s => s.RIP = 0x10d03c) (addR64R64Effect 0x10d03c 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[5326, 5242]
    (.letOp (n := 5334) (.out 0x10d03f (atFlags StatusFlags.CF (adcR64R64Effect 0x10d03f 6 12)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[5329, 5259, 5332]
    (.letOp (n := 5335) (.exec 0x10d03f (fun s => s.RIP = 0x10d03f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10d03f 6 12)) (Reg.operands [.gpr 6, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5329, 5259, 5332]
    (.letOp (n := 5336) (.out 0x10d042 (movR64R64Effect 0x10d042 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[5331]
    (.letOp (n := 5337) (.exec 0x10d042 (fun s => s.RIP = 0x10d042) (movR64R64Effect 0x10d042 0 7) (Reg.operands [.gpr 7] [])) #v[5331]
    (.letOp (n := 5338) (.out 0x10d045 (movR64Imm64Effect 0x10d045 11 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 5339) (.exec 0x10d045 (fun s => s.RIP = 0x10d045) (movR64Imm64Effect 0x10d045 11 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 5340) (.out 0x10d04f (andR64R64Effect 0x10d04f 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[5336, 5338]
    (.letOp (n := 5341) (.exec 0x10d04f (fun s => s.RIP = 0x10d04f) (andR64R64Effect 0x10d04f 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[5336, 5338]
    (.letOp (n := 5342) (.out 0x10d052 (movR64Imm64Effect 0x10d052 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 5343) (.exec 0x10d052 (fun s => s.RIP = 0x10d052) (movR64Imm64Effect 0x10d052 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 5344) (.out 0x10d05c (mulR64Effect 0x10d05c 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[5342, 5340]
    (.letOp (n := 5345) (.out 0x10d05c (mulR64Effect 0x10d05c 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[5342, 5340]
    (.letOp (n := 5346) (.exec 0x10d05c (fun s => s.RIP = 0x10d05c) (mulR64Effect 0x10d05c 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[5342, 5340]
    (.letOp (n := 5347) (.out 0x10d05f (addR64R64Effect 0x10d05f 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[5285, 5278]
    (.letOp (n := 5348) (.out 0x10d05f (addR64R64Effect 0x10d05f 13 5) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 5] []) (.flag .CF)) #v[5285, 5278]
    (.letOp (n := 5349) (.exec 0x10d05f (fun s => s.RIP = 0x10d05f) (addR64R64Effect 0x10d05f 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[5285, 5278]
    (.letOp (n := 5350) (.out 0x10d062 (atFlags StatusFlags.CF (adcR64M64Effect 0x10d062 1 (.sib 4 none 0 (.d8 0x68)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[5287, 65, 5348]
    (.letOp (n := 5351) (.exec 0x10d062 (LoadPre 0x10d062 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10d062 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10d062 1 (.sib 4 none 0 (.d8 0x68)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5287, 65, 5348]
    (.letOp (n := 5352) (.out 0x10d067 (addR64R64Effect 0x10d067 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[5347, 5344]
    (.letOp (n := 5353) (.out 0x10d067 (addR64R64Effect 0x10d067 13 0) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 0] []) (.flag .CF)) #v[5347, 5344]
    (.letOp (n := 5354) (.exec 0x10d067 (fun s => s.RIP = 0x10d067) (addR64R64Effect 0x10d067 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[5347, 5344]
    (b_l10a410_126))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_125 : List UInt8 :=
  [0x48, 0xF7, 0x64, 0x24, 0x58, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x44, 0x24, 0x18,
    0x48, 0xF7, 0x64, 0x24, 0x30, 0x48, 0x89, 0xC7, 0x4D, 0x01, 0xDF, 0x4C, 0x11, 0xC6, 0x4C, 0x01,
    0xFF, 0x48, 0x11, 0xD6, 0x4C, 0x01, 0xD7, 0x4C, 0x11, 0xE6, 0x48, 0x89, 0xF8, 0x49, 0xBB, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xD8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x01, 0xED, 0x48, 0x13, 0x4C, 0x24, 0x68, 0x49,
    0x01, 0xC5] ++ bytes_l10a410_126

theorem code_l10a410_125 : ∀ x ∈ codeRange 0x10d018 bytes_l10a410_125, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd018 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_126

def b_l10a410_124 : Block Op Label signature Reg.count 5266 :=
  .letOp (n := 5266) (.out 0x10cfc0 (shldR64R64Effect 0x10cfc0 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[5264, 5261]
    (.letOp (n := 5267) (.exec 0x10cfc0 (fun s => s.RIP = 0x10cfc0) (shldR64R64Effect 0x10cfc0 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5264, 5261]
    (.letOp (n := 5268) (.out 0x10cfc5 (movR64R64Effect 0x10cfc5 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[5261]
    (.letOp (n := 5269) (.exec 0x10cfc5 (fun s => s.RIP = 0x10cfc5) (movR64R64Effect 0x10cfc5 6 0) (Reg.operands [.gpr 0] [])) #v[5261]
    (.letOp (n := 5270) (.out 0x10cfc8 (movR64R64Effect 0x10cfc8 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5213]
    (.letOp (n := 5271) (.exec 0x10cfc8 (fun s => s.RIP = 0x10cfc8) (movR64R64Effect 0x10cfc8 0 5) (Reg.operands [.gpr 5] [])) #v[5213]
    (.letOp (n := 5272) (.out 0x10cfcb (movR64M64Effect 0x10cfcb 14 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 5273) (.exec 0x10cfcb (LoadPre 0x10cfcb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10cfcb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cfcb 14 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5274) (.out 0x10cfd3 (mulR64Effect 0x10cfd3 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[5272, 5270]
    (.letOp (n := 5275) (.out 0x10cfd3 (mulR64Effect 0x10cfd3 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[5272, 5270]
    (.letOp (n := 5276) (.exec 0x10cfd3 (fun s => s.RIP = 0x10cfd3) (mulR64Effect 0x10cfd3 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[5272, 5270]
    (.letOp (n := 5277) (.exec 0x10cfd6 (StorePre 0x10cfd6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10cfd6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10cfd6 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5275, 65]
    (.letOp (n := 5278) (.out 0x10cfdb (movR64R64Effect 0x10cfdb 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[5274]
    (.letOp (n := 5279) (.exec 0x10cfdb (fun s => s.RIP = 0x10cfdb) (movR64R64Effect 0x10cfdb 5 0) (Reg.operands [.gpr 0] [])) #v[5274]
    (.letOp (n := 5280) (.out 0x10cfde (movR64R64Effect 0x10cfde 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[5180]
    (.letOp (n := 5281) (.exec 0x10cfde (fun s => s.RIP = 0x10cfde) (movR64R64Effect 0x10cfde 0 1) (Reg.operands [.gpr 1] [])) #v[5180]
    (.letOp (n := 5282) (.out 0x10cfe1 (mulM64Effect 0x10cfe1 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5280, 65]
    (.letOp (n := 5283) (.out 0x10cfe1 (mulM64Effect 0x10cfe1 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5280, 65]
    (.letOp (n := 5284) (.exec 0x10cfe1 (LoadPre 0x10cfe1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10cfe1 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10cfe1 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5280, 65]
    (.letOp (n := 5285) (.out 0x10cfe6 (movR64R64Effect 0x10cfe6 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[5282]
    (.letOp (n := 5286) (.exec 0x10cfe6 (fun s => s.RIP = 0x10cfe6) (movR64R64Effect 0x10cfe6 13 0) (Reg.operands [.gpr 0] [])) #v[5282]
    (.letOp (n := 5287) (.out 0x10cfe9 (movR64R64Effect 0x10cfe9 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[5283]
    (.letOp (n := 5288) (.exec 0x10cfe9 (fun s => s.RIP = 0x10cfe9) (movR64R64Effect 0x10cfe9 1 2) (Reg.operands [.gpr 2] [])) #v[5283]
    (.letOp (n := 5289) (.out 0x10cfec (movR64Imm64Effect 0x10cfec 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 5290) (.exec 0x10cfec (fun s => s.RIP = 0x10cfec) (movR64Imm64Effect 0x10cfec 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 5291) (.out 0x10cff6 (andR64R64Effect 0x10cff6 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[5268, 5289]
    (.letOp (n := 5292) (.exec 0x10cff6 (fun s => s.RIP = 0x10cff6) (andR64R64Effect 0x10cff6 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[5268, 5289]
    (.letOp (n := 5293) (.exec 0x10cff9 (StorePre 0x10cff9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10cff9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cff9 6 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[5291, 65]
    (.letOp (n := 5294) (.out 0x10d001 (movR64R64Effect 0x10d001 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[5176]
    (.letOp (n := 5295) (.exec 0x10d001 (fun s => s.RIP = 0x10d001) (movR64R64Effect 0x10d001 0 11) (Reg.operands [.gpr 11] [])) #v[5176]
    (.letOp (n := 5296) (.out 0x10d004 (mulR64Effect 0x10d004 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[5193, 5294]
    (.letOp (n := 5297) (.out 0x10d004 (mulR64Effect 0x10d004 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[5193, 5294]
    (.letOp (n := 5298) (.exec 0x10d004 (fun s => s.RIP = 0x10d004) (mulR64Effect 0x10d004 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[5193, 5294]
    (.letOp (n := 5299) (.out 0x10d007 (movR64R64Effect 0x10d007 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[5297]
    (.letOp (n := 5300) (.exec 0x10d007 (fun s => s.RIP = 0x10d007) (movR64R64Effect 0x10d007 8 2) (Reg.operands [.gpr 2] [])) #v[5297]
    (.letOp (n := 5301) (.out 0x10d00a (movR64R64Effect 0x10d00a 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[5296]
    (.letOp (n := 5302) (.exec 0x10d00a (fun s => s.RIP = 0x10d00a) (movR64R64Effect 0x10d00a 11 0) (Reg.operands [.gpr 0] [])) #v[5296]
    (.letOp (n := 5303) (.out 0x10d00d (movR64M64Effect 0x10d00d 3 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 5304) (.exec 0x10d00d (LoadPre 0x10d00d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10d00d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10d00d 3 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5305) (.out 0x10d015 (movR64R64Effect 0x10d015 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[5303]
    (.letOp (n := 5306) (.exec 0x10d015 (fun s => s.RIP = 0x10d015) (movR64R64Effect 0x10d015 0 3) (Reg.operands [.gpr 3] [])) #v[5303]
    (b_l10a410_125)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_124 : List UInt8 :=
  [0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xC6, 0x48, 0x89, 0xE8, 0x4C, 0x8B, 0xB4, 0x24, 0xD0,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0x54, 0x24, 0x68, 0x48, 0x89, 0xC5, 0x48, 0x89,
    0xC8, 0x48, 0xF7, 0x64, 0x24, 0x08, 0x49, 0x89, 0xC5, 0x48, 0x89, 0xD1, 0x48, 0xB8, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC6, 0x48, 0x89, 0xB4, 0x24, 0xE0, 0x00, 0x00,
    0x00, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC3, 0x48, 0x8B, 0x9C,
    0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD8] ++ bytes_l10a410_125

theorem code_l10a410_124 : ∀ x ∈ codeRange 0x10cfc0 bytes_l10a410_124, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcfc0 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_125

def b_l10a410_123 : Block Op Label signature Reg.count 5220 :=
  .letOp (n := 5220) (.out 0x10cf6b (addR64R64Effect 0x10cf6b 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[5209, 5200]
    (.letOp (n := 5221) (.out 0x10cf6b (addR64R64Effect 0x10cf6b 14 3) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 3] []) (.flag .CF)) #v[5209, 5200]
    (.letOp (n := 5222) (.exec 0x10cf6b (fun s => s.RIP = 0x10cf6b) (addR64R64Effect 0x10cf6b 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[5209, 5200]
    (.letOp (n := 5223) (.out 0x10cf6e (atFlags StatusFlags.CF (adcR64R64Effect 0x10cf6e 10 9)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[5207, 5198, 5221]
    (.letOp (n := 5224) (.exec 0x10cf6e (fun s => s.RIP = 0x10cf6e) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cf6e 10 9)) (Reg.operands [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5207, 5198, 5221]
    (.letOp (n := 5225) (.out 0x10cf71 (addR64R64Effect 0x10cf71 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[5220, 5185]
    (.letOp (n := 5226) (.out 0x10cf71 (addR64R64Effect 0x10cf71 14 8) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 8] []) (.flag .CF)) #v[5220, 5185]
    (.letOp (n := 5227) (.exec 0x10cf71 (fun s => s.RIP = 0x10cf71) (addR64R64Effect 0x10cf71 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[5220, 5185]
    (.letOp (n := 5228) (.out 0x10cf74 (atFlags StatusFlags.CF (adcR64R64Effect 0x10cf74 10 12)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[5223, 5187, 5226]
    (.letOp (n := 5229) (.exec 0x10cf74 (fun s => s.RIP = 0x10cf74) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cf74 10 12)) (Reg.operands [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5223, 5187, 5226]
    (.letOp (n := 5230) (.out 0x10cf77 (addR64R64Effect 0x10cf77 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[5215, 5225]
    (.letOp (n := 5231) (.out 0x10cf77 (addR64R64Effect 0x10cf77 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[5215, 5225]
    (.letOp (n := 5232) (.exec 0x10cf77 (fun s => s.RIP = 0x10cf77) (addR64R64Effect 0x10cf77 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[5215, 5225]
    (.letOp (n := 5233) (.out 0x10cf7a (atFlags StatusFlags.CF (adcR64R64Effect 0x10cf7a 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[5228, 5216, 5231]
    (.letOp (n := 5234) (.exec 0x10cf7a (fun s => s.RIP = 0x10cf7a) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cf7a 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5228, 5216, 5231]
    (.letOp (n := 5235) (.out 0x10cf7d (addR64R64Effect 0x10cf7d 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[5230, 5164]
    (.letOp (n := 5236) (.out 0x10cf7d (addR64R64Effect 0x10cf7d 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[5230, 5164]
    (.letOp (n := 5237) (.exec 0x10cf7d (fun s => s.RIP = 0x10cf7d) (addR64R64Effect 0x10cf7d 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[5230, 5164]
    (.letOp (n := 5238) (.out 0x10cf80 (atFlags StatusFlags.CF (adcR64R64Effect 0x10cf80 10 15)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[5233, 5162, 5236]
    (.letOp (n := 5239) (.exec 0x10cf80 (fun s => s.RIP = 0x10cf80) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cf80 10 15)) (Reg.operands [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5233, 5162, 5236]
    (.letOp (n := 5240) (.out 0x10cf83 (movR64R64Effect 0x10cf83 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 10] []) (.reg (.gpr 12))) #v[5238]
    (.letOp (n := 5241) (.exec 0x10cf83 (fun s => s.RIP = 0x10cf83) (movR64R64Effect 0x10cf83 12 10) (Reg.operands [.gpr 10] [])) #v[5238]
    (.letOp (n := 5242) (.out 0x10cf86 (shldR64R64Effect 0x10cf86 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[5238, 5235]
    (.letOp (n := 5243) (.exec 0x10cf86 (fun s => s.RIP = 0x10cf86) (shldR64R64Effect 0x10cf86 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5238, 5235]
    (.letOp (n := 5244) (.out 0x10cf8b (shlR64Effect 0x10cf8b 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5235]
    (.letOp (n := 5245) (.exec 0x10cf8b (fun s => s.RIP = 0x10cf8b) (shlR64Effect 0x10cf8b 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5235]
    (.letOp (n := 5246) (.out 0x10cf8f (movR64Imm64Effect 0x10cf8f 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 5247) (.exec 0x10cf8f (fun s => s.RIP = 0x10cf8f) (movR64Imm64Effect 0x10cf8f 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 5248) (.out 0x10cf99 (andR64R64Effect 0x10cf99 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[5244, 5246]
    (.letOp (n := 5249) (.exec 0x10cf99 (fun s => s.RIP = 0x10cf99) (andR64R64Effect 0x10cf99 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[5244, 5246]
    (.letOp (n := 5250) (.out 0x10cf9c (orR64R64Effect 0x10cf9c 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[5248, 5218]
    (.letOp (n := 5251) (.exec 0x10cf9c (fun s => s.RIP = 0x10cf9c) (orR64R64Effect 0x10cf9c 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[5248, 5218]
    (.letOp (n := 5252) (.out 0x10cf9f (movR64Imm64Effect 0x10cf9f 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 5253) (.exec 0x10cf9f (fun s => s.RIP = 0x10cf9f) (movR64Imm64Effect 0x10cf9f 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 5254) (.out 0x10cfa9 (mulR64Effect 0x10cfa9 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[5252, 5250]
    (.letOp (n := 5255) (.out 0x10cfa9 (mulR64Effect 0x10cfa9 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[5252, 5250]
    (.letOp (n := 5256) (.exec 0x10cfa9 (fun s => s.RIP = 0x10cfa9) (mulR64Effect 0x10cfa9 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[5252, 5250]
    (.letOp (n := 5257) (.out 0x10cfac (movR64R64Effect 0x10cfac 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[5255]
    (.letOp (n := 5258) (.exec 0x10cfac (fun s => s.RIP = 0x10cfac) (movR64R64Effect 0x10cfac 9 2) (Reg.operands [.gpr 2] [])) #v[5255]
    (.letOp (n := 5259) (.out 0x10cfaf (shrR64Effect 0x10cfaf 4 12 52) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[5240]
    (.letOp (n := 5260) (.exec 0x10cfaf (fun s => s.RIP = 0x10cfaf) (shrR64Effect 0x10cfaf 4 12 52) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5240]
    (.letOp (n := 5261) (.out 0x10cfb3 (addR64M64Effect 0x10cfb3 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5254, 65]
    (.letOp (n := 5262) (.out 0x10cfb3 (addR64M64Effect 0x10cfb3 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[5254, 65]
    (.letOp (n := 5263) (.exec 0x10cfb3 (LoadPre 0x10cfb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10cfb3 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10cfb3 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5254, 65]
    (.letOp (n := 5264) (.out 0x10cfb8 (atFlags StatusFlags.CF (adcR64M64Effect 0x10cfb8 9 (.sib 4 none 0 (.d32 0xe0)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[5257, 65, 5262]
    (.letOp (n := 5265) (.exec 0x10cfb8 (LoadPre 0x10cfb8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10cfb8 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10cfb8 9 (.sib 4 none 0 (.d32 0xe0)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5257, 65, 5262]
    (b_l10a410_124))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_123 : List UInt8 :=
  [0x49, 0x01, 0xDE, 0x4D, 0x11, 0xCA, 0x4D, 0x01, 0xC6, 0x4D, 0x11, 0xE2, 0x4C, 0x01, 0xF0, 0x49,
    0x11, 0xD2, 0x48, 0x01, 0xF0, 0x4D, 0x11, 0xFA, 0x4D, 0x89, 0xD4, 0x49, 0x0F, 0xA4, 0xC2, 0x0C,
    0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21,
    0xD0, 0x4C, 0x09, 0xE8, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xE2, 0x49, 0x89, 0xD1, 0x49, 0xC1, 0xEC, 0x34, 0x48, 0x03, 0x44, 0x24, 0x68, 0x4C, 0x13, 0x8C,
    0x24, 0xE0, 0x00, 0x00, 0x00] ++ bytes_l10a410_124

theorem code_l10a410_123 : ∀ x ∈ codeRange 0x10cf6b bytes_l10a410_123, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcf6b 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_124

def b_l10a410_122 : Block Op Label signature Reg.count 5176 :=
  .letOp (n := 5176) (.out 0x10cf20 (movR64M64Effect 0x10cf20 11 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 5177) (.exec 0x10cf20 (LoadPre 0x10cf20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10cf20 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10cf20 11 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5178) (.out 0x10cf25 (movR64R64Effect 0x10cf25 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[5176]
    (.letOp (n := 5179) (.exec 0x10cf25 (fun s => s.RIP = 0x10cf25) (movR64R64Effect 0x10cf25 0 11) (Reg.operands [.gpr 11] [])) #v[5176]
    (.letOp (n := 5180) (.out 0x10cf28 (movR64M64Effect 0x10cf28 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 5181) (.exec 0x10cf28 (LoadPre 0x10cf28 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10cf28 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cf28 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5182) (.out 0x10cf30 (mulR64Effect 0x10cf30 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[5180, 5178]
    (.letOp (n := 5183) (.out 0x10cf30 (mulR64Effect 0x10cf30 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[5180, 5178]
    (.letOp (n := 5184) (.exec 0x10cf30 (fun s => s.RIP = 0x10cf30) (mulR64Effect 0x10cf30 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5180, 5178]
    (.letOp (n := 5185) (.out 0x10cf33 (movR64R64Effect 0x10cf33 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[5182]
    (.letOp (n := 5186) (.exec 0x10cf33 (fun s => s.RIP = 0x10cf33) (movR64R64Effect 0x10cf33 8 0) (Reg.operands [.gpr 0] [])) #v[5182]
    (.letOp (n := 5187) (.out 0x10cf36 (movR64R64Effect 0x10cf36 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[5183]
    (.letOp (n := 5188) (.exec 0x10cf36 (fun s => s.RIP = 0x10cf36) (movR64R64Effect 0x10cf36 12 2) (Reg.operands [.gpr 2] [])) #v[5183]
    (.letOp (n := 5189) (.out 0x10cf39 (shrR64Effect 0x10cf39 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[5166]
    (.letOp (n := 5190) (.exec 0x10cf39 (fun s => s.RIP = 0x10cf39) (shrR64Effect 0x10cf39 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5166]
    (.letOp (n := 5191) (.out 0x10cf3d (movR64R64Effect 0x10cf3d 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[5070]
    (.letOp (n := 5192) (.exec 0x10cf3d (fun s => s.RIP = 0x10cf3d) (movR64R64Effect 0x10cf3d 0 7) (Reg.operands [.gpr 7] [])) #v[5070]
    (.letOp (n := 5193) (.out 0x10cf40 (movR64M64Effect 0x10cf40 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 5194) (.exec 0x10cf40 (LoadPre 0x10cf40 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10cf40 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10cf40 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5195) (.out 0x10cf45 (mulR64Effect 0x10cf45 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[5193, 5191]
    (.letOp (n := 5196) (.out 0x10cf45 (mulR64Effect 0x10cf45 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[5193, 5191]
    (.letOp (n := 5197) (.exec 0x10cf45 (fun s => s.RIP = 0x10cf45) (mulR64Effect 0x10cf45 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[5193, 5191]
    (.letOp (n := 5198) (.out 0x10cf48 (movR64R64Effect 0x10cf48 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[5196]
    (.letOp (n := 5199) (.exec 0x10cf48 (fun s => s.RIP = 0x10cf48) (movR64R64Effect 0x10cf48 9 2) (Reg.operands [.gpr 2] [])) #v[5196]
    (.letOp (n := 5200) (.out 0x10cf4b (movR64R64Effect 0x10cf4b 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[5195]
    (.letOp (n := 5201) (.exec 0x10cf4b (fun s => s.RIP = 0x10cf4b) (movR64R64Effect 0x10cf4b 3 0) (Reg.operands [.gpr 0] [])) #v[5195]
    (.letOp (n := 5202) (.out 0x10cf4e (movR64R64Effect 0x10cf4e 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[5090]
    (.letOp (n := 5203) (.exec 0x10cf4e (fun s => s.RIP = 0x10cf4e) (movR64R64Effect 0x10cf4e 0 14) (Reg.operands [.gpr 14] [])) #v[5090]
    (.letOp (n := 5204) (.out 0x10cf51 (mulM64Effect 0x10cf51 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5202, 65]
    (.letOp (n := 5205) (.out 0x10cf51 (mulM64Effect 0x10cf51 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5202, 65]
    (.letOp (n := 5206) (.exec 0x10cf51 (LoadPre 0x10cf51 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10cf51 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10cf51 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5202, 65]
    (.letOp (n := 5207) (.out 0x10cf56 (movR64R64Effect 0x10cf56 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[5205]
    (.letOp (n := 5208) (.exec 0x10cf56 (fun s => s.RIP = 0x10cf56) (movR64R64Effect 0x10cf56 10 2) (Reg.operands [.gpr 2] [])) #v[5205]
    (.letOp (n := 5209) (.out 0x10cf59 (movR64R64Effect 0x10cf59 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[5204]
    (.letOp (n := 5210) (.exec 0x10cf59 (fun s => s.RIP = 0x10cf59) (movR64R64Effect 0x10cf59 14 0) (Reg.operands [.gpr 0] [])) #v[5204]
    (.letOp (n := 5211) (.out 0x10cf5c (movR64R64Effect 0x10cf5c 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5099]
    (.letOp (n := 5212) (.exec 0x10cf5c (fun s => s.RIP = 0x10cf5c) (movR64R64Effect 0x10cf5c 0 5) (Reg.operands [.gpr 5] [])) #v[5099]
    (.letOp (n := 5213) (.out 0x10cf5f (movR64M64Effect 0x10cf5f 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 5214) (.exec 0x10cf5f (LoadPre 0x10cf5f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10cf5f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10cf5f 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5215) (.out 0x10cf64 (mulR64Effect 0x10cf64 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[5213, 5211]
    (.letOp (n := 5216) (.out 0x10cf64 (mulR64Effect 0x10cf64 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[5213, 5211]
    (.letOp (n := 5217) (.exec 0x10cf64 (fun s => s.RIP = 0x10cf64) (mulR64Effect 0x10cf64 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[5213, 5211]
    (.letOp (n := 5218) (.out 0x10cf67 (andR32Imm8Effect 0x10cf67 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[5189]
    (.letOp (n := 5219) (.exec 0x10cf67 (fun s => s.RIP = 0x10cf67) (andR32Imm8Effect 0x10cf67 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[5189]
    (b_l10a410_123))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_122 : List UInt8 :=
  [0x4C, 0x8B, 0x5C, 0x24, 0x48, 0x4C, 0x89, 0xD8, 0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE1, 0x49, 0x89, 0xC0, 0x49, 0x89, 0xD4, 0x49, 0xC1, 0xED, 0x30, 0x48, 0x89, 0xF8,
    0x48, 0x8B, 0x7C, 0x24, 0x70, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xD1, 0x48, 0x89, 0xC3, 0x4C, 0x89,
    0xF0, 0x48, 0xF7, 0x64, 0x24, 0x30, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC6, 0x48, 0x89, 0xE8, 0x48,
    0x8B, 0x6C, 0x24, 0x28, 0x48, 0xF7, 0xE5, 0x41, 0x83, 0xE5, 0x0F] ++ bytes_l10a410_123

theorem code_l10a410_122 : ∀ x ∈ codeRange 0x10cf20 bytes_l10a410_122, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcf20 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_123

def b_l10a410_121 : Block Op Label signature Reg.count 5133 :=
  .letOp (n := 5133) (.out 0x10cebf (atFlags StatusFlags.CF (adcR64M64Effect 0x10cebf 6 (.sib 4 none 0 (.d8 0x68)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[5084, 65, 5131]
    (.letOp (n := 5134) (.exec 0x10cebf (LoadPre 0x10cebf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10cebf + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10cebf 6 (.sib 4 none 0 (.d8 0x68)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5084, 65, 5131]
    (.letOp (n := 5135) (.out 0x10cec4 (addR64R64Effect 0x10cec4 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[5130, 5097]
    (.letOp (n := 5136) (.out 0x10cec4 (addR64R64Effect 0x10cec4 8 13) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 13] []) (.flag .CF)) #v[5130, 5097]
    (.letOp (n := 5137) (.exec 0x10cec4 (fun s => s.RIP = 0x10cec4) (addR64R64Effect 0x10cec4 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[5130, 5097]
    (.letOp (n := 5138) (.out 0x10cec7 (atFlags StatusFlags.CF (adcR64R64Effect 0x10cec7 6 15)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[5133, 5095, 5136]
    (.letOp (n := 5139) (.exec 0x10cec7 (fun s => s.RIP = 0x10cec7) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cec7 6 15)) (Reg.operands [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5133, 5095, 5136]
    (.letOp (n := 5140) (.out 0x10ceca (addR64M64Effect 0x10ceca 8 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[5135, 65]
    (.letOp (n := 5141) (.out 0x10ceca (addR64M64Effect 0x10ceca 8 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[5135, 65]
    (.letOp (n := 5142) (.exec 0x10ceca (LoadPre 0x10ceca (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10ceca + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10ceca 8 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[5135, 65]
    (.letOp (n := 5143) (.out 0x10ced2 (atFlags StatusFlags.CF (adcR64M64Effect 0x10ced2 6 (.sib 4 none 0 (.d32 0xc8)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[5138, 65, 5141]
    (.letOp (n := 5144) (.exec 0x10ced2 (LoadPre 0x10ced2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10ced2 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10ced2 6 (.sib 4 none 0 (.d32 0xc8)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5138, 65, 5141]
    (.letOp (n := 5145) (.out 0x10ceda (addR64R64Effect 0x10ceda 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[5140, 5108]
    (.letOp (n := 5146) (.out 0x10ceda (addR64R64Effect 0x10ceda 8 12) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 12] []) (.flag .CF)) #v[5140, 5108]
    (.letOp (n := 5147) (.exec 0x10ceda (fun s => s.RIP = 0x10ceda) (addR64R64Effect 0x10ceda 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[5140, 5108]
    (.letOp (n := 5148) (.out 0x10cedd (atFlags StatusFlags.CF (adcR64M64Effect 0x10cedd 6 (.sib 4 none 0 (.d32 0xd8)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[5143, 65, 5146]
    (.letOp (n := 5149) (.exec 0x10cedd (LoadPre 0x10cedd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10cedd + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10cedd 6 (.sib 4 none 0 (.d32 0xd8)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5143, 65, 5146]
    (.letOp (n := 5150) (.out 0x10cee5 (addR64R64Effect 0x10cee5 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[5145, 5119]
    (.letOp (n := 5151) (.out 0x10cee5 (addR64R64Effect 0x10cee5 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[5145, 5119]
    (.letOp (n := 5152) (.exec 0x10cee5 (fun s => s.RIP = 0x10cee5) (addR64R64Effect 0x10cee5 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[5145, 5119]
    (.letOp (n := 5153) (.out 0x10cee8 (atFlags StatusFlags.CF (adcR64R64Effect 0x10cee8 6 9)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[5148, 5122, 5151]
    (.letOp (n := 5154) (.exec 0x10cee8 (fun s => s.RIP = 0x10cee8) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cee8 6 9)) (Reg.operands [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5148, 5122, 5151]
    (.letOp (n := 5155) (.out 0x10ceeb (addR64R64Effect 0x10ceeb 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[5150, 5126]
    (.letOp (n := 5156) (.out 0x10ceeb (addR64R64Effect 0x10ceeb 8 1) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 1] []) (.flag .CF)) #v[5150, 5126]
    (.letOp (n := 5157) (.exec 0x10ceeb (fun s => s.RIP = 0x10ceeb) (addR64R64Effect 0x10ceeb 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[5150, 5126]
    (.letOp (n := 5158) (.out 0x10ceee (atFlags StatusFlags.CF (adcR64R64Effect 0x10ceee 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[5153, 5128, 5156]
    (.letOp (n := 5159) (.exec 0x10ceee (fun s => s.RIP = 0x10ceee) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ceee 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5153, 5128, 5156]
    (.letOp (n := 5160) (.out 0x10cef1 (movR64R64Effect 0x10cef1 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[5158]
    (.letOp (n := 5161) (.exec 0x10cef1 (fun s => s.RIP = 0x10cef1) (movR64R64Effect 0x10cef1 15 6) (Reg.operands [.gpr 6] [])) #v[5158]
    (.letOp (n := 5162) (.out 0x10cef4 (shrR64Effect 0x10cef4 4 15 52) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[5160]
    (.letOp (n := 5163) (.exec 0x10cef4 (fun s => s.RIP = 0x10cef4) (shrR64Effect 0x10cef4 4 15 52) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5160]
    (.letOp (n := 5164) (.out 0x10cef8 (shldR64R64Effect 0x10cef8 5 6 8 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5158, 5155]
    (.letOp (n := 5165) (.exec 0x10cef8 (fun s => s.RIP = 0x10cef8) (shldR64R64Effect 0x10cef8 5 6 8 12) (Reg.operands [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5158, 5155]
    (.letOp (n := 5166) (.out 0x10cefd (movR64R64Effect 0x10cefd 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[5155]
    (.letOp (n := 5167) (.exec 0x10cefd (fun s => s.RIP = 0x10cefd) (movR64R64Effect 0x10cefd 13 8) (Reg.operands [.gpr 8] [])) #v[5155]
    (.letOp (n := 5168) (.exec 0x10cf00 (StorePre 0x10cf00 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10cf00 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cf00 8 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[5155, 65]
    (.letOp (n := 5169) (.out 0x10cf08 (movR64M64Effect 0x10cf08 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5170) (.exec 0x10cf08 (LoadPre 0x10cf08 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10cf08 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cf08 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5171) (.out 0x10cf10 (mulR64Effect 0x10cf10 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[5103, 5169]
    (.letOp (n := 5172) (.out 0x10cf10 (mulR64Effect 0x10cf10 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[5103, 5169]
    (.letOp (n := 5173) (.exec 0x10cf10 (fun s => s.RIP = 0x10cf10) (mulR64Effect 0x10cf10 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[5103, 5169]
    (.letOp (n := 5174) (.exec 0x10cf13 (StorePre 0x10cf13 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10cf13 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cf13 2 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5172, 65]
    (.letOp (n := 5175) (.exec 0x10cf1b (StorePre 0x10cf1b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10cf1b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10cf1b 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5171, 65]
    (b_l10a410_122)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_121 : List UInt8 :=
  [0x48, 0x13, 0x74, 0x24, 0x68, 0x4D, 0x01, 0xE8, 0x4C, 0x11, 0xFE, 0x4C, 0x03, 0x84, 0x24, 0xE0,
    0x00, 0x00, 0x00, 0x48, 0x13, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xE0, 0x48, 0x13,
    0xB4, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC0, 0x4C, 0x11, 0xCE, 0x49, 0x01, 0xC8, 0x48,
    0x11, 0xD6, 0x49, 0x89, 0xF7, 0x49, 0xC1, 0xEF, 0x34, 0x4C, 0x0F, 0xA4, 0xC6, 0x0C, 0x4D, 0x89,
    0xC5, 0x4C, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00,
    0x00, 0x49, 0xF7, 0xE3, 0x48, 0x89, 0x94, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24,
    0x68] ++ bytes_l10a410_122

theorem code_l10a410_121 : ∀ x ∈ codeRange 0x10cebf bytes_l10a410_121, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcebf 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_122

def b_l10a410_120 : Block Op Label signature Reg.count 5090 :=
  .letOp (n := 5090) (.out 0x10ce67 (movR64R64Effect 0x10ce67 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 12] []) (.reg (.gpr 14))) #v[5002]
    (.letOp (n := 5091) (.exec 0x10ce67 (fun s => s.RIP = 0x10ce67) (movR64R64Effect 0x10ce67 14 12) (Reg.operands [.gpr 12] [])) #v[5002]
    (.letOp (n := 5092) (.out 0x10ce6a (mulM64Effect 0x10ce6a 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5088, 65]
    (.letOp (n := 5093) (.out 0x10ce6a (mulM64Effect 0x10ce6a 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5088, 65]
    (.letOp (n := 5094) (.exec 0x10ce6a (LoadPre 0x10ce6a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10ce6a + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ce6a 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5088, 65]
    (.letOp (n := 5095) (.out 0x10ce6f (movR64R64Effect 0x10ce6f 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[5093]
    (.letOp (n := 5096) (.exec 0x10ce6f (fun s => s.RIP = 0x10ce6f) (movR64R64Effect 0x10ce6f 15 2) (Reg.operands [.gpr 2] [])) #v[5093]
    (.letOp (n := 5097) (.out 0x10ce72 (movR64R64Effect 0x10ce72 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[5092]
    (.letOp (n := 5098) (.exec 0x10ce72 (fun s => s.RIP = 0x10ce72) (movR64R64Effect 0x10ce72 13 0) (Reg.operands [.gpr 0] [])) #v[5092]
    (.letOp (n := 5099) (.out 0x10ce75 (movR64M64Effect 0x10ce75 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 5100) (.exec 0x10ce75 (LoadPre 0x10ce75 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ce75 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ce75 5 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5101) (.out 0x10ce7a (movR64R64Effect 0x10ce7a 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5099]
    (.letOp (n := 5102) (.exec 0x10ce7a (fun s => s.RIP = 0x10ce7a) (movR64R64Effect 0x10ce7a 0 5) (Reg.operands [.gpr 5] [])) #v[5099]
    (.letOp (n := 5103) (.out 0x10ce7d (movR64M64Effect 0x10ce7d 11 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 5104) (.exec 0x10ce7d (LoadPre 0x10ce7d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10ce7d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ce7d 11 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5105) (.out 0x10ce82 (mulR64Effect 0x10ce82 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[5103, 5101]
    (.letOp (n := 5106) (.out 0x10ce82 (mulR64Effect 0x10ce82 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[5103, 5101]
    (.letOp (n := 5107) (.exec 0x10ce82 (fun s => s.RIP = 0x10ce82) (mulR64Effect 0x10ce82 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[5103, 5101]
    (.letOp (n := 5108) (.out 0x10ce85 (movR64R64Effect 0x10ce85 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[5105]
    (.letOp (n := 5109) (.exec 0x10ce85 (fun s => s.RIP = 0x10ce85) (movR64R64Effect 0x10ce85 12 0) (Reg.operands [.gpr 0] [])) #v[5105]
    (.letOp (n := 5110) (.exec 0x10ce88 (StorePre 0x10ce88 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10ce88 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ce88 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5106, 65]
    (.letOp (n := 5111) (.out 0x10ce90 (shrR64Effect 0x10ce90 4 9 52) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[5021]
    (.letOp (n := 5112) (.exec 0x10ce90 (fun s => s.RIP = 0x10ce90) (shrR64Effect 0x10ce90 4 9 52) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5021]
    (.letOp (n := 5113) (.out 0x10ce94 (movR64Imm64Effect 0x10ce94 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 5114) (.exec 0x10ce94 (fun s => s.RIP = 0x10ce94) (movR64Imm64Effect 0x10ce94 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 5115) (.out 0x10ce9e (imulR64R64Effect 0x10ce9e 4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[5111, 5113]
    (.letOp (n := 5116) (.exec 0x10ce9e (fun s => s.RIP = 0x10ce9e) (imulR64R64Effect 0x10ce9e 4 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[5111, 5113]
    (.letOp (n := 5117) (.out 0x10cea2 (movR64R64Effect 0x10cea2 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[5061]
    (.letOp (n := 5118) (.exec 0x10cea2 (fun s => s.RIP = 0x10cea2) (movR64R64Effect 0x10cea2 0 10) (Reg.operands [.gpr 10] [])) #v[5061]
    (.letOp (n := 5119) (.out 0x10cea5 (mulR64Effect 0x10cea5 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[5113, 5117]
    (.letOp (n := 5120) (.out 0x10cea5 (mulR64Effect 0x10cea5 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[5113, 5117]
    (.letOp (n := 5121) (.exec 0x10cea5 (fun s => s.RIP = 0x10cea5) (mulR64Effect 0x10cea5 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[5113, 5117]
    (.letOp (n := 5122) (.out 0x10cea8 (addR64R64Effect 0x10cea8 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[5115, 5120]
    (.letOp (n := 5123) (.exec 0x10cea8 (fun s => s.RIP = 0x10cea8) (addR64R64Effect 0x10cea8 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[5115, 5120]
    (.letOp (n := 5124) (.out 0x10ceab (movR64R64Effect 0x10ceab 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[5059]
    (.letOp (n := 5125) (.exec 0x10ceab (fun s => s.RIP = 0x10ceab) (movR64R64Effect 0x10ceab 2 1) (Reg.operands [.gpr 1] [])) #v[5059]
    (.letOp (n := 5126) (.out 0x10ceae (shldR64R64Effect 0x10ceae 5 1 3 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5059, 5055]
    (.letOp (n := 5127) (.exec 0x10ceae (fun s => s.RIP = 0x10ceae) (shldR64R64Effect 0x10ceae 5 1 3 12) (Reg.operands [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5059, 5055]
    (.letOp (n := 5128) (.out 0x10ceb3 (shrR64Effect 0x10ceb3 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5124]
    (.letOp (n := 5129) (.exec 0x10ceb3 (fun s => s.RIP = 0x10ceb3) (shrR64Effect 0x10ceb3 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5124]
    (.letOp (n := 5130) (.out 0x10ceb7 (addR64M64Effect 0x10ceb7 8 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[5086, 65]
    (.letOp (n := 5131) (.out 0x10ceb7 (addR64M64Effect 0x10ceb7 8 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[5086, 65]
    (.letOp (n := 5132) (.exec 0x10ceb7 (LoadPre 0x10ceb7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10ceb7 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10ceb7 8 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[5086, 65]
    (b_l10a410_121)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_120 : List UInt8 :=
  [0x4D, 0x89, 0xE6, 0x48, 0xF7, 0x64, 0x24, 0x28, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC5, 0x48, 0x8B,
    0x6C, 0x24, 0x18, 0x48, 0x89, 0xE8, 0x4C, 0x8B, 0x5C, 0x24, 0x08, 0x49, 0xF7, 0xE3, 0x49, 0x89,
    0xC4, 0x48, 0x89, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x49, 0xC1, 0xE9, 0x34, 0x48, 0xBA, 0x10,
    0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xCA, 0x4C, 0x89, 0xD0, 0x48, 0xF7,
    0xE2, 0x49, 0x01, 0xD1, 0x48, 0x89, 0xCA, 0x48, 0x0F, 0xA4, 0xD9, 0x0C, 0x48, 0xC1, 0xEA, 0x34,
    0x4C, 0x03, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] ++ bytes_l10a410_121

theorem code_l10a410_120 : ∀ x ∈ codeRange 0x10ce67 bytes_l10a410_120, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xce67 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_121

def b_l10a410_119 : Block Op Label signature Reg.count 5050 :=
  .letOp (n := 5050) (.out 0x10ce0c (addR64R64Effect 0x10ce0c 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[5045, 5010]
    (.letOp (n := 5051) (.out 0x10ce0c (addR64R64Effect 0x10ce0c 3 14) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 14] []) (.flag .CF)) #v[5045, 5010]
    (.letOp (n := 5052) (.exec 0x10ce0c (fun s => s.RIP = 0x10ce0c) (addR64R64Effect 0x10ce0c 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[5045, 5010]
    (.letOp (n := 5053) (.out 0x10ce0f (atFlags StatusFlags.CF (adcR64M64Effect 0x10ce0f 1 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[5048, 65, 5051]
    (.letOp (n := 5054) (.exec 0x10ce0f (LoadPre 0x10ce0f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10ce0f + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10ce0f 1 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5048, 65, 5051]
    (.letOp (n := 5055) (.out 0x10ce17 (addR64R64Effect 0x10ce17 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[5050, 5034]
    (.letOp (n := 5056) (.out 0x10ce17 (addR64R64Effect 0x10ce17 3 0) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 0] []) (.flag .CF)) #v[5050, 5034]
    (.letOp (n := 5057) (.exec 0x10ce17 (fun s => s.RIP = 0x10ce17) (addR64R64Effect 0x10ce17 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[5050, 5034]
    (.letOp (n := 5058) (.exec 0x10ce1a (StorePre 0x10ce1a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10ce1a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ce1a 3 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[5055, 65]
    (.letOp (n := 5059) (.out 0x10ce22 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ce22 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[5053, 5035, 5056]
    (.letOp (n := 5060) (.exec 0x10ce22 (fun s => s.RIP = 0x10ce22) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ce22 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[5053, 5035, 5056]
    (.letOp (n := 5061) (.out 0x10ce25 (shrdR64R64Effect 0x10ce25 5 10 9 52) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[5019, 5021]
    (.letOp (n := 5062) (.exec 0x10ce25 (fun s => s.RIP = 0x10ce25) (shrdR64R64Effect 0x10ce25 5 10 9 52) (Reg.operands [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5019, 5021]
    (.letOp (n := 5063) (.out 0x10ce2a (movR64R64Effect 0x10ce2a 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[5014]
    (.letOp (n := 5064) (.exec 0x10ce2a (fun s => s.RIP = 0x10ce2a) (movR64R64Effect 0x10ce2a 0 6) (Reg.operands [.gpr 6] [])) #v[5014]
    (.letOp (n := 5065) (.out 0x10ce2d (mulR64Effect 0x10ce2d 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[4970, 5063]
    (.letOp (n := 5066) (.out 0x10ce2d (mulR64Effect 0x10ce2d 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[4970, 5063]
    (.letOp (n := 5067) (.exec 0x10ce2d (fun s => s.RIP = 0x10ce2d) (mulR64Effect 0x10ce2d 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[4970, 5063]
    (.letOp (n := 5068) (.exec 0x10ce30 (StorePre 0x10ce30 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10ce30 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ce30 2 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5066, 65]
    (.letOp (n := 5069) (.exec 0x10ce38 (StorePre 0x10ce38 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10ce38 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ce38 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5065, 65]
    (.letOp (n := 5070) (.out 0x10ce40 (movR64M64Effect 0x10ce40 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 5071) (.exec 0x10ce40 (LoadPre 0x10ce40 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10ce40 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ce40 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5072) (.out 0x10ce45 (movR64R64Effect 0x10ce45 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[5070]
    (.letOp (n := 5073) (.exec 0x10ce45 (fun s => s.RIP = 0x10ce45) (movR64R64Effect 0x10ce45 0 7) (Reg.operands [.gpr 7] [])) #v[5070]
    (.letOp (n := 5074) (.out 0x10ce48 (mulR64Effect 0x10ce48 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[4981, 5072]
    (.letOp (n := 5075) (.out 0x10ce48 (mulR64Effect 0x10ce48 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[4981, 5072]
    (.letOp (n := 5076) (.exec 0x10ce48 (fun s => s.RIP = 0x10ce48) (mulR64Effect 0x10ce48 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[4981, 5072]
    (.letOp (n := 5077) (.exec 0x10ce4b (StorePre 0x10ce4b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10ce4b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ce4b 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5075, 65]
    (.letOp (n := 5078) (.exec 0x10ce50 (StorePre 0x10ce50 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10ce50 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ce50 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5074, 65]
    (.letOp (n := 5079) (.out 0x10ce58 (movR64R64Effect 0x10ce58 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[4991]
    (.letOp (n := 5080) (.exec 0x10ce58 (fun s => s.RIP = 0x10ce58) (movR64R64Effect 0x10ce58 0 13) (Reg.operands [.gpr 13] [])) #v[4991]
    (.letOp (n := 5081) (.out 0x10ce5b (mulR64Effect 0x10ce5b 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[4977, 5079]
    (.letOp (n := 5082) (.out 0x10ce5b (mulR64Effect 0x10ce5b 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[4977, 5079]
    (.letOp (n := 5083) (.exec 0x10ce5b (fun s => s.RIP = 0x10ce5b) (mulR64Effect 0x10ce5b 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[4977, 5079]
    (.letOp (n := 5084) (.out 0x10ce5e (movR64R64Effect 0x10ce5e 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[5082]
    (.letOp (n := 5085) (.exec 0x10ce5e (fun s => s.RIP = 0x10ce5e) (movR64R64Effect 0x10ce5e 6 2) (Reg.operands [.gpr 2] [])) #v[5082]
    (.letOp (n := 5086) (.out 0x10ce61 (movR64R64Effect 0x10ce61 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[5081]
    (.letOp (n := 5087) (.exec 0x10ce61 (fun s => s.RIP = 0x10ce61) (movR64R64Effect 0x10ce61 8 0) (Reg.operands [.gpr 0] [])) #v[5081]
    (.letOp (n := 5088) (.out 0x10ce64 (movR64R64Effect 0x10ce64 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[5002]
    (.letOp (n := 5089) (.exec 0x10ce64 (fun s => s.RIP = 0x10ce64) (movR64R64Effect 0x10ce64 0 12) (Reg.operands [.gpr 12] [])) #v[5002]
    (b_l10a410_120))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_119 : List UInt8 :=
  [0x4C, 0x01, 0xF3, 0x48, 0x13, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x01, 0xC3, 0x48, 0x89,
    0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x11, 0xD1, 0x4D, 0x0F, 0xAC, 0xCA, 0x34, 0x48, 0x89,
    0xF0, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24,
    0xE0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x7C, 0x24, 0x58, 0x48, 0x89, 0xF8, 0x49, 0xF7, 0xE0, 0x48,
    0x89, 0x54, 0x24, 0x68, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE8, 0x49,
    0xF7, 0xE3, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC0, 0x4C, 0x89, 0xE0] ++ bytes_l10a410_120

theorem code_l10a410_119 : ∀ x ∈ codeRange 0x10ce0c bytes_l10a410_119, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xce0c 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_120

def b_l10a410_118 : Block Op Label signature Reg.count 5009 :=
  .letOp (n := 5009) (.exec 0x10cd9e (StorePre 0x10cd9e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10cd9e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cd9e 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5007, 65]
    (.letOp (n := 5010) (.out 0x10cda6 (movR64R64Effect 0x10cda6 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[5006]
    (.letOp (n := 5011) (.exec 0x10cda6 (fun s => s.RIP = 0x10cda6) (movR64R64Effect 0x10cda6 14 0) (Reg.operands [.gpr 0] [])) #v[5006]
    (.letOp (n := 5012) (.out 0x10cda9 (movR64M64Effect 0x10cda9 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 5013) (.exec 0x10cda9 (LoadPre 0x10cda9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10cda9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10cda9 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5014) (.out 0x10cdae (movR64M64Effect 0x10cdae 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 5015) (.exec 0x10cdae (LoadPre 0x10cdae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10cdae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10cdae 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5016) (.out 0x10cdb3 (mulR64Effect 0x10cdb3 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[5014, 5012]
    (.letOp (n := 5017) (.out 0x10cdb3 (mulR64Effect 0x10cdb3 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[5014, 5012]
    (.letOp (n := 5018) (.exec 0x10cdb3 (fun s => s.RIP = 0x10cdb3) (mulR64Effect 0x10cdb3 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[5014, 5012]
    (.letOp (n := 5019) (.out 0x10cdb6 (movR64R64Effect 0x10cdb6 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[5016]
    (.letOp (n := 5020) (.exec 0x10cdb6 (fun s => s.RIP = 0x10cdb6) (movR64R64Effect 0x10cdb6 10 0) (Reg.operands [.gpr 0] [])) #v[5016]
    (.letOp (n := 5021) (.out 0x10cdb9 (movR64R64Effect 0x10cdb9 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[5017]
    (.letOp (n := 5022) (.exec 0x10cdb9 (fun s => s.RIP = 0x10cdb9) (movR64R64Effect 0x10cdb9 9 2) (Reg.operands [.gpr 2] [])) #v[5017]
    (.letOp (n := 5023) (.out 0x10cdbc (movR64Imm64Effect 0x10cdbc 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 5024) (.exec 0x10cdbc (fun s => s.RIP = 0x10cdbc) (movR64Imm64Effect 0x10cdbc 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 5025) (.out 0x10cdc6 (andR64R64Effect 0x10cdc6 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[4940, 5023]
    (.letOp (n := 5026) (.exec 0x10cdc6 (fun s => s.RIP = 0x10cdc6) (andR64R64Effect 0x10cdc6 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[4940, 5023]
    (.letOp (n := 5027) (.exec 0x10cdc9 (StorePre 0x10cdc9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10cdc9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cdc9 5 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5025, 65]
    (.letOp (n := 5028) (.out 0x10cdd1 (andR64R64Effect 0x10cdd1 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[5016, 5023]
    (.letOp (n := 5029) (.exec 0x10cdd1 (fun s => s.RIP = 0x10cdd1) (andR64R64Effect 0x10cdd1 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[5016, 5023]
    (.letOp (n := 5030) (.out 0x10cdd4 (movR64R64Effect 0x10cdd4 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[5023]
    (.letOp (n := 5031) (.exec 0x10cdd4 (fun s => s.RIP = 0x10cdd4) (movR64R64Effect 0x10cdd4 5 2) (Reg.operands [.gpr 2] [])) #v[5023]
    (.letOp (n := 5032) (.out 0x10cdd7 (movR64Imm64Effect 0x10cdd7 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 5033) (.exec 0x10cdd7 (fun s => s.RIP = 0x10cdd7) (movR64Imm64Effect 0x10cdd7 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 5034) (.out 0x10cde1 (mulR64Effect 0x10cde1 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[5032, 5028]
    (.letOp (n := 5035) (.out 0x10cde1 (mulR64Effect 0x10cde1 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[5032, 5028]
    (.letOp (n := 5036) (.exec 0x10cde1 (fun s => s.RIP = 0x10cde1) (mulR64Effect 0x10cde1 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[5032, 5028]
    (.letOp (n := 5037) (.out 0x10cde4 (andR64R64Effect 0x10cde4 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[4954, 5030]
    (.letOp (n := 5038) (.exec 0x10cde4 (fun s => s.RIP = 0x10cde4) (andR64R64Effect 0x10cde4 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[4954, 5030]
    (.letOp (n := 5039) (.exec 0x10cde7 (StorePre 0x10cde7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10cde7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cde7 7 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[5037, 65]
    (.letOp (n := 5040) (.out 0x10cdef (addR64M64Effect 0x10cdef 3 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[5000, 65]
    (.letOp (n := 5041) (.out 0x10cdef (addR64M64Effect 0x10cdef 3 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[5000, 65]
    (.letOp (n := 5042) (.exec 0x10cdef (LoadPre 0x10cdef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10cdef + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10cdef 3 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[5000, 65]
    (.letOp (n := 5043) (.out 0x10cdf4 (atFlags StatusFlags.CF (adcR64M64Effect 0x10cdf4 1 (.sib 4 none 0 (.d32 0xe0)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[4998, 65, 5041]
    (.letOp (n := 5044) (.exec 0x10cdf4 (LoadPre 0x10cdf4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10cdf4 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10cdf4 1 (.sib 4 none 0 (.d32 0xe0)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4998, 65, 5041]
    (.letOp (n := 5045) (.out 0x10cdfc (addR64M64Effect 0x10cdfc 3 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[5040, 65]
    (.letOp (n := 5046) (.out 0x10cdfc (addR64M64Effect 0x10cdfc 3 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[5040, 65]
    (.letOp (n := 5047) (.exec 0x10cdfc (LoadPre 0x10cdfc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10cdfc + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10cdfc 3 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[5040, 65]
    (.letOp (n := 5048) (.out 0x10ce04 (atFlags StatusFlags.CF (adcR64M64Effect 0x10ce04 1 (.sib 4 none 0 (.d32 0xa8)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[5043, 65, 5046]
    (.letOp (n := 5049) (.exec 0x10ce04 (LoadPre 0x10ce04 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10ce04 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10ce04 1 (.sib 4 none 0 (.d32 0xa8)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[5043, 65, 5046]
    (b_l10a410_119)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_118 : List UInt8 :=
  [0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x44, 0x24, 0x18,
    0x48, 0x8B, 0x74, 0x24, 0x48, 0x48, 0xF7, 0xE6, 0x49, 0x89, 0xC2, 0x49, 0x89, 0xD1, 0x48, 0xBA,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD5, 0x48, 0x89, 0xAC, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x48, 0x21, 0xD0, 0x48, 0x89, 0xD5, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x21, 0xEF, 0x48, 0x89, 0xBC, 0x24, 0xB8, 0x00, 0x00,
    0x00, 0x48, 0x03, 0x5C, 0x24, 0x68, 0x48, 0x13, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x03,
    0x9C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x13, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] ++ bytes_l10a410_119

theorem code_l10a410_118 : ∀ x ∈ codeRange 0x10cd9e bytes_l10a410_118, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcd9e 110 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_119

def b_l10a410_117 : Block Op Label signature Reg.count 4970 :=
  .letOp (n := 4970) (.out 0x10cd35 (movR64M64Effect 0x10cd35 15 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 4971) (.exec 0x10cd35 (LoadPre 0x10cd35 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10cd35 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cd35 15 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4972) (.out 0x10cd3d (mulR64Effect 0x10cd3d 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[4970, 4968]
    (.letOp (n := 4973) (.out 0x10cd3d (mulR64Effect 0x10cd3d 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[4970, 4968]
    (.letOp (n := 4974) (.exec 0x10cd3d (fun s => s.RIP = 0x10cd3d) (mulR64Effect 0x10cd3d 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[4970, 4968]
    (.letOp (n := 4975) (.exec 0x10cd40 (StorePre 0x10cd40 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10cd40 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cd40 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[4973, 65]
    (.letOp (n := 4976) (.exec 0x10cd48 (StorePre 0x10cd48 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10cd48 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cd48 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4972, 65]
    (.letOp (n := 4977) (.out 0x10cd50 (movR64M64Effect 0x10cd50 11 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 4978) (.exec 0x10cd50 (LoadPre 0x10cd50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10cd50 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10cd50 11 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4979) (.out 0x10cd55 (movR64R64Effect 0x10cd55 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[4977]
    (.letOp (n := 4980) (.exec 0x10cd55 (fun s => s.RIP = 0x10cd55) (movR64R64Effect 0x10cd55 0 11) (Reg.operands [.gpr 11] [])) #v[4977]
    (.letOp (n := 4981) (.out 0x10cd58 (movR64M64Effect 0x10cd58 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 4982) (.exec 0x10cd58 (LoadPre 0x10cd58 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10cd58 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cd58 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4983) (.out 0x10cd60 (mulR64Effect 0x10cd60 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[4981, 4979]
    (.letOp (n := 4984) (.out 0x10cd60 (mulR64Effect 0x10cd60 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[4981, 4979]
    (.letOp (n := 4985) (.exec 0x10cd60 (fun s => s.RIP = 0x10cd60) (mulR64Effect 0x10cd60 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[4981, 4979]
    (.letOp (n := 4986) (.exec 0x10cd63 (StorePre 0x10cd63 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10cd63 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10cd63 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4983, 65]
    (.letOp (n := 4987) (.exec 0x10cd68 (StorePre 0x10cd68 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10cd68 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cd68 2 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[4984, 65]
    (.letOp (n := 4988) (.out 0x10cd70 (andR64R64Effect 0x10cd70 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[4936, 4864]
    (.letOp (n := 4989) (.exec 0x10cd70 (fun s => s.RIP = 0x10cd70) (andR64R64Effect 0x10cd70 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[4936, 4864]
    (.letOp (n := 4990) (.exec 0x10cd73 (StorePre 0x10cd73 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10cd73 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cd73 9 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[4988, 65]
    (.letOp (n := 4991) (.out 0x10cd7b (movR64M64Effect 0x10cd7b 13 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 4992) (.exec 0x10cd7b (LoadPre 0x10cd7b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10cd7b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10cd7b 13 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4993) (.out 0x10cd80 (movR64R64Effect 0x10cd80 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[4991]
    (.letOp (n := 4994) (.exec 0x10cd80 (fun s => s.RIP = 0x10cd80) (movR64R64Effect 0x10cd80 0 13) (Reg.operands [.gpr 13] [])) #v[4991]
    (.letOp (n := 4995) (.out 0x10cd83 (mulM64Effect 0x10cd83 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4993, 65]
    (.letOp (n := 4996) (.out 0x10cd83 (mulM64Effect 0x10cd83 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4993, 65]
    (.letOp (n := 4997) (.exec 0x10cd83 (LoadPre 0x10cd83 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10cd83 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10cd83 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4993, 65]
    (.letOp (n := 4998) (.out 0x10cd88 (movR64R64Effect 0x10cd88 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[4996]
    (.letOp (n := 4999) (.exec 0x10cd88 (fun s => s.RIP = 0x10cd88) (movR64R64Effect 0x10cd88 1 2) (Reg.operands [.gpr 2] [])) #v[4996]
    (.letOp (n := 5000) (.out 0x10cd8b (movR64R64Effect 0x10cd8b 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[4995]
    (.letOp (n := 5001) (.exec 0x10cd8b (fun s => s.RIP = 0x10cd8b) (movR64R64Effect 0x10cd8b 3 0) (Reg.operands [.gpr 0] [])) #v[4995]
    (.letOp (n := 5002) (.out 0x10cd8e (movR64M64Effect 0x10cd8e 12 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 5003) (.exec 0x10cd8e (LoadPre 0x10cd8e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10cd8e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cd8e 12 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 5004) (.out 0x10cd96 (movR64R64Effect 0x10cd96 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[5002]
    (.letOp (n := 5005) (.exec 0x10cd96 (fun s => s.RIP = 0x10cd96) (movR64R64Effect 0x10cd96 0 12) (Reg.operands [.gpr 12] [])) #v[5002]
    (.letOp (n := 5006) (.out 0x10cd99 (mulM64Effect 0x10cd99 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[5004, 65]
    (.letOp (n := 5007) (.out 0x10cd99 (mulM64Effect 0x10cd99 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[5004, 65]
    (.letOp (n := 5008) (.exec 0x10cd99 (LoadPre 0x10cd99 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10cd99 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10cd99 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5004, 65]
    (b_l10a410_118)))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_117 : List UInt8 :=
  [0x4C, 0x8B, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0x94, 0x24, 0xA8,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x5C, 0x24, 0x30,
    0x4C, 0x89, 0xD8, 0x4C, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE0, 0x48, 0x89,
    0x44, 0x24, 0x68, 0x48, 0x89, 0x94, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x49, 0x21, 0xD9, 0x4C, 0x89,
    0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x6C, 0x24, 0x70, 0x4C, 0x89, 0xE8, 0x48, 0xF7,
    0x64, 0x24, 0x28, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC3, 0x4C, 0x8B, 0xA4, 0x24, 0xC0, 0x00, 0x00,
    0x00, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0x64, 0x24, 0x08] ++ bytes_l10a410_118

theorem code_l10a410_117 : ∀ x ∈ codeRange 0x10cd35 bytes_l10a410_117, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcd35 105 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_118

def b_l10a410_116 : Block Op Label signature Reg.count 4932 :=
  .letOp (n := 4932) (.out 0x10cce5 (subR64R64Effect 0x10cce5 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 7] []) (.reg (.gpr 5))) #v[4930, 4851]
    (.letOp (n := 4933) (.exec 0x10cce5 (fun s => s.RIP = 0x10cce5) (subR64R64Effect 0x10cce5 5 7) (Reg.operands [.gpr 5, .gpr 7] [])) #v[4930, 4851]
    (.letOp (n := 4934) (.out 0x10cce8 (movR64R64Effect 0x10cce8 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[4926]
    (.letOp (n := 4935) (.exec 0x10cce8 (fun s => s.RIP = 0x10cce8) (movR64R64Effect 0x10cce8 0 2) (Reg.operands [.gpr 2] [])) #v[4926]
    (.letOp (n := 4936) (.out 0x10cceb (movR64R64Effect 0x10cceb 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[4926]
    (.letOp (n := 4937) (.exec 0x10cceb (fun s => s.RIP = 0x10cceb) (movR64R64Effect 0x10cceb 9 2) (Reg.operands [.gpr 2] [])) #v[4926]
    (.letOp (n := 4938) (.out 0x10ccee (shrR64Effect 0x10ccee 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4934]
    (.letOp (n := 4939) (.exec 0x10ccee (fun s => s.RIP = 0x10ccee) (shrR64Effect 0x10ccee 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4934]
    (.letOp (n := 4940) (.out 0x10ccf2 (addR64R64Effect 0x10ccf2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[4932, 4938]
    (.letOp (n := 4941) (.exec 0x10ccf2 (fun s => s.RIP = 0x10ccf2) (addR64R64Effect 0x10ccf2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[4932, 4938]
    (.letOp (n := 4942) (.out 0x10ccf5 (movR64M64Effect 0x10ccf5 7 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 4943) (.exec 0x10ccf5 (LoadPre 0x10ccf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10ccf5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ccf5 7 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4944) (.out 0x10ccfd (addR64R64Effect 0x10ccfd 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[4942, 4914]
    (.letOp (n := 4945) (.exec 0x10ccfd (fun s => s.RIP = 0x10ccfd) (addR64R64Effect 0x10ccfd 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[4942, 4914]
    (.letOp (n := 4946) (.out 0x10cd00 (andR64R64Effect 0x10cd00 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[4878, 4864]
    (.letOp (n := 4947) (.exec 0x10cd00 (fun s => s.RIP = 0x10cd00) (andR64R64Effect 0x10cd00 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[4878, 4864]
    (.letOp (n := 4948) (.out 0x10cd03 (subR64R64Effect 0x10cd03 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[4944, 4946]
    (.letOp (n := 4949) (.exec 0x10cd03 (fun s => s.RIP = 0x10cd03) (subR64R64Effect 0x10cd03 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[4944, 4946]
    (.letOp (n := 4950) (.out 0x10cd06 (movR64R64Effect 0x10cd06 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[4940]
    (.letOp (n := 4951) (.exec 0x10cd06 (fun s => s.RIP = 0x10cd06) (movR64R64Effect 0x10cd06 0 5) (Reg.operands [.gpr 5] [])) #v[4940]
    (.letOp (n := 4952) (.out 0x10cd09 (shrR64Effect 0x10cd09 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4950]
    (.letOp (n := 4953) (.exec 0x10cd09 (fun s => s.RIP = 0x10cd09) (shrR64Effect 0x10cd09 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4950]
    (.letOp (n := 4954) (.out 0x10cd0d (addR64R64Effect 0x10cd0d 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[4948, 4952]
    (.letOp (n := 4955) (.exec 0x10cd0d (fun s => s.RIP = 0x10cd0d) (addR64R64Effect 0x10cd0d 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[4948, 4952]
    (.letOp (n := 4956) (.out 0x10cd10 (andR64R64Effect 0x10cd10 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[4892, 4880]
    (.letOp (n := 4957) (.exec 0x10cd10 (fun s => s.RIP = 0x10cd10) (andR64R64Effect 0x10cd10 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[4892, 4880]
    (.letOp (n := 4958) (.out 0x10cd13 (movR64R64Effect 0x10cd13 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[4954]
    (.letOp (n := 4959) (.exec 0x10cd13 (fun s => s.RIP = 0x10cd13) (movR64R64Effect 0x10cd13 0 7) (Reg.operands [.gpr 7] [])) #v[4954]
    (.letOp (n := 4960) (.out 0x10cd16 (shrR64Effect 0x10cd16 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4958]
    (.letOp (n := 4961) (.exec 0x10cd16 (fun s => s.RIP = 0x10cd16) (shrR64Effect 0x10cd16 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4958]
    (.letOp (n := 4962) (.out 0x10cd1a (addR64R64Effect 0x10cd1a 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[4960, 4956]
    (.letOp (n := 4963) (.exec 0x10cd1a (fun s => s.RIP = 0x10cd1a) (addR64R64Effect 0x10cd1a 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[4960, 4956]
    (.letOp (n := 4964) (.exec 0x10cd1d (StorePre 0x10cd1d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10cd1d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cd1d 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4962, 65]
    (.letOp (n := 4965) (.out 0x10cd25 (andR64R64Effect 0x10cd25 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[4922, 4864]
    (.letOp (n := 4966) (.exec 0x10cd25 (fun s => s.RIP = 0x10cd25) (andR64R64Effect 0x10cd25 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[4922, 4864]
    (.letOp (n := 4967) (.exec 0x10cd28 (StorePre 0x10cd28 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10cd28 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cd28 8 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[4965, 65]
    (.letOp (n := 4968) (.out 0x10cd30 (movR64M64Effect 0x10cd30 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4969) (.exec 0x10cd30 (LoadPre 0x10cd30 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10cd30 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10cd30 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_117))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_116 : List UInt8 :=
  [0x48, 0x29, 0xFD, 0x48, 0x89, 0xD0, 0x49, 0x89, 0xD1, 0x48, 0xC1, 0xE8, 0x34, 0x48, 0x01, 0xC5,
    0x48, 0x8B, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xD7, 0x49, 0x21, 0xDE, 0x4C, 0x29,
    0xF7, 0x48, 0x89, 0xE8, 0x48, 0xC1, 0xE8, 0x34, 0x48, 0x01, 0xC7, 0x49, 0x21, 0xCB, 0x48, 0x89,
    0xF8, 0x48, 0xC1, 0xE8, 0x34, 0x4C, 0x01, 0xD8, 0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00,
    0x49, 0x21, 0xD8, 0x4C, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x58] ++ bytes_l10a410_117

theorem code_l10a410_116 : ∀ x ∈ codeRange 0x10cce5 bytes_l10a410_116, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcce5 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_117

def b_l10a410_115 : Block Op Label signature Reg.count 4892 :=
  .letOp (n := 4892) (.out 0x10cc7d (addR64R64Effect 0x10cc7d 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[4888, 4890]
    (.letOp (n := 4893) (.exec 0x10cc7d (fun s => s.RIP = 0x10cc7d) (addR64R64Effect 0x10cc7d 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[4888, 4890]
    (.letOp (n := 4894) (.out 0x10cc80 (movR64M64Effect 0x10cc80 6 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 4895) (.exec 0x10cc80 (LoadPre 0x10cc80 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10cc80 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cc80 6 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4896) (.out 0x10cc88 (movR64Imm64Effect 0x10cc88 0 0x3ffffbfffff0bc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 4897) (.exec 0x10cc88 (fun s => s.RIP = 0x10cc88) (movR64Imm64Effect 0x10cc88 0 0x3ffffbfffff0bc) (Reg.operands [] [])) #v[]
    (.letOp (n := 4898) (.out 0x10cc92 (addR64R64Effect 0x10cc92 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[4894, 4896]
    (.letOp (n := 4899) (.exec 0x10cc92 (fun s => s.RIP = 0x10cc92) (addR64R64Effect 0x10cc92 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[4894, 4896]
    (.letOp (n := 4900) (.out 0x10cc95 (subR64M64Effect 0x10cc95 6 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[4898, 65]
    (.letOp (n := 4901) (.exec 0x10cc95 (LoadPre 0x10cc95 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10cc95 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x10cc95 6 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[4898, 65]
    (.letOp (n := 4902) (.out 0x10cc9d (movR64R64Effect 0x10cc9d 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[4892]
    (.letOp (n := 4903) (.exec 0x10cc9d (fun s => s.RIP = 0x10cc9d) (movR64R64Effect 0x10cc9d 0 11) (Reg.operands [.gpr 11] [])) #v[4892]
    (.letOp (n := 4904) (.out 0x10cca0 (shrR64Effect 0x10cca0 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4902]
    (.letOp (n := 4905) (.exec 0x10cca0 (fun s => s.RIP = 0x10cca0) (shrR64Effect 0x10cca0 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4902]
    (.letOp (n := 4906) (.out 0x10cca4 (movR64Imm64Effect 0x10cca4 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 4907) (.exec 0x10cca4 (fun s => s.RIP = 0x10cca4) (movR64Imm64Effect 0x10cca4 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 4908) (.out 0x10ccae (imulR64R64Effect 0x10ccae 4 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[4904, 4906]
    (.letOp (n := 4909) (.exec 0x10ccae (fun s => s.RIP = 0x10ccae) (imulR64R64Effect 0x10ccae 4 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[4904, 4906]
    (.letOp (n := 4910) (.out 0x10ccb2 (addR64R64Effect 0x10ccb2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[4900, 4908]
    (.letOp (n := 4911) (.exec 0x10ccb2 (fun s => s.RIP = 0x10ccb2) (addR64R64Effect 0x10ccb2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[4900, 4908]
    (.letOp (n := 4912) (.out 0x10ccb5 (movR64M64Effect 0x10ccb5 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 4913) (.exec 0x10ccb5 (LoadPre 0x10ccb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10ccb5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ccb5 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4914) (.out 0x10ccbd (movR64Imm64Effect 0x10ccbd 10 0x3ffffffffffffc) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 4915) (.exec 0x10ccbd (fun s => s.RIP = 0x10ccbd) (movR64Imm64Effect 0x10ccbd 10 0x3ffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 4916) (.out 0x10ccc7 (addR64R64Effect 0x10ccc7 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[4912, 4914]
    (.letOp (n := 4917) (.exec 0x10ccc7 (fun s => s.RIP = 0x10ccc7) (addR64R64Effect 0x10ccc7 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[4912, 4914]
    (.letOp (n := 4918) (.out 0x10ccca (subR64R64Effect 0x10ccca 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[4916, 4782]
    (.letOp (n := 4919) (.exec 0x10ccca (fun s => s.RIP = 0x10ccca) (subR64R64Effect 0x10ccca 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[4916, 4782]
    (.letOp (n := 4920) (.out 0x10cccd (movR64R64Effect 0x10cccd 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[4910]
    (.letOp (n := 4921) (.exec 0x10cccd (fun s => s.RIP = 0x10cccd) (movR64R64Effect 0x10cccd 0 6) (Reg.operands [.gpr 6] [])) #v[4910]
    (.letOp (n := 4922) (.out 0x10ccd0 (movR64R64Effect 0x10ccd0 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[4910]
    (.letOp (n := 4923) (.exec 0x10ccd0 (fun s => s.RIP = 0x10ccd0) (movR64R64Effect 0x10ccd0 8 6) (Reg.operands [.gpr 6] [])) #v[4910]
    (.letOp (n := 4924) (.out 0x10ccd3 (shrR64Effect 0x10ccd3 4 0 52) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4920]
    (.letOp (n := 4925) (.exec 0x10ccd3 (fun s => s.RIP = 0x10ccd3) (shrR64Effect 0x10ccd3 4 0 52) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4920]
    (.letOp (n := 4926) (.out 0x10ccd7 (addR64R64Effect 0x10ccd7 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[4918, 4924]
    (.letOp (n := 4927) (.exec 0x10ccd7 (fun s => s.RIP = 0x10ccd7) (addR64R64Effect 0x10ccd7 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[4918, 4924]
    (.letOp (n := 4928) (.out 0x10ccda (movR64M64Effect 0x10ccda 5 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 4929) (.exec 0x10ccda (LoadPre 0x10ccda (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10ccda + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ccda 5 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4930) (.out 0x10cce2 (addR64R64Effect 0x10cce2 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[4928, 4914]
    (.letOp (n := 4931) (.exec 0x10cce2 (fun s => s.RIP = 0x10cce2) (addR64R64Effect 0x10cce2 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[4928, 4914]
    (b_l10a410_116))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_115 : List UInt8 :=
  [0x49, 0x01, 0xC3, 0x48, 0x8B, 0xB4, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0xB8, 0xBC, 0xF0, 0xFF,
    0xFF, 0xFB, 0xFF, 0x3F, 0x00, 0x48, 0x01, 0xC6, 0x48, 0x2B, 0xB4, 0x24, 0x50, 0x01, 0x00, 0x00,
    0x4C, 0x89, 0xD8, 0x48, 0xC1, 0xE8, 0x30, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00,
    0x00, 0x48, 0x0F, 0xAF, 0xC2, 0x48, 0x01, 0xC6, 0x48, 0x8B, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x49, 0xBA, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00, 0x4C, 0x01, 0xD2, 0x4C, 0x29, 0xCA,
    0x48, 0x89, 0xF0, 0x49, 0x89, 0xF0, 0x48, 0xC1, 0xE8, 0x34, 0x48, 0x01, 0xC2, 0x48, 0x8B, 0xAC,
    0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xD5] ++ bytes_l10a410_116

theorem code_l10a410_115 : ∀ x ∈ codeRange 0x10cc7d bytes_l10a410_115, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcc7d 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_116

def b_l10a410_114 : Block Op Label signature Reg.count 4849 :=
  .letOp (n := 4849) (.out 0x10cc24 (shldR64R64Effect 0x10cc24 5 11 7 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[4839, 4836]
    (.letOp (n := 4850) (.exec 0x10cc24 (fun s => s.RIP = 0x10cc24) (shldR64R64Effect 0x10cc24 5 11 7 12) (Reg.operands [.gpr 11, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4839, 4836]
    (.letOp (n := 4851) (.out 0x10cc29 (andR64R64Effect 0x10cc29 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[4836, 4780]
    (.letOp (n := 4852) (.exec 0x10cc29 (fun s => s.RIP = 0x10cc29) (andR64R64Effect 0x10cc29 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[4836, 4780]
    (.letOp (n := 4853) (.out 0x10cc2c (movR64R64Effect 0x10cc2c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[4841]
    (.letOp (n := 4854) (.exec 0x10cc2c (fun s => s.RIP = 0x10cc2c) (movR64R64Effect 0x10cc2c 0 3) (Reg.operands [.gpr 3] [])) #v[4841]
    (.letOp (n := 4855) (.out 0x10cc2f (mulR64Effect 0x10cc2f 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[4816, 4853]
    (.letOp (n := 4856) (.out 0x10cc2f (mulR64Effect 0x10cc2f 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[4816, 4853]
    (.letOp (n := 4857) (.exec 0x10cc2f (fun s => s.RIP = 0x10cc2f) (mulR64Effect 0x10cc2f 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[4816, 4853]
    (.letOp (n := 4858) (.out 0x10cc32 (imulR64R64Effect 0x10cc32 4 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[4843, 4816]
    (.letOp (n := 4859) (.exec 0x10cc32 (fun s => s.RIP = 0x10cc32) (imulR64R64Effect 0x10cc32 4 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[4843, 4816]
    (.letOp (n := 4860) (.out 0x10cc36 (movR64M64Effect 0x10cc36 6 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 4861) (.exec 0x10cc36 (LoadPre 0x10cc36 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10cc36 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cc36 6 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4862) (.out 0x10cc3e (andR64R64Effect 0x10cc3e 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[4860, 4780]
    (.letOp (n := 4863) (.exec 0x10cc3e (fun s => s.RIP = 0x10cc3e) (andR64R64Effect 0x10cc3e 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[4860, 4780]
    (.letOp (n := 4864) (.out 0x10cc41 (movR64R64Effect 0x10cc41 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 5] []) (.reg (.gpr 3))) #v[4780]
    (.letOp (n := 4865) (.exec 0x10cc41 (fun s => s.RIP = 0x10cc41) (movR64R64Effect 0x10cc41 3 5) (Reg.operands [.gpr 5] [])) #v[4780]
    (.letOp (n := 4866) (.out 0x10cc44 (addR64R64Effect 0x10cc44 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[4862, 4855]
    (.letOp (n := 4867) (.out 0x10cc44 (addR64R64Effect 0x10cc44 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[4862, 4855]
    (.letOp (n := 4868) (.exec 0x10cc44 (fun s => s.RIP = 0x10cc44) (addR64R64Effect 0x10cc44 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[4862, 4855]
    (.letOp (n := 4869) (.out 0x10cc47 (atFlags StatusFlags.CF (adcR64R64Effect 0x10cc47 2 8)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[4856, 4858, 4867]
    (.letOp (n := 4870) (.exec 0x10cc47 (fun s => s.RIP = 0x10cc47) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cc47 2 8)) (Reg.operands [.gpr 2, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4856, 4858, 4867]
    (.letOp (n := 4871) (.out 0x10cc4a (addR64R64Effect 0x10cc4a 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[4866, 4849]
    (.letOp (n := 4872) (.out 0x10cc4a (addR64R64Effect 0x10cc4a 6 11) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 11] []) (.flag .CF)) #v[4866, 4849]
    (.letOp (n := 4873) (.exec 0x10cc4a (fun s => s.RIP = 0x10cc4a) (addR64R64Effect 0x10cc4a 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[4866, 4849]
    (.letOp (n := 4874) (.out 0x10cc4d (atFlags StatusFlags.CF (adcR64R64Effect 0x10cc4d 2 1)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[4869, 4847, 4872]
    (.letOp (n := 4875) (.exec 0x10cc4d (fun s => s.RIP = 0x10cc4d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cc4d 2 1)) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4869, 4847, 4872]
    (.letOp (n := 4876) (.out 0x10cc50 (shldR64R64Effect 0x10cc50 5 2 6 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[4874, 4871]
    (.letOp (n := 4877) (.exec 0x10cc50 (fun s => s.RIP = 0x10cc50) (shldR64R64Effect 0x10cc50 5 2 6 12) (Reg.operands [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4874, 4871]
    (.letOp (n := 4878) (.out 0x10cc55 (movR64R64Effect 0x10cc55 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[4871]
    (.letOp (n := 4879) (.exec 0x10cc55 (fun s => s.RIP = 0x10cc55) (movR64R64Effect 0x10cc55 14 6) (Reg.operands [.gpr 6] [])) #v[4871]
    (.letOp (n := 4880) (.out 0x10cc58 (movR64Imm64Effect 0x10cc58 1 0xffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 4881) (.exec 0x10cc58 (fun s => s.RIP = 0x10cc58) (movR64Imm64Effect 0x10cc58 1 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 4882) (.out 0x10cc62 (andR64R64Effect 0x10cc62 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[4540, 4880]
    (.letOp (n := 4883) (.exec 0x10cc62 (fun s => s.RIP = 0x10cc62) (andR64R64Effect 0x10cc62 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[4540, 4880]
    (.letOp (n := 4884) (.out 0x10cc65 (addR64R64Effect 0x10cc65 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[4882, 4876]
    (.letOp (n := 4885) (.exec 0x10cc65 (fun s => s.RIP = 0x10cc65) (addR64R64Effect 0x10cc65 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[4882, 4876]
    (.letOp (n := 4886) (.out 0x10cc68 (movR64M64Effect 0x10cc68 11 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 4887) (.exec 0x10cc68 (LoadPre 0x10cc68 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10cc68 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cc68 11 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4888) (.out 0x10cc70 (subR64R64Effect 0x10cc70 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[4886, 4884]
    (.letOp (n := 4889) (.exec 0x10cc70 (fun s => s.RIP = 0x10cc70) (subR64R64Effect 0x10cc70 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[4886, 4884]
    (.letOp (n := 4890) (.out 0x10cc73 (movR64Imm64Effect 0x10cc73 0 0x3fffffffffffc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 4891) (.exec 0x10cc73 (fun s => s.RIP = 0x10cc73) (movR64Imm64Effect 0x10cc73 0 0x3fffffffffffc) (Reg.operands [] [])) #v[]
    (b_l10a410_115)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_114 : List UInt8 :=
  [0x49, 0x0F, 0xA4, 0xFB, 0x0C, 0x48, 0x21, 0xEF, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0xE6, 0x4C, 0x0F,
    0xAF, 0xC6, 0x48, 0x8B, 0xB4, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x21, 0xEE, 0x48, 0x89, 0xEB,
    0x48, 0x01, 0xC6, 0x4C, 0x11, 0xC2, 0x4C, 0x01, 0xDE, 0x48, 0x11, 0xCA, 0x48, 0x0F, 0xA4, 0xF2,
    0x0C, 0x49, 0x89, 0xF6, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x49, 0x21,
    0xCA, 0x49, 0x01, 0xD2, 0x4C, 0x8B, 0x9C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4D, 0x29, 0xD3, 0x48,
    0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00] ++ bytes_l10a410_115

theorem code_l10a410_114 : ∀ x ∈ codeRange 0x10cc24 bytes_l10a410_114, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcc24 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_115

def b_l10a410_113 : Block Op Label signature Reg.count 4802 :=
  .letOp (n := 4802) (.out 0x10cbcc (addR64R64Effect 0x10cbcc 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[4800, 4791]
    (.letOp (n := 4803) (.out 0x10cbcc (addR64R64Effect 0x10cbcc 3 14) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 14] []) (.flag .CF)) #v[4800, 4791]
    (.letOp (n := 4804) (.exec 0x10cbcc (fun s => s.RIP = 0x10cbcc) (addR64R64Effect 0x10cbcc 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[4800, 4791]
    (.letOp (n := 4805) (.out 0x10cbcf (atFlags StatusFlags.CF (adcR64R64Effect 0x10cbcf 8 12)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[4798, 4789, 4803]
    (.letOp (n := 4806) (.exec 0x10cbcf (fun s => s.RIP = 0x10cbcf) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cbcf 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4798, 4789, 4803]
    (.letOp (n := 4807) (.out 0x10cbd2 (addR64R64Effect 0x10cbd2 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[4802, 4747]
    (.letOp (n := 4808) (.out 0x10cbd2 (addR64R64Effect 0x10cbd2 3 15) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 15] []) (.flag .CF)) #v[4802, 4747]
    (.letOp (n := 4809) (.exec 0x10cbd2 (fun s => s.RIP = 0x10cbd2) (addR64R64Effect 0x10cbd2 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[4802, 4747]
    (.letOp (n := 4810) (.out 0x10cbd5 (atFlags StatusFlags.CF (adcR64R64Effect 0x10cbd5 8 6)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[4805, 4749, 4808]
    (.letOp (n := 4811) (.exec 0x10cbd5 (fun s => s.RIP = 0x10cbd5) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cbd5 8 6)) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4805, 4749, 4808]
    (.letOp (n := 4812) (.out 0x10cbd8 (movR64R64Effect 0x10cbd8 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[4807]
    (.letOp (n := 4813) (.exec 0x10cbd8 (fun s => s.RIP = 0x10cbd8) (movR64R64Effect 0x10cbd8 0 3) (Reg.operands [.gpr 3] [])) #v[4807]
    (.letOp (n := 4814) (.out 0x10cbdb (andR64R64Effect 0x10cbdb 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[4812, 4780]
    (.letOp (n := 4815) (.exec 0x10cbdb (fun s => s.RIP = 0x10cbdb) (andR64R64Effect 0x10cbdb 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[4812, 4780]
    (.letOp (n := 4816) (.out 0x10cbde (movR64Imm64Effect 0x10cbde 6 0x1000003d10) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 4817) (.exec 0x10cbde (fun s => s.RIP = 0x10cbde) (movR64Imm64Effect 0x10cbde 6 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 4818) (.out 0x10cbe8 (mulR64Effect 0x10cbe8 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[4816, 4814]
    (.letOp (n := 4819) (.out 0x10cbe8 (mulR64Effect 0x10cbe8 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[4816, 4814]
    (.letOp (n := 4820) (.exec 0x10cbe8 (fun s => s.RIP = 0x10cbe8) (mulR64Effect 0x10cbe8 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[4816, 4814]
    (.letOp (n := 4821) (.out 0x10cbeb (addR64M64Effect 0x10cbeb 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[4771, 65]
    (.letOp (n := 4822) (.out 0x10cbeb (addR64M64Effect 0x10cbeb 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[4771, 65]
    (.letOp (n := 4823) (.exec 0x10cbeb (LoadPre 0x10cbeb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10cbeb + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10cbeb 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[4771, 65]
    (.letOp (n := 4824) (.out 0x10cbf3 (atFlags StatusFlags.CF (adcR64M64Effect 0x10cbf3 11 (.sib 4 none 0 (.d8 0x68)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[4769, 65, 4822]
    (.letOp (n := 4825) (.exec 0x10cbf3 (LoadPre 0x10cbf3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10cbf3 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10cbf3 11 (.sib 4 none 0 (.d8 0x68)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4769, 65, 4822]
    (.letOp (n := 4826) (.out 0x10cbf8 (addR64M64Effect 0x10cbf8 7 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[4821, 65]
    (.letOp (n := 4827) (.out 0x10cbf8 (addR64M64Effect 0x10cbf8 7 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[4821, 65]
    (.letOp (n := 4828) (.exec 0x10cbf8 (LoadPre 0x10cbf8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10cbf8 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10cbf8 7 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[4821, 65]
    (.letOp (n := 4829) (.out 0x10cc00 (atFlags StatusFlags.CF (adcR64M64Effect 0x10cc00 11 (.sib 4 none 0 (.d32 0xa8)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[4824, 65, 4827]
    (.letOp (n := 4830) (.exec 0x10cc00 (LoadPre 0x10cc00 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10cc00 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10cc00 11 (.sib 4 none 0 (.d32 0xa8)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4824, 65, 4827]
    (.letOp (n := 4831) (.out 0x10cc08 (addR64R64Effect 0x10cc08 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[4826, 4818]
    (.letOp (n := 4832) (.out 0x10cc08 (addR64R64Effect 0x10cc08 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[4826, 4818]
    (.letOp (n := 4833) (.exec 0x10cc08 (fun s => s.RIP = 0x10cc08) (addR64R64Effect 0x10cc08 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[4826, 4818]
    (.letOp (n := 4834) (.out 0x10cc0b (atFlags StatusFlags.CF (adcR64R64Effect 0x10cc0b 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[4829, 4819, 4832]
    (.letOp (n := 4835) (.exec 0x10cc0b (fun s => s.RIP = 0x10cc0b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cc0b 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4829, 4819, 4832]
    (.letOp (n := 4836) (.out 0x10cc0e (addR64R64Effect 0x10cc0e 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[4831, 4755]
    (.letOp (n := 4837) (.out 0x10cc0e (addR64R64Effect 0x10cc0e 7 1) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 1] []) (.flag .CF)) #v[4831, 4755]
    (.letOp (n := 4838) (.exec 0x10cc0e (fun s => s.RIP = 0x10cc0e) (addR64R64Effect 0x10cc0e 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[4831, 4755]
    (.letOp (n := 4839) (.out 0x10cc11 (atFlags StatusFlags.CF (adcR64R64Effect 0x10cc11 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[4834, 4753, 4837]
    (.letOp (n := 4840) (.exec 0x10cc11 (fun s => s.RIP = 0x10cc11) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cc11 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4834, 4753, 4837]
    (.letOp (n := 4841) (.out 0x10cc14 (shrdR64R64Effect 0x10cc14 5 3 8 52) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[4807, 4810]
    (.letOp (n := 4842) (.exec 0x10cc14 (fun s => s.RIP = 0x10cc14) (shrdR64R64Effect 0x10cc14 5 3 8 52) (Reg.operands [.gpr 3, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4807, 4810]
    (.letOp (n := 4843) (.out 0x10cc19 (shrR64Effect 0x10cc19 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4810]
    (.letOp (n := 4844) (.exec 0x10cc19 (fun s => s.RIP = 0x10cc19) (shrR64Effect 0x10cc19 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4810]
    (.letOp (n := 4845) (.out 0x10cc1d (movR64R64Effect 0x10cc1d 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11] []) (.reg (.gpr 1))) #v[4839]
    (.letOp (n := 4846) (.exec 0x10cc1d (fun s => s.RIP = 0x10cc1d) (movR64R64Effect 0x10cc1d 1 11) (Reg.operands [.gpr 11] [])) #v[4839]
    (.letOp (n := 4847) (.out 0x10cc20 (shrR64Effect 0x10cc20 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4845]
    (.letOp (n := 4848) (.exec 0x10cc20 (fun s => s.RIP = 0x10cc20) (shrR64Effect 0x10cc20 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4845]
    (b_l10a410_114)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_113 : List UInt8 :=
  [0x4C, 0x01, 0xF3, 0x4D, 0x11, 0xE0, 0x4C, 0x01, 0xFB, 0x49, 0x11, 0xF0, 0x48, 0x89, 0xD8, 0x48,
    0x21, 0xE8, 0x48, 0xBE, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE6, 0x48,
    0x03, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00, 0x4C, 0x13, 0x5C, 0x24, 0x68, 0x48, 0x03, 0xBC, 0x24,
    0xF8, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x01, 0xC7, 0x49,
    0x11, 0xD3, 0x48, 0x01, 0xCF, 0x4D, 0x11, 0xEB, 0x4C, 0x0F, 0xAC, 0xC3, 0x34, 0x49, 0xC1, 0xE8,
    0x34, 0x4C, 0x89, 0xD9, 0x48, 0xC1, 0xE9, 0x34] ++ bytes_l10a410_114

theorem code_l10a410_113 : ∀ x ∈ codeRange 0x10cbcc bytes_l10a410_113, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcbcc 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_114

def b_l10a410_112 : Block Op Label signature Reg.count 4762 :=
  .letOp (n := 4762) (.exec 0x10cb64 (StorePre 0x10cb64 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10cb64 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10cb64 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[4760, 65]
    (.letOp (n := 4763) (.exec 0x10cb69 (StorePre 0x10cb69 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10cb69 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cb69 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4759, 65]
    (.letOp (n := 4764) (.out 0x10cb71 (movR64M64Effect 0x10cb71 0 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4765) (.exec 0x10cb71 (LoadPre 0x10cb71 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10cb71 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cb71 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4766) (.out 0x10cb79 (mulM64Effect 0x10cb79 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4764, 65]
    (.letOp (n := 4767) (.out 0x10cb79 (mulM64Effect 0x10cb79 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4764, 65]
    (.letOp (n := 4768) (.exec 0x10cb79 (LoadPre 0x10cb79 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10cb79 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10cb79 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4764, 65]
    (.letOp (n := 4769) (.out 0x10cb7e (movR64R64Effect 0x10cb7e 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[4767]
    (.letOp (n := 4770) (.exec 0x10cb7e (fun s => s.RIP = 0x10cb7e) (movR64R64Effect 0x10cb7e 11 2) (Reg.operands [.gpr 2] [])) #v[4767]
    (.letOp (n := 4771) (.out 0x10cb81 (movR64R64Effect 0x10cb81 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[4766]
    (.letOp (n := 4772) (.exec 0x10cb81 (fun s => s.RIP = 0x10cb81) (movR64R64Effect 0x10cb81 7 0) (Reg.operands [.gpr 0] [])) #v[4766]
    (.letOp (n := 4773) (.out 0x10cb84 (movR64M64Effect 0x10cb84 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4774) (.exec 0x10cb84 (LoadPre 0x10cb84 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10cb84 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cb84 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4775) (.out 0x10cb8c (mulM64Effect 0x10cb8c 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4773, 65]
    (.letOp (n := 4776) (.out 0x10cb8c (mulM64Effect 0x10cb8c 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4773, 65]
    (.letOp (n := 4777) (.exec 0x10cb8c (LoadPre 0x10cb8c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10cb8c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10cb8c 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4773, 65]
    (.letOp (n := 4778) (.exec 0x10cb91 (StorePre 0x10cb91 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10cb91 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cb91 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4775, 65]
    (.letOp (n := 4779) (.exec 0x10cb99 (StorePre 0x10cb99 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10cb99 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cb99 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[4776, 65]
    (.letOp (n := 4780) (.out 0x10cba1 (movR64R64Effect 0x10cba1 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[4721]
    (.letOp (n := 4781) (.exec 0x10cba1 (fun s => s.RIP = 0x10cba1) (movR64R64Effect 0x10cba1 5 3) (Reg.operands [.gpr 3] [])) #v[4721]
    (.letOp (n := 4782) (.out 0x10cba4 (andR64R64Effect 0x10cba4 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[4740, 4721]
    (.letOp (n := 4783) (.exec 0x10cba4 (fun s => s.RIP = 0x10cba4) (andR64R64Effect 0x10cba4 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[4740, 4721]
    (.letOp (n := 4784) (.out 0x10cba7 (movR64M64Effect 0x10cba7 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4785) (.exec 0x10cba7 (LoadPre 0x10cba7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10cba7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cba7 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4786) (.out 0x10cbaf (mulM64Effect 0x10cbaf 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4784, 65]
    (.letOp (n := 4787) (.out 0x10cbaf (mulM64Effect 0x10cbaf 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4784, 65]
    (.letOp (n := 4788) (.exec 0x10cbaf (LoadPre 0x10cbaf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10cbaf + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10cbaf 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4784, 65]
    (.letOp (n := 4789) (.out 0x10cbb4 (movR64R64Effect 0x10cbb4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[4787]
    (.letOp (n := 4790) (.exec 0x10cbb4 (fun s => s.RIP = 0x10cbb4) (movR64R64Effect 0x10cbb4 12 2) (Reg.operands [.gpr 2] [])) #v[4787]
    (.letOp (n := 4791) (.out 0x10cbb7 (movR64R64Effect 0x10cbb7 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[4786]
    (.letOp (n := 4792) (.exec 0x10cbb7 (fun s => s.RIP = 0x10cbb7) (movR64R64Effect 0x10cbb7 14 0) (Reg.operands [.gpr 0] [])) #v[4786]
    (.letOp (n := 4793) (.out 0x10cbba (movR64M64Effect 0x10cbba 0 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4794) (.exec 0x10cbba (LoadPre 0x10cbba (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10cbba + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cbba 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4795) (.out 0x10cbc2 (mulM64Effect 0x10cbc2 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4793, 65]
    (.letOp (n := 4796) (.out 0x10cbc2 (mulM64Effect 0x10cbc2 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4793, 65]
    (.letOp (n := 4797) (.exec 0x10cbc2 (LoadPre 0x10cbc2 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10cbc2 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x10cbc2 4 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4793, 65]
    (.letOp (n := 4798) (.out 0x10cbc6 (movR64R64Effect 0x10cbc6 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[4796]
    (.letOp (n := 4799) (.exec 0x10cbc6 (fun s => s.RIP = 0x10cbc6) (movR64R64Effect 0x10cbc6 8 2) (Reg.operands [.gpr 2] [])) #v[4796]
    (.letOp (n := 4800) (.out 0x10cbc9 (movR64R64Effect 0x10cbc9 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[4795]
    (.letOp (n := 4801) (.exec 0x10cbc9 (fun s => s.RIP = 0x10cbc9) (movR64R64Effect 0x10cbc9 3 0) (Reg.operands [.gpr 0] [])) #v[4795]
    (b_l10a410_113))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_112 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x68, 0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84,
    0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x50, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC7,
    0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x38, 0x48, 0x89, 0x84,
    0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDD,
    0x49, 0x21, 0xD9, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x10,
    0x49, 0x89, 0xD4, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0x24, 0x24, 0x49, 0x89, 0xD0, 0x48, 0x89, 0xC3] ++ bytes_l10a410_113

theorem code_l10a410_112 : ∀ x ∈ codeRange 0x10cb64 bytes_l10a410_112, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcb64 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_113

def b_l10a410_111 : Block Op Label signature Reg.count 4717 :=
  .letOp (n := 4717) (.out 0x10cb08 (atFlags StatusFlags.CF (adcR64R64Effect 0x10cb08 15 14)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[4712, 4634, 4715]
    (.letOp (n := 4718) (.exec 0x10cb08 (fun s => s.RIP = 0x10cb08) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cb08 15 14)) (Reg.operands [.gpr 15, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4712, 4634, 4715]
    (.letOp (n := 4719) (.out 0x10cb0b (movR64R64Effect 0x10cb0b 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[4714]
    (.letOp (n := 4720) (.exec 0x10cb0b (fun s => s.RIP = 0x10cb0b) (movR64R64Effect 0x10cb0b 0 8) (Reg.operands [.gpr 8] [])) #v[4714]
    (.letOp (n := 4721) (.out 0x10cb0e (movR64Imm64Effect 0x10cb0e 3 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 4722) (.exec 0x10cb0e (fun s => s.RIP = 0x10cb0e) (movR64Imm64Effect 0x10cb0e 3 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 4723) (.out 0x10cb18 (andR64R64Effect 0x10cb18 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[4719, 4721]
    (.letOp (n := 4724) (.exec 0x10cb18 (fun s => s.RIP = 0x10cb18) (andR64R64Effect 0x10cb18 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[4719, 4721]
    (.letOp (n := 4725) (.out 0x10cb1b (movR64Imm64Effect 0x10cb1b 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 4726) (.exec 0x10cb1b (fun s => s.RIP = 0x10cb1b) (movR64Imm64Effect 0x10cb1b 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 4727) (.out 0x10cb25 (mulR64Effect 0x10cb25 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[4725, 4723]
    (.letOp (n := 4728) (.out 0x10cb25 (mulR64Effect 0x10cb25 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[4725, 4723]
    (.letOp (n := 4729) (.exec 0x10cb25 (fun s => s.RIP = 0x10cb25) (mulR64Effect 0x10cb25 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[4725, 4723]
    (.letOp (n := 4730) (.out 0x10cb28 (addR64M64Effect 0x10cb28 9 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[4668, 65]
    (.letOp (n := 4731) (.out 0x10cb28 (addR64M64Effect 0x10cb28 9 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 4] []) (.flag .CF)) #v[4668, 65]
    (.letOp (n := 4732) (.exec 0x10cb28 (LoadPre 0x10cb28 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10cb28 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10cb28 9 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[4668, 65]
    (.letOp (n := 4733) (.out 0x10cb30 (atFlags StatusFlags.CF (adcR64M64Effect 0x10cb30 1 (.sib 4 none 0 (.d32 0x128)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[4670, 65, 4731]
    (.letOp (n := 4734) (.exec 0x10cb30 (LoadPre 0x10cb30 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10cb30 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10cb30 1 (.sib 4 none 0 (.d32 0x128)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4670, 65, 4731]
    (.letOp (n := 4735) (.out 0x10cb38 (addR64R64Effect 0x10cb38 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[4730, 4727]
    (.letOp (n := 4736) (.out 0x10cb38 (addR64R64Effect 0x10cb38 9 0) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 0] []) (.flag .CF)) #v[4730, 4727]
    (.letOp (n := 4737) (.exec 0x10cb38 (fun s => s.RIP = 0x10cb38) (addR64R64Effect 0x10cb38 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[4730, 4727]
    (.letOp (n := 4738) (.out 0x10cb3b (atFlags StatusFlags.CF (adcR64R64Effect 0x10cb3b 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4733, 4728, 4736]
    (.letOp (n := 4739) (.exec 0x10cb3b (fun s => s.RIP = 0x10cb3b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cb3b 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4733, 4728, 4736]
    (.letOp (n := 4740) (.out 0x10cb3e (addR64R64Effect 0x10cb3e 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[4735, 4652]
    (.letOp (n := 4741) (.out 0x10cb3e (addR64R64Effect 0x10cb3e 9 12) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 12] []) (.flag .CF)) #v[4735, 4652]
    (.letOp (n := 4742) (.exec 0x10cb3e (fun s => s.RIP = 0x10cb3e) (addR64R64Effect 0x10cb3e 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[4735, 4652]
    (.letOp (n := 4743) (.out 0x10cb41 (atFlags StatusFlags.CF (adcR64R64Effect 0x10cb41 1 5)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4738, 4650, 4741]
    (.letOp (n := 4744) (.exec 0x10cb41 (fun s => s.RIP = 0x10cb41) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cb41 1 5)) (Reg.operands [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4738, 4650, 4741]
    (.letOp (n := 4745) (.out 0x10cb44 (movR64R64Effect 0x10cb44 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[4717]
    (.letOp (n := 4746) (.exec 0x10cb44 (fun s => s.RIP = 0x10cb44) (movR64R64Effect 0x10cb44 6 15) (Reg.operands [.gpr 15] [])) #v[4717]
    (.letOp (n := 4747) (.out 0x10cb47 (shldR64R64Effect 0x10cb47 5 15 8 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[4717, 4714]
    (.letOp (n := 4748) (.exec 0x10cb47 (fun s => s.RIP = 0x10cb47) (shldR64R64Effect 0x10cb47 5 15 8 12) (Reg.operands [.gpr 15, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4717, 4714]
    (.letOp (n := 4749) (.out 0x10cb4c (shrR64Effect 0x10cb4c 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[4745]
    (.letOp (n := 4750) (.exec 0x10cb4c (fun s => s.RIP = 0x10cb4c) (shrR64Effect 0x10cb4c 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4745]
    (.letOp (n := 4751) (.out 0x10cb50 (movR64R64Effect 0x10cb50 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[4743]
    (.letOp (n := 4752) (.exec 0x10cb50 (fun s => s.RIP = 0x10cb50) (movR64R64Effect 0x10cb50 13 1) (Reg.operands [.gpr 1] [])) #v[4743]
    (.letOp (n := 4753) (.out 0x10cb53 (shrR64Effect 0x10cb53 4 13 52) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[4751]
    (.letOp (n := 4754) (.exec 0x10cb53 (fun s => s.RIP = 0x10cb53) (shrR64Effect 0x10cb53 4 13 52) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4751]
    (.letOp (n := 4755) (.out 0x10cb57 (shldR64R64Effect 0x10cb57 5 1 9 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4743, 4740]
    (.letOp (n := 4756) (.exec 0x10cb57 (fun s => s.RIP = 0x10cb57) (shldR64R64Effect 0x10cb57 5 1 9 12) (Reg.operands [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4743, 4740]
    (.letOp (n := 4757) (.out 0x10cb5c (movR64M64Effect 0x10cb5c 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4758) (.exec 0x10cb5c (LoadPre 0x10cb5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10cb5c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10cb5c 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4759) (.out 0x10cb61 (mulR64Effect 0x10cb61 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[4697, 4757]
    (.letOp (n := 4760) (.out 0x10cb61 (mulR64Effect 0x10cb61 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[4697, 4757]
    (.letOp (n := 4761) (.exec 0x10cb61 (fun s => s.RIP = 0x10cb61) (mulR64Effect 0x10cb61 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[4697, 4757]
    (b_l10a410_112)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_111 : List UInt8 :=
  [0x4D, 0x11, 0xF7, 0x4C, 0x89, 0xC0, 0x48, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x48, 0x21, 0xD8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x4C, 0x03, 0x8C, 0x24, 0x68, 0x01, 0x00, 0x00, 0x48, 0x13, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00,
    0x49, 0x01, 0xC1, 0x48, 0x11, 0xD1, 0x4D, 0x01, 0xE1, 0x48, 0x11, 0xE9, 0x4C, 0x89, 0xFE, 0x4D,
    0x0F, 0xA4, 0xC7, 0x0C, 0x48, 0xC1, 0xEE, 0x34, 0x49, 0x89, 0xCD, 0x49, 0xC1, 0xED, 0x34, 0x4C,
    0x0F, 0xA4, 0xC9, 0x0C, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0xF7, 0xE7] ++ bytes_l10a410_112

theorem code_l10a410_111 : ∀ x ∈ codeRange 0x10cb08 bytes_l10a410_111, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcb08 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_112

def b_l10a410_110 : Block Op Label signature Reg.count 4672 :=
  .letOp (n := 4672) (.out 0x10caae (movR64Imm64Effect 0x10caae 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 4673) (.exec 0x10caae (fun s => s.RIP = 0x10caae) (movR64Imm64Effect 0x10caae 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 4674) (.out 0x10cab8 (andR64R64Effect 0x10cab8 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[4654, 4672]
    (.letOp (n := 4675) (.exec 0x10cab8 (fun s => s.RIP = 0x10cab8) (andR64R64Effect 0x10cab8 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[4654, 4672]
    (.letOp (n := 4676) (.exec 0x10cabb (StorePre 0x10cabb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10cabb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10cabb 8 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[4674, 65]
    (.letOp (n := 4677) (.out 0x10cac3 (movR64M64Effect 0x10cac3 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4678) (.exec 0x10cac3 (LoadPre 0x10cac3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10cac3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cac3 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4679) (.out 0x10cacb (mulM64Effect 0x10cacb 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4677, 65]
    (.letOp (n := 4680) (.out 0x10cacb (mulM64Effect 0x10cacb 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4677, 65]
    (.letOp (n := 4681) (.exec 0x10cacb (LoadPre 0x10cacb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10cacb + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10cacb 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4677, 65]
    (.letOp (n := 4682) (.out 0x10cad0 (movR64R64Effect 0x10cad0 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[4680]
    (.letOp (n := 4683) (.exec 0x10cad0 (fun s => s.RIP = 0x10cad0) (movR64R64Effect 0x10cad0 6 2) (Reg.operands [.gpr 2] [])) #v[4680]
    (.letOp (n := 4684) (.out 0x10cad3 (movR64R64Effect 0x10cad3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[4679]
    (.letOp (n := 4685) (.exec 0x10cad3 (fun s => s.RIP = 0x10cad3) (movR64R64Effect 0x10cad3 11 0) (Reg.operands [.gpr 0] [])) #v[4679]
    (.letOp (n := 4686) (.out 0x10cad6 (movR64M64Effect 0x10cad6 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4687) (.exec 0x10cad6 (LoadPre 0x10cad6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10cad6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10cad6 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4688) (.out 0x10cade (mulM64Effect 0x10cade 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4686, 65]
    (.letOp (n := 4689) (.out 0x10cade (mulM64Effect 0x10cade 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4686, 65]
    (.letOp (n := 4690) (.exec 0x10cade (LoadPre 0x10cade (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10cade + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x10cade 4 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4686, 65]
    (.letOp (n := 4691) (.out 0x10cae2 (movR64R64Effect 0x10cae2 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[4689]
    (.letOp (n := 4692) (.exec 0x10cae2 (fun s => s.RIP = 0x10cae2) (movR64R64Effect 0x10cae2 15 2) (Reg.operands [.gpr 2] [])) #v[4689]
    (.letOp (n := 4693) (.out 0x10cae5 (movR64R64Effect 0x10cae5 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[4688]
    (.letOp (n := 4694) (.exec 0x10cae5 (fun s => s.RIP = 0x10cae5) (movR64R64Effect 0x10cae5 13 0) (Reg.operands [.gpr 0] [])) #v[4688]
    (.letOp (n := 4695) (.out 0x10cae8 (movR64R64Effect 0x10cae8 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[4591]
    (.letOp (n := 4696) (.exec 0x10cae8 (fun s => s.RIP = 0x10cae8) (movR64R64Effect 0x10cae8 0 7) (Reg.operands [.gpr 7] [])) #v[4591]
    (.letOp (n := 4697) (.out 0x10caeb (movR64M64Effect 0x10caeb 7 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 4698) (.exec 0x10caeb (LoadPre 0x10caeb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10caeb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10caeb 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4699) (.out 0x10caf3 (mulR64Effect 0x10caf3 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[4697, 4695]
    (.letOp (n := 4700) (.out 0x10caf3 (mulR64Effect 0x10caf3 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[4697, 4695]
    (.letOp (n := 4701) (.exec 0x10caf3 (fun s => s.RIP = 0x10caf3) (mulR64Effect 0x10caf3 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[4697, 4695]
    (.letOp (n := 4702) (.out 0x10caf6 (movR64R64Effect 0x10caf6 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[4699]
    (.letOp (n := 4703) (.exec 0x10caf6 (fun s => s.RIP = 0x10caf6) (movR64R64Effect 0x10caf6 8 0) (Reg.operands [.gpr 0] [])) #v[4699]
    (.letOp (n := 4704) (.out 0x10caf9 (addR64R64Effect 0x10caf9 13 11) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 11] []) (.reg (.gpr 13))) #v[4693, 4684]
    (.letOp (n := 4705) (.out 0x10caf9 (addR64R64Effect 0x10caf9 13 11) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 11] []) (.flag .CF)) #v[4693, 4684]
    (.letOp (n := 4706) (.exec 0x10caf9 (fun s => s.RIP = 0x10caf9) (addR64R64Effect 0x10caf9 13 11) (Reg.operands [.gpr 13, .gpr 11] [])) #v[4693, 4684]
    (.letOp (n := 4707) (.out 0x10cafc (atFlags StatusFlags.CF (adcR64R64Effect 0x10cafc 15 6)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[4691, 4682, 4705]
    (.letOp (n := 4708) (.exec 0x10cafc (fun s => s.RIP = 0x10cafc) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cafc 15 6)) (Reg.operands [.gpr 15, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4691, 4682, 4705]
    (.letOp (n := 4709) (.out 0x10caff (addR64R64Effect 0x10caff 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[4702, 4704]
    (.letOp (n := 4710) (.out 0x10caff (addR64R64Effect 0x10caff 8 13) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 13] []) (.flag .CF)) #v[4702, 4704]
    (.letOp (n := 4711) (.exec 0x10caff (fun s => s.RIP = 0x10caff) (addR64R64Effect 0x10caff 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[4702, 4704]
    (.letOp (n := 4712) (.out 0x10cb02 (atFlags StatusFlags.CF (adcR64R64Effect 0x10cb02 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[4707, 4700, 4710]
    (.letOp (n := 4713) (.exec 0x10cb02 (fun s => s.RIP = 0x10cb02) (atFlags StatusFlags.CF (adcR64R64Effect 0x10cb02 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4707, 4700, 4710]
    (.letOp (n := 4714) (.out 0x10cb05 (addR64R64Effect 0x10cb05 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[4709, 4624]
    (.letOp (n := 4715) (.out 0x10cb05 (addR64R64Effect 0x10cb05 8 3) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 3] []) (.flag .CF)) #v[4709, 4624]
    (.letOp (n := 4716) (.exec 0x10cb05 (fun s => s.RIP = 0x10cb05) (addR64R64Effect 0x10cb05 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[4709, 4624]
    (b_l10a410_111)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_110 : List UInt8 :=
  [0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xC0, 0x4C, 0x89, 0x84,
    0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64,
    0x24, 0x10, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC3, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0x24, 0x24, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC5, 0x48, 0x89, 0xF8, 0x48, 0x8B, 0xBC,
    0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xC0, 0x4D, 0x01, 0xDD, 0x49, 0x11,
    0xF7, 0x4D, 0x01, 0xE8, 0x49, 0x11, 0xD7, 0x49, 0x01, 0xD8] ++ bytes_l10a410_111

theorem code_l10a410_110 : ∀ x ∈ codeRange 0x10caae bytes_l10a410_110, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcaae 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_111

def b_l10a410_109 : Block Op Label signature Reg.count 4630 :=
  .letOp (n := 4630) (.out 0x10ca4c (andR64R64Effect 0x10ca4c 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[4626, 4628]
    (.letOp (n := 4631) (.exec 0x10ca4c (fun s => s.RIP = 0x10ca4c) (andR64R64Effect 0x10ca4c 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[4626, 4628]
    (.letOp (n := 4632) (.out 0x10ca4f (orR64R64Effect 0x10ca4f 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[4630, 4600]
    (.letOp (n := 4633) (.exec 0x10ca4f (fun s => s.RIP = 0x10ca4f) (orR64R64Effect 0x10ca4f 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[4630, 4600]
    (.letOp (n := 4634) (.out 0x10ca52 (shrR64Effect 0x10ca52 4 14 52) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[4622]
    (.letOp (n := 4635) (.exec 0x10ca52 (fun s => s.RIP = 0x10ca52) (shrR64Effect 0x10ca52 4 14 52) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4622]
    (.letOp (n := 4636) (.out 0x10ca56 (movR64Imm64Effect 0x10ca56 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 4637) (.exec 0x10ca56 (fun s => s.RIP = 0x10ca56) (movR64Imm64Effect 0x10ca56 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 4638) (.out 0x10ca60 (mulR64Effect 0x10ca60 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[4636, 4632]
    (.letOp (n := 4639) (.out 0x10ca60 (mulR64Effect 0x10ca60 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[4636, 4632]
    (.letOp (n := 4640) (.exec 0x10ca60 (fun s => s.RIP = 0x10ca60) (mulR64Effect 0x10ca60 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[4636, 4632]
    (.letOp (n := 4641) (.out 0x10ca63 (movR64R64Effect 0x10ca63 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[4639]
    (.letOp (n := 4642) (.exec 0x10ca63 (fun s => s.RIP = 0x10ca63) (movR64R64Effect 0x10ca63 12 2) (Reg.operands [.gpr 2] [])) #v[4639]
    (.letOp (n := 4643) (.out 0x10ca66 (addR64M64Effect 0x10ca66 0 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4638, 65]
    (.letOp (n := 4644) (.out 0x10ca66 (addR64M64Effect 0x10ca66 0 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[4638, 65]
    (.letOp (n := 4645) (.exec 0x10ca66 (LoadPre 0x10ca66 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10ca66 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10ca66 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4638, 65]
    (.letOp (n := 4646) (.out 0x10ca6e (atFlags StatusFlags.CF (adcR64M64Effect 0x10ca6e 12 (.sib 4 none 0 (.d32 0x150)))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 12))) #v[4641, 65, 4644]
    (.letOp (n := 4647) (.exec 0x10ca6e (LoadPre 0x10ca6e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10ca6e + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10ca6e 12 (.sib 4 none 0 (.d32 0x150)))) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4641, 65, 4644]
    (.letOp (n := 4648) (.out 0x10ca76 (movR64R64Effect 0x10ca76 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 12] []) (.reg (.gpr 5))) #v[4646]
    (.letOp (n := 4649) (.exec 0x10ca76 (fun s => s.RIP = 0x10ca76) (movR64R64Effect 0x10ca76 5 12) (Reg.operands [.gpr 12] [])) #v[4646]
    (.letOp (n := 4650) (.out 0x10ca79 (shrR64Effect 0x10ca79 4 5 52) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[4648]
    (.letOp (n := 4651) (.exec 0x10ca79 (fun s => s.RIP = 0x10ca79) (shrR64Effect 0x10ca79 4 5 52) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4648]
    (.letOp (n := 4652) (.out 0x10ca7d (shldR64R64Effect 0x10ca7d 5 12 0 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[4646, 4643]
    (.letOp (n := 4653) (.exec 0x10ca7d (fun s => s.RIP = 0x10ca7d) (shldR64R64Effect 0x10ca7d 5 12 0 12) (Reg.operands [.gpr 12, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4646, 4643]
    (.letOp (n := 4654) (.out 0x10ca82 (movR64R64Effect 0x10ca82 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[4643]
    (.letOp (n := 4655) (.exec 0x10ca82 (fun s => s.RIP = 0x10ca82) (movR64R64Effect 0x10ca82 8 0) (Reg.operands [.gpr 0] [])) #v[4643]
    (.letOp (n := 4656) (.out 0x10ca85 (movR64R64Effect 0x10ca85 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[4551]
    (.letOp (n := 4657) (.exec 0x10ca85 (fun s => s.RIP = 0x10ca85) (movR64R64Effect 0x10ca85 0 9) (Reg.operands [.gpr 9] [])) #v[4551]
    (.letOp (n := 4658) (.out 0x10ca88 (mulR64Effect 0x10ca88 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[4595, 4656]
    (.letOp (n := 4659) (.out 0x10ca88 (mulR64Effect 0x10ca88 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[4595, 4656]
    (.letOp (n := 4660) (.exec 0x10ca88 (fun s => s.RIP = 0x10ca88) (mulR64Effect 0x10ca88 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[4595, 4656]
    (.letOp (n := 4661) (.exec 0x10ca8b (StorePre 0x10ca8b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10ca8b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ca8b 2 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[4659, 65]
    (.letOp (n := 4662) (.exec 0x10ca93 (StorePre 0x10ca93 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10ca93 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ca93 0 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4658, 65]
    (.letOp (n := 4663) (.out 0x10ca9b (movR64M64Effect 0x10ca9b 0 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4664) (.exec 0x10ca9b (LoadPre 0x10ca9b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10ca9b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ca9b 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4665) (.out 0x10caa3 (mulM64Effect 0x10caa3 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4663, 65]
    (.letOp (n := 4666) (.out 0x10caa3 (mulM64Effect 0x10caa3 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4663, 65]
    (.letOp (n := 4667) (.exec 0x10caa3 (LoadPre 0x10caa3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10caa3 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10caa3 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4663, 65]
    (.letOp (n := 4668) (.out 0x10caa8 (movR64R64Effect 0x10caa8 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[4665]
    (.letOp (n := 4669) (.exec 0x10caa8 (fun s => s.RIP = 0x10caa8) (movR64R64Effect 0x10caa8 9 0) (Reg.operands [.gpr 0] [])) #v[4665]
    (.letOp (n := 4670) (.out 0x10caab (movR64R64Effect 0x10caab 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[4666]
    (.letOp (n := 4671) (.exec 0x10caab (fun s => s.RIP = 0x10caab) (movR64R64Effect 0x10caab 1 2) (Reg.operands [.gpr 2] [])) #v[4666]
    (b_l10a410_110))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_109 : List UInt8 :=
  [0x48, 0x21, 0xC8, 0x4C, 0x09, 0xE8, 0x49, 0xC1, 0xEE, 0x34, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD4, 0x48, 0x03, 0x84, 0x24, 0x28, 0x01,
    0x00, 0x00, 0x4C, 0x13, 0xA4, 0x24, 0x50, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE5, 0x48, 0xC1, 0xED,
    0x34, 0x49, 0x0F, 0xA4, 0xC4, 0x0C, 0x49, 0x89, 0xC0, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0xE6, 0x48,
    0x89, 0x94, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00, 0x48,
    0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x38, 0x49, 0x89, 0xC1, 0x48,
    0x89, 0xD1] ++ bytes_l10a410_110

theorem code_l10a410_109 : ∀ x ∈ codeRange 0x10ca4c bytes_l10a410_109, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xca4c 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_110

def b_l10a410_108 : Block Op Label signature Reg.count 4584 :=
  .letOp (n := 4584) (.out 0x10c9f9 (mulM64Effect 0x10c9f9 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4582, 65]
    (.letOp (n := 4585) (.out 0x10c9f9 (mulM64Effect 0x10c9f9 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4582, 65]
    (.letOp (n := 4586) (.exec 0x10c9f9 (LoadPre 0x10c9f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10c9f9 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10c9f9 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4582, 65]
    (.letOp (n := 4587) (.out 0x10ca01 (movR64R64Effect 0x10ca01 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[4585]
    (.letOp (n := 4588) (.exec 0x10ca01 (fun s => s.RIP = 0x10ca01) (movR64R64Effect 0x10ca01 14 2) (Reg.operands [.gpr 2] [])) #v[4585]
    (.letOp (n := 4589) (.out 0x10ca04 (movR64R64Effect 0x10ca04 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[4584]
    (.letOp (n := 4590) (.exec 0x10ca04 (fun s => s.RIP = 0x10ca04) (movR64R64Effect 0x10ca04 12 0) (Reg.operands [.gpr 0] [])) #v[4584]
    (.letOp (n := 4591) (.out 0x10ca07 (movR64M64Effect 0x10ca07 7 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 4592) (.exec 0x10ca07 (LoadPre 0x10ca07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10ca07 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ca07 7 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4593) (.out 0x10ca0f (movR64R64Effect 0x10ca0f 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[4591]
    (.letOp (n := 4594) (.exec 0x10ca0f (fun s => s.RIP = 0x10ca0f) (movR64R64Effect 0x10ca0f 0 7) (Reg.operands [.gpr 7] [])) #v[4591]
    (.letOp (n := 4595) (.out 0x10ca12 (movR64M64Effect 0x10ca12 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 4596) (.exec 0x10ca12 (LoadPre 0x10ca12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10ca12 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ca12 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4597) (.out 0x10ca17 (mulR64Effect 0x10ca17 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[4595, 4593]
    (.letOp (n := 4598) (.out 0x10ca17 (mulR64Effect 0x10ca17 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[4595, 4593]
    (.letOp (n := 4599) (.exec 0x10ca17 (fun s => s.RIP = 0x10ca17) (mulR64Effect 0x10ca17 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[4595, 4593]
    (.letOp (n := 4600) (.out 0x10ca1a (andR32Imm8Effect 0x10ca1a 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[4571]
    (.letOp (n := 4601) (.exec 0x10ca1a (fun s => s.RIP = 0x10ca1a) (andR32Imm8Effect 0x10ca1a 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[4571]
    (.letOp (n := 4602) (.out 0x10ca1e (addR64R64Effect 0x10ca1e 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[4580, 4565]
    (.letOp (n := 4603) (.out 0x10ca1e (addR64R64Effect 0x10ca1e 11 15) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 15] []) (.flag .CF)) #v[4580, 4565]
    (.letOp (n := 4604) (.exec 0x10ca1e (fun s => s.RIP = 0x10ca1e) (addR64R64Effect 0x10ca1e 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[4580, 4565]
    (.letOp (n := 4605) (.out 0x10ca21 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ca21 3 8)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[4578, 4567, 4603]
    (.letOp (n := 4606) (.exec 0x10ca21 (fun s => s.RIP = 0x10ca21) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ca21 3 8)) (Reg.operands [.gpr 3, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4578, 4567, 4603]
    (.letOp (n := 4607) (.out 0x10ca24 (addR64R64Effect 0x10ca24 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 12] []) (.reg (.gpr 11))) #v[4602, 4589]
    (.letOp (n := 4608) (.out 0x10ca24 (addR64R64Effect 0x10ca24 11 12) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 12] []) (.flag .CF)) #v[4602, 4589]
    (.letOp (n := 4609) (.exec 0x10ca24 (fun s => s.RIP = 0x10ca24) (addR64R64Effect 0x10ca24 11 12) (Reg.operands [.gpr 11, .gpr 12] [])) #v[4602, 4589]
    (.letOp (n := 4610) (.out 0x10ca27 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ca27 3 14)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[4605, 4587, 4608]
    (.letOp (n := 4611) (.exec 0x10ca27 (fun s => s.RIP = 0x10ca27) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ca27 3 14)) (Reg.operands [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4605, 4587, 4608]
    (.letOp (n := 4612) (.out 0x10ca2a (addR64R64Effect 0x10ca2a 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[4597, 4607]
    (.letOp (n := 4613) (.out 0x10ca2a (addR64R64Effect 0x10ca2a 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[4597, 4607]
    (.letOp (n := 4614) (.exec 0x10ca2a (fun s => s.RIP = 0x10ca2a) (addR64R64Effect 0x10ca2a 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[4597, 4607]
    (.letOp (n := 4615) (.out 0x10ca2d (atFlags StatusFlags.CF (adcR64R64Effect 0x10ca2d 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[4610, 4598, 4613]
    (.letOp (n := 4616) (.exec 0x10ca2d (fun s => s.RIP = 0x10ca2d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ca2d 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4610, 4598, 4613]
    (.letOp (n := 4617) (.out 0x10ca30 (addR64R64Effect 0x10ca30 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[4612, 4549]
    (.letOp (n := 4618) (.out 0x10ca30 (addR64R64Effect 0x10ca30 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[4612, 4549]
    (.letOp (n := 4619) (.exec 0x10ca30 (fun s => s.RIP = 0x10ca30) (addR64R64Effect 0x10ca30 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[4612, 4549]
    (.letOp (n := 4620) (.out 0x10ca33 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ca33 3 5)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[4615, 4547, 4618]
    (.letOp (n := 4621) (.exec 0x10ca33 (fun s => s.RIP = 0x10ca33) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ca33 3 5)) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4615, 4547, 4618]
    (.letOp (n := 4622) (.out 0x10ca36 (movR64R64Effect 0x10ca36 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 3] []) (.reg (.gpr 14))) #v[4620]
    (.letOp (n := 4623) (.exec 0x10ca36 (fun s => s.RIP = 0x10ca36) (movR64R64Effect 0x10ca36 14 3) (Reg.operands [.gpr 3] [])) #v[4620]
    (.letOp (n := 4624) (.out 0x10ca39 (shldR64R64Effect 0x10ca39 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[4620, 4617]
    (.letOp (n := 4625) (.exec 0x10ca39 (fun s => s.RIP = 0x10ca39) (shldR64R64Effect 0x10ca39 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4620, 4617]
    (.letOp (n := 4626) (.out 0x10ca3e (shlR64Effect 0x10ca3e 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4617]
    (.letOp (n := 4627) (.exec 0x10ca3e (fun s => s.RIP = 0x10ca3e) (shlR64Effect 0x10ca3e 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4617]
    (.letOp (n := 4628) (.out 0x10ca42 (movR64Imm64Effect 0x10ca42 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 4629) (.exec 0x10ca42 (fun s => s.RIP = 0x10ca42) (movR64Imm64Effect 0x10ca42 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (b_l10a410_109))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_108 : List UInt8 :=
  [0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x48, 0x8B,
    0xBC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x48, 0x8B, 0x74, 0x24, 0x50, 0x48, 0xF7,
    0xE6, 0x41, 0x83, 0xE5, 0x0F, 0x4D, 0x01, 0xFB, 0x4C, 0x11, 0xC3, 0x4D, 0x01, 0xE3, 0x4C, 0x11,
    0xF3, 0x4C, 0x01, 0xD8, 0x48, 0x11, 0xD3, 0x48, 0x01, 0xC8, 0x48, 0x11, 0xEB, 0x49, 0x89, 0xDE,
    0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x00] ++ bytes_l10a410_109

theorem code_l10a410_108 : ∀ x ∈ codeRange 0x10c9f9 bytes_l10a410_108, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc9f9 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_109

def b_l10a410_107 : Block Op Label signature Reg.count 4543 :=
  .letOp (n := 4543) (.out 0x10c9a0 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c9a0 1 6)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4538, 4513, 4541]
    (.letOp (n := 4544) (.exec 0x10c9a0 (fun s => s.RIP = 0x10c9a0) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c9a0 1 6)) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4538, 4513, 4541]
    (.letOp (n := 4545) (.out 0x10c9a3 (movR64R64Effect 0x10c9a3 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[4543]
    (.letOp (n := 4546) (.exec 0x10c9a3 (fun s => s.RIP = 0x10c9a3) (movR64R64Effect 0x10c9a3 5 1) (Reg.operands [.gpr 1] [])) #v[4543]
    (.letOp (n := 4547) (.out 0x10c9a6 (shrR64Effect 0x10c9a6 4 5 52) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[4545]
    (.letOp (n := 4548) (.exec 0x10c9a6 (fun s => s.RIP = 0x10c9a6) (shrR64Effect 0x10c9a6 4 5 52) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4545]
    (.letOp (n := 4549) (.out 0x10c9aa (shldR64R64Effect 0x10c9aa 5 1 10 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4543, 4540]
    (.letOp (n := 4550) (.exec 0x10c9aa (fun s => s.RIP = 0x10c9aa) (shldR64R64Effect 0x10c9aa 5 1 10 12) (Reg.operands [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4543, 4540]
    (.letOp (n := 4551) (.out 0x10c9af (movR64M64Effect 0x10c9af 9 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 4552) (.exec 0x10c9af (LoadPre 0x10c9af (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10c9af + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c9af 9 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4553) (.out 0x10c9b4 (movR64R64Effect 0x10c9b4 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[4551]
    (.letOp (n := 4554) (.exec 0x10c9b4 (fun s => s.RIP = 0x10c9b4) (movR64R64Effect 0x10c9b4 0 9) (Reg.operands [.gpr 9] [])) #v[4551]
    (.letOp (n := 4555) (.out 0x10c9b7 (mulR64Effect 0x10c9b7 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[4500, 4553]
    (.letOp (n := 4556) (.out 0x10c9b7 (mulR64Effect 0x10c9b7 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[4500, 4553]
    (.letOp (n := 4557) (.exec 0x10c9b7 (fun s => s.RIP = 0x10c9b7) (mulR64Effect 0x10c9b7 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[4500, 4553]
    (.letOp (n := 4558) (.exec 0x10c9ba (StorePre 0x10c9ba 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10c9ba + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c9ba 2 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[4556, 65]
    (.letOp (n := 4559) (.exec 0x10c9c2 (StorePre 0x10c9c2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10c9c2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c9c2 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4555, 65]
    (.letOp (n := 4560) (.out 0x10c9ca (movR64M64Effect 0x10c9ca 0 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4561) (.exec 0x10c9ca (LoadPre 0x10c9ca (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10c9ca + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c9ca 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4562) (.out 0x10c9d2 (mulM64Effect 0x10c9d2 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4560, 65]
    (.letOp (n := 4563) (.out 0x10c9d2 (mulM64Effect 0x10c9d2 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4560, 65]
    (.letOp (n := 4564) (.exec 0x10c9d2 (LoadPre 0x10c9d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10c9d2 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10c9d2 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4560, 65]
    (.letOp (n := 4565) (.out 0x10c9d7 (movR64R64Effect 0x10c9d7 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[4562]
    (.letOp (n := 4566) (.exec 0x10c9d7 (fun s => s.RIP = 0x10c9d7) (movR64R64Effect 0x10c9d7 15 0) (Reg.operands [.gpr 0] [])) #v[4562]
    (.letOp (n := 4567) (.out 0x10c9da (movR64R64Effect 0x10c9da 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[4563]
    (.letOp (n := 4568) (.exec 0x10c9da (fun s => s.RIP = 0x10c9da) (movR64R64Effect 0x10c9da 8 2) (Reg.operands [.gpr 2] [])) #v[4563]
    (.letOp (n := 4569) (.out 0x10c9dd (movR64R64Effect 0x10c9dd 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 10] []) (.reg (.gpr 13))) #v[4540]
    (.letOp (n := 4570) (.exec 0x10c9dd (fun s => s.RIP = 0x10c9dd) (movR64R64Effect 0x10c9dd 13 10) (Reg.operands [.gpr 10] [])) #v[4540]
    (.letOp (n := 4571) (.out 0x10c9e0 (shrR64Effect 0x10c9e0 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[4569]
    (.letOp (n := 4572) (.exec 0x10c9e0 (fun s => s.RIP = 0x10c9e0) (shrR64Effect 0x10c9e0 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4569]
    (.letOp (n := 4573) (.out 0x10c9e4 (movR64R64Effect 0x10c9e4 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[4476]
    (.letOp (n := 4574) (.exec 0x10c9e4 (fun s => s.RIP = 0x10c9e4) (movR64R64Effect 0x10c9e4 0 7) (Reg.operands [.gpr 7] [])) #v[4476]
    (.letOp (n := 4575) (.out 0x10c9e7 (mulM64Effect 0x10c9e7 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4573, 65]
    (.letOp (n := 4576) (.out 0x10c9e7 (mulM64Effect 0x10c9e7 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4573, 65]
    (.letOp (n := 4577) (.exec 0x10c9e7 (LoadPre 0x10c9e7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10c9e7 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x10c9e7 4 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4573, 65]
    (.letOp (n := 4578) (.out 0x10c9eb (movR64R64Effect 0x10c9eb 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[4576]
    (.letOp (n := 4579) (.exec 0x10c9eb (fun s => s.RIP = 0x10c9eb) (movR64R64Effect 0x10c9eb 3 2) (Reg.operands [.gpr 2] [])) #v[4576]
    (.letOp (n := 4580) (.out 0x10c9ee (movR64R64Effect 0x10c9ee 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[4575]
    (.letOp (n := 4581) (.exec 0x10c9ee (fun s => s.RIP = 0x10c9ee) (movR64R64Effect 0x10c9ee 11 0) (Reg.operands [.gpr 0] [])) #v[4575]
    (.letOp (n := 4582) (.out 0x10c9f1 (movR64M64Effect 0x10c9f1 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4583) (.exec 0x10c9f1 (LoadPre 0x10c9f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10c9f1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c9f1 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l10a410_108)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_107 : List UInt8 :=
  [0x48, 0x11, 0xF1, 0x48, 0x89, 0xCD, 0x48, 0xC1, 0xED, 0x34, 0x4C, 0x0F, 0xA4, 0xD1, 0x0C, 0x4C,
    0x8B, 0x4C, 0x24, 0x68, 0x4C, 0x89, 0xC8, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0x94, 0x24, 0x50, 0x01,
    0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xF8, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x10, 0x49, 0x89, 0xC7, 0x49, 0x89, 0xD0, 0x4D, 0x89, 0xD5,
    0x49, 0xC1, 0xED, 0x30, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0x24, 0x24, 0x48, 0x89, 0xD3, 0x49, 0x89,
    0xC3, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] ++ bytes_l10a410_108

theorem code_l10a410_107 : ∀ x ∈ codeRange 0x10c9a0 bytes_l10a410_107, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc9a0 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_108

def b_l10a410_106 : Block Op Label signature Reg.count 4495 :=
  .letOp (n := 4495) (.out 0x10c94d (movR64R64Effect 0x10c94d 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[4428]
    (.letOp (n := 4496) (.exec 0x10c94d (fun s => s.RIP = 0x10c94d) (movR64R64Effect 0x10c94d 0 5) (Reg.operands [.gpr 5] [])) #v[4428]
    (.letOp (n := 4497) (.out 0x10c950 (mulR64Effect 0x10c950 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[4414, 4495]
    (.letOp (n := 4498) (.out 0x10c950 (mulR64Effect 0x10c950 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[4414, 4495]
    (.letOp (n := 4499) (.exec 0x10c950 (fun s => s.RIP = 0x10c950) (mulR64Effect 0x10c950 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[4414, 4495]
    (.letOp (n := 4500) (.out 0x10c953 (movR64R64Effect 0x10c953 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 13] []) (.reg (.gpr 14))) #v[4414]
    (.letOp (n := 4501) (.exec 0x10c953 (fun s => s.RIP = 0x10c953) (movR64R64Effect 0x10c953 14 13) (Reg.operands [.gpr 13] [])) #v[4414]
    (.letOp (n := 4502) (.out 0x10c956 (movR64R64Effect 0x10c956 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[4498]
    (.letOp (n := 4503) (.exec 0x10c956 (fun s => s.RIP = 0x10c956) (movR64R64Effect 0x10c956 13 2) (Reg.operands [.gpr 2] [])) #v[4498]
    (.letOp (n := 4504) (.out 0x10c959 (movR64R64Effect 0x10c959 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[4497]
    (.letOp (n := 4505) (.exec 0x10c959 (fun s => s.RIP = 0x10c959) (movR64R64Effect 0x10c959 8 0) (Reg.operands [.gpr 0] [])) #v[4497]
    (.letOp (n := 4506) (.out 0x10c95c (movR64R64Effect 0x10c95c 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[4439]
    (.letOp (n := 4507) (.exec 0x10c95c (fun s => s.RIP = 0x10c95c) (movR64R64Effect 0x10c95c 0 11) (Reg.operands [.gpr 11] [])) #v[4439]
    (.letOp (n := 4508) (.out 0x10c95f (movR64Imm64Effect 0x10c95f 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 4509) (.exec 0x10c95f (fun s => s.RIP = 0x10c95f) (movR64Imm64Effect 0x10c95f 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 4510) (.out 0x10c969 (mulR64Effect 0x10c969 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[4508, 4506]
    (.letOp (n := 4511) (.out 0x10c969 (mulR64Effect 0x10c969 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[4508, 4506]
    (.letOp (n := 4512) (.exec 0x10c969 (fun s => s.RIP = 0x10c969) (mulR64Effect 0x10c969 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[4508, 4506]
    (.letOp (n := 4513) (.out 0x10c96c (shrR64Effect 0x10c96c 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[4456]
    (.letOp (n := 4514) (.exec 0x10c96c (fun s => s.RIP = 0x10c96c) (shrR64Effect 0x10c96c 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4456]
    (.letOp (n := 4515) (.out 0x10c970 (addR64M64Effect 0x10c970 10 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[4474, 65]
    (.letOp (n := 4516) (.out 0x10c970 (addR64M64Effect 0x10c970 10 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[4474, 65]
    (.letOp (n := 4517) (.exec 0x10c970 (LoadPre 0x10c970 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10c970 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10c970 10 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[4474, 65]
    (.letOp (n := 4518) (.out 0x10c978 (atFlags StatusFlags.CF (adcR64M64Effect 0x10c978 1 (.sib 4 none 0 (.d32 0x150)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[4472, 65, 4516]
    (.letOp (n := 4519) (.exec 0x10c978 (LoadPre 0x10c978 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10c978 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10c978 1 (.sib 4 none 0 (.d32 0x150)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4472, 65, 4516]
    (.letOp (n := 4520) (.out 0x10c980 (addR64R64Effect 0x10c980 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[4515, 4484]
    (.letOp (n := 4521) (.out 0x10c980 (addR64R64Effect 0x10c980 10 3) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 3] []) (.flag .CF)) #v[4515, 4484]
    (.letOp (n := 4522) (.exec 0x10c980 (fun s => s.RIP = 0x10c980) (addR64R64Effect 0x10c980 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[4515, 4484]
    (.letOp (n := 4523) (.out 0x10c983 (atFlags StatusFlags.CF (adcR64M64Effect 0x10c983 1 (.sib 4 none 0 (.d32 0x168)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[4518, 65, 4521]
    (.letOp (n := 4524) (.exec 0x10c983 (LoadPre 0x10c983 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10c983 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10c983 1 (.sib 4 none 0 (.d32 0x168)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4518, 65, 4521]
    (.letOp (n := 4525) (.out 0x10c98b (addR64R64Effect 0x10c98b 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[4520, 4493]
    (.letOp (n := 4526) (.out 0x10c98b (addR64R64Effect 0x10c98b 10 12) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 12] []) (.flag .CF)) #v[4520, 4493]
    (.letOp (n := 4527) (.exec 0x10c98b (fun s => s.RIP = 0x10c98b) (addR64R64Effect 0x10c98b 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[4520, 4493]
    (.letOp (n := 4528) (.out 0x10c98e (atFlags StatusFlags.CF (adcR64R64Effect 0x10c98e 1 15)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4523, 4491, 4526]
    (.letOp (n := 4529) (.exec 0x10c98e (fun s => s.RIP = 0x10c98e) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c98e 1 15)) (Reg.operands [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4523, 4491, 4526]
    (.letOp (n := 4530) (.out 0x10c991 (addR64R64Effect 0x10c991 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[4525, 4504]
    (.letOp (n := 4531) (.out 0x10c991 (addR64R64Effect 0x10c991 10 8) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 8] []) (.flag .CF)) #v[4525, 4504]
    (.letOp (n := 4532) (.exec 0x10c991 (fun s => s.RIP = 0x10c991) (addR64R64Effect 0x10c991 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[4525, 4504]
    (.letOp (n := 4533) (.out 0x10c994 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c994 1 13)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4528, 4502, 4531]
    (.letOp (n := 4534) (.exec 0x10c994 (fun s => s.RIP = 0x10c994) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c994 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4528, 4502, 4531]
    (.letOp (n := 4535) (.out 0x10c997 (addR64R64Effect 0x10c997 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[4530, 4510]
    (.letOp (n := 4536) (.out 0x10c997 (addR64R64Effect 0x10c997 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[4530, 4510]
    (.letOp (n := 4537) (.exec 0x10c997 (fun s => s.RIP = 0x10c997) (addR64R64Effect 0x10c997 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[4530, 4510]
    (.letOp (n := 4538) (.out 0x10c99a (atFlags StatusFlags.CF (adcR64R64Effect 0x10c99a 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4533, 4511, 4536]
    (.letOp (n := 4539) (.exec 0x10c99a (fun s => s.RIP = 0x10c99a) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c99a 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4533, 4511, 4536]
    (.letOp (n := 4540) (.out 0x10c99d (addR64R64Effect 0x10c99d 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[4535, 4458]
    (.letOp (n := 4541) (.out 0x10c99d (addR64R64Effect 0x10c99d 10 9) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 9] []) (.flag .CF)) #v[4535, 4458]
    (.letOp (n := 4542) (.exec 0x10c99d (fun s => s.RIP = 0x10c99d) (addR64R64Effect 0x10c99d 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[4535, 4458]
    (b_l10a410_107))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_106 : List UInt8 :=
  [0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE5, 0x4D, 0x89, 0xEE, 0x49, 0x89, 0xD5, 0x49, 0x89, 0xC0, 0x4C,
    0x89, 0xD8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48,
    0xC1, 0xEE, 0x34, 0x4C, 0x03, 0x94, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x13, 0x8C, 0x24, 0x50,
    0x01, 0x00, 0x00, 0x49, 0x01, 0xDA, 0x48, 0x13, 0x8C, 0x24, 0x68, 0x01, 0x00, 0x00, 0x4D, 0x01,
    0xE2, 0x4C, 0x11, 0xF9, 0x4D, 0x01, 0xC2, 0x4C, 0x11, 0xE9, 0x49, 0x01, 0xC2, 0x48, 0x11, 0xD1,
    0x4D, 0x01, 0xCA] ++ bytes_l10a410_107

theorem code_l10a410_106 : ∀ x ∈ codeRange 0x10c94d bytes_l10a410_106, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc94d 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_107

def b_l10a410_105 : Block Op Label signature Reg.count 4454 :=
  .letOp (n := 4454) (.out 0x10c8f6 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c8f6 9 7)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[4448, 4426, 4451]
    (.letOp (n := 4455) (.exec 0x10c8f6 (fun s => s.RIP = 0x10c8f6) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c8f6 9 7)) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4448, 4426, 4451]
    (.letOp (n := 4456) (.out 0x10c8f9 (movR64R64Effect 0x10c8f9 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[4454]
    (.letOp (n := 4457) (.exec 0x10c8f9 (fun s => s.RIP = 0x10c8f9) (movR64R64Effect 0x10c8f9 6 9) (Reg.operands [.gpr 9] [])) #v[4454]
    (.letOp (n := 4458) (.out 0x10c8fc (shldR64R64Effect 0x10c8fc 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4454, 4450]
    (.letOp (n := 4459) (.exec 0x10c8fc (fun s => s.RIP = 0x10c8fc) (shldR64R64Effect 0x10c8fc 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4454, 4450]
    (.letOp (n := 4460) (.out 0x10c901 (movR64R64Effect 0x10c901 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[4365]
    (.letOp (n := 4461) (.exec 0x10c901 (fun s => s.RIP = 0x10c901) (movR64R64Effect 0x10c901 0 3) (Reg.operands [.gpr 3] [])) #v[4365]
    (.letOp (n := 4462) (.out 0x10c904 (mulR64Effect 0x10c904 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[4432, 4460]
    (.letOp (n := 4463) (.out 0x10c904 (mulR64Effect 0x10c904 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[4432, 4460]
    (.letOp (n := 4464) (.exec 0x10c904 (fun s => s.RIP = 0x10c904) (mulR64Effect 0x10c904 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[4432, 4460]
    (.letOp (n := 4465) (.exec 0x10c907 (StorePre 0x10c907 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10c907 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c907 2 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[4463, 65]
    (.letOp (n := 4466) (.exec 0x10c90f (StorePre 0x10c90f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10c90f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c90f 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4462, 65]
    (.letOp (n := 4467) (.out 0x10c917 (movR64R64Effect 0x10c917 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[4378]
    (.letOp (n := 4468) (.exec 0x10c917 (fun s => s.RIP = 0x10c917) (movR64R64Effect 0x10c917 0 12) (Reg.operands [.gpr 12] [])) #v[4378]
    (.letOp (n := 4469) (.out 0x10c91a (mulR64Effect 0x10c91a 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[4369, 4467]
    (.letOp (n := 4470) (.out 0x10c91a (mulR64Effect 0x10c91a 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[4369, 4467]
    (.letOp (n := 4471) (.exec 0x10c91a (fun s => s.RIP = 0x10c91a) (mulR64Effect 0x10c91a 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[4369, 4467]
    (.letOp (n := 4472) (.out 0x10c91d (movR64R64Effect 0x10c91d 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[4470]
    (.letOp (n := 4473) (.exec 0x10c91d (fun s => s.RIP = 0x10c91d) (movR64R64Effect 0x10c91d 1 2) (Reg.operands [.gpr 2] [])) #v[4470]
    (.letOp (n := 4474) (.out 0x10c920 (movR64R64Effect 0x10c920 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[4469]
    (.letOp (n := 4475) (.exec 0x10c920 (fun s => s.RIP = 0x10c920) (movR64R64Effect 0x10c920 10 0) (Reg.operands [.gpr 0] [])) #v[4469]
    (.letOp (n := 4476) (.out 0x10c923 (movR64M64Effect 0x10c923 7 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 4477) (.exec 0x10c923 (LoadPre 0x10c923 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10c923 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c923 7 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4478) (.out 0x10c92b (movR64R64Effect 0x10c92b 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[4476]
    (.letOp (n := 4479) (.exec 0x10c92b (fun s => s.RIP = 0x10c92b) (movR64R64Effect 0x10c92b 0 7) (Reg.operands [.gpr 7] [])) #v[4476]
    (.letOp (n := 4480) (.out 0x10c92e (mulM64Effect 0x10c92e 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4478, 65]
    (.letOp (n := 4481) (.out 0x10c92e (mulM64Effect 0x10c92e 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4478, 65]
    (.letOp (n := 4482) (.exec 0x10c92e (LoadPre 0x10c92e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10c92e + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10c92e 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4478, 65]
    (.letOp (n := 4483) (.exec 0x10c936 (StorePre 0x10c936 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10c936 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c936 2 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[4481, 65]
    (.letOp (n := 4484) (.out 0x10c93e (movR64R64Effect 0x10c93e 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[4480]
    (.letOp (n := 4485) (.exec 0x10c93e (fun s => s.RIP = 0x10c93e) (movR64R64Effect 0x10c93e 3 0) (Reg.operands [.gpr 0] [])) #v[4480]
    (.letOp (n := 4486) (.out 0x10c941 (movR64R64Effect 0x10c941 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[4410]
    (.letOp (n := 4487) (.exec 0x10c941 (fun s => s.RIP = 0x10c941) (movR64R64Effect 0x10c941 0 15) (Reg.operands [.gpr 15] [])) #v[4410]
    (.letOp (n := 4488) (.out 0x10c944 (mulR64Effect 0x10c944 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[4396, 4486]
    (.letOp (n := 4489) (.out 0x10c944 (mulR64Effect 0x10c944 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[4396, 4486]
    (.letOp (n := 4490) (.exec 0x10c944 (fun s => s.RIP = 0x10c944) (mulR64Effect 0x10c944 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[4396, 4486]
    (.letOp (n := 4491) (.out 0x10c947 (movR64R64Effect 0x10c947 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[4489]
    (.letOp (n := 4492) (.exec 0x10c947 (fun s => s.RIP = 0x10c947) (movR64R64Effect 0x10c947 15 2) (Reg.operands [.gpr 2] [])) #v[4489]
    (.letOp (n := 4493) (.out 0x10c94a (movR64R64Effect 0x10c94a 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[4488]
    (.letOp (n := 4494) (.exec 0x10c94a (fun s => s.RIP = 0x10c94a) (movR64R64Effect 0x10c94a 12 0) (Reg.operands [.gpr 0] [])) #v[4488]
    (b_l10a410_106)))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_105 : List UInt8 :=
  [0x49, 0x11, 0xF9, 0x4C, 0x89, 0xCE, 0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xD8, 0x48, 0xF7,
    0xE1, 0x48, 0x89, 0x94, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00,
    0x00, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC2, 0x48, 0x8B, 0xBC,
    0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x94, 0x24, 0x68, 0x01, 0x00, 0x00, 0x48, 0x89, 0xC3, 0x4C, 0x89, 0xF8, 0x49, 0xF7,
    0xE6, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC4] ++ bytes_l10a410_106

theorem code_l10a410_105 : ∀ x ∈ codeRange 0x10c8f6 bytes_l10a410_105, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc8f6 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_106

def b_l10a410_104 : Block Op Label signature Reg.count 4410 :=
  .letOp (n := 4410) (.out 0x10c89e (movR64M64Effect 0x10c89e 15 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 4411) (.exec 0x10c89e (LoadPre 0x10c89e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10c89e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c89e 15 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4412) (.out 0x10c8a6 (movR64R64Effect 0x10c8a6 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[4410]
    (.letOp (n := 4413) (.exec 0x10c8a6 (fun s => s.RIP = 0x10c8a6) (movR64R64Effect 0x10c8a6 0 15) (Reg.operands [.gpr 15] [])) #v[4410]
    (.letOp (n := 4414) (.out 0x10c8a9 (movR64M64Effect 0x10c8a9 13 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 4415) (.exec 0x10c8a9 (LoadPre 0x10c8a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10c8a9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c8a9 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4416) (.out 0x10c8ae (mulR64Effect 0x10c8ae 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[4414, 4412]
    (.letOp (n := 4417) (.out 0x10c8ae (mulR64Effect 0x10c8ae 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[4414, 4412]
    (.letOp (n := 4418) (.exec 0x10c8ae (fun s => s.RIP = 0x10c8ae) (mulR64Effect 0x10c8ae 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[4414, 4412]
    (.letOp (n := 4419) (.out 0x10c8b1 (movR64R64Effect 0x10c8b1 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[4417]
    (.letOp (n := 4420) (.exec 0x10c8b1 (fun s => s.RIP = 0x10c8b1) (movR64R64Effect 0x10c8b1 7 2) (Reg.operands [.gpr 2] [])) #v[4417]
    (.letOp (n := 4421) (.out 0x10c8b4 (movR64R64Effect 0x10c8b4 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[4416]
    (.letOp (n := 4422) (.exec 0x10c8b4 (fun s => s.RIP = 0x10c8b4) (movR64R64Effect 0x10c8b4 8 0) (Reg.operands [.gpr 0] [])) #v[4416]
    (.letOp (n := 4423) (.out 0x10c8b7 (addR64R64Effect 0x10c8b7 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[4421, 4405]
    (.letOp (n := 4424) (.out 0x10c8b7 (addR64R64Effect 0x10c8b7 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[4421, 4405]
    (.letOp (n := 4425) (.exec 0x10c8b7 (fun s => s.RIP = 0x10c8b7) (addR64R64Effect 0x10c8b7 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[4421, 4405]
    (.letOp (n := 4426) (.out 0x10c8ba (atFlags StatusFlags.CF (adcR64R64Effect 0x10c8ba 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[4419, 4408, 4424]
    (.letOp (n := 4427) (.exec 0x10c8ba (fun s => s.RIP = 0x10c8ba) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c8ba 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4419, 4408, 4424]
    (.letOp (n := 4428) (.out 0x10c8bd (movR64M64Effect 0x10c8bd 5 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 4429) (.exec 0x10c8bd (LoadPre 0x10c8bd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10c8bd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c8bd 5 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4430) (.out 0x10c8c5 (movR64R64Effect 0x10c8c5 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[4428]
    (.letOp (n := 4431) (.exec 0x10c8c5 (fun s => s.RIP = 0x10c8c5) (movR64R64Effect 0x10c8c5 0 5) (Reg.operands [.gpr 5] [])) #v[4428]
    (.letOp (n := 4432) (.out 0x10c8c8 (movR64M64Effect 0x10c8c8 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 4433) (.exec 0x10c8c8 (LoadPre 0x10c8c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10c8c8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c8c8 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4434) (.out 0x10c8cd (mulR64Effect 0x10c8cd 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[4432, 4430]
    (.letOp (n := 4435) (.out 0x10c8cd (mulR64Effect 0x10c8cd 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[4432, 4430]
    (.letOp (n := 4436) (.exec 0x10c8cd (fun s => s.RIP = 0x10c8cd) (mulR64Effect 0x10c8cd 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[4432, 4430]
    (.letOp (n := 4437) (.out 0x10c8d0 (movR64R64Effect 0x10c8d0 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[4435]
    (.letOp (n := 4438) (.exec 0x10c8d0 (fun s => s.RIP = 0x10c8d0) (movR64R64Effect 0x10c8d0 11 2) (Reg.operands [.gpr 2] [])) #v[4435]
    (.letOp (n := 4439) (.out 0x10c8d3 (shldR64R64Effect 0x10c8d3 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[4437, 4434]
    (.letOp (n := 4440) (.exec 0x10c8d3 (fun s => s.RIP = 0x10c8d3) (shldR64R64Effect 0x10c8d3 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4437, 4434]
    (.letOp (n := 4441) (.out 0x10c8d8 (andR64R64Effect 0x10c8d8 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[4434, 4288]
    (.letOp (n := 4442) (.exec 0x10c8d8 (fun s => s.RIP = 0x10c8d8) (andR64R64Effect 0x10c8d8 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[4434, 4288]
    (.letOp (n := 4443) (.out 0x10c8db (movR64Imm64Effect 0x10c8db 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 4444) (.exec 0x10c8db (fun s => s.RIP = 0x10c8db) (movR64Imm64Effect 0x10c8db 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 4445) (.out 0x10c8e5 (mulR64Effect 0x10c8e5 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[4443, 4441]
    (.letOp (n := 4446) (.out 0x10c8e5 (mulR64Effect 0x10c8e5 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[4443, 4441]
    (.letOp (n := 4447) (.exec 0x10c8e5 (fun s => s.RIP = 0x10c8e5) (mulR64Effect 0x10c8e5 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[4443, 4441]
    (.letOp (n := 4448) (.out 0x10c8e8 (movR64R64Effect 0x10c8e8 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[4446]
    (.letOp (n := 4449) (.exec 0x10c8e8 (fun s => s.RIP = 0x10c8e8) (movR64R64Effect 0x10c8e8 9 2) (Reg.operands [.gpr 2] [])) #v[4446]
    (.letOp (n := 4450) (.out 0x10c8eb (addR64R64Effect 0x10c8eb 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[4445, 4423]
    (.letOp (n := 4451) (.out 0x10c8eb (addR64R64Effect 0x10c8eb 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[4445, 4423]
    (.letOp (n := 4452) (.exec 0x10c8eb (fun s => s.RIP = 0x10c8eb) (addR64R64Effect 0x10c8eb 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[4445, 4423]
    (.letOp (n := 4453) (.exec 0x10c8ee (StorePre 0x10c8ee 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10c8ee + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c8ee 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4450, 65]
    (b_l10a410_105))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_104 : List UInt8 :=
  [0x4C, 0x8B, 0xBC, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF8, 0x4C, 0x8B, 0x6C, 0x24, 0x38,
    0x49, 0xF7, 0xE5, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0, 0x49, 0x01, 0xF0, 0x48, 0x11, 0xCF, 0x48,
    0x8B, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE8, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48,
    0xF7, 0xE1, 0x49, 0x89, 0xD3, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x4C, 0x21, 0xC8, 0x48, 0xBA, 0x10,
    0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xD1, 0x4C, 0x01, 0xC0,
    0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] ++ bytes_l10a410_105

theorem code_l10a410_104 : ∀ x ∈ codeRange 0x10c89e bytes_l10a410_104, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc89e 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_105

def b_l10a410_103 : Block Op Label signature Reg.count 4365 :=
  .letOp (n := 4365) (.out 0x10c84e (movR64M64Effect 0x10c84e 3 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 4366) (.exec 0x10c84e (LoadPre 0x10c84e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10c84e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c84e 3 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4367) (.out 0x10c853 (movR64R64Effect 0x10c853 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[4365]
    (.letOp (n := 4368) (.exec 0x10c853 (fun s => s.RIP = 0x10c853) (movR64R64Effect 0x10c853 0 3) (Reg.operands [.gpr 3] [])) #v[4365]
    (.letOp (n := 4369) (.out 0x10c856 (movR64M64Effect 0x10c856 10 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 4370) (.exec 0x10c856 (LoadPre 0x10c856 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10c856 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10c856 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4371) (.out 0x10c85a (mulR64Effect 0x10c85a 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[4369, 4367]
    (.letOp (n := 4372) (.out 0x10c85a (mulR64Effect 0x10c85a 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[4369, 4367]
    (.letOp (n := 4373) (.exec 0x10c85a (fun s => s.RIP = 0x10c85a) (mulR64Effect 0x10c85a 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[4369, 4367]
    (.letOp (n := 4374) (.out 0x10c85d (movR64R64Effect 0x10c85d 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[4372]
    (.letOp (n := 4375) (.exec 0x10c85d (fun s => s.RIP = 0x10c85d) (movR64R64Effect 0x10c85d 1 2) (Reg.operands [.gpr 2] [])) #v[4372]
    (.letOp (n := 4376) (.out 0x10c860 (movR64R64Effect 0x10c860 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[4371]
    (.letOp (n := 4377) (.exec 0x10c860 (fun s => s.RIP = 0x10c860) (movR64R64Effect 0x10c860 6 0) (Reg.operands [.gpr 0] [])) #v[4371]
    (.letOp (n := 4378) (.out 0x10c863 (movR64M64Effect 0x10c863 12 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 4379) (.exec 0x10c863 (LoadPre 0x10c863 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10c863 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c863 12 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4380) (.out 0x10c86b (movR64R64Effect 0x10c86b 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[4378]
    (.letOp (n := 4381) (.exec 0x10c86b (fun s => s.RIP = 0x10c86b) (movR64R64Effect 0x10c86b 0 12) (Reg.operands [.gpr 12] [])) #v[4378]
    (.letOp (n := 4382) (.out 0x10c86e (mulM64Effect 0x10c86e 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4380, 65]
    (.letOp (n := 4383) (.out 0x10c86e (mulM64Effect 0x10c86e 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4380, 65]
    (.letOp (n := 4384) (.exec 0x10c86e (LoadPre 0x10c86e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10c86e + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10c86e 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4380, 65]
    (.letOp (n := 4385) (.out 0x10c876 (movR64R64Effect 0x10c876 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[4383]
    (.letOp (n := 4386) (.exec 0x10c876 (fun s => s.RIP = 0x10c876) (movR64R64Effect 0x10c876 7 2) (Reg.operands [.gpr 2] [])) #v[4383]
    (.letOp (n := 4387) (.out 0x10c879 (movR64R64Effect 0x10c879 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[4382]
    (.letOp (n := 4388) (.exec 0x10c879 (fun s => s.RIP = 0x10c879) (movR64R64Effect 0x10c879 8 0) (Reg.operands [.gpr 0] [])) #v[4382]
    (.letOp (n := 4389) (.out 0x10c87c (addR64R64Effect 0x10c87c 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[4387, 4376]
    (.letOp (n := 4390) (.out 0x10c87c (addR64R64Effect 0x10c87c 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[4387, 4376]
    (.letOp (n := 4391) (.exec 0x10c87c (fun s => s.RIP = 0x10c87c) (addR64R64Effect 0x10c87c 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[4387, 4376]
    (.letOp (n := 4392) (.out 0x10c87f (atFlags StatusFlags.CF (adcR64R64Effect 0x10c87f 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[4385, 4374, 4390]
    (.letOp (n := 4393) (.exec 0x10c87f (fun s => s.RIP = 0x10c87f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c87f 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4385, 4374, 4390]
    (.letOp (n := 4394) (.out 0x10c882 (movR64M64Effect 0x10c882 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4395) (.exec 0x10c882 (LoadPre 0x10c882 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10c882 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c882 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4396) (.out 0x10c88a (movR64M64Effect 0x10c88a 14 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 4397) (.exec 0x10c88a (LoadPre 0x10c88a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10c88a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c88a 14 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4398) (.out 0x10c88f (mulR64Effect 0x10c88f 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[4396, 4394]
    (.letOp (n := 4399) (.out 0x10c88f (mulR64Effect 0x10c88f 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[4396, 4394]
    (.letOp (n := 4400) (.exec 0x10c88f (fun s => s.RIP = 0x10c88f) (mulR64Effect 0x10c88f 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[4396, 4394]
    (.letOp (n := 4401) (.out 0x10c892 (movR64R64Effect 0x10c892 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[4399]
    (.letOp (n := 4402) (.exec 0x10c892 (fun s => s.RIP = 0x10c892) (movR64R64Effect 0x10c892 1 2) (Reg.operands [.gpr 2] [])) #v[4399]
    (.letOp (n := 4403) (.out 0x10c895 (movR64R64Effect 0x10c895 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[4398]
    (.letOp (n := 4404) (.exec 0x10c895 (fun s => s.RIP = 0x10c895) (movR64R64Effect 0x10c895 6 0) (Reg.operands [.gpr 0] [])) #v[4398]
    (.letOp (n := 4405) (.out 0x10c898 (addR64R64Effect 0x10c898 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[4403, 4389]
    (.letOp (n := 4406) (.out 0x10c898 (addR64R64Effect 0x10c898 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[4403, 4389]
    (.letOp (n := 4407) (.exec 0x10c898 (fun s => s.RIP = 0x10c898) (addR64R64Effect 0x10c898 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[4403, 4389]
    (.letOp (n := 4408) (.out 0x10c89b (atFlags StatusFlags.CF (adcR64R64Effect 0x10c89b 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4401, 4392, 4406]
    (.letOp (n := 4409) (.exec 0x10c89b (fun s => s.RIP = 0x10c89b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c89b 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4401, 4392, 4406]
    (b_l10a410_104)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_103 : List UInt8 :=
  [0x48, 0x8B, 0x5C, 0x24, 0x68, 0x48, 0x89, 0xD8, 0x4C, 0x8B, 0x14, 0x24, 0x49, 0xF7, 0xE2, 0x48,
    0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x8B, 0xA4, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE0,
    0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0, 0x49, 0x01,
    0xF0, 0x48, 0x11, 0xCF, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x74, 0x24,
    0x50, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x01, 0xC6, 0x48, 0x11, 0xF9] ++ bytes_l10a410_104

theorem code_l10a410_103 : ∀ x ∈ codeRange 0x10c84e bytes_l10a410_103, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc84e 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_104

def b_l10a410_102 : Block Op Label signature Reg.count 4325 :=
  .letOp (n := 4325) (.out 0x10c7ed (shldR64R64Effect 0x10c7ed 5 1 5 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4315, 4312]
    (.letOp (n := 4326) (.exec 0x10c7ed (fun s => s.RIP = 0x10c7ed) (shldR64R64Effect 0x10c7ed 5 1 5 12) (Reg.operands [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4315, 4312]
    (.letOp (n := 4327) (.out 0x10c7f2 (andR64R64Effect 0x10c7f2 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[4312, 4288]
    (.letOp (n := 4328) (.exec 0x10c7f2 (fun s => s.RIP = 0x10c7f2) (andR64R64Effect 0x10c7f2 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[4312, 4288]
    (.letOp (n := 4329) (.exec 0x10c7f5 (StorePre 0x10c7f5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10c7f5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c7f5 5 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[4327, 65]
    (.letOp (n := 4330) (.out 0x10c7fd (movR64R64Effect 0x10c7fd 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[4317]
    (.letOp (n := 4331) (.exec 0x10c7fd (fun s => s.RIP = 0x10c7fd) (movR64R64Effect 0x10c7fd 0 14) (Reg.operands [.gpr 14] [])) #v[4317]
    (.letOp (n := 4332) (.out 0x10c800 (mulR64Effect 0x10c800 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[4292, 4330]
    (.letOp (n := 4333) (.out 0x10c800 (mulR64Effect 0x10c800 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[4292, 4330]
    (.letOp (n := 4334) (.exec 0x10c800 (fun s => s.RIP = 0x10c800) (mulR64Effect 0x10c800 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[4292, 4330]
    (.letOp (n := 4335) (.out 0x10c803 (imulR64R64Effect 0x10c803 4 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[4319, 4292]
    (.letOp (n := 4336) (.exec 0x10c803 (fun s => s.RIP = 0x10c803) (imulR64R64Effect 0x10c803 4 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[4319, 4292]
    (.letOp (n := 4337) (.out 0x10c807 (movR64M64Effect 0x10c807 7 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 4338) (.exec 0x10c807 (LoadPre 0x10c807 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10c807 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c807 7 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4339) (.out 0x10c80f (andR64R64Effect 0x10c80f 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[4337, 4288]
    (.letOp (n := 4340) (.exec 0x10c80f (fun s => s.RIP = 0x10c80f) (andR64R64Effect 0x10c80f 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[4337, 4288]
    (.letOp (n := 4341) (.out 0x10c812 (addR64R64Effect 0x10c812 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[4339, 4332]
    (.letOp (n := 4342) (.out 0x10c812 (addR64R64Effect 0x10c812 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[4339, 4332]
    (.letOp (n := 4343) (.exec 0x10c812 (fun s => s.RIP = 0x10c812) (addR64R64Effect 0x10c812 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[4339, 4332]
    (.letOp (n := 4344) (.out 0x10c815 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c815 2 10)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[4333, 4335, 4342]
    (.letOp (n := 4345) (.exec 0x10c815 (fun s => s.RIP = 0x10c815) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c815 2 10)) (Reg.operands [.gpr 2, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4333, 4335, 4342]
    (.letOp (n := 4346) (.out 0x10c818 (addR64R64Effect 0x10c818 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[4341, 4325]
    (.letOp (n := 4347) (.out 0x10c818 (addR64R64Effect 0x10c818 7 1) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 1] []) (.flag .CF)) #v[4341, 4325]
    (.letOp (n := 4348) (.exec 0x10c818 (fun s => s.RIP = 0x10c818) (addR64R64Effect 0x10c818 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[4341, 4325]
    (.letOp (n := 4349) (.out 0x10c81b (atFlags StatusFlags.CF (adcR64R64Effect 0x10c81b 2 6)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[4344, 4323, 4347]
    (.letOp (n := 4350) (.exec 0x10c81b (fun s => s.RIP = 0x10c81b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c81b 2 6)) (Reg.operands [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4344, 4323, 4347]
    (.letOp (n := 4351) (.out 0x10c81e (shldR64R64Effect 0x10c81e 5 2 7 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[4349, 4346]
    (.letOp (n := 4352) (.exec 0x10c81e (fun s => s.RIP = 0x10c81e) (shldR64R64Effect 0x10c81e 5 2 7 12) (Reg.operands [.gpr 2, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4349, 4346]
    (.letOp (n := 4353) (.out 0x10c823 (movR64Imm64Effect 0x10c823 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 4354) (.exec 0x10c823 (fun s => s.RIP = 0x10c823) (movR64Imm64Effect 0x10c823 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 4355) (.out 0x10c82d (movR64M64Effect 0x10c82d 1 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 4356) (.exec 0x10c82d (LoadPre 0x10c82d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10c82d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c82d 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4357) (.out 0x10c835 (andR64R64Effect 0x10c835 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[4355, 4353]
    (.letOp (n := 4358) (.exec 0x10c835 (fun s => s.RIP = 0x10c835) (andR64R64Effect 0x10c835 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[4355, 4353]
    (.letOp (n := 4359) (.out 0x10c838 (addR64R64Effect 0x10c838 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[4357, 4351]
    (.letOp (n := 4360) (.exec 0x10c838 (fun s => s.RIP = 0x10c838) (addR64R64Effect 0x10c838 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[4357, 4351]
    (.letOp (n := 4361) (.exec 0x10c83b (StorePre 0x10c83b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10c83b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c83b 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[4359, 65]
    (.letOp (n := 4362) (.out 0x10c843 (andR64R64Effect 0x10c843 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[4346, 4288]
    (.letOp (n := 4363) (.exec 0x10c843 (fun s => s.RIP = 0x10c843) (andR64R64Effect 0x10c843 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[4346, 4288]
    (.letOp (n := 4364) (.exec 0x10c846 (StorePre 0x10c846 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10c846 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c846 7 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[4362, 65]
    (b_l10a410_103))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_102 : List UInt8 :=
  [0x48, 0x0F, 0xA4, 0xE9, 0x0C, 0x4C, 0x21, 0xCD, 0x48, 0x89, 0xAC, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xE7, 0x4C, 0x0F, 0xAF, 0xD7, 0x48, 0x8B, 0xBC, 0x24, 0xB8, 0x00,
    0x00, 0x00, 0x4C, 0x21, 0xCF, 0x48, 0x01, 0xC7, 0x4C, 0x11, 0xD2, 0x48, 0x01, 0xCF, 0x48, 0x11,
    0xF2, 0x48, 0x0F, 0xA4, 0xFA, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00,
    0x48, 0x8B, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x21, 0xC1, 0x48, 0x01, 0xD1, 0x48, 0x89,
    0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x21, 0xCF, 0x48, 0x89, 0xBC, 0x24, 0xB8, 0x00, 0x00,
    0x00] ++ bytes_l10a410_103

theorem code_l10a410_102 : ∀ x ∈ codeRange 0x10c7ed bytes_l10a410_102, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc7ed 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_103

def b_l10a410_101 : Block Op Label signature Reg.count 4279 :=
  .letOp (n := 4279) (.out 0x10c795 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c795 10 8)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[4272, 4263, 4277]
    (.letOp (n := 4280) (.exec 0x10c795 (fun s => s.RIP = 0x10c795) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c795 10 8)) (Reg.operands [.gpr 10, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4272, 4263, 4277]
    (.letOp (n := 4281) (.out 0x10c798 (addR64R64Effect 0x10c798 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[4276, 4218]
    (.letOp (n := 4282) (.out 0x10c798 (addR64R64Effect 0x10c798 14 9) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 9] []) (.flag .CF)) #v[4276, 4218]
    (.letOp (n := 4283) (.exec 0x10c798 (fun s => s.RIP = 0x10c798) (addR64R64Effect 0x10c798 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[4276, 4218]
    (.letOp (n := 4284) (.out 0x10c79b (atFlags StatusFlags.CF (adcR64R64Effect 0x10c79b 10 7)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[4279, 4220, 4282]
    (.letOp (n := 4285) (.exec 0x10c79b (fun s => s.RIP = 0x10c79b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c79b 10 7)) (Reg.operands [.gpr 10, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4279, 4220, 4282]
    (.letOp (n := 4286) (.out 0x10c79e (movR64R64Effect 0x10c79e 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[4281]
    (.letOp (n := 4287) (.exec 0x10c79e (fun s => s.RIP = 0x10c79e) (movR64R64Effect 0x10c79e 0 14) (Reg.operands [.gpr 14] [])) #v[4281]
    (.letOp (n := 4288) (.out 0x10c7a1 (movR64Imm64Effect 0x10c7a1 9 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 4289) (.exec 0x10c7a1 (fun s => s.RIP = 0x10c7a1) (movR64Imm64Effect 0x10c7a1 9 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 4290) (.out 0x10c7ab (andR64R64Effect 0x10c7ab 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[4286, 4288]
    (.letOp (n := 4291) (.exec 0x10c7ab (fun s => s.RIP = 0x10c7ab) (andR64R64Effect 0x10c7ab 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[4286, 4288]
    (.letOp (n := 4292) (.out 0x10c7ae (movR64Imm64Effect 0x10c7ae 7 0x1000003d10) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 4293) (.exec 0x10c7ae (fun s => s.RIP = 0x10c7ae) (movR64Imm64Effect 0x10c7ae 7 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 4294) (.out 0x10c7b8 (mulR64Effect 0x10c7b8 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[4292, 4290]
    (.letOp (n := 4295) (.out 0x10c7b8 (mulR64Effect 0x10c7b8 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[4292, 4290]
    (.letOp (n := 4296) (.exec 0x10c7b8 (fun s => s.RIP = 0x10c7b8) (mulR64Effect 0x10c7b8 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[4292, 4290]
    (.letOp (n := 4297) (.out 0x10c7bb (addR64R64Effect 0x10c7bb 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[4251, 4244]
    (.letOp (n := 4298) (.out 0x10c7bb (addR64R64Effect 0x10c7bb 5 11) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 11] []) (.flag .CF)) #v[4251, 4244]
    (.letOp (n := 4299) (.exec 0x10c7bb (fun s => s.RIP = 0x10c7bb) (addR64R64Effect 0x10c7bb 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[4251, 4244]
    (.letOp (n := 4300) (.out 0x10c7be (atFlags StatusFlags.CF (adcR64R64Effect 0x10c7be 1 15)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4253, 4242, 4298]
    (.letOp (n := 4301) (.exec 0x10c7be (fun s => s.RIP = 0x10c7be) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c7be 1 15)) (Reg.operands [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4253, 4242, 4298]
    (.letOp (n := 4302) (.out 0x10c7c1 (addR64M64Effect 0x10c7c1 5 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[4297, 65]
    (.letOp (n := 4303) (.out 0x10c7c1 (addR64M64Effect 0x10c7c1 5 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[4297, 65]
    (.letOp (n := 4304) (.exec 0x10c7c1 (LoadPre 0x10c7c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10c7c1 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10c7c1 5 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[4297, 65]
    (.letOp (n := 4305) (.out 0x10c7c9 (atFlags StatusFlags.CF (adcR64M64Effect 0x10c7c9 1 (.sib 4 none 0 (.d32 0xa0)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[4300, 65, 4303]
    (.letOp (n := 4306) (.exec 0x10c7c9 (LoadPre 0x10c7c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10c7c9 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10c7c9 1 (.sib 4 none 0 (.d32 0xa0)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4300, 65, 4303]
    (.letOp (n := 4307) (.out 0x10c7d1 (addR64R64Effect 0x10c7d1 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[4302, 4294]
    (.letOp (n := 4308) (.out 0x10c7d1 (addR64R64Effect 0x10c7d1 5 0) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 0] []) (.flag .CF)) #v[4302, 4294]
    (.letOp (n := 4309) (.exec 0x10c7d1 (fun s => s.RIP = 0x10c7d1) (addR64R64Effect 0x10c7d1 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[4302, 4294]
    (.letOp (n := 4310) (.out 0x10c7d4 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c7d4 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4305, 4295, 4308]
    (.letOp (n := 4311) (.exec 0x10c7d4 (fun s => s.RIP = 0x10c7d4) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c7d4 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4305, 4295, 4308]
    (.letOp (n := 4312) (.out 0x10c7d7 (addR64R64Effect 0x10c7d7 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 6] []) (.reg (.gpr 5))) #v[4307, 4228]
    (.letOp (n := 4313) (.out 0x10c7d7 (addR64R64Effect 0x10c7d7 5 6) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 6] []) (.flag .CF)) #v[4307, 4228]
    (.letOp (n := 4314) (.exec 0x10c7d7 (fun s => s.RIP = 0x10c7d7) (addR64R64Effect 0x10c7d7 5 6) (Reg.operands [.gpr 5, .gpr 6] [])) #v[4307, 4228]
    (.letOp (n := 4315) (.out 0x10c7da (atFlags StatusFlags.CF (adcR64R64Effect 0x10c7da 1 13)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[4310, 4224, 4313]
    (.letOp (n := 4316) (.exec 0x10c7da (fun s => s.RIP = 0x10c7da) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c7da 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4310, 4224, 4313]
    (.letOp (n := 4317) (.out 0x10c7dd (shrdR64R64Effect 0x10c7dd 5 14 10 52) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[4281, 4284]
    (.letOp (n := 4318) (.exec 0x10c7dd (fun s => s.RIP = 0x10c7dd) (shrdR64R64Effect 0x10c7dd 5 14 10 52) (Reg.operands [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4281, 4284]
    (.letOp (n := 4319) (.out 0x10c7e2 (shrR64Effect 0x10c7e2 4 10 52) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[4284]
    (.letOp (n := 4320) (.exec 0x10c7e2 (fun s => s.RIP = 0x10c7e2) (shrR64Effect 0x10c7e2 4 10 52) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4284]
    (.letOp (n := 4321) (.out 0x10c7e6 (movR64R64Effect 0x10c7e6 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[4315]
    (.letOp (n := 4322) (.exec 0x10c7e6 (fun s => s.RIP = 0x10c7e6) (movR64R64Effect 0x10c7e6 6 1) (Reg.operands [.gpr 1] [])) #v[4315]
    (.letOp (n := 4323) (.out 0x10c7e9 (shrR64Effect 0x10c7e9 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[4321]
    (.letOp (n := 4324) (.exec 0x10c7e9 (fun s => s.RIP = 0x10c7e9) (shrR64Effect 0x10c7e9 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4321]
    (b_l10a410_102))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_101 : List UInt8 :=
  [0x4D, 0x11, 0xC2, 0x4D, 0x01, 0xCE, 0x49, 0x11, 0xFA, 0x4C, 0x89, 0xF0, 0x49, 0xB9, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xC8, 0x48, 0xBF, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x4C, 0x01, 0xDD, 0x4C, 0x11, 0xF9, 0x48, 0x03, 0xAC, 0x24,
    0xD8, 0x00, 0x00, 0x00, 0x48, 0x13, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x01, 0xC5, 0x48,
    0x11, 0xD1, 0x48, 0x01, 0xF5, 0x4C, 0x11, 0xE9, 0x4D, 0x0F, 0xAC, 0xD6, 0x34, 0x49, 0xC1, 0xEA,
    0x34, 0x48, 0x89, 0xCE, 0x48, 0xC1, 0xEE, 0x34] ++ bytes_l10a410_102

theorem code_l10a410_101 : ∀ x ∈ codeRange 0x10c795 bytes_l10a410_101, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc795 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_102

def b_l10a410_100 : Block Op Label signature Reg.count 4236 :=
  .letOp (n := 4236) (.exec 0x10c73d (StorePre 0x10c73d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10c73d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c73d 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4232, 65]
    (.letOp (n := 4237) (.out 0x10c745 (movR64M64Effect 0x10c745 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4238) (.exec 0x10c745 (LoadPre 0x10c745 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10c745 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c745 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4239) (.out 0x10c74a (mulM64Effect 0x10c74a 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4237, 65]
    (.letOp (n := 4240) (.out 0x10c74a (mulM64Effect 0x10c74a 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4237, 65]
    (.letOp (n := 4241) (.exec 0x10c74a (LoadPre 0x10c74a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10c74a + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10c74a 8 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4237, 65]
    (.letOp (n := 4242) (.out 0x10c752 (movR64R64Effect 0x10c752 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[4240]
    (.letOp (n := 4243) (.exec 0x10c752 (fun s => s.RIP = 0x10c752) (movR64R64Effect 0x10c752 15 2) (Reg.operands [.gpr 2] [])) #v[4240]
    (.letOp (n := 4244) (.out 0x10c755 (movR64R64Effect 0x10c755 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[4239]
    (.letOp (n := 4245) (.exec 0x10c755 (fun s => s.RIP = 0x10c755) (movR64R64Effect 0x10c755 11 0) (Reg.operands [.gpr 0] [])) #v[4239]
    (.letOp (n := 4246) (.out 0x10c758 (movR64M64Effect 0x10c758 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4247) (.exec 0x10c758 (LoadPre 0x10c758 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10c758 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c758 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4248) (.out 0x10c75d (mulR64Effect 0x10c75d 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[4139, 4246]
    (.letOp (n := 4249) (.out 0x10c75d (mulR64Effect 0x10c75d 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[4139, 4246]
    (.letOp (n := 4250) (.exec 0x10c75d (fun s => s.RIP = 0x10c75d) (mulR64Effect 0x10c75d 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[4139, 4246]
    (.letOp (n := 4251) (.out 0x10c760 (movR64R64Effect 0x10c760 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[4248]
    (.letOp (n := 4252) (.exec 0x10c760 (fun s => s.RIP = 0x10c760) (movR64R64Effect 0x10c760 5 0) (Reg.operands [.gpr 0] [])) #v[4248]
    (.letOp (n := 4253) (.out 0x10c763 (movR64R64Effect 0x10c763 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[4249]
    (.letOp (n := 4254) (.exec 0x10c763 (fun s => s.RIP = 0x10c763) (movR64R64Effect 0x10c763 1 2) (Reg.operands [.gpr 2] [])) #v[4249]
    (.letOp (n := 4255) (.out 0x10c766 (andR64R64Effect 0x10c766 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[4226, 4190]
    (.letOp (n := 4256) (.exec 0x10c766 (fun s => s.RIP = 0x10c766) (andR64R64Effect 0x10c766 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[4226, 4190]
    (.letOp (n := 4257) (.exec 0x10c769 (StorePre 0x10c769 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10c769 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c769 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[4255, 65]
    (.letOp (n := 4258) (.out 0x10c771 (movR64M64Effect 0x10c771 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4259) (.exec 0x10c771 (LoadPre 0x10c771 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10c771 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c771 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4260) (.out 0x10c776 (mulM64Effect 0x10c776 8 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4258, 65]
    (.letOp (n := 4261) (.out 0x10c776 (mulM64Effect 0x10c776 8 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4258, 65]
    (.letOp (n := 4262) (.exec 0x10c776 (LoadPre 0x10c776 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x10c776 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10c776 8 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4258, 65]
    (.letOp (n := 4263) (.out 0x10c77e (movR64R64Effect 0x10c77e 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[4261]
    (.letOp (n := 4264) (.exec 0x10c77e (fun s => s.RIP = 0x10c77e) (movR64R64Effect 0x10c77e 8 2) (Reg.operands [.gpr 2] [])) #v[4261]
    (.letOp (n := 4265) (.out 0x10c781 (movR64R64Effect 0x10c781 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[4260]
    (.letOp (n := 4266) (.exec 0x10c781 (fun s => s.RIP = 0x10c781) (movR64R64Effect 0x10c781 12 0) (Reg.operands [.gpr 0] [])) #v[4260]
    (.letOp (n := 4267) (.out 0x10c784 (movR64M64Effect 0x10c784 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 4268) (.exec 0x10c784 (LoadPre 0x10c784 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10c784 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10c784 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4269) (.out 0x10c789 (mulR64Effect 0x10c789 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[4169, 4267]
    (.letOp (n := 4270) (.out 0x10c789 (mulR64Effect 0x10c789 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[4169, 4267]
    (.letOp (n := 4271) (.exec 0x10c789 (fun s => s.RIP = 0x10c789) (mulR64Effect 0x10c789 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[4169, 4267]
    (.letOp (n := 4272) (.out 0x10c78c (movR64R64Effect 0x10c78c 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[4270]
    (.letOp (n := 4273) (.exec 0x10c78c (fun s => s.RIP = 0x10c78c) (movR64R64Effect 0x10c78c 10 2) (Reg.operands [.gpr 2] [])) #v[4270]
    (.letOp (n := 4274) (.out 0x10c78f (movR64R64Effect 0x10c78f 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[4269]
    (.letOp (n := 4275) (.exec 0x10c78f (fun s => s.RIP = 0x10c78f) (movR64R64Effect 0x10c78f 14 0) (Reg.operands [.gpr 0] [])) #v[4269]
    (.letOp (n := 4276) (.out 0x10c792 (addR64R64Effect 0x10c792 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[4274, 4265]
    (.letOp (n := 4277) (.out 0x10c792 (addR64R64Effect 0x10c792 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[4274, 4265]
    (.letOp (n := 4278) (.exec 0x10c792 (fun s => s.RIP = 0x10c792) (addR64R64Effect 0x10c792 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[4274, 4265]
    (b_l10a410_101)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_100 : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0xF7, 0xA4,
    0x24, 0x20, 0x01, 0x00, 0x00, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC3, 0x48, 0x8B, 0x44, 0x24, 0x08,
    0x48, 0xF7, 0xE5, 0x48, 0x89, 0xC5, 0x48, 0x89, 0xD1, 0x4D, 0x21, 0xF0, 0x4C, 0x89, 0x84, 0x24,
    0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0xF7, 0xA4, 0x24, 0x08, 0x01, 0x00,
    0x00, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0xF7, 0xE3, 0x49,
    0x89, 0xD2, 0x49, 0x89, 0xC6, 0x4D, 0x01, 0xE6] ++ bytes_l10a410_101

theorem code_l10a410_100 : ∀ x ∈ codeRange 0x10c73d bytes_l10a410_100, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc73d 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_101

def b_l10a410_99 : Block Op Label signature Reg.count 4192 :=
  .letOp (n := 4192) (.out 0x10c6de (andR64R64Effect 0x10c6de 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[4188, 4190]
    (.letOp (n := 4193) (.exec 0x10c6de (fun s => s.RIP = 0x10c6de) (andR64R64Effect 0x10c6de 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[4188, 4190]
    (.letOp (n := 4194) (.out 0x10c6e1 (movR64Imm64Effect 0x10c6e1 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 4195) (.exec 0x10c6e1 (fun s => s.RIP = 0x10c6e1) (movR64Imm64Effect 0x10c6e1 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 4196) (.out 0x10c6eb (mulR64Effect 0x10c6eb 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[4194, 4192]
    (.letOp (n := 4197) (.out 0x10c6eb (mulR64Effect 0x10c6eb 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[4194, 4192]
    (.letOp (n := 4198) (.exec 0x10c6eb (fun s => s.RIP = 0x10c6eb) (mulR64Effect 0x10c6eb 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[4194, 4192]
    (.letOp (n := 4199) (.out 0x10c6ee (movR64M64Effect 0x10c6ee 1 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 4200) (.exec 0x10c6ee (LoadPre 0x10c6ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10c6ee + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10c6ee 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 4201) (.out 0x10c6f6 (addR64M64Effect 0x10c6f6 1 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[4199, 65]
    (.letOp (n := 4202) (.out 0x10c6f6 (addR64M64Effect 0x10c6f6 1 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 4] []) (.flag .CF)) #v[4199, 65]
    (.letOp (n := 4203) (.exec 0x10c6f6 (LoadPre 0x10c6f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10c6f6 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10c6f6 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[4199, 65]
    (.letOp (n := 4204) (.out 0x10c6fe (atFlags StatusFlags.CF (adcR64M64Effect 0x10c6fe 6 (.sib 4 none 0 (.d32 0xa0)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[4134, 65, 4202]
    (.letOp (n := 4205) (.exec 0x10c6fe (LoadPre 0x10c6fe (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10c6fe + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10c6fe 6 (.sib 4 none 0 (.d32 0xa0)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4134, 65, 4202]
    (.letOp (n := 4206) (.out 0x10c706 (addR64R64Effect 0x10c706 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[4201, 4196]
    (.letOp (n := 4207) (.out 0x10c706 (addR64R64Effect 0x10c706 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[4201, 4196]
    (.letOp (n := 4208) (.exec 0x10c706 (fun s => s.RIP = 0x10c706) (addR64R64Effect 0x10c706 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[4201, 4196]
    (.letOp (n := 4209) (.out 0x10c709 (atFlags StatusFlags.CF (adcR64R64Effect 0x10c709 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[4204, 4197, 4207]
    (.letOp (n := 4210) (.exec 0x10c709 (fun s => s.RIP = 0x10c709) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c709 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4204, 4197, 4207]
    (.letOp (n := 4211) (.out 0x10c70c (addR64R64Effect 0x10c70c 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[4206, 4118]
    (.letOp (n := 4212) (.out 0x10c70c (addR64R64Effect 0x10c70c 1 10) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 10] []) (.flag .CF)) #v[4206, 4118]
    (.letOp (n := 4213) (.exec 0x10c70c (fun s => s.RIP = 0x10c70c) (addR64R64Effect 0x10c70c 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[4206, 4118]
    (.letOp (n := 4214) (.out 0x10c70f (atFlags StatusFlags.CF (adcR64R64Effect 0x10c70f 6 13)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[4209, 4116, 4212]
    (.letOp (n := 4215) (.exec 0x10c70f (fun s => s.RIP = 0x10c70f) (atFlags StatusFlags.CF (adcR64R64Effect 0x10c70f 6 13)) (Reg.operands [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[4209, 4116, 4212]
    (.letOp (n := 4216) (.out 0x10c712 (movR64R64Effect 0x10c712 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[4186]
    (.letOp (n := 4217) (.exec 0x10c712 (fun s => s.RIP = 0x10c712) (movR64R64Effect 0x10c712 7 9) (Reg.operands [.gpr 9] [])) #v[4186]
    (.letOp (n := 4218) (.out 0x10c715 (shldR64R64Effect 0x10c715 5 9 8 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4186, 4183]
    (.letOp (n := 4219) (.exec 0x10c715 (fun s => s.RIP = 0x10c715) (shldR64R64Effect 0x10c715 5 9 8 12) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4186, 4183]
    (.letOp (n := 4220) (.out 0x10c71a (shrR64Effect 0x10c71a 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[4216]
    (.letOp (n := 4221) (.exec 0x10c71a (fun s => s.RIP = 0x10c71a) (shrR64Effect 0x10c71a 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4216]
    (.letOp (n := 4222) (.out 0x10c71e (movR64R64Effect 0x10c71e 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[4214]
    (.letOp (n := 4223) (.exec 0x10c71e (fun s => s.RIP = 0x10c71e) (movR64R64Effect 0x10c71e 13 6) (Reg.operands [.gpr 6] [])) #v[4214]
    (.letOp (n := 4224) (.out 0x10c721 (shrR64Effect 0x10c721 4 13 52) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[4222]
    (.letOp (n := 4225) (.exec 0x10c721 (fun s => s.RIP = 0x10c721) (shrR64Effect 0x10c721 4 13 52) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4222]
    (.letOp (n := 4226) (.out 0x10c725 (movR64R64Effect 0x10c725 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[4211]
    (.letOp (n := 4227) (.exec 0x10c725 (fun s => s.RIP = 0x10c725) (movR64R64Effect 0x10c725 8 1) (Reg.operands [.gpr 1] [])) #v[4211]
    (.letOp (n := 4228) (.out 0x10c728 (shldR64R64Effect 0x10c728 5 6 1 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[4214, 4211]
    (.letOp (n := 4229) (.exec 0x10c728 (fun s => s.RIP = 0x10c728) (shldR64R64Effect 0x10c728 5 6 1 12) (Reg.operands [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4214, 4211]
    (.letOp (n := 4230) (.out 0x10c72d (movR64R64Effect 0x10c72d 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[4162]
    (.letOp (n := 4231) (.exec 0x10c72d (fun s => s.RIP = 0x10c72d) (movR64R64Effect 0x10c72d 0 11) (Reg.operands [.gpr 11] [])) #v[4162]
    (.letOp (n := 4232) (.out 0x10c730 (mulM64Effect 0x10c730 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[4230, 65]
    (.letOp (n := 4233) (.out 0x10c730 (mulM64Effect 0x10c730 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[4230, 65]
    (.letOp (n := 4234) (.exec 0x10c730 (LoadPre 0x10c730 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10c730 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10c730 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[4230, 65]
    (.letOp (n := 4235) (.exec 0x10c735 (StorePre 0x10c735 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10c735 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10c735 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[4233, 65]
    (b_l10a410_100))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a410_99 : List UInt8 :=
  [0x4C, 0x21, 0xF0, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1,
    0x48, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x03, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00,
    0x48, 0x13, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x01, 0xC1, 0x48, 0x11, 0xD6, 0x4C, 0x01,
    0xD1, 0x4C, 0x11, 0xEE, 0x4C, 0x89, 0xCF, 0x4D, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0xC1, 0xEF, 0x34,
    0x49, 0x89, 0xF5, 0x49, 0xC1, 0xED, 0x34, 0x49, 0x89, 0xC8, 0x48, 0x0F, 0xA4, 0xCE, 0x0C, 0x4C,
    0x89, 0xD8, 0x48, 0xF7, 0x64, 0x24, 0x60, 0x48, 0x89, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00] ++ bytes_l10a410_100

theorem code_l10a410_99 : ∀ x ∈ codeRange 0x10c6de bytes_l10a410_99, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc6de 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a410_100

def b_l10e010_14 : Block Op Label signature Reg.count 643 :=
  .letOp (n := 643) (.out 0x10e4ac (popR64Effect 0x10e4ac 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[641]
    (.letOp (n := 644) (.out 0x10e4ac (popR64Effect 0x10e4ac 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[641]
    (.letOp (n := 645) (.exec 0x10e4ac (PopPre 0x10e4ac) (popR64Effect 0x10e4ac 2 13) (Reg.operands [.gpr 4] [])) #v[641]
    (.letOp (n := 646) (.out 0x10e4ae (popR64Effect 0x10e4ae 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[644]
    (.letOp (n := 647) (.out 0x10e4ae (popR64Effect 0x10e4ae 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[644]
    (.letOp (n := 648) (.exec 0x10e4ae (PopPre 0x10e4ae) (popR64Effect 0x10e4ae 2 14) (Reg.operands [.gpr 4] [])) #v[644]
    (.letOp (n := 649) (.out 0x10e4b0 (popR64Effect 0x10e4b0 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[647]
    (.letOp (n := 650) (.out 0x10e4b0 (popR64Effect 0x10e4b0 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[647]
    (.letOp (n := 651) (.exec 0x10e4b0 (PopPre 0x10e4b0) (popR64Effect 0x10e4b0 2 15) (Reg.operands [.gpr 4] [])) #v[647]
    (.letOp (n := 652) (.out 0x10e4b2 (popR64Effect 0x10e4b2 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[650]
    (.letOp (n := 653) (.out 0x10e4b2 (popR64Effect 0x10e4b2 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[650]
    (.letOp (n := 654) (.exec 0x10e4b2 (PopPre 0x10e4b2) (popR64Effect 0x10e4b2 1 5) (Reg.operands [.gpr 4] [])) #v[650]
    (.letOp (n := 655) (.out 0x10e4b3 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[653]
    (.letOp (n := 656) (.out 0x10e4b3 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[653]
    (.letOp (n := 657) (.exec 0x10e4b3 (RetPre 0x10e4b3) (retEffect) (Reg.operands [.gpr 4] [])) #v[653]
    (.terminate (.ret (RegMap.args [(0, 579), (1, 594), (2, 628), (3, 637), (4, 656), (5, 652), (6, 586), (7, 596), (8, 466), (9, 561), (10, 257), (11, 559), (12, 640), (13, 643), (14, 646), (15, 649), (22, 22), (39, 39), (50, 50), (51, 51)] 658) (some ⟨655, by decide⟩)))))))))))))))))

def bytes_l10e010_14 : List UInt8 :=
  [0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10e010_14 : ∀ x ∈ codeRange 0x10e4ac bytes_l10e010_14, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe4ac 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l10e010_13 : Block Op Label signature Reg.count 612 :=
  .letOp (n := 612) (.exec 0x10e461 (StorePre 0x10e461 4 (fun s => AddrMode.addr (.base 0 (.d8 0x28)) s (0x10e461 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e461 2 (.base 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[610, 579]
    (.letOp (n := 613) (.out 0x10e465 (movR64M64Effect 0x10e465 2 (.base 7 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[596]
    (.letOp (n := 614) (.exec 0x10e465 (LoadPre 0x10e465 (fun s => AddrMode.addr (.base 7 (.d8 0x70)) s (0x10e465 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e465 2 (.base 7 (.d8 0x70))) (Reg.operands [.gpr 7] [])) #v[596]
    (.letOp (n := 615) (.exec 0x10e469 (StorePre 0x10e469 4 (fun s => AddrMode.addr (.base 0 (.d8 0x70)) s (0x10e469 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e469 2 (.base 0 (.d8 0x70))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[613, 579]
    (.letOp (n := 616) (.out 0x10e46d (movR64M64Effect 0x10e46d 2 (.base 7 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[596]
    (.letOp (n := 617) (.exec 0x10e46d (LoadPre 0x10e46d (fun s => AddrMode.addr (.base 7 (.d8 0x68)) s (0x10e46d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e46d 2 (.base 7 (.d8 0x68))) (Reg.operands [.gpr 7] [])) #v[596]
    (.letOp (n := 618) (.exec 0x10e471 (StorePre 0x10e471 4 (fun s => AddrMode.addr (.base 0 (.d8 0x68)) s (0x10e471 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e471 2 (.base 0 (.d8 0x68))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[616, 579]
    (.letOp (n := 619) (.out 0x10e475 (movR64M64Effect 0x10e475 2 (.base 7 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[596]
    (.letOp (n := 620) (.exec 0x10e475 (LoadPre 0x10e475 (fun s => AddrMode.addr (.base 7 (.d8 0x60)) s (0x10e475 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e475 2 (.base 7 (.d8 0x60))) (Reg.operands [.gpr 7] [])) #v[596]
    (.letOp (n := 621) (.exec 0x10e479 (StorePre 0x10e479 4 (fun s => AddrMode.addr (.base 0 (.d8 0x60)) s (0x10e479 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e479 2 (.base 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[619, 579]
    (.letOp (n := 622) (.out 0x10e47d (movR64M64Effect 0x10e47d 2 (.base 7 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[596]
    (.letOp (n := 623) (.exec 0x10e47d (LoadPre 0x10e47d (fun s => AddrMode.addr (.base 7 (.d8 0x58)) s (0x10e47d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e47d 2 (.base 7 (.d8 0x58))) (Reg.operands [.gpr 7] [])) #v[596]
    (.letOp (n := 624) (.exec 0x10e481 (StorePre 0x10e481 4 (fun s => AddrMode.addr (.base 0 (.d8 0x58)) s (0x10e481 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e481 2 (.base 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[622, 579]
    (.letOp (n := 625) (.out 0x10e485 (movR64M64Effect 0x10e485 2 (.base 7 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[596]
    (.letOp (n := 626) (.exec 0x10e485 (LoadPre 0x10e485 (fun s => AddrMode.addr (.base 7 (.d8 0x50)) s (0x10e485 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e485 2 (.base 7 (.d8 0x50))) (Reg.operands [.gpr 7] [])) #v[596]
    (.letOp (n := 627) (.exec 0x10e489 (StorePre 0x10e489 4 (fun s => AddrMode.addr (.base 0 (.d8 0x50)) s (0x10e489 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e489 2 (.base 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[625, 579]
    (.letOp (n := 628) (.out 0x10e48d (movR64M64Effect 0x10e48d 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 629) (.exec 0x10e48d (LoadPre 0x10e48d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e48d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e48d 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 630) (.exec 0x10e492 (StorePre 0x10e492 3 (fun s => AddrMode.addr (.base 0 .none) s (0x10e492 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10e492 2 (.base 0 .none)) (Reg.operands [.gpr 2, .gpr 0] [])) #v[628, 579]
    (.letOp (n := 631) (.exec 0x10e495 (StorePre 0x10e495 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10e495 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e495 12 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 0] [])) #v[498, 579]
    (.letOp (n := 632) (.exec 0x10e499 (StorePre 0x10e499 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10e499 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e499 3 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 3, .gpr 0] [])) #v[563, 579]
    (.letOp (n := 633) (.exec 0x10e49d (StorePre 0x10e49d 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x10e49d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e49d 6 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[586, 579]
    (.letOp (n := 634) (.exec 0x10e4a1 (StorePre 0x10e4a1 4 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x10e4a1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e4a1 1 (.base 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[594, 579]
    (.letOp (n := 635) (.out 0x10e4a5 (addR64Imm8Effect 0x10e4a5 4 0x50) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 636) (.exec 0x10e4a5 (fun s => s.RIP = 0x10e4a5) (addR64Imm8Effect 0x10e4a5 4 0x50) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 637) (.out 0x10e4a9 (popR64Effect 0x10e4a9 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[635]
    (.letOp (n := 638) (.out 0x10e4a9 (popR64Effect 0x10e4a9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[635]
    (.letOp (n := 639) (.exec 0x10e4a9 (PopPre 0x10e4a9) (popR64Effect 0x10e4a9 1 3) (Reg.operands [.gpr 4] [])) #v[635]
    (.letOp (n := 640) (.out 0x10e4aa (popR64Effect 0x10e4aa 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[638]
    (.letOp (n := 641) (.out 0x10e4aa (popR64Effect 0x10e4aa 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[638]
    (.letOp (n := 642) (.exec 0x10e4aa (PopPre 0x10e4aa) (popR64Effect 0x10e4aa 2 12) (Reg.operands [.gpr 4] [])) #v[638]
    (b_l10e010_14)))))))))))))))))))))))))))))))

def bytes_l10e010_13 : List UInt8 :=
  [0x48, 0x89, 0x50, 0x28, 0x48, 0x8B, 0x57, 0x70, 0x48, 0x89, 0x50, 0x70, 0x48, 0x8B, 0x57, 0x68,
    0x48, 0x89, 0x50, 0x68, 0x48, 0x8B, 0x57, 0x60, 0x48, 0x89, 0x50, 0x60, 0x48, 0x8B, 0x57, 0x58,
    0x48, 0x89, 0x50, 0x58, 0x48, 0x8B, 0x57, 0x50, 0x48, 0x89, 0x50, 0x50, 0x48, 0x8B, 0x54, 0x24,
    0x08, 0x48, 0x89, 0x10, 0x4C, 0x89, 0x60, 0x08, 0x48, 0x89, 0x58, 0x10, 0x48, 0x89, 0x70, 0x18,
    0x48, 0x89, 0x48, 0x20, 0x48, 0x83, 0xC4, 0x50, 0x5B, 0x41, 0x5C] ++ bytes_l10e010_14

theorem code_l10e010_13 : ∀ x ∈ codeRange 0x10e461 bytes_l10e010_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe461 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_14

def b_l10e010_12 : Block Op Label signature Reg.count 574 :=
  .letOp (n := 574) (.out 0x10e40f (addR64R64Effect 0x10e40f 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[572, 567]
    (.letOp (n := 575) (.out 0x10e40f (addR64R64Effect 0x10e40f 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[572, 567]
    (.letOp (n := 576) (.exec 0x10e40f (fun s => s.RIP = 0x10e40f) (addR64R64Effect 0x10e40f 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[572, 567]
    (.letOp (n := 577) (.out 0x10e412 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e412 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[568, 575]
    (.letOp (n := 578) (.exec 0x10e412 (fun s => s.RIP = 0x10e412) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e412 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[568, 575]
    (.letOp (n := 579) (.out 0x10e416 (movR64R64Effect 0x10e416 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 580) (.exec 0x10e416 (fun s => s.RIP = 0x10e416) (movR64R64Effect 0x10e416 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 581) (.out 0x10e419 (addR64R64Effect 0x10e419 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[574, 561]
    (.letOp (n := 582) (.out 0x10e419 (addR64R64Effect 0x10e419 1 9) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 9] []) (.flag .CF)) #v[574, 561]
    (.letOp (n := 583) (.exec 0x10e419 (fun s => s.RIP = 0x10e419) (addR64R64Effect 0x10e419 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[574, 561]
    (.letOp (n := 584) (.out 0x10e41c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e41c 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[577, 582]
    (.letOp (n := 585) (.exec 0x10e41c (fun s => s.RIP = 0x10e41c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e41c 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[577, 582]
    (.letOp (n := 586) (.out 0x10e420 (andR64R64Effect 0x10e420 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[391, 581]
    (.letOp (n := 587) (.exec 0x10e420 (fun s => s.RIP = 0x10e420) (andR64R64Effect 0x10e420 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[391, 581]
    (.letOp (n := 588) (.out 0x10e423 (shldR64R64Effect 0x10e423 5 2 1 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[584, 581]
    (.letOp (n := 589) (.exec 0x10e423 (fun s => s.RIP = 0x10e423) (shldR64R64Effect 0x10e423 5 2 1 12) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[584, 581]
    (.letOp (n := 590) (.out 0x10e428 (movR64Imm64Effect 0x10e428 1 0xffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 591) (.exec 0x10e428 (fun s => s.RIP = 0x10e428) (movR64Imm64Effect 0x10e428 1 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 592) (.out 0x10e432 (andR64R64Effect 0x10e432 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[590, 257]
    (.letOp (n := 593) (.exec 0x10e432 (fun s => s.RIP = 0x10e432) (andR64R64Effect 0x10e432 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[590, 257]
    (.letOp (n := 594) (.out 0x10e435 (addR64R64Effect 0x10e435 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[592, 588]
    (.letOp (n := 595) (.exec 0x10e435 (fun s => s.RIP = 0x10e435) (addR64R64Effect 0x10e435 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[592, 588]
    (.letOp (n := 596) (.out 0x10e438 (movR64M64Effect 0x10e438 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 597) (.exec 0x10e438 (LoadPre 0x10e438 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e438 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e438 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 598) (.out 0x10e43d (movR64M64Effect 0x10e43d 2 (.base 7 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[596]
    (.letOp (n := 599) (.exec 0x10e43d (LoadPre 0x10e43d (fun s => AddrMode.addr (.base 7 (.d8 0x48)) s (0x10e43d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e43d 2 (.base 7 (.d8 0x48))) (Reg.operands [.gpr 7] [])) #v[596]
    (.letOp (n := 600) (.exec 0x10e441 (StorePre 0x10e441 4 (fun s => AddrMode.addr (.base 0 (.d8 0x48)) s (0x10e441 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e441 2 (.base 0 (.d8 0x48))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[598, 579]
    (.letOp (n := 601) (.out 0x10e445 (movR64M64Effect 0x10e445 2 (.base 7 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[596]
    (.letOp (n := 602) (.exec 0x10e445 (LoadPre 0x10e445 (fun s => AddrMode.addr (.base 7 (.d8 0x40)) s (0x10e445 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e445 2 (.base 7 (.d8 0x40))) (Reg.operands [.gpr 7] [])) #v[596]
    (.letOp (n := 603) (.exec 0x10e449 (StorePre 0x10e449 4 (fun s => AddrMode.addr (.base 0 (.d8 0x40)) s (0x10e449 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e449 2 (.base 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[601, 579]
    (.letOp (n := 604) (.out 0x10e44d (movR64M64Effect 0x10e44d 2 (.base 7 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[596]
    (.letOp (n := 605) (.exec 0x10e44d (LoadPre 0x10e44d (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x10e44d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e44d 2 (.base 7 (.d8 0x38))) (Reg.operands [.gpr 7] [])) #v[596]
    (.letOp (n := 606) (.exec 0x10e451 (StorePre 0x10e451 4 (fun s => AddrMode.addr (.base 0 (.d8 0x38)) s (0x10e451 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e451 2 (.base 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[604, 579]
    (.letOp (n := 607) (.out 0x10e455 (movR64M64Effect 0x10e455 2 (.base 7 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[596]
    (.letOp (n := 608) (.exec 0x10e455 (LoadPre 0x10e455 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x10e455 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e455 2 (.base 7 (.d8 0x30))) (Reg.operands [.gpr 7] [])) #v[596]
    (.letOp (n := 609) (.exec 0x10e459 (StorePre 0x10e459 4 (fun s => AddrMode.addr (.base 0 (.d8 0x30)) s (0x10e459 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e459 2 (.base 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[607, 579]
    (.letOp (n := 610) (.out 0x10e45d (movR64M64Effect 0x10e45d 2 (.base 7 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[596]
    (.letOp (n := 611) (.exec 0x10e45d (LoadPre 0x10e45d (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x10e45d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e45d 2 (.base 7 (.d8 0x28))) (Reg.operands [.gpr 7] [])) #v[596]
    (b_l10e010_13))))))))))))))))))))))))))))))))))))))

def bytes_l10e010_12 : List UInt8 :=
  [0x48, 0x01, 0xC1, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x89, 0xF8, 0x4C, 0x01, 0xC9, 0x48, 0x83, 0xD2,
    0x00, 0x48, 0x21, 0xCE, 0x48, 0x0F, 0xA4, 0xCA, 0x0C, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x00, 0x00, 0x4C, 0x21, 0xD1, 0x48, 0x01, 0xD1, 0x48, 0x8B, 0x7C, 0x24, 0x48, 0x48, 0x8B,
    0x57, 0x48, 0x48, 0x89, 0x50, 0x48, 0x48, 0x8B, 0x57, 0x40, 0x48, 0x89, 0x50, 0x40, 0x48, 0x8B,
    0x57, 0x38, 0x48, 0x89, 0x50, 0x38, 0x48, 0x8B, 0x57, 0x30, 0x48, 0x89, 0x50, 0x30, 0x48, 0x8B,
    0x57, 0x28] ++ bytes_l10e010_13

theorem code_l10e010_12 : ∀ x ∈ codeRange 0x10e40f bytes_l10e010_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe40f 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_13

def b_l10e010_11 : Block Op Label signature Reg.count 528 :=
  .letOp (n := 528) (.out 0x10e3c0 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e3c0 11 8)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[523, 466, 526]
    (.letOp (n := 529) (.exec 0x10e3c0 (fun s => s.RIP = 0x10e3c0) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e3c0 11 8)) (Reg.operands [.gpr 11, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[523, 466, 526]
    (.letOp (n := 530) (.out 0x10e3c3 (movR64R64Effect 0x10e3c3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[525]
    (.letOp (n := 531) (.exec 0x10e3c3 (fun s => s.RIP = 0x10e3c3) (movR64R64Effect 0x10e3c3 0 15) (Reg.operands [.gpr 15] [])) #v[525]
    (.letOp (n := 532) (.out 0x10e3c6 (andR64R64Effect 0x10e3c6 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[530, 391]
    (.letOp (n := 533) (.exec 0x10e3c6 (fun s => s.RIP = 0x10e3c6) (andR64R64Effect 0x10e3c6 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[530, 391]
    (.letOp (n := 534) (.out 0x10e3c9 (movR64Imm64Effect 0x10e3c9 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 535) (.exec 0x10e3c9 (fun s => s.RIP = 0x10e3c9) (movR64Imm64Effect 0x10e3c9 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 536) (.out 0x10e3d3 (mulR64Effect 0x10e3d3 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[534, 532]
    (.letOp (n := 537) (.out 0x10e3d3 (mulR64Effect 0x10e3d3 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[534, 532]
    (.letOp (n := 538) (.exec 0x10e3d3 (fun s => s.RIP = 0x10e3d3) (mulR64Effect 0x10e3d3 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[534, 532]
    (.letOp (n := 539) (.out 0x10e3d6 (addR64M64Effect 0x10e3d6 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[486, 65]
    (.letOp (n := 540) (.out 0x10e3d6 (addR64M64Effect 0x10e3d6 3 (.sib 4 none 0 .none)) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[486, 65]
    (.letOp (n := 541) (.exec 0x10e3d6 (LoadPre 0x10e3d6 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e3d6 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x10e3d6 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 3, .gpr 4] [])) #v[486, 65]
    (.letOp (n := 542) (.out 0x10e3da (atFlags StatusFlags.CF (adcR64M64Effect 0x10e3da 9 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[484, 65, 540]
    (.letOp (n := 543) (.exec 0x10e3da (LoadPre 0x10e3da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e3da + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e3da 9 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[484, 65, 540]
    (.letOp (n := 544) (.out 0x10e3df (addR64R64Effect 0x10e3df 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[539, 495]
    (.letOp (n := 545) (.out 0x10e3df (addR64R64Effect 0x10e3df 3 5) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 5] []) (.flag .CF)) #v[539, 495]
    (.letOp (n := 546) (.exec 0x10e3df (fun s => s.RIP = 0x10e3df) (addR64R64Effect 0x10e3df 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[539, 495]
    (.letOp (n := 547) (.out 0x10e3e2 (atFlags StatusFlags.CF (adcR64M64Effect 0x10e3e2 9 (.sib 4 none 0 (.d8 0x18)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[542, 65, 545]
    (.letOp (n := 548) (.exec 0x10e3e2 (LoadPre 0x10e3e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e3e2 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e3e2 9 (.sib 4 none 0 (.d8 0x18)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[542, 65, 545]
    (.letOp (n := 549) (.out 0x10e3e7 (addR64R64Effect 0x10e3e7 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[544, 536]
    (.letOp (n := 550) (.out 0x10e3e7 (addR64R64Effect 0x10e3e7 3 0) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 0] []) (.flag .CF)) #v[544, 536]
    (.letOp (n := 551) (.exec 0x10e3e7 (fun s => s.RIP = 0x10e3e7) (addR64R64Effect 0x10e3e7 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[544, 536]
    (.letOp (n := 552) (.out 0x10e3ea (atFlags StatusFlags.CF (adcR64R64Effect 0x10e3ea 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[547, 537, 550]
    (.letOp (n := 553) (.exec 0x10e3ea (fun s => s.RIP = 0x10e3ea) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e3ea 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[547, 537, 550]
    (.letOp (n := 554) (.out 0x10e3ed (addR64R64Effect 0x10e3ed 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[549, 468]
    (.letOp (n := 555) (.out 0x10e3ed (addR64R64Effect 0x10e3ed 3 13) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 13] []) (.flag .CF)) #v[549, 468]
    (.letOp (n := 556) (.exec 0x10e3ed (fun s => s.RIP = 0x10e3ed) (addR64R64Effect 0x10e3ed 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[549, 468]
    (.letOp (n := 557) (.out 0x10e3f0 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e3f0 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[552, 555]
    (.letOp (n := 558) (.exec 0x10e3f0 (fun s => s.RIP = 0x10e3f0) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e3f0 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[552, 555]
    (.letOp (n := 559) (.out 0x10e3f4 (shldR64R64Effect 0x10e3f4 5 11 15 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[528, 525]
    (.letOp (n := 560) (.exec 0x10e3f4 (fun s => s.RIP = 0x10e3f4) (shldR64R64Effect 0x10e3f4 5 11 15 12) (Reg.operands [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[528, 525]
    (.letOp (n := 561) (.out 0x10e3f9 (shldR64R64Effect 0x10e3f9 5 9 3 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[557, 554]
    (.letOp (n := 562) (.exec 0x10e3f9 (fun s => s.RIP = 0x10e3f9) (shldR64R64Effect 0x10e3f9 5 9 3 12) (Reg.operands [.gpr 9, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[557, 554]
    (.letOp (n := 563) (.out 0x10e3fe (andR64R64Effect 0x10e3fe 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[554, 391]
    (.letOp (n := 564) (.exec 0x10e3fe (fun s => s.RIP = 0x10e3fe) (andR64R64Effect 0x10e3fe 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[554, 391]
    (.letOp (n := 565) (.out 0x10e401 (movR64R64Effect 0x10e401 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[559]
    (.letOp (n := 566) (.exec 0x10e401 (fun s => s.RIP = 0x10e401) (movR64R64Effect 0x10e401 0 11) (Reg.operands [.gpr 11] [])) #v[559]
    (.letOp (n := 567) (.out 0x10e404 (mulR64Effect 0x10e404 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[534, 565]
    (.letOp (n := 568) (.out 0x10e404 (mulR64Effect 0x10e404 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[534, 565]
    (.letOp (n := 569) (.exec 0x10e404 (fun s => s.RIP = 0x10e404) (mulR64Effect 0x10e404 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[534, 565]
    (.letOp (n := 570) (.out 0x10e407 (movR64M64Effect 0x10e407 1 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 571) (.exec 0x10e407 (LoadPre 0x10e407 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e407 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e407 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 572) (.out 0x10e40c (andR64R64Effect 0x10e40c 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[570, 391]
    (.letOp (n := 573) (.exec 0x10e40c (fun s => s.RIP = 0x10e40c) (andR64R64Effect 0x10e40c 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[570, 391]
    (b_l10e010_12))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e010_11 : List UInt8 :=
  [0x4D, 0x11, 0xC3, 0x4C, 0x89, 0xF8, 0x48, 0x21, 0xF0, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x03, 0x1C, 0x24, 0x4C, 0x13, 0x4C, 0x24, 0x10, 0x48,
    0x01, 0xEB, 0x4C, 0x13, 0x4C, 0x24, 0x18, 0x48, 0x01, 0xC3, 0x49, 0x11, 0xD1, 0x4C, 0x01, 0xEB,
    0x49, 0x83, 0xD1, 0x00, 0x4D, 0x0F, 0xA4, 0xFB, 0x0C, 0x49, 0x0F, 0xA4, 0xD9, 0x0C, 0x48, 0x21,
    0xF3, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0xE1, 0x48, 0x8B, 0x4C, 0x24, 0x40, 0x48, 0x21, 0xF1] ++ bytes_l10e010_12

theorem code_l10e010_11 : ∀ x ∈ codeRange 0x10e3c0 bytes_l10e010_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe3c0 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_12

def b_l10e010_10 : Block Op Label signature Reg.count 484 :=
  .letOp (n := 484) (.out 0x10e367 (movR64R64Effect 0x10e367 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[482]
    (.letOp (n := 485) (.exec 0x10e367 (fun s => s.RIP = 0x10e367) (movR64R64Effect 0x10e367 9 2) (Reg.operands [.gpr 2] [])) #v[482]
    (.letOp (n := 486) (.out 0x10e36a (movR64R64Effect 0x10e36a 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[481]
    (.letOp (n := 487) (.exec 0x10e36a (fun s => s.RIP = 0x10e36a) (movR64R64Effect 0x10e36a 3 0) (Reg.operands [.gpr 0] [])) #v[481]
    (.letOp (n := 488) (.out 0x10e36d (movR64M64Effect 0x10e36d 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 489) (.exec 0x10e36d (LoadPre 0x10e36d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e36d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e36d 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 490) (.out 0x10e372 (movR64Imm64Effect 0x10e372 1 0x96c28719501ee) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 491) (.exec 0x10e372 (fun s => s.RIP = 0x10e372) (movR64Imm64Effect 0x10e372 1 0x96c28719501ee) (Reg.operands [] [])) #v[]
    (.letOp (n := 492) (.out 0x10e37c (mulR64Effect 0x10e37c 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[490, 488]
    (.letOp (n := 493) (.out 0x10e37c (mulR64Effect 0x10e37c 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[490, 488]
    (.letOp (n := 494) (.exec 0x10e37c (fun s => s.RIP = 0x10e37c) (mulR64Effect 0x10e37c 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[490, 488]
    (.letOp (n := 495) (.out 0x10e37f (movR64R64Effect 0x10e37f 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[492]
    (.letOp (n := 496) (.exec 0x10e37f (fun s => s.RIP = 0x10e37f) (movR64R64Effect 0x10e37f 5 0) (Reg.operands [.gpr 0] [])) #v[492]
    (.letOp (n := 497) (.exec 0x10e382 (StorePre 0x10e382 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e382 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e382 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[493, 65]
    (.letOp (n := 498) (.out 0x10e387 (andR64R64Effect 0x10e387 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[461, 391]
    (.letOp (n := 499) (.exec 0x10e387 (fun s => s.RIP = 0x10e387) (andR64R64Effect 0x10e387 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[461, 391]
    (.letOp (n := 500) (.out 0x10e38a (movR64M64Effect 0x10e38a 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 501) (.exec 0x10e38a (LoadPre 0x10e38a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e38a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e38a 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 502) (.out 0x10e38f (movR64Imm64Effect 0x10e38f 1 0x7ae96a2b657c) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 503) (.exec 0x10e38f (fun s => s.RIP = 0x10e38f) (movR64Imm64Effect 0x10e38f 1 0x7ae96a2b657c) (Reg.operands [] [])) #v[]
    (.letOp (n := 504) (.out 0x10e399 (mulR64Effect 0x10e399 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[502, 500]
    (.letOp (n := 505) (.out 0x10e399 (mulR64Effect 0x10e399 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[502, 500]
    (.letOp (n := 506) (.exec 0x10e399 (fun s => s.RIP = 0x10e399) (mulR64Effect 0x10e399 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[502, 500]
    (.letOp (n := 507) (.out 0x10e39c (movR64R64Effect 0x10e39c 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[505]
    (.letOp (n := 508) (.exec 0x10e39c (fun s => s.RIP = 0x10e39c) (movR64R64Effect 0x10e39c 11 2) (Reg.operands [.gpr 2] [])) #v[505]
    (.letOp (n := 509) (.out 0x10e39f (movR64R64Effect 0x10e39f 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[504]
    (.letOp (n := 510) (.exec 0x10e39f (fun s => s.RIP = 0x10e39f) (movR64R64Effect 0x10e39f 1 0) (Reg.operands [.gpr 0] [])) #v[504]
    (.letOp (n := 511) (.out 0x10e3a2 (movR64M64Effect 0x10e3a2 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 512) (.exec 0x10e3a2 (LoadPre 0x10e3a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e3a2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e3a2 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 513) (.out 0x10e3a7 (movR64Imm64Effect 0x10e3a7 2 0x7106e64479ea) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 514) (.exec 0x10e3a7 (fun s => s.RIP = 0x10e3a7) (movR64Imm64Effect 0x10e3a7 2 0x7106e64479ea) (Reg.operands [] [])) #v[]
    (.letOp (n := 515) (.out 0x10e3b1 (mulR64Effect 0x10e3b1 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[513, 511]
    (.letOp (n := 516) (.out 0x10e3b1 (mulR64Effect 0x10e3b1 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[513, 511]
    (.letOp (n := 517) (.exec 0x10e3b1 (fun s => s.RIP = 0x10e3b1) (mulR64Effect 0x10e3b1 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[513, 511]
    (.letOp (n := 518) (.out 0x10e3b4 (movR64R64Effect 0x10e3b4 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[515]
    (.letOp (n := 519) (.exec 0x10e3b4 (fun s => s.RIP = 0x10e3b4) (movR64R64Effect 0x10e3b4 15 0) (Reg.operands [.gpr 0] [])) #v[515]
    (.letOp (n := 520) (.out 0x10e3b7 (addR64R64Effect 0x10e3b7 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[518, 509]
    (.letOp (n := 521) (.out 0x10e3b7 (addR64R64Effect 0x10e3b7 15 1) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 1] []) (.flag .CF)) #v[518, 509]
    (.letOp (n := 522) (.exec 0x10e3b7 (fun s => s.RIP = 0x10e3b7) (addR64R64Effect 0x10e3b7 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[518, 509]
    (.letOp (n := 523) (.out 0x10e3ba (atFlags StatusFlags.CF (adcR64R64Effect 0x10e3ba 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[507, 516, 521]
    (.letOp (n := 524) (.exec 0x10e3ba (fun s => s.RIP = 0x10e3ba) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e3ba 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[507, 516, 521]
    (.letOp (n := 525) (.out 0x10e3bd (addR64R64Effect 0x10e3bd 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[520, 442]
    (.letOp (n := 526) (.out 0x10e3bd (addR64R64Effect 0x10e3bd 15 14) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 14] []) (.flag .CF)) #v[520, 442]
    (.letOp (n := 527) (.exec 0x10e3bd (fun s => s.RIP = 0x10e3bd) (addR64R64Effect 0x10e3bd 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[520, 442]
    (b_l10e010_11))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e010_10 : List UInt8 :=
  [0x49, 0x89, 0xD1, 0x48, 0x89, 0xC3, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0xB9, 0xEE, 0x01, 0x95,
    0x71, 0x28, 0x6C, 0x09, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC5, 0x48, 0x89, 0x54, 0x24, 0x18,
    0x49, 0x21, 0xF4, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0xB9, 0x7C, 0x65, 0x2B, 0x6A, 0xE9, 0x7A,
    0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC1, 0x48, 0x8B, 0x44, 0x24, 0x30,
    0x48, 0xBA, 0xEA, 0x79, 0x44, 0xE6, 0x06, 0x71, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xC7,
    0x49, 0x01, 0xCF, 0x49, 0x11, 0xD3, 0x4D, 0x01, 0xF7] ++ bytes_l10e010_11

theorem code_l10e010_10 : ∀ x ∈ codeRange 0x10e367 bytes_l10e010_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe367 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_11

def b_l10e010_9 : Block Op Label signature Reg.count 440 :=
  .letOp (n := 440) (.out 0x10e30e (movR64R64Effect 0x10e30e 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[438]
    (.letOp (n := 441) (.exec 0x10e30e (fun s => s.RIP = 0x10e30e) (movR64R64Effect 0x10e30e 14 8) (Reg.operands [.gpr 8] [])) #v[438]
    (.letOp (n := 442) (.out 0x10e311 (shldR64R64Effect 0x10e311 5 14 0 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[440, 435]
    (.letOp (n := 443) (.exec 0x10e311 (fun s => s.RIP = 0x10e311) (shldR64R64Effect 0x10e311 5 14 0 12) (Reg.operands [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[440, 435]
    (.letOp (n := 444) (.out 0x10e316 (andR64R64Effect 0x10e316 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[435, 391]
    (.letOp (n := 445) (.exec 0x10e316 (fun s => s.RIP = 0x10e316) (andR64R64Effect 0x10e316 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[435, 391]
    (.letOp (n := 446) (.out 0x10e319 (movR64Imm64Effect 0x10e319 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 447) (.exec 0x10e319 (fun s => s.RIP = 0x10e319) (movR64Imm64Effect 0x10e319 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 448) (.out 0x10e323 (mulR64Effect 0x10e323 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[446, 444]
    (.letOp (n := 449) (.out 0x10e323 (mulR64Effect 0x10e323 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[446, 444]
    (.letOp (n := 450) (.exec 0x10e323 (fun s => s.RIP = 0x10e323) (mulR64Effect 0x10e323 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[446, 444]
    (.letOp (n := 451) (.out 0x10e326 (addR64M64Effect 0x10e326 12 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[387, 65]
    (.letOp (n := 452) (.out 0x10e326 (addR64M64Effect 0x10e326 12 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 4] []) (.flag .CF)) #v[387, 65]
    (.letOp (n := 453) (.exec 0x10e326 (LoadPre 0x10e326 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e326 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e326 12 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[387, 65]
    (.letOp (n := 454) (.out 0x10e32b (atFlags StatusFlags.CF (adcR64M64Effect 0x10e32b 13 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 13))) #v[389, 65, 452]
    (.letOp (n := 455) (.exec 0x10e32b (LoadPre 0x10e32b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e32b + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e32b 13 (.sib 4 none 0 .none))) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[389, 65, 452]
    (.letOp (n := 456) (.out 0x10e32f (addR64R64Effect 0x10e32f 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[451, 448]
    (.letOp (n := 457) (.out 0x10e32f (addR64R64Effect 0x10e32f 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[451, 448]
    (.letOp (n := 458) (.exec 0x10e32f (fun s => s.RIP = 0x10e32f) (addR64R64Effect 0x10e32f 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[451, 448]
    (.letOp (n := 459) (.out 0x10e332 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e332 13 2)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[454, 449, 457]
    (.letOp (n := 460) (.exec 0x10e332 (fun s => s.RIP = 0x10e332) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e332 13 2)) (Reg.operands [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[454, 449, 457]
    (.letOp (n := 461) (.out 0x10e335 (addR64R64Effect 0x10e335 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 9] []) (.reg (.gpr 12))) #v[456, 369]
    (.letOp (n := 462) (.out 0x10e335 (addR64R64Effect 0x10e335 12 9) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 9] []) (.flag .CF)) #v[456, 369]
    (.letOp (n := 463) (.exec 0x10e335 (fun s => s.RIP = 0x10e335) (addR64R64Effect 0x10e335 12 9) (Reg.operands [.gpr 12, .gpr 9] [])) #v[456, 369]
    (.letOp (n := 464) (.out 0x10e338 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e338 13 11)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[459, 367, 462]
    (.letOp (n := 465) (.exec 0x10e338 (fun s => s.RIP = 0x10e338) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e338 13 11)) (Reg.operands [.gpr 13, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[459, 367, 462]
    (.letOp (n := 466) (.out 0x10e33b (shrR64Effect 0x10e33b 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[438]
    (.letOp (n := 467) (.exec 0x10e33b (fun s => s.RIP = 0x10e33b) (shrR64Effect 0x10e33b 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[438]
    (.letOp (n := 468) (.out 0x10e33f (shldR64R64Effect 0x10e33f 5 13 12 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[464, 461]
    (.letOp (n := 469) (.exec 0x10e33f (fun s => s.RIP = 0x10e33f) (shldR64R64Effect 0x10e33f 5 13 12 12) (Reg.operands [.gpr 13, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[464, 461]
    (.letOp (n := 470) (.out 0x10e344 (movR64M64Effect 0x10e344 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 471) (.exec 0x10e344 (LoadPre 0x10e344 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e344 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e344 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 472) (.out 0x10e349 (mulR64Effect 0x10e349 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[420, 470]
    (.letOp (n := 473) (.out 0x10e349 (mulR64Effect 0x10e349 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[420, 470]
    (.letOp (n := 474) (.exec 0x10e349 (fun s => s.RIP = 0x10e349) (mulR64Effect 0x10e349 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[420, 470]
    (.letOp (n := 475) (.exec 0x10e34c (StorePre 0x10e34c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e34c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e34c 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[473, 65]
    (.letOp (n := 476) (.exec 0x10e351 (StorePre 0x10e351 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e351 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e351 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[472, 65]
    (.letOp (n := 477) (.out 0x10e355 (movR64M64Effect 0x10e355 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 478) (.exec 0x10e355 (LoadPre 0x10e355 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e355 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e355 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 479) (.out 0x10e35a (movR64Imm64Effect 0x10e35a 1 0x7512f58995c13) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 480) (.exec 0x10e35a (fun s => s.RIP = 0x10e35a) (movR64Imm64Effect 0x10e35a 1 0x7512f58995c13) (Reg.operands [] [])) #v[]
    (.letOp (n := 481) (.out 0x10e364 (mulR64Effect 0x10e364 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[479, 477]
    (.letOp (n := 482) (.out 0x10e364 (mulR64Effect 0x10e364 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[479, 477]
    (.letOp (n := 483) (.exec 0x10e364 (fun s => s.RIP = 0x10e364) (mulR64Effect 0x10e364 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[479, 477]
    (b_l10e010_10))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e010_9 : List UInt8 :=
  [0x4D, 0x89, 0xC6, 0x49, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0x21, 0xF0, 0x48, 0xB9, 0x10, 0x3D, 0x00,
    0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x4C, 0x03, 0x64, 0x24, 0x38, 0x4C, 0x13, 0x2C,
    0x24, 0x49, 0x01, 0xC4, 0x49, 0x11, 0xD5, 0x4D, 0x01, 0xCC, 0x4D, 0x11, 0xDD, 0x49, 0xC1, 0xE8,
    0x34, 0x4D, 0x0F, 0xA4, 0xE5, 0x0C, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0xF7, 0xE3, 0x48, 0x89,
    0x54, 0x24, 0x10, 0x48, 0x89, 0x04, 0x24, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0xB9, 0x13, 0x5C,
    0x99, 0x58, 0x2F, 0x51, 0x07, 0x00, 0x48, 0xF7, 0xE1] ++ bytes_l10e010_10

theorem code_l10e010_9 : ∀ x ∈ codeRange 0x10e30e bytes_l10e010_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe30e 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_10

def b_l10e010_8 : Block Op Label signature Reg.count 395 :=
  .letOp (n := 395) (.exec 0x10e2b6 (StorePre 0x10e2b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e2b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e2b6 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[393, 65]
    (.letOp (n := 396) (.out 0x10e2bb (movR64M64Effect 0x10e2bb 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 397) (.exec 0x10e2bb (LoadPre 0x10e2bb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e2bb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e2bb 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 398) (.out 0x10e2c0 (movR64Imm64Effect 0x10e2c0 1 0x7ae96a2b657c) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 399) (.exec 0x10e2c0 (fun s => s.RIP = 0x10e2c0) (movR64Imm64Effect 0x10e2c0 1 0x7ae96a2b657c) (Reg.operands [] [])) #v[]
    (.letOp (n := 400) (.out 0x10e2ca (mulR64Effect 0x10e2ca 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[398, 396]
    (.letOp (n := 401) (.out 0x10e2ca (mulR64Effect 0x10e2ca 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[398, 396]
    (.letOp (n := 402) (.exec 0x10e2ca (fun s => s.RIP = 0x10e2ca) (mulR64Effect 0x10e2ca 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[398, 396]
    (.letOp (n := 403) (.out 0x10e2cd (movR64R64Effect 0x10e2cd 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[401]
    (.letOp (n := 404) (.exec 0x10e2cd (fun s => s.RIP = 0x10e2cd) (movR64R64Effect 0x10e2cd 1 2) (Reg.operands [.gpr 2] [])) #v[401]
    (.letOp (n := 405) (.out 0x10e2d0 (movR64R64Effect 0x10e2d0 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[400]
    (.letOp (n := 406) (.exec 0x10e2d0 (fun s => s.RIP = 0x10e2d0) (movR64R64Effect 0x10e2d0 14 0) (Reg.operands [.gpr 0] [])) #v[400]
    (.letOp (n := 407) (.out 0x10e2d3 (movR64R64Effect 0x10e2d3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[301]
    (.letOp (n := 408) (.exec 0x10e2d3 (fun s => s.RIP = 0x10e2d3) (movR64R64Effect 0x10e2d3 0 8) (Reg.operands [.gpr 8] [])) #v[301]
    (.letOp (n := 409) (.out 0x10e2d6 (movR64Imm64Effect 0x10e2d6 2 0x7106e64479ea) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 410) (.exec 0x10e2d6 (fun s => s.RIP = 0x10e2d6) (movR64Imm64Effect 0x10e2d6 2 0x7106e64479ea) (Reg.operands [] [])) #v[]
    (.letOp (n := 411) (.out 0x10e2e0 (mulR64Effect 0x10e2e0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[409, 407]
    (.letOp (n := 412) (.out 0x10e2e0 (mulR64Effect 0x10e2e0 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[409, 407]
    (.letOp (n := 413) (.exec 0x10e2e0 (fun s => s.RIP = 0x10e2e0) (mulR64Effect 0x10e2e0 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[409, 407]
    (.letOp (n := 414) (.out 0x10e2e3 (movR64R64Effect 0x10e2e3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[412]
    (.letOp (n := 415) (.exec 0x10e2e3 (fun s => s.RIP = 0x10e2e3) (movR64R64Effect 0x10e2e3 8 2) (Reg.operands [.gpr 2] [])) #v[412]
    (.letOp (n := 416) (.out 0x10e2e6 (movR64R64Effect 0x10e2e6 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[411]
    (.letOp (n := 417) (.exec 0x10e2e6 (fun s => s.RIP = 0x10e2e6) (movR64R64Effect 0x10e2e6 15 0) (Reg.operands [.gpr 0] [])) #v[411]
    (.letOp (n := 418) (.out 0x10e2e9 (movR64M64Effect 0x10e2e9 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 419) (.exec 0x10e2e9 (LoadPre 0x10e2e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e2e9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e2e9 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 420) (.out 0x10e2ee (movR64Imm64Effect 0x10e2ee 3 0xc3434e99cf049) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 421) (.exec 0x10e2ee (fun s => s.RIP = 0x10e2ee) (movR64Imm64Effect 0x10e2ee 3 0xc3434e99cf049) (Reg.operands [] [])) #v[]
    (.letOp (n := 422) (.out 0x10e2f8 (mulR64Effect 0x10e2f8 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[420, 418]
    (.letOp (n := 423) (.out 0x10e2f8 (mulR64Effect 0x10e2f8 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[420, 418]
    (.letOp (n := 424) (.exec 0x10e2f8 (fun s => s.RIP = 0x10e2f8) (mulR64Effect 0x10e2f8 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[420, 418]
    (.letOp (n := 425) (.out 0x10e2fb (addR64R64Effect 0x10e2fb 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[416, 405]
    (.letOp (n := 426) (.out 0x10e2fb (addR64R64Effect 0x10e2fb 15 14) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 14] []) (.flag .CF)) #v[416, 405]
    (.letOp (n := 427) (.exec 0x10e2fb (fun s => s.RIP = 0x10e2fb) (addR64R64Effect 0x10e2fb 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[416, 405]
    (.letOp (n := 428) (.out 0x10e2fe (atFlags StatusFlags.CF (adcR64R64Effect 0x10e2fe 8 1)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[414, 403, 426]
    (.letOp (n := 429) (.exec 0x10e2fe (fun s => s.RIP = 0x10e2fe) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e2fe 8 1)) (Reg.operands [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[414, 403, 426]
    (.letOp (n := 430) (.out 0x10e301 (addR64R64Effect 0x10e301 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[422, 425]
    (.letOp (n := 431) (.out 0x10e301 (addR64R64Effect 0x10e301 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[422, 425]
    (.letOp (n := 432) (.exec 0x10e301 (fun s => s.RIP = 0x10e301) (addR64R64Effect 0x10e301 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[422, 425]
    (.letOp (n := 433) (.out 0x10e304 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e304 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[428, 423, 431]
    (.letOp (n := 434) (.exec 0x10e304 (fun s => s.RIP = 0x10e304) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e304 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[428, 423, 431]
    (.letOp (n := 435) (.out 0x10e307 (addR64R64Effect 0x10e307 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[430, 343]
    (.letOp (n := 436) (.out 0x10e307 (addR64R64Effect 0x10e307 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[430, 343]
    (.letOp (n := 437) (.exec 0x10e307 (fun s => s.RIP = 0x10e307) (addR64R64Effect 0x10e307 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[430, 343]
    (.letOp (n := 438) (.out 0x10e30a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e30a 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[433, 436]
    (.letOp (n := 439) (.exec 0x10e30a (fun s => s.RIP = 0x10e30a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e30a 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[433, 436]
    (b_l10e010_9)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e010_8 : List UInt8 :=
  [0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0xB9, 0x7C, 0x65, 0x2B, 0x6A,
    0xE9, 0x7A, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC6, 0x4C, 0x89, 0xC0,
    0x48, 0xBA, 0xEA, 0x79, 0x44, 0xE6, 0x06, 0x71, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xD0,
    0x49, 0x89, 0xC7, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0xBB, 0x49, 0xF0, 0x9C, 0xE9, 0x34, 0x34,
    0x0C, 0x00, 0x48, 0xF7, 0xE3, 0x4D, 0x01, 0xF7, 0x49, 0x11, 0xC8, 0x4C, 0x01, 0xF8, 0x49, 0x11,
    0xD0, 0x48, 0x01, 0xE8, 0x49, 0x83, 0xD0, 0x00] ++ bytes_l10e010_9

theorem code_l10e010_8 : ∀ x ∈ codeRange 0x10e2b6 bytes_l10e010_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe2b6 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_9

def b_l10e010_7 : Block Op Label signature Reg.count 353 :=
  .letOp (n := 353) (.out 0x10e25a (movR64Imm64Effect 0x10e25a 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 354) (.exec 0x10e25a (fun s => s.RIP = 0x10e25a) (movR64Imm64Effect 0x10e25a 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 355) (.out 0x10e264 (mulR64Effect 0x10e264 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[353, 351]
    (.letOp (n := 356) (.out 0x10e264 (mulR64Effect 0x10e264 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[353, 351]
    (.letOp (n := 357) (.exec 0x10e264 (fun s => s.RIP = 0x10e264) (mulR64Effect 0x10e264 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[353, 351]
    (.letOp (n := 358) (.out 0x10e267 (movR64R64Effect 0x10e267 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[356]
    (.letOp (n := 359) (.exec 0x10e267 (fun s => s.RIP = 0x10e267) (movR64R64Effect 0x10e267 9 2) (Reg.operands [.gpr 2] [])) #v[356]
    (.letOp (n := 360) (.out 0x10e26a (addR64M64Effect 0x10e26a 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[355, 65]
    (.letOp (n := 361) (.out 0x10e26a (addR64M64Effect 0x10e26a 0 (.sib 4 none 0 .none)) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[355, 65]
    (.letOp (n := 362) (.exec 0x10e26a (LoadPre 0x10e26a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e26a + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x10e26a 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[355, 65]
    (.letOp (n := 363) (.out 0x10e26e (atFlags StatusFlags.CF (adcR64M64Effect 0x10e26e 9 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[358, 65, 361]
    (.letOp (n := 364) (.exec 0x10e26e (LoadPre 0x10e26e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e26e + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e26e 9 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[358, 65, 361]
    (.letOp (n := 365) (.out 0x10e273 (movR64R64Effect 0x10e273 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[363]
    (.letOp (n := 366) (.exec 0x10e273 (fun s => s.RIP = 0x10e273) (movR64R64Effect 0x10e273 11 9) (Reg.operands [.gpr 9] [])) #v[363]
    (.letOp (n := 367) (.out 0x10e276 (shrR64Effect 0x10e276 4 11 52) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[365]
    (.letOp (n := 368) (.exec 0x10e276 (fun s => s.RIP = 0x10e276) (shrR64Effect 0x10e276 4 11 52) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[365]
    (.letOp (n := 369) (.out 0x10e27a (shldR64R64Effect 0x10e27a 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[363, 360]
    (.letOp (n := 370) (.exec 0x10e27a (fun s => s.RIP = 0x10e27a) (shldR64R64Effect 0x10e27a 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[363, 360]
    (.letOp (n := 371) (.out 0x10e27f (movR64R64Effect 0x10e27f 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[360]
    (.letOp (n := 372) (.exec 0x10e27f (fun s => s.RIP = 0x10e27f) (movR64R64Effect 0x10e27f 1 0) (Reg.operands [.gpr 0] [])) #v[360]
    (.letOp (n := 373) (.out 0x10e282 (movR64M64Effect 0x10e282 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 374) (.exec 0x10e282 (LoadPre 0x10e282 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e282 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e282 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 375) (.out 0x10e287 (mulR64Effect 0x10e287 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[316, 373]
    (.letOp (n := 376) (.out 0x10e287 (mulR64Effect 0x10e287 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[316, 373]
    (.letOp (n := 377) (.exec 0x10e287 (fun s => s.RIP = 0x10e287) (mulR64Effect 0x10e287 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[316, 373]
    (.letOp (n := 378) (.exec 0x10e28a (StorePre 0x10e28a 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e28a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e28a 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[376, 65]
    (.letOp (n := 379) (.exec 0x10e28e (StorePre 0x10e28e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e28e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e28e 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[375, 65]
    (.letOp (n := 380) (.out 0x10e293 (movR64R64Effect 0x10e293 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[273]
    (.letOp (n := 381) (.exec 0x10e293 (fun s => s.RIP = 0x10e293) (movR64R64Effect 0x10e293 0 13) (Reg.operands [.gpr 13] [])) #v[273]
    (.letOp (n := 382) (.out 0x10e296 (movR64Imm64Effect 0x10e296 2 0x96c28719501ee) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 383) (.exec 0x10e296 (fun s => s.RIP = 0x10e296) (movR64Imm64Effect 0x10e296 2 0x96c28719501ee) (Reg.operands [] [])) #v[]
    (.letOp (n := 384) (.out 0x10e2a0 (mulR64Effect 0x10e2a0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[382, 380]
    (.letOp (n := 385) (.out 0x10e2a0 (mulR64Effect 0x10e2a0 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[382, 380]
    (.letOp (n := 386) (.exec 0x10e2a0 (fun s => s.RIP = 0x10e2a0) (mulR64Effect 0x10e2a0 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[382, 380]
    (.letOp (n := 387) (.out 0x10e2a3 (movR64R64Effect 0x10e2a3 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[384]
    (.letOp (n := 388) (.exec 0x10e2a3 (fun s => s.RIP = 0x10e2a3) (movR64R64Effect 0x10e2a3 12 0) (Reg.operands [.gpr 0] [])) #v[384]
    (.letOp (n := 389) (.out 0x10e2a6 (movR64R64Effect 0x10e2a6 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[385]
    (.letOp (n := 390) (.exec 0x10e2a6 (fun s => s.RIP = 0x10e2a6) (movR64R64Effect 0x10e2a6 13 2) (Reg.operands [.gpr 2] [])) #v[385]
    (.letOp (n := 391) (.out 0x10e2a9 (movR64Imm64Effect 0x10e2a9 6 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 392) (.exec 0x10e2a9 (fun s => s.RIP = 0x10e2a9) (movR64Imm64Effect 0x10e2a9 6 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 393) (.out 0x10e2b3 (andR64R64Effect 0x10e2b3 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[371, 391]
    (.letOp (n := 394) (.exec 0x10e2b3 (fun s => s.RIP = 0x10e2b3) (andR64R64Effect 0x10e2b3 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[371, 391]
    (b_l10e010_8))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e010_7 : List UInt8 :=
  [0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD1,
    0x48, 0x03, 0x04, 0x24, 0x4C, 0x13, 0x4C, 0x24, 0x08, 0x4D, 0x89, 0xCB, 0x49, 0xC1, 0xEB, 0x34,
    0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xC1, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x49, 0xF7, 0xE4,
    0x48, 0x89, 0x14, 0x24, 0x48, 0x89, 0x44, 0x24, 0x38, 0x4C, 0x89, 0xE8, 0x48, 0xBA, 0xEE, 0x01,
    0x95, 0x71, 0x28, 0x6C, 0x09, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD5, 0x48,
    0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xF1] ++ bytes_l10e010_8

theorem code_l10e010_7 : ∀ x ∈ codeRange 0x10e25a bytes_l10e010_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe25a 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_8

def b_l10e010_6 : Block Op Label signature Reg.count 307 :=
  .letOp (n := 307) (.out 0x10e20c (mulR64Effect 0x10e20c 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[305, 303]
    (.letOp (n := 308) (.out 0x10e20c (mulR64Effect 0x10e20c 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[305, 303]
    (.letOp (n := 309) (.exec 0x10e20c (fun s => s.RIP = 0x10e20c) (mulR64Effect 0x10e20c 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[305, 303]
    (.letOp (n := 310) (.out 0x10e20f (movR64R64Effect 0x10e20f 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[308]
    (.letOp (n := 311) (.exec 0x10e20f (fun s => s.RIP = 0x10e20f) (movR64R64Effect 0x10e20f 3 2) (Reg.operands [.gpr 2] [])) #v[308]
    (.letOp (n := 312) (.out 0x10e212 (movR64R64Effect 0x10e212 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[307]
    (.letOp (n := 313) (.exec 0x10e212 (fun s => s.RIP = 0x10e212) (movR64R64Effect 0x10e212 14 0) (Reg.operands [.gpr 0] [])) #v[307]
    (.letOp (n := 314) (.out 0x10e215 (movR64R64Effect 0x10e215 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[98]
    (.letOp (n := 315) (.exec 0x10e215 (fun s => s.RIP = 0x10e215) (movR64R64Effect 0x10e215 0 12) (Reg.operands [.gpr 12] [])) #v[98]
    (.letOp (n := 316) (.out 0x10e218 (movR64Imm64Effect 0x10e218 12 0x7512f58995c13) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 317) (.exec 0x10e218 (fun s => s.RIP = 0x10e218) (movR64Imm64Effect 0x10e218 12 0x7512f58995c13) (Reg.operands [] [])) #v[]
    (.letOp (n := 318) (.out 0x10e222 (mulR64Effect 0x10e222 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[316, 314]
    (.letOp (n := 319) (.out 0x10e222 (mulR64Effect 0x10e222 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[316, 314]
    (.letOp (n := 320) (.exec 0x10e222 (fun s => s.RIP = 0x10e222) (mulR64Effect 0x10e222 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[316, 314]
    (.letOp (n := 321) (.out 0x10e225 (andR32Imm8Effect 0x10e225 3 6 0xf) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[288]
    (.letOp (n := 322) (.exec 0x10e225 (fun s => s.RIP = 0x10e225) (andR32Imm8Effect 0x10e225 3 6 0xf) (Reg.operands [.gpr 6] [])) #v[288]
    (.letOp (n := 323) (.out 0x10e228 (addR64R64Effect 0x10e228 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[299, 282]
    (.letOp (n := 324) (.out 0x10e228 (addR64R64Effect 0x10e228 11 1) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 1] []) (.flag .CF)) #v[299, 282]
    (.letOp (n := 325) (.exec 0x10e228 (fun s => s.RIP = 0x10e228) (addR64R64Effect 0x10e228 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[299, 282]
    (.letOp (n := 326) (.out 0x10e22b (atFlags StatusFlags.CF (adcR64R64Effect 0x10e22b 5 9)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[297, 284, 324]
    (.letOp (n := 327) (.exec 0x10e22b (fun s => s.RIP = 0x10e22b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e22b 5 9)) (Reg.operands [.gpr 5, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[297, 284, 324]
    (.letOp (n := 328) (.out 0x10e22e (addR64R64Effect 0x10e22e 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[323, 312]
    (.letOp (n := 329) (.out 0x10e22e (addR64R64Effect 0x10e22e 11 14) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 14] []) (.flag .CF)) #v[323, 312]
    (.letOp (n := 330) (.exec 0x10e22e (fun s => s.RIP = 0x10e22e) (addR64R64Effect 0x10e22e 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[323, 312]
    (.letOp (n := 331) (.out 0x10e231 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e231 5 3)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[326, 310, 329]
    (.letOp (n := 332) (.exec 0x10e231 (fun s => s.RIP = 0x10e231) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e231 5 3)) (Reg.operands [.gpr 5, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[326, 310, 329]
    (.letOp (n := 333) (.out 0x10e234 (addR64R64Effect 0x10e234 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[318, 328]
    (.letOp (n := 334) (.out 0x10e234 (addR64R64Effect 0x10e234 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[318, 328]
    (.letOp (n := 335) (.exec 0x10e234 (fun s => s.RIP = 0x10e234) (addR64R64Effect 0x10e234 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[318, 328]
    (.letOp (n := 336) (.out 0x10e237 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e237 5 2)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[331, 319, 334]
    (.letOp (n := 337) (.exec 0x10e237 (fun s => s.RIP = 0x10e237) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e237 5 2)) (Reg.operands [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[331, 319, 334]
    (.letOp (n := 338) (.out 0x10e23a (addR64R64Effect 0x10e23a 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[333, 262]
    (.letOp (n := 339) (.out 0x10e23a (addR64R64Effect 0x10e23a 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[333, 262]
    (.letOp (n := 340) (.exec 0x10e23a (fun s => s.RIP = 0x10e23a) (addR64R64Effect 0x10e23a 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[333, 262]
    (.letOp (n := 341) (.out 0x10e23d (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e23d 5 0x0)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[336, 339]
    (.letOp (n := 342) (.exec 0x10e23d (fun s => s.RIP = 0x10e23d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e23d 5 0x0)) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[336, 339]
    (.letOp (n := 343) (.out 0x10e241 (shldR64R64Effect 0x10e241 5 5 0 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[341, 338]
    (.letOp (n := 344) (.exec 0x10e241 (fun s => s.RIP = 0x10e241) (shldR64R64Effect 0x10e241 5 5 0 12) (Reg.operands [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[341, 338]
    (.letOp (n := 345) (.out 0x10e246 (shlR64Effect 0x10e246 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[338]
    (.letOp (n := 346) (.exec 0x10e246 (fun s => s.RIP = 0x10e246) (shlR64Effect 0x10e246 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[338]
    (.letOp (n := 347) (.out 0x10e24a (movR64Imm64Effect 0x10e24a 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 348) (.exec 0x10e24a (fun s => s.RIP = 0x10e24a) (movR64Imm64Effect 0x10e24a 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 349) (.out 0x10e254 (andR64R64Effect 0x10e254 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[345, 347]
    (.letOp (n := 350) (.exec 0x10e254 (fun s => s.RIP = 0x10e254) (andR64R64Effect 0x10e254 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[345, 347]
    (.letOp (n := 351) (.out 0x10e257 (orR64R64Effect 0x10e257 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[349, 321]
    (.letOp (n := 352) (.exec 0x10e257 (fun s => s.RIP = 0x10e257) (orR64R64Effect 0x10e257 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[349, 321]
    (b_l10e010_7))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e010_6 : List UInt8 :=
  [0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC6, 0x4C, 0x89, 0xE0, 0x49, 0xBC, 0x13, 0x5C,
    0x99, 0x58, 0x2F, 0x51, 0x07, 0x00, 0x49, 0xF7, 0xE4, 0x83, 0xE6, 0x0F, 0x49, 0x01, 0xCB, 0x4C,
    0x11, 0xCD, 0x4D, 0x01, 0xF3, 0x48, 0x11, 0xDD, 0x4C, 0x01, 0xD8, 0x48, 0x11, 0xD5, 0x4C, 0x01,
    0xF8, 0x48, 0x83, 0xD5, 0x00, 0x48, 0x0F, 0xA4, 0xC5, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xB9,
    0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x48, 0x09, 0xF0] ++ bytes_l10e010_7

theorem code_l10e010_6 : ∀ x ∈ codeRange 0x10e20c bytes_l10e010_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe20c 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_7

def b_l10e010_5 : Block Op Label signature Reg.count 266 :=
  .letOp (n := 266) (.out 0x10e1aa (movR64Imm64Effect 0x10e1aa 1 0x96c28719501ee) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 267) (.exec 0x10e1aa (fun s => s.RIP = 0x10e1aa) (movR64Imm64Effect 0x10e1aa 1 0x96c28719501ee) (Reg.operands [] [])) #v[]
    (.letOp (n := 268) (.out 0x10e1b4 (mulR64Effect 0x10e1b4 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[266, 264]
    (.letOp (n := 269) (.out 0x10e1b4 (mulR64Effect 0x10e1b4 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[266, 264]
    (.letOp (n := 270) (.exec 0x10e1b4 (fun s => s.RIP = 0x10e1b4) (mulR64Effect 0x10e1b4 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[266, 264]
    (.letOp (n := 271) (.exec 0x10e1b7 (StorePre 0x10e1b7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e1b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e1b7 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[269, 65]
    (.letOp (n := 272) (.exec 0x10e1bc (StorePre 0x10e1bc 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e1bc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e1bc 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[268, 65]
    (.letOp (n := 273) (.out 0x10e1c0 (movR64M64Effect 0x10e1c0 13 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 274) (.exec 0x10e1c0 (LoadPre 0x10e1c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e1c0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e1c0 13 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 275) (.out 0x10e1c5 (movR64R64Effect 0x10e1c5 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[273]
    (.letOp (n := 276) (.exec 0x10e1c5 (fun s => s.RIP = 0x10e1c5) (movR64R64Effect 0x10e1c5 0 13) (Reg.operands [.gpr 13] [])) #v[273]
    (.letOp (n := 277) (.out 0x10e1c8 (movR64Imm64Effect 0x10e1c8 1 0x7ae96a2b657c) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 278) (.exec 0x10e1c8 (fun s => s.RIP = 0x10e1c8) (movR64Imm64Effect 0x10e1c8 1 0x7ae96a2b657c) (Reg.operands [] [])) #v[]
    (.letOp (n := 279) (.out 0x10e1d2 (mulR64Effect 0x10e1d2 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[277, 275]
    (.letOp (n := 280) (.out 0x10e1d2 (mulR64Effect 0x10e1d2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[277, 275]
    (.letOp (n := 281) (.exec 0x10e1d2 (fun s => s.RIP = 0x10e1d2) (mulR64Effect 0x10e1d2 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[277, 275]
    (.letOp (n := 282) (.out 0x10e1d5 (movR64R64Effect 0x10e1d5 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[279]
    (.letOp (n := 283) (.exec 0x10e1d5 (fun s => s.RIP = 0x10e1d5) (movR64R64Effect 0x10e1d5 1 0) (Reg.operands [.gpr 0] [])) #v[279]
    (.letOp (n := 284) (.out 0x10e1d8 (movR64R64Effect 0x10e1d8 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[280]
    (.letOp (n := 285) (.exec 0x10e1d8 (fun s => s.RIP = 0x10e1d8) (movR64R64Effect 0x10e1d8 9 2) (Reg.operands [.gpr 2] [])) #v[280]
    (.letOp (n := 286) (.out 0x10e1db (movR64R64Effect 0x10e1db 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[257]
    (.letOp (n := 287) (.exec 0x10e1db (fun s => s.RIP = 0x10e1db) (movR64R64Effect 0x10e1db 6 10) (Reg.operands [.gpr 10] [])) #v[257]
    (.letOp (n := 288) (.out 0x10e1de (shrR64Effect 0x10e1de 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[286]
    (.letOp (n := 289) (.exec 0x10e1de (fun s => s.RIP = 0x10e1de) (shrR64Effect 0x10e1de 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[286]
    (.letOp (n := 290) (.out 0x10e1e2 (movR64M64Effect 0x10e1e2 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 291) (.exec 0x10e1e2 (LoadPre 0x10e1e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e1e2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e1e2 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 292) (.out 0x10e1e7 (movR64Imm64Effect 0x10e1e7 2 0x7106e64479ea) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 293) (.exec 0x10e1e7 (fun s => s.RIP = 0x10e1e7) (movR64Imm64Effect 0x10e1e7 2 0x7106e64479ea) (Reg.operands [] [])) #v[]
    (.letOp (n := 294) (.out 0x10e1f1 (mulR64Effect 0x10e1f1 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[292, 290]
    (.letOp (n := 295) (.out 0x10e1f1 (mulR64Effect 0x10e1f1 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[292, 290]
    (.letOp (n := 296) (.exec 0x10e1f1 (fun s => s.RIP = 0x10e1f1) (mulR64Effect 0x10e1f1 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[292, 290]
    (.letOp (n := 297) (.out 0x10e1f4 (movR64R64Effect 0x10e1f4 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[295]
    (.letOp (n := 298) (.exec 0x10e1f4 (fun s => s.RIP = 0x10e1f4) (movR64R64Effect 0x10e1f4 5 2) (Reg.operands [.gpr 2] [])) #v[295]
    (.letOp (n := 299) (.out 0x10e1f7 (movR64R64Effect 0x10e1f7 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[294]
    (.letOp (n := 300) (.exec 0x10e1f7 (fun s => s.RIP = 0x10e1f7) (movR64R64Effect 0x10e1f7 11 0) (Reg.operands [.gpr 0] [])) #v[294]
    (.letOp (n := 301) (.out 0x10e1fa (movR64M64Effect 0x10e1fa 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 302) (.exec 0x10e1fa (LoadPre 0x10e1fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e1fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e1fa 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 303) (.out 0x10e1ff (movR64R64Effect 0x10e1ff 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[301]
    (.letOp (n := 304) (.exec 0x10e1ff (fun s => s.RIP = 0x10e1ff) (movR64R64Effect 0x10e1ff 0 8) (Reg.operands [.gpr 8] [])) #v[301]
    (.letOp (n := 305) (.out 0x10e202 (movR64Imm64Effect 0x10e202 2 0xc3434e99cf049) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 306) (.exec 0x10e202 (fun s => s.RIP = 0x10e202) (movR64Imm64Effect 0x10e202 2 0xc3434e99cf049) (Reg.operands [] [])) #v[]
    (b_l10e010_6)))))))))))))))))))))))))))))))))))))))))

def bytes_l10e010_5 : List UInt8 :=
  [0x48, 0xB9, 0xEE, 0x01, 0x95, 0x71, 0x28, 0x6C, 0x09, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0x54,
    0x24, 0x08, 0x48, 0x89, 0x04, 0x24, 0x4C, 0x8B, 0x6C, 0x24, 0x28, 0x4C, 0x89, 0xE8, 0x48, 0xB9,
    0x7C, 0x65, 0x2B, 0x6A, 0xE9, 0x7A, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC1, 0x49, 0x89,
    0xD1, 0x4C, 0x89, 0xD6, 0x48, 0xC1, 0xEE, 0x30, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0xBA, 0xEA,
    0x79, 0x44, 0xE6, 0x06, 0x71, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD5, 0x49, 0x89, 0xC3,
    0x4C, 0x8B, 0x44, 0x24, 0x20, 0x4C, 0x89, 0xC0, 0x48, 0xBA, 0x49, 0xF0, 0x9C, 0xE9, 0x34, 0x34,
    0x0C, 0x00] ++ bytes_l10e010_6

theorem code_l10e010_5 : ∀ x ∈ codeRange 0x10e1aa bytes_l10e010_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe1aa 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_6

def b_l10e010_4 : Block Op Label signature Reg.count 218 :=
  .letOp (n := 218) (.out 0x10e161 (mulR64Effect 0x10e161 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[216, 214]
    (.letOp (n := 219) (.out 0x10e161 (mulR64Effect 0x10e161 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[216, 214]
    (.letOp (n := 220) (.exec 0x10e161 (fun s => s.RIP = 0x10e161) (mulR64Effect 0x10e161 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[216, 214]
    (.letOp (n := 221) (.out 0x10e164 (movR64R64Effect 0x10e164 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[219]
    (.letOp (n := 222) (.exec 0x10e164 (fun s => s.RIP = 0x10e164) (movR64R64Effect 0x10e164 11 2) (Reg.operands [.gpr 2] [])) #v[219]
    (.letOp (n := 223) (.out 0x10e167 (movR64R64Effect 0x10e167 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[218]
    (.letOp (n := 224) (.exec 0x10e167 (fun s => s.RIP = 0x10e167) (movR64R64Effect 0x10e167 1 0) (Reg.operands [.gpr 0] [])) #v[218]
    (.letOp (n := 225) (.out 0x10e16a (movR64R64Effect 0x10e16a 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[167]
    (.letOp (n := 226) (.exec 0x10e16a (fun s => s.RIP = 0x10e16a) (movR64R64Effect 0x10e16a 0 9) (Reg.operands [.gpr 9] [])) #v[167]
    (.letOp (n := 227) (.out 0x10e16d (movR64Imm64Effect 0x10e16d 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 228) (.exec 0x10e16d (fun s => s.RIP = 0x10e16d) (movR64Imm64Effect 0x10e16d 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 229) (.out 0x10e177 (mulR64Effect 0x10e177 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[227, 225]
    (.letOp (n := 230) (.out 0x10e177 (mulR64Effect 0x10e177 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[227, 225]
    (.letOp (n := 231) (.exec 0x10e177 (fun s => s.RIP = 0x10e177) (mulR64Effect 0x10e177 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[227, 225]
    (.letOp (n := 232) (.out 0x10e17a (addR64M64Effect 0x10e17a 10 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[189, 65]
    (.letOp (n := 233) (.out 0x10e17a (addR64M64Effect 0x10e17a 10 (.sib 4 none 0 .none)) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[189, 65]
    (.letOp (n := 234) (.exec 0x10e17a (LoadPre 0x10e17a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e17a + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x10e17a 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[189, 65]
    (.letOp (n := 235) (.out 0x10e17e (atFlags StatusFlags.CF (adcR64M64Effect 0x10e17e 15 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 15))) #v[187, 65, 233]
    (.letOp (n := 236) (.exec 0x10e17e (LoadPre 0x10e17e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e17e + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e17e 15 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[187, 65, 233]
    (.letOp (n := 237) (.out 0x10e183 (addR64R64Effect 0x10e183 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[232, 200]
    (.letOp (n := 238) (.out 0x10e183 (addR64R64Effect 0x10e183 10 13) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 13] []) (.flag .CF)) #v[232, 200]
    (.letOp (n := 239) (.exec 0x10e183 (fun s => s.RIP = 0x10e183) (addR64R64Effect 0x10e183 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[232, 200]
    (.letOp (n := 240) (.out 0x10e186 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e186 15 3)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[235, 198, 238]
    (.letOp (n := 241) (.exec 0x10e186 (fun s => s.RIP = 0x10e186) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e186 15 3)) (Reg.operands [.gpr 15, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[235, 198, 238]
    (.letOp (n := 242) (.out 0x10e189 (addR64R64Effect 0x10e189 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[237, 211]
    (.letOp (n := 243) (.out 0x10e189 (addR64R64Effect 0x10e189 10 14) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 14] []) (.flag .CF)) #v[237, 211]
    (.letOp (n := 244) (.exec 0x10e189 (fun s => s.RIP = 0x10e189) (addR64R64Effect 0x10e189 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[237, 211]
    (.letOp (n := 245) (.out 0x10e18c (atFlags StatusFlags.CF (adcR64R64Effect 0x10e18c 15 5)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[240, 209, 243]
    (.letOp (n := 246) (.exec 0x10e18c (fun s => s.RIP = 0x10e18c) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e18c 15 5)) (Reg.operands [.gpr 15, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[240, 209, 243]
    (.letOp (n := 247) (.out 0x10e18f (addR64R64Effect 0x10e18f 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[242, 223]
    (.letOp (n := 248) (.out 0x10e18f (addR64R64Effect 0x10e18f 10 1) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 1] []) (.flag .CF)) #v[242, 223]
    (.letOp (n := 249) (.exec 0x10e18f (fun s => s.RIP = 0x10e18f) (addR64R64Effect 0x10e18f 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[242, 223]
    (.letOp (n := 250) (.out 0x10e192 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e192 15 11)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[245, 221, 248]
    (.letOp (n := 251) (.exec 0x10e192 (fun s => s.RIP = 0x10e192) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e192 15 11)) (Reg.operands [.gpr 15, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[245, 221, 248]
    (.letOp (n := 252) (.out 0x10e195 (addR64R64Effect 0x10e195 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[247, 229]
    (.letOp (n := 253) (.out 0x10e195 (addR64R64Effect 0x10e195 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[247, 229]
    (.letOp (n := 254) (.exec 0x10e195 (fun s => s.RIP = 0x10e195) (addR64R64Effect 0x10e195 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[247, 229]
    (.letOp (n := 255) (.out 0x10e198 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e198 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[250, 230, 253]
    (.letOp (n := 256) (.exec 0x10e198 (fun s => s.RIP = 0x10e198) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e198 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[250, 230, 253]
    (.letOp (n := 257) (.out 0x10e19b (addR64R64Effect 0x10e19b 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[252, 169]
    (.letOp (n := 258) (.out 0x10e19b (addR64R64Effect 0x10e19b 10 8) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 8] []) (.flag .CF)) #v[252, 169]
    (.letOp (n := 259) (.exec 0x10e19b (fun s => s.RIP = 0x10e19b) (addR64R64Effect 0x10e19b 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[252, 169]
    (.letOp (n := 260) (.out 0x10e19e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e19e 15 0x0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[255, 258]
    (.letOp (n := 261) (.exec 0x10e19e (fun s => s.RIP = 0x10e19e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e19e 15 0x0)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[255, 258]
    (.letOp (n := 262) (.out 0x10e1a2 (shldR64R64Effect 0x10e1a2 5 15 10 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[260, 257]
    (.letOp (n := 263) (.exec 0x10e1a2 (fun s => s.RIP = 0x10e1a2) (shldR64R64Effect 0x10e1a2 5 15 10 12) (Reg.operands [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[260, 257]
    (.letOp (n := 264) (.out 0x10e1a7 (movR64R64Effect 0x10e1a7 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[171]
    (.letOp (n := 265) (.exec 0x10e1a7 (fun s => s.RIP = 0x10e1a7) (movR64R64Effect 0x10e1a7 0 6) (Reg.operands [.gpr 6] [])) #v[171]
    (b_l10e010_5))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e010_4 : List UInt8 :=
  [0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC1, 0x4C, 0x89, 0xC8, 0x48, 0xBA, 0x10, 0x3D,
    0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x03, 0x14, 0x24, 0x4C, 0x13, 0x7C,
    0x24, 0x08, 0x4D, 0x01, 0xEA, 0x49, 0x11, 0xDF, 0x4D, 0x01, 0xF2, 0x49, 0x11, 0xEF, 0x49, 0x01,
    0xCA, 0x4D, 0x11, 0xDF, 0x49, 0x01, 0xC2, 0x49, 0x11, 0xD7, 0x4D, 0x01, 0xC2, 0x49, 0x83, 0xD7,
    0x00, 0x4D, 0x0F, 0xA4, 0xD7, 0x0C, 0x48, 0x89, 0xF0] ++ bytes_l10e010_5

theorem code_l10e010_4 : ∀ x ∈ codeRange 0x10e161 bytes_l10e010_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe161 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_5

def b_l10e010_3 : Block Op Label signature Reg.count 178 :=
  .letOp (n := 178) (.exec 0x10e104 (StorePre 0x10e104 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e104 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e104 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[176, 65]
    (.letOp (n := 179) (.exec 0x10e109 (StorePre 0x10e109 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e109 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e109 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[175, 65]
    (.letOp (n := 180) (.out 0x10e10d (movR64R64Effect 0x10e10d 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 181) (.exec 0x10e10d (fun s => s.RIP = 0x10e10d) (movR64R64Effect 0x10e10d 0 15) (Reg.operands [.gpr 15] [])) #v[70]
    (.letOp (n := 182) (.out 0x10e110 (movR64Imm64Effect 0x10e110 1 0x7106e64479ea) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 183) (.exec 0x10e110 (fun s => s.RIP = 0x10e110) (movR64Imm64Effect 0x10e110 1 0x7106e64479ea) (Reg.operands [] [])) #v[]
    (.letOp (n := 184) (.out 0x10e11a (mulR64Effect 0x10e11a 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[182, 180]
    (.letOp (n := 185) (.out 0x10e11a (mulR64Effect 0x10e11a 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[182, 180]
    (.letOp (n := 186) (.exec 0x10e11a (fun s => s.RIP = 0x10e11a) (mulR64Effect 0x10e11a 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[182, 180]
    (.letOp (n := 187) (.out 0x10e11d (movR64R64Effect 0x10e11d 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[185]
    (.letOp (n := 188) (.exec 0x10e11d (fun s => s.RIP = 0x10e11d) (movR64R64Effect 0x10e11d 15 2) (Reg.operands [.gpr 2] [])) #v[185]
    (.letOp (n := 189) (.out 0x10e120 (movR64R64Effect 0x10e120 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[184]
    (.letOp (n := 190) (.exec 0x10e120 (fun s => s.RIP = 0x10e120) (movR64R64Effect 0x10e120 10 0) (Reg.operands [.gpr 0] [])) #v[184]
    (.letOp (n := 191) (.out 0x10e123 (movR64R64Effect 0x10e123 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[72]
    (.letOp (n := 192) (.exec 0x10e123 (fun s => s.RIP = 0x10e123) (movR64R64Effect 0x10e123 0 13) (Reg.operands [.gpr 13] [])) #v[72]
    (.letOp (n := 193) (.out 0x10e126 (movR64Imm64Effect 0x10e126 1 0xc3434e99cf049) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 194) (.exec 0x10e126 (fun s => s.RIP = 0x10e126) (movR64Imm64Effect 0x10e126 1 0xc3434e99cf049) (Reg.operands [] [])) #v[]
    (.letOp (n := 195) (.out 0x10e130 (mulR64Effect 0x10e130 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[193, 191]
    (.letOp (n := 196) (.out 0x10e130 (mulR64Effect 0x10e130 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[193, 191]
    (.letOp (n := 197) (.exec 0x10e130 (fun s => s.RIP = 0x10e130) (mulR64Effect 0x10e130 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[193, 191]
    (.letOp (n := 198) (.out 0x10e133 (movR64R64Effect 0x10e133 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[196]
    (.letOp (n := 199) (.exec 0x10e133 (fun s => s.RIP = 0x10e133) (movR64R64Effect 0x10e133 3 2) (Reg.operands [.gpr 2] [])) #v[196]
    (.letOp (n := 200) (.out 0x10e136 (movR64R64Effect 0x10e136 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[195]
    (.letOp (n := 201) (.exec 0x10e136 (fun s => s.RIP = 0x10e136) (movR64R64Effect 0x10e136 13 0) (Reg.operands [.gpr 0] [])) #v[195]
    (.letOp (n := 202) (.out 0x10e139 (movR64R64Effect 0x10e139 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 203) (.exec 0x10e139 (fun s => s.RIP = 0x10e139) (movR64R64Effect 0x10e139 0 5) (Reg.operands [.gpr 5] [])) #v[74]
    (.letOp (n := 204) (.out 0x10e13c (movR64Imm64Effect 0x10e13c 1 0x7512f58995c13) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 205) (.exec 0x10e13c (fun s => s.RIP = 0x10e13c) (movR64Imm64Effect 0x10e13c 1 0x7512f58995c13) (Reg.operands [] [])) #v[]
    (.letOp (n := 206) (.out 0x10e146 (mulR64Effect 0x10e146 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[204, 202]
    (.letOp (n := 207) (.out 0x10e146 (mulR64Effect 0x10e146 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[204, 202]
    (.letOp (n := 208) (.exec 0x10e146 (fun s => s.RIP = 0x10e146) (mulR64Effect 0x10e146 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[204, 202]
    (.letOp (n := 209) (.out 0x10e149 (movR64R64Effect 0x10e149 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[207]
    (.letOp (n := 210) (.exec 0x10e149 (fun s => s.RIP = 0x10e149) (movR64R64Effect 0x10e149 5 2) (Reg.operands [.gpr 2] [])) #v[207]
    (.letOp (n := 211) (.out 0x10e14c (movR64R64Effect 0x10e14c 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[206]
    (.letOp (n := 212) (.exec 0x10e14c (fun s => s.RIP = 0x10e14c) (movR64R64Effect 0x10e14c 14 0) (Reg.operands [.gpr 0] [])) #v[206]
    (.letOp (n := 213) (.exec 0x10e14f (StorePre 0x10e14f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e14f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e14f 12 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[98, 65]
    (.letOp (n := 214) (.out 0x10e154 (movR64R64Effect 0x10e154 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[98]
    (.letOp (n := 215) (.exec 0x10e154 (fun s => s.RIP = 0x10e154) (movR64R64Effect 0x10e154 0 12) (Reg.operands [.gpr 12] [])) #v[98]
    (.letOp (n := 216) (.out 0x10e157 (movR64Imm64Effect 0x10e157 1 0x96c28719501ee) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 217) (.exec 0x10e157 (fun s => s.RIP = 0x10e157) (movR64Imm64Effect 0x10e157 1 0x96c28719501ee) (Reg.operands [] [])) #v[]
    (b_l10e010_4))))))))))))))))))))))))))))))))))))))))

def bytes_l10e010_3 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x08, 0x48, 0x89, 0x04, 0x24, 0x4C, 0x89, 0xF8, 0x48, 0xB9, 0xEA, 0x79,
    0x44, 0xE6, 0x06, 0x71, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC2, 0x4C,
    0x89, 0xE8, 0x48, 0xB9, 0x49, 0xF0, 0x9C, 0xE9, 0x34, 0x34, 0x0C, 0x00, 0x48, 0xF7, 0xE1, 0x48,
    0x89, 0xD3, 0x49, 0x89, 0xC5, 0x48, 0x89, 0xE8, 0x48, 0xB9, 0x13, 0x5C, 0x99, 0x58, 0x2F, 0x51,
    0x07, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD5, 0x49, 0x89, 0xC6, 0x4C, 0x89, 0x64, 0x24, 0x30,
    0x4C, 0x89, 0xE0, 0x48, 0xB9, 0xEE, 0x01, 0x95, 0x71, 0x28, 0x6C, 0x09, 0x00] ++ bytes_l10e010_4

theorem code_l10e010_3 : ∀ x ∈ codeRange 0x10e104 bytes_l10e010_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe104 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_4

def b_l10e010_2 : Block Op Label signature Reg.count 134 :=
  .letOp (n := 134) (.out 0x10e0ab (addR64R64Effect 0x10e0ab 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[132, 117]
    (.letOp (n := 135) (.out 0x10e0ab (addR64R64Effect 0x10e0ab 11 8) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 8] []) (.flag .CF)) #v[132, 117]
    (.letOp (n := 136) (.exec 0x10e0ab (fun s => s.RIP = 0x10e0ab) (addR64R64Effect 0x10e0ab 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[132, 117]
    (.letOp (n := 137) (.out 0x10e0ae (atFlags StatusFlags.CF (adcR64R64Effect 0x10e0ae 10 1)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[130, 120, 135]
    (.letOp (n := 138) (.exec 0x10e0ae (fun s => s.RIP = 0x10e0ae) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e0ae 10 1)) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[130, 120, 135]
    (.letOp (n := 139) (.out 0x10e0b1 (movR64Imm64Effect 0x10e0b1 14 0x7ae96a2b657c) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 140) (.exec 0x10e0b1 (fun s => s.RIP = 0x10e0b1) (movR64Imm64Effect 0x10e0b1 14 0x7ae96a2b657c) (Reg.operands [] [])) #v[]
    (.letOp (n := 141) (.out 0x10e0bb (movR64R64Effect 0x10e0bb 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[98]
    (.letOp (n := 142) (.exec 0x10e0bb (fun s => s.RIP = 0x10e0bb) (movR64R64Effect 0x10e0bb 0 12) (Reg.operands [.gpr 12] [])) #v[98]
    (.letOp (n := 143) (.out 0x10e0be (mulR64Effect 0x10e0be 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[139, 141]
    (.letOp (n := 144) (.out 0x10e0be (mulR64Effect 0x10e0be 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[139, 141]
    (.letOp (n := 145) (.exec 0x10e0be (fun s => s.RIP = 0x10e0be) (mulR64Effect 0x10e0be 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[139, 141]
    (.letOp (n := 146) (.out 0x10e0c1 (movR64R64Effect 0x10e0c1 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[143]
    (.letOp (n := 147) (.exec 0x10e0c1 (fun s => s.RIP = 0x10e0c1) (movR64R64Effect 0x10e0c1 3 0) (Reg.operands [.gpr 0] [])) #v[143]
    (.letOp (n := 148) (.out 0x10e0c4 (movR64R64Effect 0x10e0c4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[144]
    (.letOp (n := 149) (.exec 0x10e0c4 (fun s => s.RIP = 0x10e0c4) (movR64R64Effect 0x10e0c4 9 2) (Reg.operands [.gpr 2] [])) #v[144]
    (.letOp (n := 150) (.out 0x10e0c7 (movR64Imm64Effect 0x10e0c7 0 0xffffffffffffc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 151) (.exec 0x10e0c7 (fun s => s.RIP = 0x10e0c7) (movR64Imm64Effect 0x10e0c7 0 0xffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 152) (.out 0x10e0d1 (andR64R64Effect 0x10e0d1 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[150, 146]
    (.letOp (n := 153) (.exec 0x10e0d1 (fun s => s.RIP = 0x10e0d1) (andR64R64Effect 0x10e0d1 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[150, 146]
    (.letOp (n := 154) (.out 0x10e0d4 (movR64Imm64Effect 0x10e0d4 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 155) (.exec 0x10e0d4 (fun s => s.RIP = 0x10e0d4) (movR64Imm64Effect 0x10e0d4 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 156) (.out 0x10e0de (mulR64Effect 0x10e0de 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[154, 152]
    (.letOp (n := 157) (.out 0x10e0de (mulR64Effect 0x10e0de 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[154, 152]
    (.letOp (n := 158) (.exec 0x10e0de (fun s => s.RIP = 0x10e0de) (mulR64Effect 0x10e0de 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[154, 152]
    (.letOp (n := 159) (.out 0x10e0e1 (movR64R64Effect 0x10e0e1 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[157]
    (.letOp (n := 160) (.exec 0x10e0e1 (fun s => s.RIP = 0x10e0e1) (movR64R64Effect 0x10e0e1 8 2) (Reg.operands [.gpr 2] [])) #v[157]
    (.letOp (n := 161) (.out 0x10e0e4 (addR64R64Effect 0x10e0e4 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[156, 134]
    (.letOp (n := 162) (.out 0x10e0e4 (addR64R64Effect 0x10e0e4 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[156, 134]
    (.letOp (n := 163) (.exec 0x10e0e4 (fun s => s.RIP = 0x10e0e4) (addR64R64Effect 0x10e0e4 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[156, 134]
    (.letOp (n := 164) (.exec 0x10e0e7 (StorePre 0x10e0e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e0e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e0e7 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[161, 65]
    (.letOp (n := 165) (.out 0x10e0ec (atFlags StatusFlags.CF (adcR64R64Effect 0x10e0ec 8 10)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[159, 137, 162]
    (.letOp (n := 166) (.exec 0x10e0ec (fun s => s.RIP = 0x10e0ec) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e0ec 8 10)) (Reg.operands [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[159, 137, 162]
    (.letOp (n := 167) (.out 0x10e0ef (shldR64R64Effect 0x10e0ef 5 9 3 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[148, 146]
    (.letOp (n := 168) (.exec 0x10e0ef (fun s => s.RIP = 0x10e0ef) (shldR64R64Effect 0x10e0ef 5 9 3 12) (Reg.operands [.gpr 9, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[148, 146]
    (.letOp (n := 169) (.out 0x10e0f4 (shldR64R64Effect 0x10e0f4 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[165, 161]
    (.letOp (n := 170) (.exec 0x10e0f4 (fun s => s.RIP = 0x10e0f4) (shldR64R64Effect 0x10e0f4 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[165, 161]
    (.letOp (n := 171) (.out 0x10e0f9 (movR64M64Effect 0x10e0f9 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 172) (.exec 0x10e0f9 (LoadPre 0x10e0f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e0f9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e0f9 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 173) (.out 0x10e0fe (movR64R64Effect 0x10e0fe 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[171]
    (.letOp (n := 174) (.exec 0x10e0fe (fun s => s.RIP = 0x10e0fe) (movR64R64Effect 0x10e0fe 0 6) (Reg.operands [.gpr 6] [])) #v[171]
    (.letOp (n := 175) (.out 0x10e101 (mulR64Effect 0x10e101 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[139, 173]
    (.letOp (n := 176) (.out 0x10e101 (mulR64Effect 0x10e101 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[139, 173]
    (.letOp (n := 177) (.exec 0x10e101 (fun s => s.RIP = 0x10e101) (mulR64Effect 0x10e101 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[139, 173]
    (b_l10e010_3))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e010_2 : List UInt8 :=
  [0x4D, 0x01, 0xC3, 0x49, 0x11, 0xCA, 0x49, 0xBE, 0x7C, 0x65, 0x2B, 0x6A, 0xE9, 0x7A, 0x00, 0x00,
    0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0xC3, 0x49, 0x89, 0xD1, 0x48, 0xB8, 0xFC, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD8, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD0, 0x4C, 0x01, 0xD8, 0x48, 0x89, 0x44, 0x24,
    0x40, 0x4D, 0x11, 0xD0, 0x49, 0x0F, 0xA4, 0xD9, 0x0C, 0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x48, 0x8B,
    0x74, 0x24, 0x10, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE6] ++ bytes_l10e010_3

theorem code_l10e010_2 : ∀ x ∈ codeRange 0x10e0ab bytes_l10e010_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe0ab 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_3

def b_l10e010_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x10e05c (mulR64Effect 0x10e05c 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[86, 88]
    (.letOp (n := 92) (.out 0x10e05c (mulR64Effect 0x10e05c 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[86, 88]
    (.letOp (n := 93) (.exec 0x10e05c (fun s => s.RIP = 0x10e05c) (mulR64Effect 0x10e05c 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[86, 88]
    (.letOp (n := 94) (.out 0x10e05f (movR64R64Effect 0x10e05f 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[91]
    (.letOp (n := 95) (.exec 0x10e05f (fun s => s.RIP = 0x10e05f) (movR64R64Effect 0x10e05f 9 0) (Reg.operands [.gpr 0] [])) #v[91]
    (.letOp (n := 96) (.out 0x10e062 (movR64R64Effect 0x10e062 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[92]
    (.letOp (n := 97) (.exec 0x10e062 (fun s => s.RIP = 0x10e062) (movR64R64Effect 0x10e062 10 2) (Reg.operands [.gpr 2] [])) #v[92]
    (.letOp (n := 98) (.out 0x10e065 (movR64M64Effect 0x10e065 12 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 99) (.exec 0x10e065 (LoadPre 0x10e065 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x10e065 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e065 12 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 100) (.out 0x10e069 (addR64R64Effect 0x10e069 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[94, 82]
    (.letOp (n := 101) (.out 0x10e069 (addR64R64Effect 0x10e069 9 1) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 1] []) (.flag .CF)) #v[94, 82]
    (.letOp (n := 102) (.exec 0x10e069 (fun s => s.RIP = 0x10e069) (addR64R64Effect 0x10e069 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[94, 82]
    (.letOp (n := 103) (.out 0x10e06c (atFlags StatusFlags.CF (adcR64R64Effect 0x10e06c 10 8)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[96, 84, 101]
    (.letOp (n := 104) (.exec 0x10e06c (fun s => s.RIP = 0x10e06c) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e06c 10 8)) (Reg.operands [.gpr 10, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[96, 84, 101]
    (.letOp (n := 105) (.out 0x10e06f (movR64Imm64Effect 0x10e06f 1 0x7512f58995c13) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 106) (.exec 0x10e06f (fun s => s.RIP = 0x10e06f) (movR64Imm64Effect 0x10e06f 1 0x7512f58995c13) (Reg.operands [] [])) #v[]
    (.letOp (n := 107) (.out 0x10e079 (movR64R64Effect 0x10e079 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[72]
    (.letOp (n := 108) (.exec 0x10e079 (fun s => s.RIP = 0x10e079) (movR64R64Effect 0x10e079 0 13) (Reg.operands [.gpr 13] [])) #v[72]
    (.letOp (n := 109) (.exec 0x10e07c (StorePre 0x10e07c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e07c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e07c 13 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[72, 65]
    (.letOp (n := 110) (.out 0x10e081 (mulR64Effect 0x10e081 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[105, 107]
    (.letOp (n := 111) (.out 0x10e081 (mulR64Effect 0x10e081 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[105, 107]
    (.letOp (n := 112) (.exec 0x10e081 (fun s => s.RIP = 0x10e081) (mulR64Effect 0x10e081 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[105, 107]
    (.letOp (n := 113) (.out 0x10e084 (movR64R64Effect 0x10e084 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[111]
    (.letOp (n := 114) (.exec 0x10e084 (fun s => s.RIP = 0x10e084) (movR64R64Effect 0x10e084 1 2) (Reg.operands [.gpr 2] [])) #v[111]
    (.letOp (n := 115) (.out 0x10e087 (movR64R64Effect 0x10e087 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[110]
    (.letOp (n := 116) (.exec 0x10e087 (fun s => s.RIP = 0x10e087) (movR64R64Effect 0x10e087 8 0) (Reg.operands [.gpr 0] [])) #v[110]
    (.letOp (n := 117) (.out 0x10e08a (addR64R64Effect 0x10e08a 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[115, 100]
    (.letOp (n := 118) (.out 0x10e08a (addR64R64Effect 0x10e08a 8 9) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 9] []) (.flag .CF)) #v[115, 100]
    (.letOp (n := 119) (.exec 0x10e08a (fun s => s.RIP = 0x10e08a) (addR64R64Effect 0x10e08a 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[115, 100]
    (.letOp (n := 120) (.out 0x10e08d (atFlags StatusFlags.CF (adcR64R64Effect 0x10e08d 1 10)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[113, 103, 118]
    (.letOp (n := 121) (.exec 0x10e08d (fun s => s.RIP = 0x10e08d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e08d 1 10)) (Reg.operands [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[113, 103, 118]
    (.letOp (n := 122) (.out 0x10e090 (movR64Imm64Effect 0x10e090 2 0x96c28719501ee) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 123) (.exec 0x10e090 (fun s => s.RIP = 0x10e090) (movR64Imm64Effect 0x10e090 2 0x96c28719501ee) (Reg.operands [] [])) #v[]
    (.letOp (n := 124) (.out 0x10e09a (movR64R64Effect 0x10e09a 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 125) (.exec 0x10e09a (fun s => s.RIP = 0x10e09a) (movR64R64Effect 0x10e09a 0 5) (Reg.operands [.gpr 5] [])) #v[74]
    (.letOp (n := 126) (.exec 0x10e09d (StorePre 0x10e09d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e09d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e09d 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[74, 65]
    (.letOp (n := 127) (.out 0x10e0a2 (mulR64Effect 0x10e0a2 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[122, 124]
    (.letOp (n := 128) (.out 0x10e0a2 (mulR64Effect 0x10e0a2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[122, 124]
    (.letOp (n := 129) (.exec 0x10e0a2 (fun s => s.RIP = 0x10e0a2) (mulR64Effect 0x10e0a2 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[122, 124]
    (.letOp (n := 130) (.out 0x10e0a5 (movR64R64Effect 0x10e0a5 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[128]
    (.letOp (n := 131) (.exec 0x10e0a5 (fun s => s.RIP = 0x10e0a5) (movR64R64Effect 0x10e0a5 10 2) (Reg.operands [.gpr 2] [])) #v[128]
    (.letOp (n := 132) (.out 0x10e0a8 (movR64R64Effect 0x10e0a8 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[127]
    (.letOp (n := 133) (.exec 0x10e0a8 (fun s => s.RIP = 0x10e0a8) (movR64R64Effect 0x10e0a8 11 0) (Reg.operands [.gpr 0] [])) #v[127]
    (b_l10e010_2)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e010_1 : List UInt8 :=
  [0x48, 0xF7, 0xE2, 0x49, 0x89, 0xC1, 0x49, 0x89, 0xD2, 0x4C, 0x8B, 0x66, 0x20, 0x49, 0x01, 0xC9,
    0x4D, 0x11, 0xC2, 0x48, 0xB9, 0x13, 0x5C, 0x99, 0x58, 0x2F, 0x51, 0x07, 0x00, 0x4C, 0x89, 0xE8,
    0x4C, 0x89, 0x6C, 0x24, 0x18, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC0, 0x4D, 0x01,
    0xC8, 0x4C, 0x11, 0xD1, 0x48, 0xBA, 0xEE, 0x01, 0x95, 0x71, 0x28, 0x6C, 0x09, 0x00, 0x48, 0x89,
    0xE8, 0x48, 0x89, 0x6C, 0x24, 0x20, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC3] ++ bytes_l10e010_2

theorem code_l10e010_1 : ∀ x ∈ codeRange 0x10e05c bytes_l10e010_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe05c 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_2

def b_l10e010 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10e010 (pushR64Effect 0x10e010 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x10e010 (PushPre 0x10e010 1) (pushR64Effect 0x10e010 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x10e011 (pushR64Effect 0x10e011 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x10e011 (PushPre 0x10e011 2) (pushR64Effect 0x10e011 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x10e013 (pushR64Effect 0x10e013 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x10e013 (PushPre 0x10e013 2) (pushR64Effect 0x10e013 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x10e015 (pushR64Effect 0x10e015 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x10e015 (PushPre 0x10e015 2) (pushR64Effect 0x10e015 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x10e017 (pushR64Effect 0x10e017 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x10e017 (PushPre 0x10e017 2) (pushR64Effect 0x10e017 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x10e019 (pushR64Effect 0x10e019 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x10e019 (PushPre 0x10e019 1) (pushR64Effect 0x10e019 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10e01a (subR64Imm8Effect 0x10e01a 4 0x50) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10e01a (fun s => s.RIP = 0x10e01a) (subR64Imm8Effect 0x10e01a 4 0x50) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10e01e (movR64M64Effect 0x10e01e 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 68) (.exec 0x10e01e (LoadPre 0x10e01e (fun s => AddrMode.addr (.base 6 .none) s (0x10e01e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10e01e 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.exec 0x10e021 (StorePre 0x10e021 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e021 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e021 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[67, 65]
    (.letOp (n := 70) (.out 0x10e026 (movR64M64Effect 0x10e026 15 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 71) (.exec 0x10e026 (LoadPre 0x10e026 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10e026 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e026 15 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 72) (.out 0x10e02a (movR64M64Effect 0x10e02a 13 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 73) (.exec 0x10e02a (LoadPre 0x10e02a (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10e02a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e02a 13 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 74) (.out 0x10e02e (movR64M64Effect 0x10e02e 5 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 75) (.exec 0x10e02e (LoadPre 0x10e02e (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10e02e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e02e 5 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 76) (.exec 0x10e032 (StorePre 0x10e032 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e032 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e032 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 65]
    (.letOp (n := 77) (.out 0x10e037 (movR64Imm64Effect 0x10e037 1 0x7106e64479ea) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 78) (.exec 0x10e037 (fun s => s.RIP = 0x10e037) (movR64Imm64Effect 0x10e037 1 0x7106e64479ea) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x10e041 (mulR64Effect 0x10e041 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[77, 67]
    (.letOp (n := 80) (.out 0x10e041 (mulR64Effect 0x10e041 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[77, 67]
    (.letOp (n := 81) (.exec 0x10e041 (fun s => s.RIP = 0x10e041) (mulR64Effect 0x10e041 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[77, 67]
    (.letOp (n := 82) (.out 0x10e044 (movR64R64Effect 0x10e044 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 83) (.exec 0x10e044 (fun s => s.RIP = 0x10e044) (movR64R64Effect 0x10e044 1 0) (Reg.operands [.gpr 0] [])) #v[79]
    (.letOp (n := 84) (.out 0x10e047 (movR64R64Effect 0x10e047 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[80]
    (.letOp (n := 85) (.exec 0x10e047 (fun s => s.RIP = 0x10e047) (movR64R64Effect 0x10e047 8 2) (Reg.operands [.gpr 2] [])) #v[80]
    (.letOp (n := 86) (.out 0x10e04a (movR64Imm64Effect 0x10e04a 2 0xc3434e99cf049) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 87) (.exec 0x10e04a (fun s => s.RIP = 0x10e04a) (movR64Imm64Effect 0x10e04a 2 0xc3434e99cf049) (Reg.operands [] [])) #v[]
    (.letOp (n := 88) (.out 0x10e054 (movR64R64Effect 0x10e054 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 89) (.exec 0x10e054 (fun s => s.RIP = 0x10e054) (movR64R64Effect 0x10e054 0 15) (Reg.operands [.gpr 15] [])) #v[70]
    (.letOp (n := 90) (.exec 0x10e057 (StorePre 0x10e057 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e057 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e057 15 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[70, 65]
    (b_l10e010_1))))))))))))))))))))))))))))))))))))))

def bytes_l10e010 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x50, 0x48, 0x8B,
    0x06, 0x48, 0x89, 0x44, 0x24, 0x10, 0x4C, 0x8B, 0x7E, 0x08, 0x4C, 0x8B, 0x6E, 0x10, 0x48, 0x8B,
    0x6E, 0x18, 0x48, 0x89, 0x74, 0x24, 0x48, 0x48, 0xB9, 0xEA, 0x79, 0x44, 0xE6, 0x06, 0x71, 0x00,
    0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC1, 0x49, 0x89, 0xD0, 0x48, 0xBA, 0x49, 0xF0, 0x9C, 0xE9,
    0x34, 0x34, 0x0C, 0x00, 0x4C, 0x89, 0xF8, 0x4C, 0x89, 0x7C, 0x24, 0x28] ++ bytes_l10e010_1

theorem code_l10e010 : ∀ x ∈ codeRange 0x10e010 bytes_l10e010, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe010 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e010_1

end K256.Proofs.Ecdh.LIR
