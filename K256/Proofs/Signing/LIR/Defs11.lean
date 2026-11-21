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

@[cfg_block] def b_l11543e_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x1154d7 (atFlags (condHolds 4) (setccR8Effect 0x1154d7 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[125, 126]
    (.letOp (n := 129) (.exec 0x1154d7 (fun s => s.RIP = 0x1154d7) (atFlags (condHolds 4) (setccR8Effect 0x1154d7 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[125, 126]
    (.letOp (n := 130) (.out 0x1154da (movR64Imm64Effect 0x1154da 1 0xffffefffffc2e) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 131) (.exec 0x1154da (fun s => s.RIP = 0x1154da) (movR64Imm64Effect 0x1154da 1 0xffffefffffc2e) (Reg.operands [] [])) #v[]
    (.letOp (n := 132) (.out 0x1154e4 (cmpR64R64Effect 0x1154e4 15 1) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 1] []) (.flag .CF)) #v[107, 130]
    (.letOp (n := 133) (.out 0x1154e4 (cmpR64R64Effect 0x1154e4 15 1) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 1] []) (.flag .ZF)) #v[107, 130]
    (.letOp (n := 134) (.exec 0x1154e4 (fun s => s.RIP = 0x1154e4) (cmpR64R64Effect 0x1154e4 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[107, 130]
    (.letOp (n := 135) (.out 0x1154e7 (atFlags (condHolds 7) (setccR8Effect 0x1154e7 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 1))) #v[130, 132, 133]
    (.letOp (n := 136) (.exec 0x1154e7 (fun s => s.RIP = 0x1154e7) (atFlags (condHolds 7) (setccR8Effect 0x1154e7 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[130, 132, 133]
    (.letOp (n := 137) (.out 0x1154ea (andR8R8Effect 0x1154ea 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[135, 128]
    (.letOp (n := 138) (.exec 0x1154ea (fun s => s.RIP = 0x1154ea) (andR8R8Effect 0x1154ea 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[135, 128]
    (.letOp (n := 139) (.out 0x1154ec (movzxR32R8Effect 0x1154ec 3 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[137]
    (.letOp (n := 140) (.exec 0x1154ec (fun s => s.RIP = 0x1154ec) (movzxR32R8Effect 0x1154ec 3 7 1) (Reg.operands [.gpr 1] [])) #v[137]
    (.letOp (n := 141) (.out 0x1154ef (callEffect (fun _ => 0x127d50) 0x1154f4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 142) (.exec 0x1154ef (PushPre 0x1154ef 5) (callEffect (fun _ => 0x127d50) 0x1154f4) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 143) (.const ⟨64, 0x1154f4⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 128), (1, 137), (2, 2), (3, 99), (4, 141), (5, 103), (6, 6), (7, 139), (8, 8), (9, 9), (10, 10), (11, 11), (12, 109), (13, 101), (14, 111), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)] 144⟩ { target := .l1154f4, kept := #v[], arity := rfl, guard := some (Fin.last 143) })))))))))))))))))

def bytes_l11543e_2 : List UInt8 :=
  [0x0F, 0x94, 0xC0, 0x48, 0xB9, 0x2E, 0xFC, 0xFF, 0xFF, 0xFE, 0xFF, 0x0F, 0x00, 0x49, 0x39, 0xCF,
    0x0F, 0x97, 0xC1, 0x20, 0xC1, 0x0F, 0xB6, 0xF9, 0xE8, 0x5C, 0x28, 0x01, 0x00]

theorem code_l11543e_2 : ∀ x ∈ codeRange 0x1154d7 bytes_l11543e_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x154d7 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11543e_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.exec 0x115482 (StorePre 0x115482 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x115482 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115482 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[86, 66]
    (.letOp (n := 89) (.out 0x115487 (movR64M64Effect 0x115487 12 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 90) (.exec 0x115487 (LoadPre 0x115487 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x115487 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x115487 12 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 91) (.out 0x11548b (bswapR64Effect 0x11548b 3 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[89]
    (.letOp (n := 92) (.exec 0x11548b (fun s => s.RIP = 0x11548b) (bswapR64Effect 0x11548b 3 12) (Reg.operands [.gpr 12] [])) #v[89]
    (.letOp (n := 93) (.out 0x11548e (movR64M64Effect 0x11548e 15 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 94) (.exec 0x11548e (LoadPre 0x11548e (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x11548e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11548e 15 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 95) (.out 0x115492 (bswapR64Effect 0x115492 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[93]
    (.letOp (n := 96) (.exec 0x115492 (fun s => s.RIP = 0x115492) (bswapR64Effect 0x115492 3 15) (Reg.operands [.gpr 15] [])) #v[93]
    (.letOp (n := 97) (.out 0x115495 (movR64R64Effect 0x115495 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 14] []) (.reg (.gpr 3))) #v[82]
    (.letOp (n := 98) (.exec 0x115495 (fun s => s.RIP = 0x115495) (movR64R64Effect 0x115495 3 14) (Reg.operands [.gpr 14] [])) #v[82]
    (.letOp (n := 99) (.out 0x115498 (shldR64R64Effect 0x115498 5 3 13 36) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[97, 84]
    (.letOp (n := 100) (.exec 0x115498 (fun s => s.RIP = 0x115498) (shldR64R64Effect 0x115498 5 3 13 36) (Reg.operands [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[97, 84]
    (.letOp (n := 101) (.out 0x11549d (shldR64R64Effect 0x11549d 5 13 12 24) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[84, 91]
    (.letOp (n := 102) (.exec 0x11549d (fun s => s.RIP = 0x11549d) (shldR64R64Effect 0x11549d 5 13 12 24) (Reg.operands [.gpr 13, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[84, 91]
    (.letOp (n := 103) (.out 0x1154a2 (movR64Imm64Effect 0x1154a2 5 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 104) (.exec 0x1154a2 (fun s => s.RIP = 0x1154a2) (movR64Imm64Effect 0x1154a2 5 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 105) (.out 0x1154ac (shldR64R64Effect 0x1154ac 5 12 15 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[91, 95]
    (.letOp (n := 106) (.exec 0x1154ac (fun s => s.RIP = 0x1154ac) (shldR64R64Effect 0x1154ac 5 12 15 12) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91, 95]
    (.letOp (n := 107) (.out 0x1154b1 (andR64R64Effect 0x1154b1 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 5] []) (.reg (.gpr 15))) #v[95, 103]
    (.letOp (n := 108) (.exec 0x1154b1 (fun s => s.RIP = 0x1154b1) (andR64R64Effect 0x1154b1 15 5) (Reg.operands [.gpr 15, .gpr 5] [])) #v[95, 103]
    (.letOp (n := 109) (.out 0x1154b4 (andR64R64Effect 0x1154b4 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[105, 103]
    (.letOp (n := 110) (.exec 0x1154b4 (fun s => s.RIP = 0x1154b4) (andR64R64Effect 0x1154b4 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[105, 103]
    (.letOp (n := 111) (.out 0x1154b7 (shrR64Effect 0x1154b7 4 14 16) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[82]
    (.letOp (n := 112) (.exec 0x1154b7 (fun s => s.RIP = 0x1154b7) (shrR64Effect 0x1154b7 4 14 16) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[82]
    (.letOp (n := 113) (.out 0x1154bb (movR64R64Effect 0x1154bb 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[101]
    (.letOp (n := 114) (.exec 0x1154bb (fun s => s.RIP = 0x1154bb) (movR64R64Effect 0x1154bb 0 13) (Reg.operands [.gpr 13] [])) #v[101]
    (.letOp (n := 115) (.out 0x1154be (andR64R64Effect 0x1154be 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[113, 99]
    (.letOp (n := 116) (.exec 0x1154be (fun s => s.RIP = 0x1154be) (andR64R64Effect 0x1154be 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[113, 99]
    (.letOp (n := 117) (.out 0x1154c1 (andR64R64Effect 0x1154c1 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[115, 109]
    (.letOp (n := 118) (.exec 0x1154c1 (fun s => s.RIP = 0x1154c1) (andR64R64Effect 0x1154c1 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[115, 109]
    (.letOp (n := 119) (.out 0x1154c4 (movR64Imm64Effect 0x1154c4 1 0xffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 120) (.exec 0x1154c4 (fun s => s.RIP = 0x1154c4) (movR64Imm64Effect 0x1154c4 1 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 121) (.out 0x1154ce (xorR64R64Effect 0x1154ce 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[119, 111]
    (.letOp (n := 122) (.exec 0x1154ce (fun s => s.RIP = 0x1154ce) (xorR64R64Effect 0x1154ce 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[119, 111]
    (.letOp (n := 123) (.out 0x1154d1 (xorR64R64Effect 0x1154d1 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[117, 103]
    (.letOp (n := 124) (.exec 0x1154d1 (fun s => s.RIP = 0x1154d1) (xorR64R64Effect 0x1154d1 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[117, 103]
    (.letOp (n := 125) (.out 0x1154d4 (orR64R64Effect 0x1154d4 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[123, 121]
    (.letOp (n := 126) (.out 0x1154d4 (orR64R64Effect 0x1154d4 0 1) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 1] []) (.flag .ZF)) #v[123, 121]
    (.letOp (n := 127) (.exec 0x1154d4 (fun s => s.RIP = 0x1154d4) (orR64R64Effect 0x1154d4 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[123, 121]
    (b_l11543e_2))))))))))))))))))))))))))))))))))))))))

def bytes_l11543e_1 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x60, 0x4C, 0x8B, 0x66, 0x10, 0x49, 0x0F, 0xCC, 0x4C, 0x8B, 0x7E, 0x18,
    0x49, 0x0F, 0xCF, 0x4C, 0x89, 0xF3, 0x4C, 0x0F, 0xA4, 0xEB, 0x24, 0x4D, 0x0F, 0xA4, 0xE5, 0x18,
    0x48, 0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4D, 0x0F, 0xA4, 0xFC, 0x0C, 0x49,
    0x21, 0xEF, 0x49, 0x21, 0xEC, 0x49, 0xC1, 0xEE, 0x10, 0x4C, 0x89, 0xE8, 0x48, 0x21, 0xD8, 0x4C,
    0x21, 0xE0, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x4C, 0x31, 0xF1, 0x48,
    0x31, 0xE8, 0x48, 0x09, 0xC8] ++ bytes_l11543e_2

theorem code_l11543e_1 : ∀ x ∈ codeRange 0x115482 bytes_l11543e_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15482 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11543e_2

@[cfg_block] def b_l11543e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11543e (fun s => s.RIP = 0x11543e) (fun _ => nopEffect 0x11543e 2) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.out 0x115440 (pushR64Effect 0x115440 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 55) (.exec 0x115440 (PushPre 0x115440 1) (pushR64Effect 0x115440 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 56) (.out 0x115441 (pushR64Effect 0x115441 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[54, 15]
    (.letOp (n := 57) (.exec 0x115441 (PushPre 0x115441 2) (pushR64Effect 0x115441 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[54, 15]
    (.letOp (n := 58) (.out 0x115443 (pushR64Effect 0x115443 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[56, 14]
    (.letOp (n := 59) (.exec 0x115443 (PushPre 0x115443 2) (pushR64Effect 0x115443 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 60) (.out 0x115445 (pushR64Effect 0x115445 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[58, 13]
    (.letOp (n := 61) (.exec 0x115445 (PushPre 0x115445 2) (pushR64Effect 0x115445 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[58, 13]
    (.letOp (n := 62) (.out 0x115447 (pushR64Effect 0x115447 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[60, 12]
    (.letOp (n := 63) (.exec 0x115447 (PushPre 0x115447 2) (pushR64Effect 0x115447 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[60, 12]
    (.letOp (n := 64) (.out 0x115449 (pushR64Effect 0x115449 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[62, 3]
    (.letOp (n := 65) (.exec 0x115449 (PushPre 0x115449 1) (pushR64Effect 0x115449 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 66) (.out 0x11544a (subR64Imm32Effect 0x11544a 4 0x98) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 67) (.exec 0x11544a (fun s => s.RIP = 0x11544a) (subR64Imm32Effect 0x11544a 4 0x98) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 68) (.exec 0x115451 (StorePre 0x115451 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x115451 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115451 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 66]
    (.letOp (n := 69) (.out 0x115456 (movR64M64Effect 0x115456 0 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 70) (.exec 0x115456 (LoadPre 0x115456 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x115456 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x115456 0 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.exec 0x11545a (StorePre 0x11545a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11545a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11545a 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 66]
    (.letOp (n := 72) (.out 0x11545f (movR64M64Effect 0x11545f 0 (.base 6 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 73) (.exec 0x11545f (LoadPre 0x11545f (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x11545f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11545f 0 (.base 6 (.d8 0x28))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 74) (.exec 0x115463 (StorePre 0x115463 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x115463 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115463 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 66]
    (.letOp (n := 75) (.out 0x115468 (movR64M64Effect 0x115468 0 (.base 6 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 76) (.exec 0x115468 (LoadPre 0x115468 (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x115468 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x115468 0 (.base 6 (.d8 0x30))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.exec 0x11546c (StorePre 0x11546c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11546c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11546c 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 66]
    (.letOp (n := 78) (.out 0x115471 (movR64M64Effect 0x115471 14 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 79) (.exec 0x115471 (LoadPre 0x115471 (fun s => AddrMode.addr (.base 6 .none) s (0x115471 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x115471 14 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 80) (.out 0x115474 (movR64M64Effect 0x115474 13 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 81) (.exec 0x115474 (LoadPre 0x115474 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x115474 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x115474 13 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 82) (.out 0x115478 (bswapR64Effect 0x115478 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[78]
    (.letOp (n := 83) (.exec 0x115478 (fun s => s.RIP = 0x115478) (bswapR64Effect 0x115478 3 14) (Reg.operands [.gpr 14] [])) #v[78]
    (.letOp (n := 84) (.out 0x11547b (bswapR64Effect 0x11547b 3 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[80]
    (.letOp (n := 85) (.exec 0x11547b (fun s => s.RIP = 0x11547b) (bswapR64Effect 0x11547b 3 13) (Reg.operands [.gpr 13] [])) #v[80]
    (.letOp (n := 86) (.out 0x11547e (movR64M64Effect 0x11547e 0 (.base 6 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 87) (.exec 0x11547e (LoadPre 0x11547e (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x11547e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11547e 0 (.base 6 (.d8 0x38))) (Reg.operands [.gpr 6] [])) #v[6]
    (b_l11543e_1)))))))))))))))))))))))))))))))))))

def bytes_l11543e : List UInt8 :=
  [0x66, 0x90, 0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x98,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x7C, 0x24, 0x10, 0x48, 0x8B, 0x46, 0x20, 0x48, 0x89, 0x44, 0x24,
    0x38, 0x48, 0x8B, 0x46, 0x28, 0x48, 0x89, 0x44, 0x24, 0x70, 0x48, 0x8B, 0x46, 0x30, 0x48, 0x89,
    0x44, 0x24, 0x68, 0x4C, 0x8B, 0x36, 0x4C, 0x8B, 0x6E, 0x08, 0x49, 0x0F, 0xCE, 0x49, 0x0F, 0xCD,
    0x48, 0x8B, 0x46, 0x38] ++ bytes_l11543e_1

theorem code_l11543e : ∀ x ∈ codeRange 0x11543e bytes_l11543e, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1543e 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11543e_1

@[cfg_block] def b_l1154f4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1154f4 (notR8Effect 0x1154f4 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x1154f4 (fun s => s.RIP = 0x1154f4) (notR8Effect 0x1154f4 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1154f6 (andAlImm8Effect 0x1154f6 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1154f6 (fun s => s.RIP = 0x1154f6) (andAlImm8Effect 0x1154f6 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1154f8 (movzxR32R8Effect 0x1154f8 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x1154f8 (fun s => s.RIP = 0x1154f8) (movzxR32R8Effect 0x1154f8 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x1154fb (callEffect (fun _ => 0x127d50) 0x115500) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1154fb (PushPre 0x1154fb 5) (callEffect (fun _ => 0x127d50) 0x115500) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x115500⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l115500, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1154f4 : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x50, 0x28, 0x01, 0x00]

theorem code_l1154f4 : ∀ x ∈ codeRange 0x1154f4 bytes_l1154f4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x154f4 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l115500 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x115500 (cmpAlImm8Effect 0x115500 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x115500 (fun s => s.RIP = 0x115500) (cmpAlImm8Effect 0x115500 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11572a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l115508, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l115500 : List UInt8 :=
  [0x3C, 0x01, 0x0F, 0x85, 0x22, 0x02, 0x00, 0x00]

theorem code_l115500 : ∀ x ∈ codeRange 0x115500 bytes_l115500, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15500 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l115508 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x115508 (StorePre 0x115508 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x115508 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x115508 4 0 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x11550c (andR64R64Effect 0x11550c 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[13, 5]
    (.letOp (n := 55) (.exec 0x11550c (fun s => s.RIP = 0x11550c) (andR64R64Effect 0x11550c 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[13, 5]
    (.letOp (n := 56) (.out 0x11550f (andR64R64Effect 0x11550f 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[3, 5]
    (.letOp (n := 57) (.exec 0x11550f (fun s => s.RIP = 0x11550f) (andR64R64Effect 0x11550f 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[3, 5]
    (.letOp (n := 58) (.out 0x115512 (movR64R64Effect 0x115512 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 59) (.exec 0x115512 (fun s => s.RIP = 0x115512) (movR64R64Effect 0x115512 0 3) (Reg.operands [.gpr 3] [])) #v[56]
    (.letOp (n := 60) (.out 0x115515 (orR64R64Effect 0x115515 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[58, 14]
    (.letOp (n := 61) (.exec 0x115515 (fun s => s.RIP = 0x115515) (orR64R64Effect 0x115515 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[58, 14]
    (.letOp (n := 62) (.out 0x115518 (movR64R64Effect 0x115518 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 63) (.exec 0x115518 (fun s => s.RIP = 0x115518) (movR64R64Effect 0x115518 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x11551b (orR64R64Effect 0x11551b 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[62, 54]
    (.letOp (n := 65) (.exec 0x11551b (fun s => s.RIP = 0x11551b) (orR64R64Effect 0x11551b 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[62, 54]
    (.letOp (n := 66) (.out 0x11551e (orR64R64Effect 0x11551e 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[64, 60]
    (.letOp (n := 67) (.exec 0x11551e (fun s => s.RIP = 0x11551e) (orR64R64Effect 0x11551e 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[64, 60]
    (.letOp (n := 68) (.out 0x115521 (xorR32R32Effect 0x115521 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 69) (.exec 0x115521 (fun s => s.RIP = 0x115521) (xorR32R32Effect 0x115521 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 70) (.out 0x115523 (orR64R64Effect 0x115523 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[66, 12]
    (.letOp (n := 71) (.out 0x115523 (orR64R64Effect 0x115523 1 12) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 12] []) (.flag .ZF)) #v[66, 12]
    (.letOp (n := 72) (.exec 0x115523 (fun s => s.RIP = 0x115523) (orR64R64Effect 0x115523 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[66, 12]
    (.letOp (n := 73) (.out 0x115526 (atFlags (condHolds 4) (setccR8Effect 0x115526 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[68, 71]
    (.letOp (n := 74) (.exec 0x115526 (fun s => s.RIP = 0x115526) (atFlags (condHolds 4) (setccR8Effect 0x115526 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[68, 71]
    (.letOp (n := 75) (.out 0x11552a (callEffect (fun _ => 0x127d50) 0x11552f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 76) (.exec 0x11552a (PushPre 0x11552a 5) (callEffect (fun _ => 0x127d50) 0x11552f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.const ⟨64, 0x11552f⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 60), (1, 70), (2, 2), (3, 56), (4, 75), (5, 5), (6, 6), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l11552f, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l115508 : List UInt8 :=
  [0x88, 0x44, 0x24, 0x0F, 0x49, 0x21, 0xED, 0x48, 0x21, 0xEB, 0x48, 0x89, 0xD8, 0x4C, 0x09, 0xF0,
    0x4C, 0x89, 0xF9, 0x4C, 0x09, 0xE9, 0x48, 0x09, 0xC1, 0x31, 0xFF, 0x4C, 0x09, 0xE1, 0x40, 0x0F,
    0x94, 0xC7, 0xE8, 0x21, 0x28, 0x01, 0x00]

theorem code_l115508 : ∀ x ∈ codeRange 0x115508 bytes_l115508, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15508 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11552f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11552f (testR8R8Effect 0x11552f 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x11552f (fun s => s.RIP = 0x11552f) (testR8R8Effect 0x11552f 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11572a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l115537, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11552f : List UInt8 :=
  [0x84, 0xC0, 0x0F, 0x85, 0xF3, 0x01, 0x00, 0x00]

theorem code_l11552f : ∀ x ∈ codeRange 0x11552f bytes_l11552f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1552f 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l115537_2 : Block Op Label signature Reg.count 126 :=
  .letOp (n := 126) (.exec 0x1155db (StorePre 0x1155db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1155db + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1155db 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[124, 4]
    (.letOp (n := 127) (.out 0x1155e0 (xorR32R32Effect 0x1155e0 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[124, 124]
    (.letOp (n := 128) (.exec 0x1155e0 (fun s => s.RIP = 0x1155e0) (xorR32R32Effect 0x1155e0 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[124, 124]
    (.letOp (n := 129) (.out 0x1155e2 (subR64M64Effect 0x1155e2 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[127, 4]
    (.letOp (n := 130) (.exec 0x1155e2 (LoadPre 0x1155e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1155e2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1155e2 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[127, 4]
    (.letOp (n := 131) (.out 0x1155e7 (sarR64Effect 0x1155e7 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[129]
    (.letOp (n := 132) (.exec 0x1155e7 (fun s => s.RIP = 0x1155e7) (sarR64Effect 0x1155e7 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[129]
    (.letOp (n := 133) (.out 0x1155eb (addR64R64Effect 0x1155eb 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[131, 59]
    (.letOp (n := 134) (.exec 0x1155eb (fun s => s.RIP = 0x1155eb) (addR64R64Effect 0x1155eb 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[131, 59]
    (.letOp (n := 135) (.out 0x1155ee (incR64Effect 0x1155ee 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[133]
    (.letOp (n := 136) (.exec 0x1155ee (fun s => s.RIP = 0x1155ee) (incR64Effect 0x1155ee 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[133]
    (.letOp (n := 137) (.out 0x1155f1 (movR64R64Effect 0x1155f1 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 138) (.exec 0x1155f1 (fun s => s.RIP = 0x1155f1) (movR64R64Effect 0x1155f1 2 13) (Reg.operands [.gpr 13] [])) #v[59]
    (.letOp (n := 139) (.out 0x1155f4 (notR64Effect 0x1155f4 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[137]
    (.letOp (n := 140) (.exec 0x1155f4 (fun s => s.RIP = 0x1155f4) (notR64Effect 0x1155f4 2) (Reg.operands [.gpr 2] [])) #v[137]
    (.letOp (n := 141) (.out 0x1155f7 (orR64R64Effect 0x1155f7 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[139, 135]
    (.letOp (n := 142) (.exec 0x1155f7 (fun s => s.RIP = 0x1155f7) (orR64R64Effect 0x1155f7 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[139, 135]
    (.letOp (n := 143) (.out 0x1155fa (shrR64Effect 0x1155fa 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[141]
    (.letOp (n := 144) (.exec 0x1155fa (fun s => s.RIP = 0x1155fa) (shrR64Effect 0x1155fa 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[141]
    (.letOp (n := 145) (.exec 0x1155fe (StorePre 0x1155fe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1155fe + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1155fe 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[143, 4]
    (.letOp (n := 146) (.out 0x115603 (movzxR32M8Effect 0x115603 5 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 147) (.exec 0x115603 (LoadPre 0x115603 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x115603 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x115603 5 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 148) (.out 0x115608 (andAlImm8Effect 0x115608 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[146]
    (.letOp (n := 149) (.exec 0x115608 (fun s => s.RIP = 0x115608) (andAlImm8Effect 0x115608 0x1) (Reg.operands [.gpr 0] [])) #v[146]
    (.letOp (n := 150) (.out 0x11560a (movzxR32R8Effect 0x11560a 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[148]
    (.letOp (n := 151) (.exec 0x11560a (fun s => s.RIP = 0x11560a) (movzxR32R8Effect 0x11560a 3 7 0) (Reg.operands [.gpr 0] [])) #v[148]
    (.letOp (n := 152) (.out 0x11560d (callEffect (fun _ => 0x127d50) 0x115612) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 153) (.exec 0x11560d (PushPre 0x11560d 5) (callEffect (fun _ => 0x127d50) 0x115612) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 154) (.const ⟨64, 0x115612⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 148), (1, 135), (2, 143), (3, 71), (4, 152), (5, 63), (6, 6), (7, 150), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 155⟩ { target := .l115612, kept := #v[], arity := rfl, guard := some (Fin.last 154) }))))))))))))))))))))))))))))))

def bytes_l115537_2 : List UInt8 :=
  [0x48, 0x89, 0x4C, 0x24, 0x18, 0x31, 0xC9, 0x48, 0x2B, 0x4C, 0x24, 0x18, 0x48, 0xC1, 0xF9, 0x3F,
    0x4C, 0x01, 0xE9, 0x48, 0xFF, 0xC1, 0x4C, 0x89, 0xEA, 0x48, 0xF7, 0xD2, 0x48, 0x09, 0xCA, 0x48,
    0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x18, 0x0F, 0xB6, 0x44, 0x24, 0x18, 0x24, 0x01, 0x0F,
    0xB6, 0xF8, 0xE8, 0x3E, 0x27, 0x01, 0x00]

theorem code_l115537_2 : ∀ x ∈ codeRange 0x1155db bytes_l115537_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x155db 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l115537_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.out 0x11558f (xorR32R32Effect 0x11558f 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[83, 83]
    (.letOp (n := 88) (.exec 0x11558f (fun s => s.RIP = 0x11558f) (xorR32R32Effect 0x11558f 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[83, 83]
    (.letOp (n := 89) (.out 0x115591 (subR64M64Effect 0x115591 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[87, 4]
    (.letOp (n := 90) (.exec 0x115591 (LoadPre 0x115591 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x115591 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x115591 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 91) (.out 0x115596 (sarR64Effect 0x115596 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[89]
    (.letOp (n := 92) (.exec 0x115596 (fun s => s.RIP = 0x115596) (sarR64Effect 0x115596 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[89]
    (.letOp (n := 93) (.out 0x11559a (movR64Imm64Effect 0x11559a 2 0x4551231950b75fc5) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 94) (.exec 0x11559a (fun s => s.RIP = 0x11559a) (movR64Imm64Effect 0x11559a 2 0x4551231950b75fc5) (Reg.operands [] [])) #v[]
    (.letOp (n := 95) (.out 0x1155a4 (addR64R64Effect 0x1155a4 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[93, 67]
    (.letOp (n := 96) (.exec 0x1155a4 (fun s => s.RIP = 0x1155a4) (addR64R64Effect 0x1155a4 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[93, 67]
    (.letOp (n := 97) (.out 0x1155a7 (addR64R64Effect 0x1155a7 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[95, 91]
    (.letOp (n := 98) (.exec 0x1155a7 (fun s => s.RIP = 0x1155a7) (addR64R64Effect 0x1155a7 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[95, 91]
    (.letOp (n := 99) (.out 0x1155aa (movR64R64Effect 0x1155aa 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 100) (.exec 0x1155aa (fun s => s.RIP = 0x1155aa) (movR64R64Effect 0x1155aa 1 14) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 101) (.out 0x1155ad (notR64Effect 0x1155ad 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[99]
    (.letOp (n := 102) (.exec 0x1155ad (fun s => s.RIP = 0x1155ad) (notR64Effect 0x1155ad 1) (Reg.operands [.gpr 1] [])) #v[99]
    (.letOp (n := 103) (.out 0x1155b0 (orR64R64Effect 0x1155b0 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[101, 97]
    (.letOp (n := 104) (.exec 0x1155b0 (fun s => s.RIP = 0x1155b0) (orR64R64Effect 0x1155b0 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[101, 97]
    (.letOp (n := 105) (.out 0x1155b3 (shrR64Effect 0x1155b3 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[103]
    (.letOp (n := 106) (.exec 0x1155b3 (fun s => s.RIP = 0x1155b3) (shrR64Effect 0x1155b3 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[103]
    (.letOp (n := 107) (.exec 0x1155b7 (StorePre 0x1155b7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1155b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1155b7 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[105, 4]
    (.letOp (n := 108) (.out 0x1155bc (xorR32R32Effect 0x1155bc 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[105, 105]
    (.letOp (n := 109) (.exec 0x1155bc (fun s => s.RIP = 0x1155bc) (xorR32R32Effect 0x1155bc 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[105, 105]
    (.letOp (n := 110) (.out 0x1155be (subR64M64Effect 0x1155be 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[108, 4]
    (.letOp (n := 111) (.exec 0x1155be (LoadPre 0x1155be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1155be + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1155be 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[108, 4]
    (.letOp (n := 112) (.out 0x1155c3 (sarR64Effect 0x1155c3 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[110]
    (.letOp (n := 113) (.exec 0x1155c3 (fun s => s.RIP = 0x1155c3) (sarR64Effect 0x1155c3 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[110]
    (.letOp (n := 114) (.out 0x1155c7 (movR64R64Effect 0x1155c7 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[63]
    (.letOp (n := 115) (.exec 0x1155c7 (fun s => s.RIP = 0x1155c7) (movR64R64Effect 0x1155c7 2 5) (Reg.operands [.gpr 5] [])) #v[63]
    (.letOp (n := 116) (.out 0x1155ca (notR64Effect 0x1155ca 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[114]
    (.letOp (n := 117) (.exec 0x1155ca (fun s => s.RIP = 0x1155ca) (notR64Effect 0x1155ca 2) (Reg.operands [.gpr 2] [])) #v[114]
    (.letOp (n := 118) (.out 0x1155cd (addR64R64Effect 0x1155cd 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[112, 63]
    (.letOp (n := 119) (.exec 0x1155cd (fun s => s.RIP = 0x1155cd) (addR64R64Effect 0x1155cd 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[112, 63]
    (.letOp (n := 120) (.out 0x1155d0 (addR64Imm8Effect 0x1155d0 1 0x2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[118]
    (.letOp (n := 121) (.exec 0x1155d0 (fun s => s.RIP = 0x1155d0) (addR64Imm8Effect 0x1155d0 1 0x2) (Reg.operands [.gpr 1] [])) #v[118]
    (.letOp (n := 122) (.out 0x1155d4 (orR64R64Effect 0x1155d4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[120, 116]
    (.letOp (n := 123) (.exec 0x1155d4 (fun s => s.RIP = 0x1155d4) (orR64R64Effect 0x1155d4 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[120, 116]
    (.letOp (n := 124) (.out 0x1155d7 (shrR64Effect 0x1155d7 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[122]
    (.letOp (n := 125) (.exec 0x1155d7 (fun s => s.RIP = 0x1155d7) (shrR64Effect 0x1155d7 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[122]
    (b_l115537_2)))))))))))))))))))))))))))))))))))))))

def bytes_l115537_1 : List UInt8 :=
  [0x31, 0xC9, 0x48, 0x2B, 0x4C, 0x24, 0x18, 0x48, 0xC1, 0xF9, 0x3F, 0x48, 0xBA, 0xC5, 0x5F, 0xB7,
    0x50, 0x19, 0x23, 0x51, 0x45, 0x4C, 0x01, 0xF2, 0x48, 0x01, 0xCA, 0x4C, 0x89, 0xF1, 0x48, 0xF7,
    0xD1, 0x48, 0x09, 0xD1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x31, 0xC9, 0x48,
    0x2B, 0x4C, 0x24, 0x18, 0x48, 0xC1, 0xF9, 0x3F, 0x48, 0x89, 0xEA, 0x48, 0xF7, 0xD2, 0x48, 0x01,
    0xE9, 0x48, 0x83, 0xC1, 0x02, 0x48, 0x09, 0xD1, 0x48, 0xC1, 0xE9, 0x3F] ++ bytes_l115537_2

theorem code_l115537_1 : ∀ x ∈ codeRange 0x11558f bytes_l115537_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1558f 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115537_2

@[cfg_block] def b_l115537 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x115537 (StorePre 0x115537 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x115537 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115537 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 54) (.exec 0x11553c (StorePre 0x11553c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11553c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11553c 13 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 55) (.exec 0x115541 (StorePre 0x115541 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x115541 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115541 3 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 56) (.exec 0x115546 (StorePre 0x115546 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x115546 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115546 14 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 57) (.out 0x11554b (movR64M64Effect 0x11554b 13 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 58) (.exec 0x11554b (LoadPre 0x11554b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11554b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11554b 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x115550 (bswapR64Effect 0x115550 3 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 60) (.exec 0x115550 (fun s => s.RIP = 0x115550) (bswapR64Effect 0x115550 3 13) (Reg.operands [.gpr 13] [])) #v[57]
    (.letOp (n := 61) (.out 0x115553 (movR64M64Effect 0x115553 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 62) (.exec 0x115553 (LoadPre 0x115553 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x115553 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115553 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x115558 (bswapR64Effect 0x115558 3 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[61]
    (.letOp (n := 64) (.exec 0x115558 (fun s => s.RIP = 0x115558) (bswapR64Effect 0x115558 3 5) (Reg.operands [.gpr 5] [])) #v[61]
    (.letOp (n := 65) (.out 0x11555b (movR64M64Effect 0x11555b 14 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 66) (.exec 0x11555b (LoadPre 0x11555b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11555b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11555b 14 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x115560 (bswapR64Effect 0x115560 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 68) (.exec 0x115560 (fun s => s.RIP = 0x115560) (bswapR64Effect 0x115560 3 14) (Reg.operands [.gpr 14] [])) #v[65]
    (.letOp (n := 69) (.out 0x115563 (movR64M64Effect 0x115563 3 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 70) (.exec 0x115563 (LoadPre 0x115563 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x115563 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115563 3 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x115568 (bswapR64Effect 0x115568 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[69]
    (.letOp (n := 72) (.exec 0x115568 (fun s => s.RIP = 0x115568) (bswapR64Effect 0x115568 3 3) (Reg.operands [.gpr 3] [])) #v[69]
    (.letOp (n := 73) (.out 0x11556b (movR64Imm64Effect 0x11556b 0 0x402da1732fc9bebf) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 74) (.exec 0x11556b (fun s => s.RIP = 0x11556b) (movR64Imm64Effect 0x11556b 0 0x402da1732fc9bebf) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x115575 (addR64R64Effect 0x115575 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[73, 71]
    (.letOp (n := 76) (.exec 0x115575 (fun s => s.RIP = 0x115575) (addR64R64Effect 0x115575 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[73, 71]
    (.letOp (n := 77) (.out 0x115578 (movR64R64Effect 0x115578 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[71]
    (.letOp (n := 78) (.exec 0x115578 (fun s => s.RIP = 0x115578) (movR64R64Effect 0x115578 1 3) (Reg.operands [.gpr 3] [])) #v[71]
    (.letOp (n := 79) (.out 0x11557b (notR64Effect 0x11557b 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[77]
    (.letOp (n := 80) (.exec 0x11557b (fun s => s.RIP = 0x11557b) (notR64Effect 0x11557b 1) (Reg.operands [.gpr 1] [])) #v[77]
    (.letOp (n := 81) (.out 0x11557e (orR64R64Effect 0x11557e 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[79, 75]
    (.letOp (n := 82) (.exec 0x11557e (fun s => s.RIP = 0x11557e) (orR64R64Effect 0x11557e 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[79, 75]
    (.letOp (n := 83) (.out 0x115581 (shrR64Effect 0x115581 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[81]
    (.letOp (n := 84) (.exec 0x115581 (fun s => s.RIP = 0x115581) (shrR64Effect 0x115581 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.exec 0x115585 (StorePre 0x115585 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x115585 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115585 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 86) (.exec 0x11558a (fun s => s.RIP = 0x11558a) (leaR64Effect 0x11558a 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l115537_1))))))))))))))))))))))))))))))))))

def bytes_l115537 : List UInt8 :=
  [0x4C, 0x89, 0x7C, 0x24, 0x40, 0x4C, 0x89, 0x6C, 0x24, 0x48, 0x48, 0x89, 0x5C, 0x24, 0x50, 0x4C,
    0x89, 0x74, 0x24, 0x58, 0x4C, 0x8B, 0x6C, 0x24, 0x38, 0x49, 0x0F, 0xCD, 0x48, 0x8B, 0x6C, 0x24,
    0x70, 0x48, 0x0F, 0xCD, 0x4C, 0x8B, 0x74, 0x24, 0x68, 0x49, 0x0F, 0xCE, 0x48, 0x8B, 0x5C, 0x24,
    0x60, 0x48, 0x0F, 0xCB, 0x48, 0xB8, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40, 0x48, 0x01,
    0xD8, 0x48, 0x89, 0xD9, 0x48, 0xF7, 0xD1, 0x48, 0x09, 0xC1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89,
    0x4C, 0x24, 0x18, 0x48, 0x8D, 0x44, 0x24, 0x18] ++ bytes_l115537_1

theorem code_l115537 : ∀ x ∈ codeRange 0x115537 bytes_l115537, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15537 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115537_1

@[cfg_block] def b_l115612_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.exec 0x115656 (StorePre 0x115656 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x115656 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115656 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 90) (.exec 0x11565b (StorePre 0x11565b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11565b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11565b 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 91) (.exec 0x115663 (StorePre 0x115663 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x115663 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115663 3 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 92) (.exec 0x11566b (StorePre 0x11566b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11566b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11566b (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 93) (.exec 0x115674 (StorePre 0x115674 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x115674 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x115674 (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 94) (.exec 0x11567d (StorePre 0x11567d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11567d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11567d (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.exec 0x115686 (StorePre 0x115686 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x115686 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x115686 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 96) (.out 0x11568f (leaR64Effect 0x11568f 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 97) (.exec 0x11568f (fun s => s.RIP = 0x11568f) (leaR64Effect 0x11568f 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 98) (.out 0x115694 (leaR64Effect 0x115694 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 99) (.exec 0x115694 (fun s => s.RIP = 0x115694) (leaR64Effect 0x115694 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 100) (.out 0x115699 (movR32Imm32Effect 0x115699 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 101) (.exec 0x115699 (fun s => s.RIP = 0x115699) (movR32Imm32Effect 0x115699 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 102) (.out 0x11569e (movR32Imm32Effect 0x11569e 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 103) (.exec 0x11569e (fun s => s.RIP = 0x11569e) (movR32Imm32Effect 0x11569e 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 104) (.out 0x1156a3 (callEffect (fun _ => 0x127f50) 0x1156a8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 105) (.exec 0x1156a3 (PushPre 0x1156a3 5) (callEffect (fun _ => 0x127f50) 0x1156a8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.const ⟨64, 0x1156a8⟩) #v[]
    (.terminate (.call ⟨.l127f50, RegMap.args [(0, 57), (1, 102), (2, 98), (3, 83), (4, 104), (5, 5), (6, 100), (7, 96), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 85), (14, 73), (15, 53), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)] 107⟩ { target := .l1156a8, kept := #v[], arity := rfl, guard := some (Fin.last 106) })))))))))))))))))))

def bytes_l115612_1 : List UInt8 :=
  [0x48, 0x89, 0x4C, 0x24, 0x38, 0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x9C,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x78, 0x48, 0x8D,
    0x54, 0x24, 0x18, 0xBE, 0x04, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0xE8, 0xA8, 0x28,
    0x01, 0x00]

theorem code_l115612_1 : ∀ x ∈ codeRange 0x115656 bytes_l115612_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15656 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l115612 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x115612 (movR32R32Effect 0x115612 3 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[0]
    (.letOp (n := 54) (.exec 0x115612 (fun s => s.RIP = 0x115612) (movR32R32Effect 0x115612 3 15 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.exec 0x115615 (StorePre 0x115615 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x115615 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x115615 4 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 56) (.exec 0x115619 (fun s => s.RIP = 0x115619) (leaR64Effect 0x115619 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11561e (movzxR32M8Effect 0x11561e 5 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 58) (.exec 0x11561e (LoadPre 0x11561e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11561e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11561e 5 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x115623 (xorR32R32Effect 0x115623 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 60) (.exec 0x115623 (fun s => s.RIP = 0x115623) (xorR32R32Effect 0x115623 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 61) (.out 0x115625 (testR8R8Effect 0x115625 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[57, 57]
    (.letOp (n := 62) (.exec 0x115625 (fun s => s.RIP = 0x115625) (testR8R8Effect 0x115625 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[57, 57]
    (.letOp (n := 63) (.out 0x115627 (atFlags (condHolds 5) (cmovR64R64Effect 0x115627 4 1 3)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[59, 3, 61]
    (.letOp (n := 64) (.exec 0x115627 (fun s => s.RIP = 0x115627) (atFlags (condHolds 5) (cmovR64R64Effect 0x115627 4 1 3)) (Reg.operands [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[59, 3, 61]
    (.letOp (n := 65) (.out 0x11562b (xorR32R32Effect 0x11562b 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 66) (.exec 0x11562b (fun s => s.RIP = 0x11562b) (xorR32R32Effect 0x11562b 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 67) (.out 0x11562d (xorR32R32Effect 0x11562d 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 68) (.exec 0x11562d (fun s => s.RIP = 0x11562d) (xorR32R32Effect 0x11562d 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 69) (.out 0x11562f (testR8R8Effect 0x11562f 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[57, 57]
    (.letOp (n := 70) (.exec 0x11562f (fun s => s.RIP = 0x11562f) (testR8R8Effect 0x11562f 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[57, 57]
    (.letOp (n := 71) (.out 0x115631 (atFlags (condHolds 5) (cmovR64R64Effect 0x115631 4 2 14)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[67, 14, 69]
    (.letOp (n := 72) (.exec 0x115631 (fun s => s.RIP = 0x115631) (atFlags (condHolds 5) (cmovR64R64Effect 0x115631 4 2 14)) (Reg.operands [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[67, 14, 69]
    (.letOp (n := 73) (.out 0x115635 (movR64R64Effect 0x115635 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[63]
    (.letOp (n := 74) (.exec 0x115635 (fun s => s.RIP = 0x115635) (movR64R64Effect 0x115635 14 1) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 75) (.out 0x115638 (xorR32R32Effect 0x115638 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[63, 63]
    (.letOp (n := 76) (.exec 0x115638 (fun s => s.RIP = 0x115638) (xorR32R32Effect 0x115638 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[63, 63]
    (.letOp (n := 77) (.out 0x11563a (testR8R8Effect 0x11563a 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[57, 57]
    (.letOp (n := 78) (.exec 0x11563a (fun s => s.RIP = 0x11563a) (testR8R8Effect 0x11563a 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[57, 57]
    (.letOp (n := 79) (.out 0x11563c (atFlags (condHolds 5) (cmovR64R64Effect 0x11563c 4 1 5)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[75, 5, 77]
    (.letOp (n := 80) (.exec 0x11563c (fun s => s.RIP = 0x11563c) (atFlags (condHolds 5) (cmovR64R64Effect 0x11563c 4 1 5)) (Reg.operands [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[75, 5, 77]
    (.letOp (n := 81) (.out 0x115640 (testR8R8Effect 0x115640 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[57, 57]
    (.letOp (n := 82) (.exec 0x115640 (fun s => s.RIP = 0x115640) (testR8R8Effect 0x115640 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[57, 57]
    (.letOp (n := 83) (.out 0x115642 (atFlags (condHolds 5) (cmovR64R64Effect 0x115642 4 3 13)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 3))) #v[65, 13, 81]
    (.letOp (n := 84) (.exec 0x115642 (fun s => s.RIP = 0x115642) (atFlags (condHolds 5) (cmovR64R64Effect 0x115642 4 3 13)) (Reg.operands [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[65, 13, 81]
    (.letOp (n := 85) (.out 0x115646 (movR64R64Effect 0x115646 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 86) (.exec 0x115646 (fun s => s.RIP = 0x115646) (movR64R64Effect 0x115646 13 2) (Reg.operands [.gpr 2] [])) #v[71]
    (.letOp (n := 87) (.exec 0x115649 (StorePre 0x115649 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x115649 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115649 14 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 88) (.exec 0x11564e (StorePre 0x11564e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11564e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11564e 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[71, 4]
    (b_l115612_1))))))))))))))))))))))))))))))))))))

def bytes_l115612 : List UInt8 :=
  [0x41, 0x89, 0xC7, 0x88, 0x44, 0x24, 0x18, 0x48, 0x8D, 0x44, 0x24, 0x18, 0x0F, 0xB6, 0x44, 0x24,
    0x18, 0x31, 0xC9, 0x84, 0xC0, 0x48, 0x0F, 0x45, 0xCB, 0x31, 0xDB, 0x31, 0xD2, 0x84, 0xC0, 0x49,
    0x0F, 0x45, 0xD6, 0x49, 0x89, 0xCE, 0x31, 0xC9, 0x84, 0xC0, 0x48, 0x0F, 0x45, 0xCD, 0x84, 0xC0,
    0x49, 0x0F, 0x45, 0xDD, 0x49, 0x89, 0xD5, 0x4C, 0x89, 0x74, 0x24, 0x78, 0x48, 0x89, 0x94, 0x24,
    0x80, 0x00, 0x00, 0x00] ++ bytes_l115612_1

theorem code_l115612 : ∀ x ∈ codeRange 0x115612 bytes_l115612, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15612 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115612_1

@[cfg_block] def b_l1156a8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1156a8 (andAlImm8Effect 0x1156a8 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x1156a8 (fun s => s.RIP = 0x1156a8) (andAlImm8Effect 0x1156a8 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1156aa (movzxR32R8Effect 0x1156aa 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x1156aa (fun s => s.RIP = 0x1156aa) (movzxR32R8Effect 0x1156aa 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1156ad (callEffect (fun _ => 0x127d50) 0x1156b2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1156ad (PushPre 0x1156ad 5) (callEffect (fun _ => 0x127d50) 0x1156b2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1156b2⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l1156b2, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1156a8 : List UInt8 :=
  [0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x9E, 0x26, 0x01, 0x00]

theorem code_l1156a8 : ∀ x ∈ codeRange 0x1156a8 bytes_l1156a8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x156a8 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1156b2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1156b2 (notR8Effect 0x1156b2 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x1156b2 (fun s => s.RIP = 0x1156b2) (notR8Effect 0x1156b2 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1156b4 (andAlImm8Effect 0x1156b4 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1156b4 (fun s => s.RIP = 0x1156b4) (andAlImm8Effect 0x1156b4 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1156b6 (movzxR32R8Effect 0x1156b6 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x1156b6 (fun s => s.RIP = 0x1156b6) (movzxR32R8Effect 0x1156b6 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x1156b9 (callEffect (fun _ => 0x127d50) 0x1156be) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1156b9 (PushPre 0x1156b9 5) (callEffect (fun _ => 0x127d50) 0x1156be) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1156be⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1156be, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1156b2 : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x92, 0x26, 0x01, 0x00]

theorem code_l1156b2 : ∀ x ∈ codeRange 0x1156b2 bytes_l1156b2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x156b2 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1156be : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1156be (andR8R8Effect 0x1156be 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[0, 15]
    (.letOp (n := 54) (.exec 0x1156be (fun s => s.RIP = 0x1156be) (andR8R8Effect 0x1156be 3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[0, 15]
    (.letOp (n := 55) (.out 0x1156c1 (movzxR32R8Effect 0x1156c1 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x1156c1 (fun s => s.RIP = 0x1156c1) (movzxR32R8Effect 0x1156c1 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1156c4 (callEffect (fun _ => 0x127d50) 0x1156c9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1156c4 (PushPre 0x1156c4 5) (callEffect (fun _ => 0x127d50) 0x1156c9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1156c9⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l1156c9, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1156be : List UInt8 :=
  [0x44, 0x20, 0xF8, 0x0F, 0xB6, 0xF8, 0xE8, 0x87, 0x26, 0x01, 0x00]

theorem code_l1156be : ∀ x ∈ codeRange 0x1156be bytes_l1156be, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x156be 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1156c9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1156c9 (cmpAlImm8Effect 0x1156c9 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x1156c9 (fun s => s.RIP = 0x1156c9) (cmpAlImm8Effect 0x1156c9 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11572a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1156cd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1156c9 : List UInt8 :=
  [0x3C, 0x01, 0x75, 0x5D]

theorem code_l1156c9 : ∀ x ∈ codeRange 0x1156c9 bytes_l1156c9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x156c9 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1156cd_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.exec 0x11571e (StorePre 0x11571e 4 (fun s => AddrMode.addr (.base 5 (.d8 0x40)) s (0x11571e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11571e 2 (.base 5 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[69, 75]
    (.letOp (n := 87) (.exec 0x115722 (StorePre 0x115722 4 (fun s => AddrMode.addr (.base 5 (.d8 0x48)) s (0x115722 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x115722 1 (.base 5 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[73, 75]
    (.letOp (n := 88) (.out 0x115726 (xorR32R32Effect 0x115726 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[77, 77]
    (.letOp (n := 89) (.exec 0x115726 (fun s => s.RIP = 0x115726) (xorR32R32Effect 0x115726 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[77, 77]
    (.terminate (.br ⟨.l11573c, RegMap.args [(0, 88), (1, 73), (2, 69), (3, 3), (4, 4), (5, 75), (6, 65), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩)))))

def bytes_l1156cd_1 : List UInt8 :=
  [0x48, 0x89, 0x55, 0x40, 0x48, 0x89, 0x4D, 0x48, 0x31, 0xC0, 0xEB, 0x12]

theorem code_l1156cd_1 : ∀ x ∈ codeRange 0x11571e bytes_l1156cd_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1571e 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1156cd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1156cd (movzxR32M8Effect 0x1156cd 5 0 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1156cd (LoadPre 0x1156cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1156cd + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1156cd 5 0 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1156d2 (negR64Effect 0x1156d2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1156d2 (fun s => s.RIP = 0x1156d2) (negR64Effect 0x1156d2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1156d5 (movR64M64Effect 0x1156d5 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x1156d5 (LoadPre 0x1156d5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1156d5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1156d5 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1156da (andR64R64Effect 0x1156da 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x1156da (fun s => s.RIP = 0x1156da) (andR64R64Effect 0x1156da 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x1156dd (andR64R64Effect 0x1156dd 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[12, 55]
    (.letOp (n := 62) (.exec 0x1156dd (fun s => s.RIP = 0x1156dd) (andR64R64Effect 0x1156dd 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[12, 55]
    (.letOp (n := 63) (.out 0x1156e0 (movR64M64Effect 0x1156e0 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 64) (.exec 0x1156e0 (LoadPre 0x1156e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1156e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1156e0 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1156e5 (andR64R64Effect 0x1156e5 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[63, 55]
    (.letOp (n := 66) (.exec 0x1156e5 (fun s => s.RIP = 0x1156e5) (andR64R64Effect 0x1156e5 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[63, 55]
    (.letOp (n := 67) (.out 0x1156e8 (movR64M64Effect 0x1156e8 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x1156e8 (LoadPre 0x1156e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1156e8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1156e8 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x1156ed (andR64R64Effect 0x1156ed 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[67, 55]
    (.letOp (n := 70) (.exec 0x1156ed (fun s => s.RIP = 0x1156ed) (andR64R64Effect 0x1156ed 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[67, 55]
    (.letOp (n := 71) (.out 0x1156f0 (movR64M64Effect 0x1156f0 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 72) (.exec 0x1156f0 (LoadPre 0x1156f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1156f0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1156f0 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x1156f5 (andR64R64Effect 0x1156f5 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[71, 55]
    (.letOp (n := 74) (.exec 0x1156f5 (fun s => s.RIP = 0x1156f5) (andR64R64Effect 0x1156f5 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[71, 55]
    (.letOp (n := 75) (.out 0x1156f8 (movR64M64Effect 0x1156f8 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 76) (.exec 0x1156f8 (LoadPre 0x1156f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1156f8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1156f8 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x1156fd (movR64M64Effect 0x1156fd 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 78) (.exec 0x1156fd (LoadPre 0x1156fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1156fd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1156fd 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x115702 (StorePre 0x115702 4 (fun s => AddrMode.addr (.base 5 (.d8 0x18)) s (0x115702 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x115702 0 (.base 5 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[77, 75]
    (.letOp (n := 80) (.exec 0x115706 (StorePre 0x115706 4 (fun s => AddrMode.addr (.base 5 (.d8 0x20)) s (0x115706 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x115706 3 (.base 5 (.d8 0x20))) (Reg.operands [.gpr 3, .gpr 5] [])) #v[3, 75]
    (.letOp (n := 81) (.exec 0x11570a (StorePre 0x11570a 4 (fun s => AddrMode.addr (.base 5 (.d8 0x8)) s (0x11570a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11570a 14 (.base 5 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 5] [])) #v[14, 75]
    (.letOp (n := 82) (.exec 0x11570e (StorePre 0x11570e 4 (fun s => AddrMode.addr (.base 5 (.d8 0x10)) s (0x11570e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11570e 13 (.base 5 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 5] [])) #v[13, 75]
    (.letOp (n := 83) (.exec 0x115712 (StorePre 0x115712 4 (fun s => AddrMode.addr (.base 5 (.d8 0x28)) s (0x115712 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x115712 7 (.base 5 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 5] [])) #v[59, 75]
    (.letOp (n := 84) (.exec 0x115716 (StorePre 0x115716 4 (fun s => AddrMode.addr (.base 5 (.d8 0x30)) s (0x115716 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x115716 12 (.base 5 (.d8 0x30))) (Reg.operands [.gpr 12, .gpr 5] [])) #v[61, 75]
    (.letOp (n := 85) (.exec 0x11571a (StorePre 0x11571a 4 (fun s => AddrMode.addr (.base 5 (.d8 0x38)) s (0x11571a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11571a 6 (.base 5 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[65, 75]
    (b_l1156cd_1)))))))))))))))))))))))))))))))))

def bytes_l1156cd : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x0F, 0x48, 0xF7, 0xD8, 0x48, 0x8B, 0x7C, 0x24, 0x40, 0x48, 0x21, 0xC7,
    0x49, 0x21, 0xC4, 0x48, 0x8B, 0x74, 0x24, 0x48, 0x48, 0x21, 0xC6, 0x48, 0x8B, 0x54, 0x24, 0x50,
    0x48, 0x21, 0xC2, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0x48, 0x21, 0xC1, 0x48, 0x8B, 0x6C, 0x24, 0x10,
    0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x45, 0x18, 0x48, 0x89, 0x5D, 0x20, 0x4C, 0x89, 0x75,
    0x08, 0x4C, 0x89, 0x6D, 0x10, 0x48, 0x89, 0x7D, 0x28, 0x4C, 0x89, 0x65, 0x30, 0x48, 0x89, 0x75,
    0x38] ++ bytes_l1156cd_1

theorem code_l1156cd : ∀ x ∈ codeRange 0x1156cd bytes_l1156cd, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x156cd 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1156cd_1

@[cfg_block] def b_l11572a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11572a (movR64M64Effect 0x11572a 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x11572a (LoadPre 0x11572a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11572a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11572a 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11572f (StorePre 0x11572f 8 (fun s => AddrMode.addr (.base 5 (.d8 0x8)) s (0x11572f + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x11572f (.base 5 (.d8 0x8)) 0x0) (Reg.operands [.gpr 5] [])) #v[53]
    (.letOp (n := 56) (.out 0x115737 (movR32Imm32Effect 0x115737 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 57) (.exec 0x115737 (fun s => s.RIP = 0x115737) (movR32Imm32Effect 0x115737 5 0 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l11573c, RegMap.args [(0, 56), (1, 1), (2, 2), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l11572a : List UInt8 :=
  [0x48, 0x8B, 0x6C, 0x24, 0x10, 0x48, 0xC7, 0x45, 0x08, 0x00, 0x00, 0x00, 0x00, 0xB8, 0x01, 0x00,
    0x00, 0x00]

theorem code_l11572a : ∀ x ∈ codeRange 0x11572a bytes_l11572a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1572a 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11573c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11573c (StorePre 0x11573c 4 (fun s => AddrMode.addr (.base 5 (.d8 0x0)) s (0x11573c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11573c 0 (.base 5 (.d8 0x0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[0, 5]
    (.letOp (n := 54) (.out 0x115740 (movR64R64Effect 0x115740 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 55) (.exec 0x115740 (fun s => s.RIP = 0x115740) (movR64R64Effect 0x115740 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 56) (.out 0x115743 (addR64Imm32Effect 0x115743 4 0x98) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x115743 (fun s => s.RIP = 0x115743) (addR64Imm32Effect 0x115743 4 0x98) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x11574a (popR64Effect 0x11574a 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[56]
    (.letOp (n := 59) (.out 0x11574a (popR64Effect 0x11574a 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x11574a (PopPre 0x11574a) (popR64Effect 0x11574a 1 3) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x11574b (popR64Effect 0x11574b 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[59]
    (.letOp (n := 62) (.out 0x11574b (popR64Effect 0x11574b 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x11574b (PopPre 0x11574b) (popR64Effect 0x11574b 2 12) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x11574d (popR64Effect 0x11574d 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[62]
    (.letOp (n := 65) (.out 0x11574d (popR64Effect 0x11574d 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x11574d (PopPre 0x11574d) (popR64Effect 0x11574d 2 13) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x11574f (popR64Effect 0x11574f 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 68) (.out 0x11574f (popR64Effect 0x11574f 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x11574f (PopPre 0x11574f) (popR64Effect 0x11574f 2 14) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x115751 (popR64Effect 0x115751 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[68]
    (.letOp (n := 71) (.out 0x115751 (popR64Effect 0x115751 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x115751 (PopPre 0x115751) (popR64Effect 0x115751 2 15) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x115753 (popR64Effect 0x115753 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[71]
    (.letOp (n := 74) (.out 0x115753 (popR64Effect 0x115753 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x115753 (PopPre 0x115753) (popR64Effect 0x115753 1 5) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x115754 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[74]
    (.letOp (n := 77) (.out 0x115754 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x115754 (RetPre 0x115754) (retEffect) (Reg.operands [.gpr 4] [])) #v[74]
    (.terminate (.ret (RegMap.args [(0, 54), (1, 1), (2, 2), (3, 58), (4, 77), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 79) (some ⟨76, by decide⟩))))))))))))))))))))))))))))

def bytes_l11573c : List UInt8 :=
  [0x48, 0x89, 0x45, 0x00, 0x48, 0x89, 0xE8, 0x48, 0x81, 0xC4, 0x98, 0x00, 0x00, 0x00, 0x5B, 0x41,
    0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l11573c : ∀ x ∈ codeRange 0x11573c bytes_l11573c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1573c 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l115950_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.out 0x11599c (movR64R64Effect 0x11599c 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 88) (.exec 0x11599c (fun s => s.RIP = 0x11599c) (movR64R64Effect 0x11599c 6 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 89) (.out 0x11599f (callEffect (fun _ => 0x1145f0) 0x1159a4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 90) (.exec 0x11599f (PushPre 0x11599f 5) (callEffect (fun _ => 0x1145f0) 0x1159a4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 91) (.const ⟨64, 0x1159a4⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 79), (1, 81), (3, 67), (4, 89), (5, 5), (6, 87), (7, 85), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 92⟩ { target := .l1159a4, kept := #v[], arity := rfl, guard := some (Fin.last 91) }))))))

def bytes_l115950_1 : List UInt8 :=
  [0x48, 0x89, 0xE6, 0xE8, 0x4C, 0xEC, 0xFF, 0xFF]

theorem code_l115950_1 : ∀ x ∈ codeRange 0x11599c bytes_l115950_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1599c 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l115950 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x115950 (pushR64Effect 0x115950 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x115950 (PushPre 0x115950 1) (pushR64Effect 0x115950 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x115951 (pushR64Effect 0x115951 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x115951 (PushPre 0x115951 2) (pushR64Effect 0x115951 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x115953 (pushR64Effect 0x115953 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x115953 (PushPre 0x115953 2) (pushR64Effect 0x115953 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x115955 (pushR64Effect 0x115955 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x115955 (PushPre 0x115955 2) (pushR64Effect 0x115955 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x115957 (pushR64Effect 0x115957 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x115957 (PushPre 0x115957 2) (pushR64Effect 0x115957 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x115959 (pushR64Effect 0x115959 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x115959 (PushPre 0x115959 1) (pushR64Effect 0x115959 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x11595a (subR64Imm32Effect 0x11595a 4 0x188) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x11595a (fun s => s.RIP = 0x11595a) (subR64Imm32Effect 0x11595a 4 0x188) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x115961 (movR64R64Effect 0x115961 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 68) (.exec 0x115961 (fun s => s.RIP = 0x115961) (movR64R64Effect 0x115961 3 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.exec 0x115964 (StorePre 0x115964 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x115964 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115964 7 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 70) (.out 0x11596c (movR64M64Effect 0x11596c 0 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 71) (.exec 0x11596c (LoadPre 0x11596c (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x11596c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11596c 0 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 72) (.exec 0x115970 (StorePre 0x115970 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x115970 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115970 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 65]
    (.letOp (n := 73) (.out 0x115975 (movR64M64Effect 0x115975 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 74) (.exec 0x115975 (LoadPre 0x115975 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x115975 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x115975 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 75) (.exec 0x115979 (StorePre 0x115979 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x115979 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115979 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 65]
    (.letOp (n := 76) (.out 0x11597e (movR64M64Effect 0x11597e 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 77) (.exec 0x11597e (LoadPre 0x11597e (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x11597e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11597e 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 78) (.exec 0x115982 (StorePre 0x115982 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x115982 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115982 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[76, 65]
    (.letOp (n := 79) (.out 0x115987 (movR64M64Effect 0x115987 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 80) (.exec 0x115987 (LoadPre 0x115987 (fun s => AddrMode.addr (.base 6 .none) s (0x115987 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x115987 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 81) (.out 0x11598a (movR64M64Effect 0x11598a 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 82) (.exec 0x11598a (LoadPre 0x11598a (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11598a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11598a 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 83) (.exec 0x11598e (StorePre 0x11598e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11598e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11598e 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[81, 65]
    (.letOp (n := 84) (.exec 0x115993 (StorePre 0x115993 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x115993 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x115993 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 65]
    (.letOp (n := 85) (.out 0x115997 (leaR64Effect 0x115997 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 86) (.exec 0x115997 (fun s => s.RIP = 0x115997) (leaR64Effect 0x115997 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l115950_1))))))))))))))))))))))))))))))))))

def bytes_l115950 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x88, 0x01, 0x00,
    0x00, 0x48, 0x89, 0xF3, 0x48, 0x89, 0xBC, 0x24, 0x80, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x20,
    0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B,
    0x46, 0x10, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x48, 0x89,
    0x4C, 0x24, 0x08, 0x48, 0x89, 0x04, 0x24, 0x48, 0x8D, 0x7C, 0x24, 0x28] ++ bytes_l115950_1

theorem code_l115950 : ∀ x ∈ codeRange 0x115950 bytes_l115950, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15950 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115950_1

def b_l1159a4_12 : Block Op Label signature Reg.count 567 :=
  .letOp (n := 567) (.exec 0x115de4 (StorePre 0x115de4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x115de4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115de4 12 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[565, 4]
    (.letOp (n := 568) (.out 0x115dec (movR64M64Effect 0x115dec 5 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 569) (.exec 0x115dec (LoadPre 0x115dec (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x115dec + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115dec 5 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 570) (.out 0x115df4 (andR64R64Effect 0x115df4 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[568, 503]
    (.letOp (n := 571) (.exec 0x115df4 (fun s => s.RIP = 0x115df4) (andR64R64Effect 0x115df4 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[568, 503]
    (.letOp (n := 572) (.exec 0x115df7 (StorePre 0x115df7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x115df7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115df7 5 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[570, 4]
    (.letOp (n := 573) (.exec 0x115dff (StorePre 0x115dff 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x115dff + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x115dff 5 (.sib 4 none 0 .none)) (Reg.operands [.gpr 5, .gpr 4] [])) #v[570, 4]
    (.letOp (n := 574) (.out 0x115e03 (movR64M64Effect 0x115e03 0 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 575) (.exec 0x115e03 (LoadPre 0x115e03 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x115e03 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115e03 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 576) (.out 0x115e0b (andR64R64Effect 0x115e0b 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[574, 503]
    (.letOp (n := 577) (.exec 0x115e0b (fun s => s.RIP = 0x115e0b) (andR64R64Effect 0x115e0b 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[574, 503]
    (.letOp (n := 578) (.exec 0x115e0e (StorePre 0x115e0e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x115e0e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115e0e 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[576, 4]
    (.letOp (n := 579) (.exec 0x115e16 (StorePre 0x115e16 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x115e16 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115e16 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[576, 4]
    (.letOp (n := 580) (.out 0x115e1b (andR64R64Effect 0x115e1b 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[527, 503]
    (.letOp (n := 581) (.exec 0x115e1b (fun s => s.RIP = 0x115e1b) (andR64R64Effect 0x115e1b 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[527, 503]
    (.letOp (n := 582) (.exec 0x115e1e (StorePre 0x115e1e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x115e1e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115e1e 8 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[580, 4]
    (.letOp (n := 583) (.exec 0x115e26 (StorePre 0x115e26 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x115e26 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115e26 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[580, 4]
    (.letOp (n := 584) (.out 0x115e2b (andR64R64Effect 0x115e2b 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[552, 503]
    (.letOp (n := 585) (.exec 0x115e2b (fun s => s.RIP = 0x115e2b) (andR64R64Effect 0x115e2b 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[552, 503]
    (.letOp (n := 586) (.exec 0x115e2e (StorePre 0x115e2e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x115e2e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115e2e 13 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[584, 4]
    (.letOp (n := 587) (.exec 0x115e36 (StorePre 0x115e36 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x115e36 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115e36 13 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[584, 4]
    (.letOp (n := 588) (.exec 0x115e3b (StorePre 0x115e3b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x115e3b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115e3b 12 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[565, 4]
    (.letOp (n := 589) (.out 0x115e40 (leaR64Effect 0x115e40 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 590) (.exec 0x115e40 (fun s => s.RIP = 0x115e40) (leaR64Effect 0x115e40 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 591) (.out 0x115e45 (movR64R64Effect 0x115e45 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 592) (.exec 0x115e45 (fun s => s.RIP = 0x115e45) (movR64R64Effect 0x115e45 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 593) (.out 0x115e48 (callEffect (fun _ => 0x1145f0) 0x115e4d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 594) (.exec 0x115e48 (PushPre 0x115e48 5) (callEffect (fun _ => 0x1145f0) 0x115e4d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 595) (.const ⟨64, 0x115e4d⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 576), (1, 442), (2, 557), (3, 460), (4, 593), (5, 570), (6, 591), (7, 589), (8, 580), (9, 532), (10, 484), (11, 458), (12, 565), (13, 584), (14, 496), (15, 503), (22, 22), (39, 39), (50, 50), (51, 51)] 596⟩ { target := .l115e4d, kept := #v[], arity := rfl, guard := some (Fin.last 595) }))))))))))))))))))))))))))))))

def bytes_l1159a4_12 : List UInt8 :=
  [0x4C, 0x89, 0xA4, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xAC, 0x24, 0xF0, 0x00, 0x00, 0x00,
    0x4C, 0x21, 0xFD, 0x48, 0x89, 0xAC, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x2C, 0x24, 0x48,
    0x8B, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x4C, 0x21, 0xF8, 0x48, 0x89, 0x84, 0x24, 0x20, 0x01,
    0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x08, 0x4D, 0x21, 0xF8, 0x4C, 0x89, 0x84, 0x24, 0x38, 0x01,
    0x00, 0x00, 0x4C, 0x89, 0x44, 0x24, 0x10, 0x4D, 0x21, 0xFD, 0x4C, 0x89, 0xAC, 0x24, 0x00, 0x01,
    0x00, 0x00, 0x4C, 0x89, 0x6C, 0x24, 0x18, 0x4C, 0x89, 0x64, 0x24, 0x20, 0x48, 0x8D, 0x7C, 0x24,
    0x28, 0x48, 0x89, 0xE6, 0xE8, 0xA3, 0xE7, 0xFF, 0xFF]

theorem code_l1159a4_12 : ∀ x ∈ codeRange 0x115de4 bytes_l1159a4_12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15de4 105 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l1159a4_11 : Block Op Label signature Reg.count 525 :=
  .letOp (n := 525) (.out 0x115d8a (atFlags StatusFlags.CF (adcR64R64Effect 0x115d8a 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[520, 510, 523]
    (.letOp (n := 526) (.exec 0x115d8a (fun s => s.RIP = 0x115d8a) (atFlags StatusFlags.CF (adcR64R64Effect 0x115d8a 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[520, 510, 523]
    (.letOp (n := 527) (.out 0x115d8d (addR64R64Effect 0x115d8d 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[522, 442]
    (.letOp (n := 528) (.out 0x115d8d (addR64R64Effect 0x115d8d 8 1) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 1] []) (.flag .CF)) #v[522, 442]
    (.letOp (n := 529) (.exec 0x115d8d (fun s => s.RIP = 0x115d8d) (addR64R64Effect 0x115d8d 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[522, 442]
    (.letOp (n := 530) (.out 0x115d90 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115d90 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[525, 528]
    (.letOp (n := 531) (.exec 0x115d90 (fun s => s.RIP = 0x115d90) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115d90 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[525, 528]
    (.letOp (n := 532) (.out 0x115d94 (shldR64R64Effect 0x115d94 5 9 14 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[499, 496]
    (.letOp (n := 533) (.exec 0x115d94 (fun s => s.RIP = 0x115d94) (shldR64R64Effect 0x115d94 5 9 14 12) (Reg.operands [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[499, 496]
    (.letOp (n := 534) (.out 0x115d99 (shldR64R64Effect 0x115d99 5 7 8 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[530, 527]
    (.letOp (n := 535) (.exec 0x115d99 (fun s => s.RIP = 0x115d99) (shldR64R64Effect 0x115d99 5 7 8 12) (Reg.operands [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[530, 527]
    (.letOp (n := 536) (.exec 0x115d9e (StorePre 0x115d9e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x115d9e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115d9e 10 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[484, 4]
    (.letOp (n := 537) (.out 0x115da3 (movR64R64Effect 0x115da3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[532]
    (.letOp (n := 538) (.exec 0x115da3 (fun s => s.RIP = 0x115da3) (movR64R64Effect 0x115da3 0 9) (Reg.operands [.gpr 9] [])) #v[532]
    (.letOp (n := 539) (.out 0x115da6 (mulR64Effect 0x115da6 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[507, 537]
    (.letOp (n := 540) (.out 0x115da6 (mulR64Effect 0x115da6 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[507, 537]
    (.letOp (n := 541) (.exec 0x115da6 (fun s => s.RIP = 0x115da6) (mulR64Effect 0x115da6 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[507, 537]
    (.letOp (n := 542) (.exec 0x115da9 (StorePre 0x115da9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x115da9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115da9 13 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[476, 4]
    (.letOp (n := 543) (.out 0x115dae (movR64M64Effect 0x115dae 13 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 544) (.exec 0x115dae (LoadPre 0x115dae (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x115dae + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115dae 13 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 545) (.out 0x115db6 (andR64R64Effect 0x115db6 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[543, 503]
    (.letOp (n := 546) (.exec 0x115db6 (fun s => s.RIP = 0x115db6) (andR64R64Effect 0x115db6 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[543, 503]
    (.letOp (n := 547) (.out 0x115db9 (addR64R64Effect 0x115db9 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[545, 539]
    (.letOp (n := 548) (.out 0x115db9 (addR64R64Effect 0x115db9 13 0) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 0] []) (.flag .CF)) #v[545, 539]
    (.letOp (n := 549) (.exec 0x115db9 (fun s => s.RIP = 0x115db9) (addR64R64Effect 0x115db9 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[545, 539]
    (.letOp (n := 550) (.out 0x115dbc (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115dbc 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[540, 548]
    (.letOp (n := 551) (.exec 0x115dbc (fun s => s.RIP = 0x115dbc) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115dbc 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[540, 548]
    (.letOp (n := 552) (.out 0x115dc0 (addR64R64Effect 0x115dc0 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 7] []) (.reg (.gpr 13))) #v[547, 534]
    (.letOp (n := 553) (.out 0x115dc0 (addR64R64Effect 0x115dc0 13 7) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 7] []) (.flag .CF)) #v[547, 534]
    (.letOp (n := 554) (.exec 0x115dc0 (fun s => s.RIP = 0x115dc0) (addR64R64Effect 0x115dc0 13 7) (Reg.operands [.gpr 13, .gpr 7] [])) #v[547, 534]
    (.letOp (n := 555) (.out 0x115dc3 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115dc3 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[550, 553]
    (.letOp (n := 556) (.exec 0x115dc3 (fun s => s.RIP = 0x115dc3) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115dc3 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[550, 553]
    (.letOp (n := 557) (.out 0x115dc7 (shldR64R64Effect 0x115dc7 5 2 13 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[555, 552]
    (.letOp (n := 558) (.exec 0x115dc7 (fun s => s.RIP = 0x115dc7) (shldR64R64Effect 0x115dc7 5 2 13 12) (Reg.operands [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[555, 552]
    (.letOp (n := 559) (.out 0x115dcc (movR64Imm64Effect 0x115dcc 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 560) (.exec 0x115dcc (fun s => s.RIP = 0x115dcc) (movR64Imm64Effect 0x115dcc 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 561) (.out 0x115dd6 (movR64M64Effect 0x115dd6 12 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 562) (.exec 0x115dd6 (LoadPre 0x115dd6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x115dd6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115dd6 12 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 563) (.out 0x115dde (andR64R64Effect 0x115dde 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[561, 559]
    (.letOp (n := 564) (.exec 0x115dde (fun s => s.RIP = 0x115dde) (andR64R64Effect 0x115dde 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[561, 559]
    (.letOp (n := 565) (.out 0x115de1 (addR64R64Effect 0x115de1 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[563, 557]
    (.letOp (n := 566) (.exec 0x115de1 (fun s => s.RIP = 0x115de1) (addR64R64Effect 0x115de1 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[563, 557]
    (b_l1159a4_12))))))))))))))))))))))))))))))))))))))))))

def bytes_l1159a4_11 : List UInt8 :=
  [0x48, 0x11, 0xD7, 0x49, 0x01, 0xC8, 0x48, 0x83, 0xD7, 0x00, 0x4D, 0x0F, 0xA4, 0xF1, 0x0C, 0x4C,
    0x0F, 0xA4, 0xC7, 0x0C, 0x4C, 0x89, 0x54, 0x24, 0x20, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0xE6, 0x4C,
    0x89, 0x6C, 0x24, 0x18, 0x4C, 0x8B, 0xAC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4D, 0x21, 0xFD, 0x49,
    0x01, 0xC5, 0x48, 0x83, 0xD2, 0x00, 0x49, 0x01, 0xFD, 0x48, 0x83, 0xD2, 0x00, 0x4C, 0x0F, 0xA4,
    0xEA, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x4C, 0x8B, 0xA4, 0x24,
    0xF8, 0x00, 0x00, 0x00, 0x49, 0x21, 0xC4, 0x49, 0x01, 0xD4] ++ bytes_l1159a4_12

theorem code_l1159a4_11 : ∀ x ∈ codeRange 0x115d8a bytes_l1159a4_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15d8a 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1159a4_12

def b_l1159a4_10 : Block Op Label signature Reg.count 478 :=
  .letOp (n := 478) (.out 0x115d35 (movR64R64Effect 0x115d35 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[474]
    (.letOp (n := 479) (.exec 0x115d35 (fun s => s.RIP = 0x115d35) (movR64R64Effect 0x115d35 9 2) (Reg.operands [.gpr 2] [])) #v[474]
    (.letOp (n := 480) (.out 0x115d38 (movR64R64Effect 0x115d38 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[473]
    (.letOp (n := 481) (.exec 0x115d38 (fun s => s.RIP = 0x115d38) (movR64R64Effect 0x115d38 15 0) (Reg.operands [.gpr 0] [])) #v[473]
    (.letOp (n := 482) (.out 0x115d3b (movR64M64Effect 0x115d3b 0 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 483) (.exec 0x115d3b (LoadPre 0x115d3b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x115d3b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115d3b 0 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 484) (.out 0x115d43 (movR64M64Effect 0x115d43 10 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 485) (.exec 0x115d43 (LoadPre 0x115d43 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x115d43 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115d43 10 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 486) (.out 0x115d4b (mulR64Effect 0x115d4b 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[484, 482]
    (.letOp (n := 487) (.out 0x115d4b (mulR64Effect 0x115d4b 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[484, 482]
    (.letOp (n := 488) (.exec 0x115d4b (fun s => s.RIP = 0x115d4b) (mulR64Effect 0x115d4b 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[484, 482]
    (.letOp (n := 489) (.out 0x115d4e (movR64R64Effect 0x115d4e 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[486]
    (.letOp (n := 490) (.exec 0x115d4e (fun s => s.RIP = 0x115d4e) (movR64R64Effect 0x115d4e 14 0) (Reg.operands [.gpr 0] [])) #v[486]
    (.letOp (n := 491) (.out 0x115d51 (addR64R64Effect 0x115d51 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[489, 480]
    (.letOp (n := 492) (.out 0x115d51 (addR64R64Effect 0x115d51 14 15) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 15] []) (.flag .CF)) #v[489, 480]
    (.letOp (n := 493) (.exec 0x115d51 (fun s => s.RIP = 0x115d51) (addR64R64Effect 0x115d51 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[489, 480]
    (.letOp (n := 494) (.out 0x115d54 (atFlags StatusFlags.CF (adcR64R64Effect 0x115d54 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[478, 487, 492]
    (.letOp (n := 495) (.exec 0x115d54 (fun s => s.RIP = 0x115d54) (atFlags StatusFlags.CF (adcR64R64Effect 0x115d54 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[478, 487, 492]
    (.letOp (n := 496) (.out 0x115d57 (addR64R64Effect 0x115d57 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[491, 415]
    (.letOp (n := 497) (.out 0x115d57 (addR64R64Effect 0x115d57 14 6) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 6] []) (.flag .CF)) #v[491, 415]
    (.letOp (n := 498) (.exec 0x115d57 (fun s => s.RIP = 0x115d57) (addR64R64Effect 0x115d57 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[491, 415]
    (.letOp (n := 499) (.out 0x115d5a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115d5a 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[494, 497]
    (.letOp (n := 500) (.exec 0x115d5a (fun s => s.RIP = 0x115d5a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115d5a 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[494, 497]
    (.letOp (n := 501) (.out 0x115d5e (movR64R64Effect 0x115d5e 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[496]
    (.letOp (n := 502) (.exec 0x115d5e (fun s => s.RIP = 0x115d5e) (movR64R64Effect 0x115d5e 0 14) (Reg.operands [.gpr 14] [])) #v[496]
    (.letOp (n := 503) (.out 0x115d61 (movR64Imm64Effect 0x115d61 15 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 504) (.exec 0x115d61 (fun s => s.RIP = 0x115d61) (movR64Imm64Effect 0x115d61 15 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 505) (.out 0x115d6b (andR64R64Effect 0x115d6b 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[501, 503]
    (.letOp (n := 506) (.exec 0x115d6b (fun s => s.RIP = 0x115d6b) (andR64R64Effect 0x115d6b 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[501, 503]
    (.letOp (n := 507) (.out 0x115d6e (movR64Imm64Effect 0x115d6e 6 0x1000003d10) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 508) (.exec 0x115d6e (fun s => s.RIP = 0x115d6e) (movR64Imm64Effect 0x115d6e 6 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 509) (.out 0x115d78 (mulR64Effect 0x115d78 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[507, 505]
    (.letOp (n := 510) (.out 0x115d78 (mulR64Effect 0x115d78 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[507, 505]
    (.letOp (n := 511) (.exec 0x115d78 (fun s => s.RIP = 0x115d78) (mulR64Effect 0x115d78 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[507, 505]
    (.letOp (n := 512) (.out 0x115d7b (addR64R64Effect 0x115d7b 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[469, 460]
    (.letOp (n := 513) (.out 0x115d7b (addR64R64Effect 0x115d7b 8 3) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 3] []) (.flag .CF)) #v[469, 460]
    (.letOp (n := 514) (.exec 0x115d7b (fun s => s.RIP = 0x115d7b) (addR64R64Effect 0x115d7b 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[469, 460]
    (.letOp (n := 515) (.out 0x115d7e (atFlags StatusFlags.CF (adcR64R64Effect 0x115d7e 7 11)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[467, 458, 513]
    (.letOp (n := 516) (.exec 0x115d7e (fun s => s.RIP = 0x115d7e) (atFlags StatusFlags.CF (adcR64R64Effect 0x115d7e 7 11)) (Reg.operands [.gpr 7, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[467, 458, 513]
    (.letOp (n := 517) (.out 0x115d81 (addR64R64Effect 0x115d81 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[512, 451]
    (.letOp (n := 518) (.out 0x115d81 (addR64R64Effect 0x115d81 8 12) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 12] []) (.flag .CF)) #v[512, 451]
    (.letOp (n := 519) (.exec 0x115d81 (fun s => s.RIP = 0x115d81) (addR64R64Effect 0x115d81 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[512, 451]
    (.letOp (n := 520) (.out 0x115d84 (atFlags StatusFlags.CF (adcR64R64Effect 0x115d84 7 5)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[515, 449, 518]
    (.letOp (n := 521) (.exec 0x115d84 (fun s => s.RIP = 0x115d84) (atFlags StatusFlags.CF (adcR64R64Effect 0x115d84 7 5)) (Reg.operands [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[515, 449, 518]
    (.letOp (n := 522) (.out 0x115d87 (addR64R64Effect 0x115d87 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[517, 509]
    (.letOp (n := 523) (.out 0x115d87 (addR64R64Effect 0x115d87 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[517, 509]
    (.letOp (n := 524) (.exec 0x115d87 (fun s => s.RIP = 0x115d87) (addR64R64Effect 0x115d87 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[517, 509]
    (b_l1159a4_11)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1159a4_10 : List UInt8 :=
  [0x49, 0x89, 0xD1, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00, 0x4C, 0x8B,
    0x94, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xC6, 0x4D, 0x01, 0xFE, 0x49,
    0x11, 0xD1, 0x49, 0x01, 0xF6, 0x49, 0x83, 0xD1, 0x00, 0x4C, 0x89, 0xF0, 0x49, 0xBF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xF8, 0x48, 0xBE, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE6, 0x49, 0x01, 0xD8, 0x4C, 0x11, 0xDF, 0x4D, 0x01, 0xE0, 0x48,
    0x11, 0xEF, 0x49, 0x01, 0xC0] ++ bytes_l1159a4_11

theorem code_l1159a4_10 : ∀ x ∈ codeRange 0x115d35 bytes_l1159a4_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15d35 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1159a4_11

def b_l1159a4_9 : Block Op Label signature Reg.count 434 :=
  .letOp (n := 434) (.out 0x115ce2 (atFlags StatusFlags.CF (adcR64R64Effect 0x115ce2 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[429, 424, 432]
    (.letOp (n := 435) (.exec 0x115ce2 (fun s => s.RIP = 0x115ce2) (atFlags StatusFlags.CF (adcR64R64Effect 0x115ce2 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[429, 424, 432]
    (.letOp (n := 436) (.out 0x115ce5 (addR64R64Effect 0x115ce5 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[431, 349]
    (.letOp (n := 437) (.out 0x115ce5 (addR64R64Effect 0x115ce5 15 8) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 8] []) (.flag .CF)) #v[431, 349]
    (.letOp (n := 438) (.exec 0x115ce5 (fun s => s.RIP = 0x115ce5) (addR64R64Effect 0x115ce5 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[431, 349]
    (.letOp (n := 439) (.exec 0x115ce8 (StorePre 0x115ce8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x115ce8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115ce8 15 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[436, 4]
    (.letOp (n := 440) (.out 0x115cf0 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115cf0 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[434, 437]
    (.letOp (n := 441) (.exec 0x115cf0 (fun s => s.RIP = 0x115cf0) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115cf0 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[434, 437]
    (.letOp (n := 442) (.out 0x115cf4 (shldR64R64Effect 0x115cf4 5 1 15 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[440, 436]
    (.letOp (n := 443) (.exec 0x115cf4 (fun s => s.RIP = 0x115cf4) (shldR64R64Effect 0x115cf4 5 1 15 12) (Reg.operands [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[440, 436]
    (.letOp (n := 444) (.out 0x115cf9 (movR64R64Effect 0x115cf9 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[393]
    (.letOp (n := 445) (.exec 0x115cf9 (fun s => s.RIP = 0x115cf9) (movR64R64Effect 0x115cf9 0 12) (Reg.operands [.gpr 12] [])) #v[393]
    (.letOp (n := 446) (.out 0x115cfc (mulR64Effect 0x115cfc 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[353, 444]
    (.letOp (n := 447) (.out 0x115cfc (mulR64Effect 0x115cfc 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[353, 444]
    (.letOp (n := 448) (.exec 0x115cfc (fun s => s.RIP = 0x115cfc) (mulR64Effect 0x115cfc 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[353, 444]
    (.letOp (n := 449) (.out 0x115cff (movR64R64Effect 0x115cff 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[447]
    (.letOp (n := 450) (.exec 0x115cff (fun s => s.RIP = 0x115cff) (movR64R64Effect 0x115cff 5 2) (Reg.operands [.gpr 2] [])) #v[447]
    (.letOp (n := 451) (.out 0x115d02 (movR64R64Effect 0x115d02 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[446]
    (.letOp (n := 452) (.exec 0x115d02 (fun s => s.RIP = 0x115d02) (movR64R64Effect 0x115d02 12 0) (Reg.operands [.gpr 0] [])) #v[446]
    (.letOp (n := 453) (.out 0x115d05 (movR64M64Effect 0x115d05 0 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 454) (.exec 0x115d05 (LoadPre 0x115d05 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x115d05 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115d05 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 455) (.out 0x115d0d (mulM64Effect 0x115d0d 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[453, 4]
    (.letOp (n := 456) (.out 0x115d0d (mulM64Effect 0x115d0d 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[453, 4]
    (.letOp (n := 457) (.exec 0x115d0d (LoadPre 0x115d0d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x115d0d + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x115d0d 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[453, 4]
    (.letOp (n := 458) (.out 0x115d15 (movR64R64Effect 0x115d15 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[456]
    (.letOp (n := 459) (.exec 0x115d15 (fun s => s.RIP = 0x115d15) (movR64R64Effect 0x115d15 11 2) (Reg.operands [.gpr 2] [])) #v[456]
    (.letOp (n := 460) (.out 0x115d18 (movR64R64Effect 0x115d18 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[455]
    (.letOp (n := 461) (.exec 0x115d18 (fun s => s.RIP = 0x115d18) (movR64R64Effect 0x115d18 3 0) (Reg.operands [.gpr 0] [])) #v[455]
    (.letOp (n := 462) (.out 0x115d1b (movR64R64Effect 0x115d1b 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[360]
    (.letOp (n := 463) (.exec 0x115d1b (fun s => s.RIP = 0x115d1b) (movR64R64Effect 0x115d1b 0 10) (Reg.operands [.gpr 10] [])) #v[360]
    (.letOp (n := 464) (.out 0x115d1e (mulR64Effect 0x115d1e 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[373, 462]
    (.letOp (n := 465) (.out 0x115d1e (mulR64Effect 0x115d1e 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[373, 462]
    (.letOp (n := 466) (.exec 0x115d1e (fun s => s.RIP = 0x115d1e) (mulR64Effect 0x115d1e 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[373, 462]
    (.letOp (n := 467) (.out 0x115d21 (movR64R64Effect 0x115d21 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[465]
    (.letOp (n := 468) (.exec 0x115d21 (fun s => s.RIP = 0x115d21) (movR64R64Effect 0x115d21 7 2) (Reg.operands [.gpr 2] [])) #v[465]
    (.letOp (n := 469) (.out 0x115d24 (movR64R64Effect 0x115d24 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[464]
    (.letOp (n := 470) (.exec 0x115d24 (fun s => s.RIP = 0x115d24) (movR64R64Effect 0x115d24 8 0) (Reg.operands [.gpr 0] [])) #v[464]
    (.letOp (n := 471) (.out 0x115d27 (movR64M64Effect 0x115d27 0 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 472) (.exec 0x115d27 (LoadPre 0x115d27 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x115d27 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115d27 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 473) (.out 0x115d2f (mulR64Effect 0x115d2f 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[384, 471]
    (.letOp (n := 474) (.out 0x115d2f (mulR64Effect 0x115d2f 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[384, 471]
    (.letOp (n := 475) (.exec 0x115d2f (fun s => s.RIP = 0x115d2f) (mulR64Effect 0x115d2f 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[384, 471]
    (.letOp (n := 476) (.out 0x115d32 (movR64R64Effect 0x115d32 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[384]
    (.letOp (n := 477) (.exec 0x115d32 (fun s => s.RIP = 0x115d32) (movR64R64Effect 0x115d32 13 9) (Reg.operands [.gpr 9] [])) #v[384]
    (b_l1159a4_10))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1159a4_9 : List UInt8 :=
  [0x48, 0x11, 0xD1, 0x4D, 0x01, 0xC7, 0x4C, 0x89, 0xBC, 0x24, 0x20, 0x01, 0x00, 0x00, 0x48, 0x83,
    0xD1, 0x00, 0x4C, 0x0F, 0xA4, 0xF9, 0x0C, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xD5,
    0x49, 0x89, 0xC4, 0x48, 0x8B, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0xB0,
    0x00, 0x00, 0x00, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC3, 0x4C, 0x89, 0xD0, 0x49, 0xF7, 0xE5, 0x48,
    0x89, 0xD7, 0x49, 0x89, 0xC0, 0x48, 0x8B, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE1,
    0x4D, 0x89, 0xCD] ++ bytes_l1159a4_10

theorem code_l1159a4_9 : ∀ x ∈ codeRange 0x115ce2 bytes_l1159a4_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15ce2 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1159a4_10

def b_l1159a4_8 : Block Op Label signature Reg.count 386 :=
  .letOp (n := 386) (.out 0x115c87 (mulR64Effect 0x115c87 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[384, 382]
    (.letOp (n := 387) (.out 0x115c87 (mulR64Effect 0x115c87 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[384, 382]
    (.letOp (n := 388) (.exec 0x115c87 (fun s => s.RIP = 0x115c87) (mulR64Effect 0x115c87 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[384, 382]
    (.letOp (n := 389) (.out 0x115c8a (movR64R64Effect 0x115c8a 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[387]
    (.letOp (n := 390) (.exec 0x115c8a (fun s => s.RIP = 0x115c8a) (movR64R64Effect 0x115c8a 6 2) (Reg.operands [.gpr 2] [])) #v[387]
    (.letOp (n := 391) (.out 0x115c8d (movR64R64Effect 0x115c8d 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[386]
    (.letOp (n := 392) (.exec 0x115c8d (fun s => s.RIP = 0x115c8d) (movR64R64Effect 0x115c8d 14 0) (Reg.operands [.gpr 0] [])) #v[386]
    (.letOp (n := 393) (.out 0x115c90 (movR64M64Effect 0x115c90 12 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 394) (.exec 0x115c90 (LoadPre 0x115c90 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x115c90 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115c90 12 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 395) (.out 0x115c98 (movR64R64Effect 0x115c98 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[393]
    (.letOp (n := 396) (.exec 0x115c98 (fun s => s.RIP = 0x115c98) (movR64R64Effect 0x115c98 0 12) (Reg.operands [.gpr 12] [])) #v[393]
    (.letOp (n := 397) (.out 0x115c9b (mulM64Effect 0x115c9b 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[395, 4]
    (.letOp (n := 398) (.out 0x115c9b (mulM64Effect 0x115c9b 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[395, 4]
    (.letOp (n := 399) (.exec 0x115c9b (LoadPre 0x115c9b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x115c9b + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x115c9b 8 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[395, 4]
    (.letOp (n := 400) (.out 0x115ca3 (addR64R64Effect 0x115ca3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[397, 391]
    (.letOp (n := 401) (.out 0x115ca3 (addR64R64Effect 0x115ca3 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[397, 391]
    (.letOp (n := 402) (.exec 0x115ca3 (fun s => s.RIP = 0x115ca3) (addR64R64Effect 0x115ca3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[397, 391]
    (.letOp (n := 403) (.out 0x115ca6 (atFlags StatusFlags.CF (adcR64R64Effect 0x115ca6 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[389, 398, 401]
    (.letOp (n := 404) (.exec 0x115ca6 (fun s => s.RIP = 0x115ca6) (atFlags StatusFlags.CF (adcR64R64Effect 0x115ca6 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[389, 398, 401]
    (.letOp (n := 405) (.out 0x115ca9 (addR64R64Effect 0x115ca9 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[400, 380]
    (.letOp (n := 406) (.out 0x115ca9 (addR64R64Effect 0x115ca9 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[400, 380]
    (.letOp (n := 407) (.exec 0x115ca9 (fun s => s.RIP = 0x115ca9) (addR64R64Effect 0x115ca9 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[400, 380]
    (.letOp (n := 408) (.out 0x115cac (atFlags StatusFlags.CF (adcR64R64Effect 0x115cac 6 11)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[403, 378, 406]
    (.letOp (n := 409) (.exec 0x115cac (fun s => s.RIP = 0x115cac) (atFlags StatusFlags.CF (adcR64R64Effect 0x115cac 6 11)) (Reg.operands [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[403, 378, 406]
    (.letOp (n := 410) (.out 0x115caf (addR64R64Effect 0x115caf 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[405, 326]
    (.letOp (n := 411) (.out 0x115caf (addR64R64Effect 0x115caf 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[405, 326]
    (.letOp (n := 412) (.exec 0x115caf (fun s => s.RIP = 0x115caf) (addR64R64Effect 0x115caf 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[405, 326]
    (.letOp (n := 413) (.out 0x115cb2 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115cb2 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[408, 411]
    (.letOp (n := 414) (.exec 0x115cb2 (fun s => s.RIP = 0x115cb2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115cb2 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[408, 411]
    (.letOp (n := 415) (.out 0x115cb6 (shldR64R64Effect 0x115cb6 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[413, 410]
    (.letOp (n := 416) (.exec 0x115cb6 (fun s => s.RIP = 0x115cb6) (shldR64R64Effect 0x115cb6 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[413, 410]
    (.letOp (n := 417) (.out 0x115cbb (movR64Imm64Effect 0x115cbb 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 418) (.exec 0x115cbb (fun s => s.RIP = 0x115cbb) (movR64Imm64Effect 0x115cbb 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 419) (.out 0x115cc5 (andR64R64Effect 0x115cc5 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[410, 417]
    (.letOp (n := 420) (.exec 0x115cc5 (fun s => s.RIP = 0x115cc5) (andR64R64Effect 0x115cc5 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[410, 417]
    (.letOp (n := 421) (.out 0x115cc8 (movR64Imm64Effect 0x115cc8 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 422) (.exec 0x115cc8 (fun s => s.RIP = 0x115cc8) (movR64Imm64Effect 0x115cc8 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 423) (.out 0x115cd2 (mulR64Effect 0x115cd2 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[421, 419]
    (.letOp (n := 424) (.out 0x115cd2 (mulR64Effect 0x115cd2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[421, 419]
    (.letOp (n := 425) (.exec 0x115cd2 (fun s => s.RIP = 0x115cd2) (mulR64Effect 0x115cd2 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[421, 419]
    (.letOp (n := 426) (.out 0x115cd5 (addR64M64Effect 0x115cd5 15 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[369, 4]
    (.letOp (n := 427) (.out 0x115cd5 (addR64M64Effect 0x115cd5 15 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[369, 4]
    (.letOp (n := 428) (.exec 0x115cd5 (LoadPre 0x115cd5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x115cd5 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x115cd5 15 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[369, 4]
    (.letOp (n := 429) (.out 0x115cda (atFlags StatusFlags.CF (adcR64M64Effect 0x115cda 1 (.sib 4 none 0 (.d8 0x50)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[367, 4, 427]
    (.letOp (n := 430) (.exec 0x115cda (LoadPre 0x115cda (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x115cda + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x115cda 1 (.sib 4 none 0 (.d8 0x50)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[367, 4, 427]
    (.letOp (n := 431) (.out 0x115cdf (addR64R64Effect 0x115cdf 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[426, 423]
    (.letOp (n := 432) (.out 0x115cdf (addR64R64Effect 0x115cdf 15 0) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 0] []) (.flag .CF)) #v[426, 423]
    (.letOp (n := 433) (.exec 0x115cdf (fun s => s.RIP = 0x115cdf) (addR64R64Effect 0x115cdf 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[426, 423]
    (b_l1159a4_9))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1159a4_8 : List UInt8 :=
  [0x49, 0xF7, 0xE1, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC6, 0x4C, 0x8B, 0xA4, 0x24, 0x30, 0x01, 0x00,
    0x00, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xF0, 0x48,
    0x11, 0xD6, 0x48, 0x01, 0xD8, 0x4C, 0x11, 0xDE, 0x48, 0x01, 0xF8, 0x48, 0x83, 0xD6, 0x00, 0x48,
    0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21,
    0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x03,
    0x7C, 0x24, 0x70, 0x48, 0x13, 0x4C, 0x24, 0x50, 0x49, 0x01, 0xC7] ++ bytes_l1159a4_9

theorem code_l1159a4_8 : ∀ x ∈ codeRange 0x115c87 bytes_l1159a4_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15c87 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1159a4_9

def b_l1159a4_7 : Block Op Label signature Reg.count 346 :=
  .letOp (n := 346) (.exec 0x115c2d (StorePre 0x115c2d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x115c2d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115c2d 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[343, 4]
    (.letOp (n := 347) (.out 0x115c35 (atFlags StatusFlags.CF (adcR64M64Effect 0x115c35 8 (.sib 4 none 0 (.d8 0x50)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[341, 4, 344]
    (.letOp (n := 348) (.exec 0x115c35 (LoadPre 0x115c35 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x115c35 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x115c35 8 (.sib 4 none 0 (.d8 0x50)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[341, 4, 344]
    (.letOp (n := 349) (.out 0x115c3a (shldR64R64Effect 0x115c3a 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[347, 343]
    (.letOp (n := 350) (.exec 0x115c3a (fun s => s.RIP = 0x115c3a) (shldR64R64Effect 0x115c3a 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[347, 343]
    (.letOp (n := 351) (.out 0x115c3f (movR64R64Effect 0x115c3f 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[299]
    (.letOp (n := 352) (.exec 0x115c3f (fun s => s.RIP = 0x115c3f) (movR64R64Effect 0x115c3f 0 12) (Reg.operands [.gpr 12] [])) #v[299]
    (.letOp (n := 353) (.out 0x115c42 (movR64M64Effect 0x115c42 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 354) (.exec 0x115c42 (LoadPre 0x115c42 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x115c42 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115c42 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 355) (.out 0x115c47 (mulR64Effect 0x115c47 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[353, 351]
    (.letOp (n := 356) (.out 0x115c47 (mulR64Effect 0x115c47 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[353, 351]
    (.letOp (n := 357) (.exec 0x115c47 (fun s => s.RIP = 0x115c47) (mulR64Effect 0x115c47 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[353, 351]
    (.letOp (n := 358) (.exec 0x115c4a (StorePre 0x115c4a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x115c4a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115c4a 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[356, 4]
    (.letOp (n := 359) (.exec 0x115c4f (StorePre 0x115c4f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x115c4f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115c4f 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[355, 4]
    (.letOp (n := 360) (.out 0x115c54 (movR64M64Effect 0x115c54 10 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 361) (.exec 0x115c54 (LoadPre 0x115c54 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x115c54 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115c54 10 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 362) (.out 0x115c5c (movR64R64Effect 0x115c5c 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[360]
    (.letOp (n := 363) (.exec 0x115c5c (fun s => s.RIP = 0x115c5c) (movR64R64Effect 0x115c5c 0 10) (Reg.operands [.gpr 10] [])) #v[360]
    (.letOp (n := 364) (.out 0x115c5f (mulR64Effect 0x115c5f 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[268, 362]
    (.letOp (n := 365) (.out 0x115c5f (mulR64Effect 0x115c5f 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[268, 362]
    (.letOp (n := 366) (.exec 0x115c5f (fun s => s.RIP = 0x115c5f) (mulR64Effect 0x115c5f 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[268, 362]
    (.letOp (n := 367) (.out 0x115c62 (movR64R64Effect 0x115c62 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[365]
    (.letOp (n := 368) (.exec 0x115c62 (fun s => s.RIP = 0x115c62) (movR64R64Effect 0x115c62 1 2) (Reg.operands [.gpr 2] [])) #v[365]
    (.letOp (n := 369) (.out 0x115c65 (movR64R64Effect 0x115c65 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[364]
    (.letOp (n := 370) (.exec 0x115c65 (fun s => s.RIP = 0x115c65) (movR64R64Effect 0x115c65 15 0) (Reg.operands [.gpr 0] [])) #v[364]
    (.letOp (n := 371) (.out 0x115c68 (movR64R64Effect 0x115c68 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[264]
    (.letOp (n := 372) (.exec 0x115c68 (fun s => s.RIP = 0x115c68) (movR64R64Effect 0x115c68 0 13) (Reg.operands [.gpr 13] [])) #v[264]
    (.letOp (n := 373) (.out 0x115c6b (movR64M64Effect 0x115c6b 13 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 374) (.exec 0x115c6b (LoadPre 0x115c6b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x115c6b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115c6b 13 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 375) (.out 0x115c73 (mulR64Effect 0x115c73 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[373, 371]
    (.letOp (n := 376) (.out 0x115c73 (mulR64Effect 0x115c73 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[373, 371]
    (.letOp (n := 377) (.exec 0x115c73 (fun s => s.RIP = 0x115c73) (mulR64Effect 0x115c73 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[373, 371]
    (.letOp (n := 378) (.out 0x115c76 (movR64R64Effect 0x115c76 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[376]
    (.letOp (n := 379) (.exec 0x115c76 (fun s => s.RIP = 0x115c76) (movR64R64Effect 0x115c76 11 2) (Reg.operands [.gpr 2] [])) #v[376]
    (.letOp (n := 380) (.out 0x115c79 (movR64R64Effect 0x115c79 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[375]
    (.letOp (n := 381) (.exec 0x115c79 (fun s => s.RIP = 0x115c79) (movR64R64Effect 0x115c79 3 0) (Reg.operands [.gpr 0] [])) #v[375]
    (.letOp (n := 382) (.out 0x115c7c (movR64R64Effect 0x115c7c 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[277]
    (.letOp (n := 383) (.exec 0x115c7c (fun s => s.RIP = 0x115c7c) (movR64R64Effect 0x115c7c 0 9) (Reg.operands [.gpr 9] [])) #v[277]
    (.letOp (n := 384) (.out 0x115c7f (movR64M64Effect 0x115c7f 9 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 385) (.exec 0x115c7f (LoadPre 0x115c7f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x115c7f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115c7f 9 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1159a4_8))))))))))))))))))))))))))))))))))))))))

def bytes_l1159a4_7 : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x44, 0x24, 0x50, 0x49, 0x0F, 0xA4,
    0xC0, 0x0C, 0x4C, 0x89, 0xE0, 0x48, 0x8B, 0x6C, 0x24, 0x68, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0x54,
    0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x70, 0x4C, 0x8B, 0x94, 0x24, 0x60, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0xD0, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC7, 0x4C, 0x89, 0xE8, 0x4C, 0x8B,
    0xAC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC3, 0x4C,
    0x89, 0xC8, 0x4C, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] ++ bytes_l1159a4_8

theorem code_l1159a4_7 : ∀ x ∈ codeRange 0x115c2d bytes_l1159a4_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15c2d 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1159a4_8

def b_l1159a4_6 : Block Op Label signature Reg.count 299 :=
  .letOp (n := 299) (.out 0x115bd5 (movR64M64Effect 0x115bd5 12 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 300) (.exec 0x115bd5 (LoadPre 0x115bd5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x115bd5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115bd5 12 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 301) (.out 0x115bdd (movR64R64Effect 0x115bdd 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[299]
    (.letOp (n := 302) (.exec 0x115bdd (fun s => s.RIP = 0x115bdd) (movR64R64Effect 0x115bdd 0 12) (Reg.operands [.gpr 12] [])) #v[299]
    (.letOp (n := 303) (.out 0x115be0 (mulR64Effect 0x115be0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[204, 301]
    (.letOp (n := 304) (.out 0x115be0 (mulR64Effect 0x115be0 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[204, 301]
    (.letOp (n := 305) (.exec 0x115be0 (fun s => s.RIP = 0x115be0) (mulR64Effect 0x115be0 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[204, 301]
    (.letOp (n := 306) (.out 0x115be3 (addR64R64Effect 0x115be3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[303, 297]
    (.letOp (n := 307) (.out 0x115be3 (addR64R64Effect 0x115be3 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[303, 297]
    (.letOp (n := 308) (.exec 0x115be3 (fun s => s.RIP = 0x115be3) (addR64R64Effect 0x115be3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[303, 297]
    (.letOp (n := 309) (.out 0x115be6 (atFlags StatusFlags.CF (adcR64R64Effect 0x115be6 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[295, 304, 307]
    (.letOp (n := 310) (.exec 0x115be6 (fun s => s.RIP = 0x115be6) (atFlags StatusFlags.CF (adcR64R64Effect 0x115be6 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[295, 304, 307]
    (.letOp (n := 311) (.out 0x115be9 (addR64R64Effect 0x115be9 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[306, 284]
    (.letOp (n := 312) (.out 0x115be9 (addR64R64Effect 0x115be9 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[306, 284]
    (.letOp (n := 313) (.exec 0x115be9 (fun s => s.RIP = 0x115be9) (addR64R64Effect 0x115be9 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[306, 284]
    (.letOp (n := 314) (.out 0x115bec (atFlags StatusFlags.CF (adcR64R64Effect 0x115bec 7 10)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[309, 286, 312]
    (.letOp (n := 315) (.exec 0x115bec (fun s => s.RIP = 0x115bec) (atFlags StatusFlags.CF (adcR64R64Effect 0x115bec 7 10)) (Reg.operands [.gpr 7, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[309, 286, 312]
    (.letOp (n := 316) (.out 0x115bef (addR64R64Effect 0x115bef 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[311, 275]
    (.letOp (n := 317) (.out 0x115bef (addR64R64Effect 0x115bef 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[311, 275]
    (.letOp (n := 318) (.exec 0x115bef (fun s => s.RIP = 0x115bef) (addR64R64Effect 0x115bef 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[311, 275]
    (.letOp (n := 319) (.out 0x115bf2 (atFlags StatusFlags.CF (adcR64R64Effect 0x115bf2 7 8)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[314, 273, 317]
    (.letOp (n := 320) (.exec 0x115bf2 (fun s => s.RIP = 0x115bf2) (atFlags StatusFlags.CF (adcR64R64Effect 0x115bf2 7 8)) (Reg.operands [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[314, 273, 317]
    (.letOp (n := 321) (.out 0x115bf5 (addR64R64Effect 0x115bf5 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[316, 251]
    (.letOp (n := 322) (.out 0x115bf5 (addR64R64Effect 0x115bf5 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[316, 251]
    (.letOp (n := 323) (.exec 0x115bf5 (fun s => s.RIP = 0x115bf5) (addR64R64Effect 0x115bf5 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[316, 251]
    (.letOp (n := 324) (.out 0x115bf8 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115bf8 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[319, 322]
    (.letOp (n := 325) (.exec 0x115bf8 (fun s => s.RIP = 0x115bf8) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115bf8 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[319, 322]
    (.letOp (n := 326) (.out 0x115bfc (shldR64R64Effect 0x115bfc 5 7 0 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[324, 321]
    (.letOp (n := 327) (.exec 0x115bfc (fun s => s.RIP = 0x115bfc) (shldR64R64Effect 0x115bfc 5 7 0 12) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[324, 321]
    (.letOp (n := 328) (.out 0x115c01 (shlR64Effect 0x115c01 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[321]
    (.letOp (n := 329) (.exec 0x115c01 (fun s => s.RIP = 0x115c01) (shlR64Effect 0x115c01 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[321]
    (.letOp (n := 330) (.out 0x115c05 (movR64Imm64Effect 0x115c05 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 331) (.exec 0x115c05 (fun s => s.RIP = 0x115c05) (movR64Imm64Effect 0x115c05 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 332) (.out 0x115c0f (andR64R64Effect 0x115c0f 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[328, 330]
    (.letOp (n := 333) (.exec 0x115c0f (fun s => s.RIP = 0x115c0f) (andR64R64Effect 0x115c0f 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[328, 330]
    (.letOp (n := 334) (.out 0x115c12 (orR64R64Effect 0x115c12 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[332, 288]
    (.letOp (n := 335) (.exec 0x115c12 (fun s => s.RIP = 0x115c12) (orR64R64Effect 0x115c12 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[332, 288]
    (.letOp (n := 336) (.out 0x115c15 (movR64Imm64Effect 0x115c15 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 337) (.exec 0x115c15 (fun s => s.RIP = 0x115c15) (movR64Imm64Effect 0x115c15 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 338) (.out 0x115c1f (mulR64Effect 0x115c1f 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[336, 334]
    (.letOp (n := 339) (.out 0x115c1f (mulR64Effect 0x115c1f 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[336, 334]
    (.letOp (n := 340) (.exec 0x115c1f (fun s => s.RIP = 0x115c1f) (mulR64Effect 0x115c1f 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[336, 334]
    (.letOp (n := 341) (.out 0x115c22 (movR64R64Effect 0x115c22 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[339]
    (.letOp (n := 342) (.exec 0x115c22 (fun s => s.RIP = 0x115c22) (movR64R64Effect 0x115c22 8 2) (Reg.operands [.gpr 2] [])) #v[339]
    (.letOp (n := 343) (.out 0x115c25 (addR64M64Effect 0x115c25 0 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[338, 4]
    (.letOp (n := 344) (.out 0x115c25 (addR64M64Effect 0x115c25 0 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[338, 4]
    (.letOp (n := 345) (.exec 0x115c25 (LoadPre 0x115c25 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x115c25 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x115c25 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[338, 4]
    (b_l1159a4_7)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1159a4_6 : List UInt8 :=
  [0x4C, 0x8B, 0xA4, 0x24, 0x48, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0xE3, 0x4C, 0x01,
    0xF0, 0x48, 0x11, 0xD7, 0x4C, 0x01, 0xD8, 0x4C, 0x11, 0xD7, 0x48, 0x01, 0xE8, 0x4C, 0x11, 0xC7,
    0x48, 0x01, 0xF0, 0x48, 0x83, 0xD7, 0x00, 0x48, 0x0F, 0xA4, 0xC7, 0x0C, 0x48, 0xC1, 0xE0, 0x04,
    0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x4C, 0x09, 0xF8,
    0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xD0,
    0x48, 0x03, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] ++ bytes_l1159a4_7

theorem code_l1159a4_6 : ∀ x ∈ codeRange 0x115bd5 bytes_l1159a4_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15bd5 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1159a4_7

def b_l1159a4_5 : Block Op Label signature Reg.count 257 :=
  .letOp (n := 257) (.out 0x115b78 (movR64R64Effect 0x115b78 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[200]
    (.letOp (n := 258) (.exec 0x115b78 (fun s => s.RIP = 0x115b78) (movR64R64Effect 0x115b78 0 8) (Reg.operands [.gpr 8] [])) #v[200]
    (.letOp (n := 259) (.out 0x115b7b (mulR64Effect 0x115b7b 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[164, 257]
    (.letOp (n := 260) (.out 0x115b7b (mulR64Effect 0x115b7b 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[164, 257]
    (.letOp (n := 261) (.exec 0x115b7b (fun s => s.RIP = 0x115b7b) (mulR64Effect 0x115b7b 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[164, 257]
    (.letOp (n := 262) (.exec 0x115b7e (StorePre 0x115b7e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x115b7e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115b7e 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[260, 4]
    (.letOp (n := 263) (.exec 0x115b83 (StorePre 0x115b83 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x115b83 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115b83 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[259, 4]
    (.letOp (n := 264) (.out 0x115b8b (movR64M64Effect 0x115b8b 13 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 265) (.exec 0x115b8b (LoadPre 0x115b8b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x115b8b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115b8b 13 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 266) (.out 0x115b93 (movR64R64Effect 0x115b93 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[264]
    (.letOp (n := 267) (.exec 0x115b93 (fun s => s.RIP = 0x115b93) (movR64R64Effect 0x115b93 0 13) (Reg.operands [.gpr 13] [])) #v[264]
    (.letOp (n := 268) (.out 0x115b96 (movR64M64Effect 0x115b96 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 269) (.exec 0x115b96 (LoadPre 0x115b96 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x115b96 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115b96 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 270) (.out 0x115b9e (mulR64Effect 0x115b9e 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[268, 266]
    (.letOp (n := 271) (.out 0x115b9e (mulR64Effect 0x115b9e 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[268, 266]
    (.letOp (n := 272) (.exec 0x115b9e (fun s => s.RIP = 0x115b9e) (mulR64Effect 0x115b9e 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[268, 266]
    (.letOp (n := 273) (.out 0x115ba1 (movR64R64Effect 0x115ba1 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[271]
    (.letOp (n := 274) (.exec 0x115ba1 (fun s => s.RIP = 0x115ba1) (movR64R64Effect 0x115ba1 8 2) (Reg.operands [.gpr 2] [])) #v[271]
    (.letOp (n := 275) (.out 0x115ba4 (movR64R64Effect 0x115ba4 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[270]
    (.letOp (n := 276) (.exec 0x115ba4 (fun s => s.RIP = 0x115ba4) (movR64R64Effect 0x115ba4 5 0) (Reg.operands [.gpr 0] [])) #v[270]
    (.letOp (n := 277) (.out 0x115ba7 (movR64M64Effect 0x115ba7 9 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 278) (.exec 0x115ba7 (LoadPre 0x115ba7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x115ba7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115ba7 9 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 279) (.out 0x115baf (movR64R64Effect 0x115baf 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[277]
    (.letOp (n := 280) (.exec 0x115baf (fun s => s.RIP = 0x115baf) (movR64R64Effect 0x115baf 0 9) (Reg.operands [.gpr 9] [])) #v[277]
    (.letOp (n := 281) (.out 0x115bb2 (mulR64Effect 0x115bb2 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[182, 279]
    (.letOp (n := 282) (.out 0x115bb2 (mulR64Effect 0x115bb2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[182, 279]
    (.letOp (n := 283) (.exec 0x115bb2 (fun s => s.RIP = 0x115bb2) (mulR64Effect 0x115bb2 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[182, 279]
    (.letOp (n := 284) (.out 0x115bb5 (movR64R64Effect 0x115bb5 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[281]
    (.letOp (n := 285) (.exec 0x115bb5 (fun s => s.RIP = 0x115bb5) (movR64R64Effect 0x115bb5 11 0) (Reg.operands [.gpr 0] [])) #v[281]
    (.letOp (n := 286) (.out 0x115bb8 (movR64R64Effect 0x115bb8 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[282]
    (.letOp (n := 287) (.exec 0x115bb8 (fun s => s.RIP = 0x115bb8) (movR64R64Effect 0x115bb8 10 2) (Reg.operands [.gpr 2] [])) #v[282]
    (.letOp (n := 288) (.out 0x115bbb (andR32Imm8Effect 0x115bbb 4 15 0xf) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[255]
    (.letOp (n := 289) (.exec 0x115bbb (fun s => s.RIP = 0x115bbb) (andR32Imm8Effect 0x115bbb 4 15 0xf) (Reg.operands [.gpr 15] [])) #v[255]
    (.letOp (n := 290) (.out 0x115bbf (movR64M64Effect 0x115bbf 0 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 291) (.exec 0x115bbf (LoadPre 0x115bbf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x115bbf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115bbf 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 292) (.out 0x115bc7 (mulM64Effect 0x115bc7 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[290, 4]
    (.letOp (n := 293) (.out 0x115bc7 (mulM64Effect 0x115bc7 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[290, 4]
    (.letOp (n := 294) (.exec 0x115bc7 (LoadPre 0x115bc7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x115bc7 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x115bc7 8 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[290, 4]
    (.letOp (n := 295) (.out 0x115bcf (movR64R64Effect 0x115bcf 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[293]
    (.letOp (n := 296) (.exec 0x115bcf (fun s => s.RIP = 0x115bcf) (movR64R64Effect 0x115bcf 7 2) (Reg.operands [.gpr 2] [])) #v[293]
    (.letOp (n := 297) (.out 0x115bd2 (movR64R64Effect 0x115bd2 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[292]
    (.letOp (n := 298) (.exec 0x115bd2 (fun s => s.RIP = 0x115bd2) (movR64R64Effect 0x115bd2 14 0) (Reg.operands [.gpr 0] [])) #v[292]
    (b_l1159a4_6))))))))))))))))))))))))))))))))))))))))))

def bytes_l1159a4_5 : List UInt8 :=
  [0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0x54, 0x24, 0x50, 0x48, 0x89, 0x84, 0x24, 0xF0,
    0x00, 0x00, 0x00, 0x4C, 0x8B, 0xAC, 0x24, 0x40, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE8, 0x48, 0x8B,
    0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD0, 0x48, 0x89, 0xC5, 0x4C,
    0x8B, 0x8C, 0x24, 0x50, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xC8, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xC3,
    0x49, 0x89, 0xD2, 0x41, 0x83, 0xE7, 0x0F, 0x48, 0x8B, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x48,
    0xF7, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC6] ++ bytes_l1159a4_6

theorem code_l1159a4_5 : ∀ x ∈ codeRange 0x115b78 bytes_l1159a4_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15b78 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1159a4_6

def b_l1159a4_4 : Block Op Label signature Reg.count 211 :=
  .letOp (n := 211) (.out 0x115b20 (movR64R64Effect 0x115b20 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[206]
    (.letOp (n := 212) (.exec 0x115b20 (fun s => s.RIP = 0x115b20) (movR64R64Effect 0x115b20 7 0) (Reg.operands [.gpr 0] [])) #v[206]
    (.letOp (n := 213) (.out 0x115b23 (movR64R64Effect 0x115b23 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[158]
    (.letOp (n := 214) (.exec 0x115b23 (fun s => s.RIP = 0x115b23) (movR64R64Effect 0x115b23 0 9) (Reg.operands [.gpr 9] [])) #v[158]
    (.letOp (n := 215) (.out 0x115b26 (movR64Imm64Effect 0x115b26 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 216) (.exec 0x115b26 (fun s => s.RIP = 0x115b26) (movR64Imm64Effect 0x115b26 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 217) (.out 0x115b30 (mulR64Effect 0x115b30 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[215, 213]
    (.letOp (n := 218) (.out 0x115b30 (mulR64Effect 0x115b30 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[215, 213]
    (.letOp (n := 219) (.exec 0x115b30 (fun s => s.RIP = 0x115b30) (mulR64Effect 0x115b30 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[215, 213]
    (.letOp (n := 220) (.out 0x115b33 (addR64R64Effect 0x115b33 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[211, 198]
    (.letOp (n := 221) (.out 0x115b33 (addR64R64Effect 0x115b33 7 12) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 12] []) (.flag .CF)) #v[211, 198]
    (.letOp (n := 222) (.exec 0x115b33 (fun s => s.RIP = 0x115b33) (addR64R64Effect 0x115b33 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[211, 198]
    (.letOp (n := 223) (.out 0x115b36 (atFlags StatusFlags.CF (adcR64R64Effect 0x115b36 6 15)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[209, 196, 221]
    (.letOp (n := 224) (.exec 0x115b36 (fun s => s.RIP = 0x115b36) (atFlags StatusFlags.CF (adcR64R64Effect 0x115b36 6 15)) (Reg.operands [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[209, 196, 221]
    (.letOp (n := 225) (.out 0x115b39 (addR64R64Effect 0x115b39 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[220, 189]
    (.letOp (n := 226) (.out 0x115b39 (addR64R64Effect 0x115b39 7 14) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 14] []) (.flag .CF)) #v[220, 189]
    (.letOp (n := 227) (.exec 0x115b39 (fun s => s.RIP = 0x115b39) (addR64R64Effect 0x115b39 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[220, 189]
    (.letOp (n := 228) (.out 0x115b3c (atFlags StatusFlags.CF (adcR64R64Effect 0x115b3c 6 11)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[223, 187, 226]
    (.letOp (n := 229) (.exec 0x115b3c (fun s => s.RIP = 0x115b3c) (atFlags StatusFlags.CF (adcR64R64Effect 0x115b3c 6 11)) (Reg.operands [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[223, 187, 226]
    (.letOp (n := 230) (.out 0x115b3f (addR64R64Effect 0x115b3f 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[225, 178]
    (.letOp (n := 231) (.out 0x115b3f (addR64R64Effect 0x115b3f 7 5) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 5] []) (.flag .CF)) #v[225, 178]
    (.letOp (n := 232) (.exec 0x115b3f (fun s => s.RIP = 0x115b3f) (addR64R64Effect 0x115b3f 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[225, 178]
    (.letOp (n := 233) (.out 0x115b42 (atFlags StatusFlags.CF (adcR64M64Effect 0x115b42 6 (.sib 4 none 0 (.d32 0xf0)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[228, 4, 231]
    (.letOp (n := 234) (.exec 0x115b42 (LoadPre 0x115b42 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x115b42 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x115b42 6 (.sib 4 none 0 (.d32 0xf0)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[228, 4, 231]
    (.letOp (n := 235) (.out 0x115b4a (addR64M64Effect 0x115b4a 7 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[230, 4]
    (.letOp (n := 236) (.out 0x115b4a (addR64M64Effect 0x115b4a 7 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[230, 4]
    (.letOp (n := 237) (.exec 0x115b4a (LoadPre 0x115b4a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x115b4a + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x115b4a 7 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[230, 4]
    (.letOp (n := 238) (.out 0x115b52 (atFlags StatusFlags.CF (adcR64M64Effect 0x115b52 6 (.sib 4 none 0 (.d8 0x50)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[233, 4, 236]
    (.letOp (n := 239) (.exec 0x115b52 (LoadPre 0x115b52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x115b52 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x115b52 6 (.sib 4 none 0 (.d8 0x50)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[233, 4, 236]
    (.letOp (n := 240) (.out 0x115b57 (addR64R64Effect 0x115b57 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[235, 217]
    (.letOp (n := 241) (.out 0x115b57 (addR64R64Effect 0x115b57 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[235, 217]
    (.letOp (n := 242) (.exec 0x115b57 (fun s => s.RIP = 0x115b57) (addR64R64Effect 0x115b57 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[235, 217]
    (.letOp (n := 243) (.out 0x115b5a (atFlags StatusFlags.CF (adcR64R64Effect 0x115b5a 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[238, 218, 241]
    (.letOp (n := 244) (.exec 0x115b5a (fun s => s.RIP = 0x115b5a) (atFlags StatusFlags.CF (adcR64R64Effect 0x115b5a 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[238, 218, 241]
    (.letOp (n := 245) (.out 0x115b5d (addR64R64Effect 0x115b5d 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[240, 160]
    (.letOp (n := 246) (.out 0x115b5d (addR64R64Effect 0x115b5d 7 1) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 1] []) (.flag .CF)) #v[240, 160]
    (.letOp (n := 247) (.exec 0x115b5d (fun s => s.RIP = 0x115b5d) (addR64R64Effect 0x115b5d 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[240, 160]
    (.letOp (n := 248) (.exec 0x115b60 (StorePre 0x115b60 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x115b60 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115b60 7 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[245, 4]
    (.letOp (n := 249) (.out 0x115b68 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115b68 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[243, 246]
    (.letOp (n := 250) (.exec 0x115b68 (fun s => s.RIP = 0x115b68) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115b68 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[243, 246]
    (.letOp (n := 251) (.out 0x115b6c (shldR64R64Effect 0x115b6c 5 6 7 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[249, 245]
    (.letOp (n := 252) (.exec 0x115b6c (fun s => s.RIP = 0x115b6c) (shldR64R64Effect 0x115b6c 5 6 7 12) (Reg.operands [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[249, 245]
    (.letOp (n := 253) (.out 0x115b71 (movR64R64Effect 0x115b71 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[245]
    (.letOp (n := 254) (.exec 0x115b71 (fun s => s.RIP = 0x115b71) (movR64R64Effect 0x115b71 15 7) (Reg.operands [.gpr 7] [])) #v[245]
    (.letOp (n := 255) (.out 0x115b74 (shrR64Effect 0x115b74 4 15 48) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[253]
    (.letOp (n := 256) (.exec 0x115b74 (fun s => s.RIP = 0x115b74) (shrR64Effect 0x115b74 4 15 48) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[253]
    (b_l1159a4_5))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1159a4_4 : List UInt8 :=
  [0x48, 0x89, 0xC7, 0x4C, 0x89, 0xC8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE2, 0x4C, 0x01, 0xE7, 0x4C, 0x11, 0xFE, 0x4C, 0x01, 0xF7, 0x4C, 0x11, 0xDE, 0x48,
    0x01, 0xEF, 0x48, 0x13, 0xB4, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x03, 0xBC, 0x24, 0xF8, 0x00,
    0x00, 0x00, 0x48, 0x13, 0x74, 0x24, 0x50, 0x48, 0x01, 0xC7, 0x48, 0x11, 0xD6, 0x48, 0x01, 0xCF,
    0x48, 0x89, 0xBC, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x83, 0xD6, 0x00, 0x48, 0x0F, 0xA4, 0xFE,
    0x0C, 0x49, 0x89, 0xFF, 0x49, 0xC1, 0xEF, 0x30] ++ bytes_l1159a4_5

theorem code_l1159a4_4 : ∀ x ∈ codeRange 0x115b20 bytes_l1159a4_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15b20 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1159a4_5

def b_l1159a4_3 : Block Op Label signature Reg.count 170 :=
  .letOp (n := 170) (.exec 0x115ac4 (StorePre 0x115ac4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x115ac4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115ac4 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[168, 4]
    (.letOp (n := 171) (.exec 0x115ac9 (StorePre 0x115ac9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x115ac9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115ac9 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[167, 4]
    (.letOp (n := 172) (.out 0x115ad1 (movR64R64Effect 0x115ad1 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 173) (.exec 0x115ad1 (fun s => s.RIP = 0x115ad1) (movR64R64Effect 0x115ad1 0 12) (Reg.operands [.gpr 12] [])) #v[70]
    (.letOp (n := 174) (.out 0x115ad4 (mulR64Effect 0x115ad4 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[60, 172]
    (.letOp (n := 175) (.out 0x115ad4 (mulR64Effect 0x115ad4 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[60, 172]
    (.letOp (n := 176) (.exec 0x115ad4 (fun s => s.RIP = 0x115ad4) (mulR64Effect 0x115ad4 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[60, 172]
    (.letOp (n := 177) (.exec 0x115ad7 (StorePre 0x115ad7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x115ad7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115ad7 2 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[175, 4]
    (.letOp (n := 178) (.out 0x115adf (movR64R64Effect 0x115adf 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[174]
    (.letOp (n := 179) (.exec 0x115adf (fun s => s.RIP = 0x115adf) (movR64R64Effect 0x115adf 5 0) (Reg.operands [.gpr 0] [])) #v[174]
    (.letOp (n := 180) (.out 0x115ae2 (movR64M64Effect 0x115ae2 0 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 181) (.exec 0x115ae2 (LoadPre 0x115ae2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x115ae2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115ae2 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 182) (.out 0x115aea (movR64M64Effect 0x115aea 10 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 183) (.exec 0x115aea (LoadPre 0x115aea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x115aea + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115aea 10 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 184) (.out 0x115af2 (mulR64Effect 0x115af2 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[182, 180]
    (.letOp (n := 185) (.out 0x115af2 (mulR64Effect 0x115af2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[182, 180]
    (.letOp (n := 186) (.exec 0x115af2 (fun s => s.RIP = 0x115af2) (mulR64Effect 0x115af2 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[182, 180]
    (.letOp (n := 187) (.out 0x115af5 (movR64R64Effect 0x115af5 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[185]
    (.letOp (n := 188) (.exec 0x115af5 (fun s => s.RIP = 0x115af5) (movR64R64Effect 0x115af5 11 2) (Reg.operands [.gpr 2] [])) #v[185]
    (.letOp (n := 189) (.out 0x115af8 (movR64R64Effect 0x115af8 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[184]
    (.letOp (n := 190) (.exec 0x115af8 (fun s => s.RIP = 0x115af8) (movR64R64Effect 0x115af8 14 0) (Reg.operands [.gpr 0] [])) #v[184]
    (.letOp (n := 191) (.out 0x115afb (movR64R64Effect 0x115afb 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[91]
    (.letOp (n := 192) (.exec 0x115afb (fun s => s.RIP = 0x115afb) (movR64R64Effect 0x115afb 0 7) (Reg.operands [.gpr 7] [])) #v[91]
    (.letOp (n := 193) (.out 0x115afe (mulR64Effect 0x115afe 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[108, 191]
    (.letOp (n := 194) (.out 0x115afe (mulR64Effect 0x115afe 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[108, 191]
    (.letOp (n := 195) (.exec 0x115afe (fun s => s.RIP = 0x115afe) (mulR64Effect 0x115afe 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[108, 191]
    (.letOp (n := 196) (.out 0x115b01 (movR64R64Effect 0x115b01 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[194]
    (.letOp (n := 197) (.exec 0x115b01 (fun s => s.RIP = 0x115b01) (movR64R64Effect 0x115b01 15 2) (Reg.operands [.gpr 2] [])) #v[194]
    (.letOp (n := 198) (.out 0x115b04 (movR64R64Effect 0x115b04 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[193]
    (.letOp (n := 199) (.exec 0x115b04 (fun s => s.RIP = 0x115b04) (movR64R64Effect 0x115b04 12 0) (Reg.operands [.gpr 0] [])) #v[193]
    (.letOp (n := 200) (.out 0x115b07 (movR64M64Effect 0x115b07 8 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 201) (.exec 0x115b07 (LoadPre 0x115b07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x115b07 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115b07 8 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 202) (.out 0x115b0f (movR64R64Effect 0x115b0f 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[200]
    (.letOp (n := 203) (.exec 0x115b0f (fun s => s.RIP = 0x115b0f) (movR64R64Effect 0x115b0f 0 8) (Reg.operands [.gpr 8] [])) #v[200]
    (.letOp (n := 204) (.out 0x115b12 (movR64M64Effect 0x115b12 3 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 205) (.exec 0x115b12 (LoadPre 0x115b12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x115b12 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115b12 3 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 206) (.out 0x115b1a (mulR64Effect 0x115b1a 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[204, 202]
    (.letOp (n := 207) (.out 0x115b1a (mulR64Effect 0x115b1a 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[204, 202]
    (.letOp (n := 208) (.exec 0x115b1a (fun s => s.RIP = 0x115b1a) (mulR64Effect 0x115b1a 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[204, 202]
    (.letOp (n := 209) (.out 0x115b1d (movR64R64Effect 0x115b1d 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[207]
    (.letOp (n := 210) (.exec 0x115b1d (fun s => s.RIP = 0x115b1d) (movR64R64Effect 0x115b1d 6 2) (Reg.operands [.gpr 2] [])) #v[207]
    (b_l1159a4_4)))))))))))))))))))))))))))))))))))))))))

def bytes_l1159a4_3 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x50, 0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE0,
    0x49, 0xF7, 0xE2, 0x48, 0x89, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC5, 0x48, 0x8B,
    0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0xF7,
    0xE2, 0x49, 0x89, 0xD3, 0x49, 0x89, 0xC6, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD7,
    0x49, 0x89, 0xC4, 0x4C, 0x8B, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xC0, 0x48, 0x8B,
    0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0xD6] ++ bytes_l1159a4_4

theorem code_l1159a4_3 : ∀ x ∈ codeRange 0x115ac4 bytes_l1159a4_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15ac4 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1159a4_4

def b_l1159a4_2 : Block Op Label signature Reg.count 126 :=
  .letOp (n := 126) (.out 0x115a63 (movR64R64Effect 0x115a63 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[121]
    (.letOp (n := 127) (.exec 0x115a63 (fun s => s.RIP = 0x115a63) (movR64R64Effect 0x115a63 11 0) (Reg.operands [.gpr 0] [])) #v[121]
    (.letOp (n := 128) (.out 0x115a66 (movR64Imm64Effect 0x115a66 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 129) (.exec 0x115a66 (fun s => s.RIP = 0x115a66) (movR64Imm64Effect 0x115a66 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 130) (.out 0x115a70 (andR64R64Effect 0x115a70 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[121, 128]
    (.letOp (n := 131) (.exec 0x115a70 (fun s => s.RIP = 0x115a70) (andR64R64Effect 0x115a70 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[121, 128]
    (.letOp (n := 132) (.out 0x115a73 (movR64Imm64Effect 0x115a73 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 133) (.exec 0x115a73 (fun s => s.RIP = 0x115a73) (movR64Imm64Effect 0x115a73 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 134) (.out 0x115a7d (mulR64Effect 0x115a7d 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[132, 130]
    (.letOp (n := 135) (.out 0x115a7d (mulR64Effect 0x115a7d 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[132, 130]
    (.letOp (n := 136) (.exec 0x115a7d (fun s => s.RIP = 0x115a7d) (mulR64Effect 0x115a7d 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[132, 130]
    (.letOp (n := 137) (.out 0x115a80 (addR64R64Effect 0x115a80 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[111, 97]
    (.letOp (n := 138) (.out 0x115a80 (addR64R64Effect 0x115a80 13 14) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 14] []) (.flag .CF)) #v[111, 97]
    (.letOp (n := 139) (.exec 0x115a80 (fun s => s.RIP = 0x115a80) (addR64R64Effect 0x115a80 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[111, 97]
    (.letOp (n := 140) (.out 0x115a83 (atFlags StatusFlags.CF (adcR64R64Effect 0x115a83 1 15)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[113, 99, 138]
    (.letOp (n := 141) (.exec 0x115a83 (fun s => s.RIP = 0x115a83) (atFlags StatusFlags.CF (adcR64R64Effect 0x115a83 1 15)) (Reg.operands [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[113, 99, 138]
    (.letOp (n := 142) (.out 0x115a86 (addR64R64Effect 0x115a86 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 6] []) (.reg (.gpr 13))) #v[137, 87]
    (.letOp (n := 143) (.out 0x115a86 (addR64R64Effect 0x115a86 13 6) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 6] []) (.flag .CF)) #v[137, 87]
    (.letOp (n := 144) (.exec 0x115a86 (fun s => s.RIP = 0x115a86) (addR64R64Effect 0x115a86 13 6) (Reg.operands [.gpr 13, .gpr 6] [])) #v[137, 87]
    (.letOp (n := 145) (.out 0x115a89 (atFlags StatusFlags.CF (adcR64M64Effect 0x115a89 1 (.sib 4 none 0 (.d32 0xf8)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[140, 4, 143]
    (.letOp (n := 146) (.exec 0x115a89 (LoadPre 0x115a89 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x115a89 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x115a89 1 (.sib 4 none 0 (.d32 0xf8)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[140, 4, 143]
    (.letOp (n := 147) (.out 0x115a91 (addR64M64Effect 0x115a91 13 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[142, 4]
    (.letOp (n := 148) (.out 0x115a91 (addR64M64Effect 0x115a91 13 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[142, 4]
    (.letOp (n := 149) (.exec 0x115a91 (LoadPre 0x115a91 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x115a91 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x115a91 13 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[142, 4]
    (.letOp (n := 150) (.out 0x115a96 (atFlags StatusFlags.CF (adcR64M64Effect 0x115a96 1 (.sib 4 none 0 (.d32 0x100)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[145, 4, 148]
    (.letOp (n := 151) (.exec 0x115a96 (LoadPre 0x115a96 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x115a96 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x115a96 1 (.sib 4 none 0 (.d32 0x100)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[145, 4, 148]
    (.letOp (n := 152) (.out 0x115a9e (addR64R64Effect 0x115a9e 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[147, 134]
    (.letOp (n := 153) (.out 0x115a9e (addR64R64Effect 0x115a9e 13 0) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 0] []) (.flag .CF)) #v[147, 134]
    (.letOp (n := 154) (.exec 0x115a9e (fun s => s.RIP = 0x115a9e) (addR64R64Effect 0x115a9e 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[147, 134]
    (.letOp (n := 155) (.exec 0x115aa1 (StorePre 0x115aa1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x115aa1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115aa1 13 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[152, 4]
    (.letOp (n := 156) (.out 0x115aa9 (atFlags StatusFlags.CF (adcR64R64Effect 0x115aa9 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[150, 135, 153]
    (.letOp (n := 157) (.exec 0x115aa9 (fun s => s.RIP = 0x115aa9) (atFlags StatusFlags.CF (adcR64R64Effect 0x115aa9 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[150, 135, 153]
    (.letOp (n := 158) (.out 0x115aac (shldR64R64Effect 0x115aac 5 9 11 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[124, 126]
    (.letOp (n := 159) (.exec 0x115aac (fun s => s.RIP = 0x115aac) (shldR64R64Effect 0x115aac 5 9 11 12) (Reg.operands [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[124, 126]
    (.letOp (n := 160) (.out 0x115ab1 (shldR64R64Effect 0x115ab1 5 1 13 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[156, 152]
    (.letOp (n := 161) (.exec 0x115ab1 (fun s => s.RIP = 0x115ab1) (shldR64R64Effect 0x115ab1 5 1 13 12) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[156, 152]
    (.letOp (n := 162) (.out 0x115ab6 (movR64R64Effect 0x115ab6 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[101]
    (.letOp (n := 163) (.exec 0x115ab6 (fun s => s.RIP = 0x115ab6) (movR64R64Effect 0x115ab6 0 8) (Reg.operands [.gpr 8] [])) #v[101]
    (.letOp (n := 164) (.out 0x115ab9 (movR64R64Effect 0x115ab9 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 5] []) (.reg (.gpr 13))) #v[58]
    (.letOp (n := 165) (.exec 0x115ab9 (fun s => s.RIP = 0x115ab9) (movR64R64Effect 0x115ab9 13 5) (Reg.operands [.gpr 5] [])) #v[58]
    (.letOp (n := 166) (.exec 0x115abc (StorePre 0x115abc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x115abc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115abc 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 167) (.out 0x115ac1 (mulR64Effect 0x115ac1 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[58, 162]
    (.letOp (n := 168) (.out 0x115ac1 (mulR64Effect 0x115ac1 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[58, 162]
    (.letOp (n := 169) (.exec 0x115ac1 (fun s => s.RIP = 0x115ac1) (mulR64Effect 0x115ac1 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[58, 162]
    (b_l1159a4_3))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1159a4_2 : List UInt8 :=
  [0x49, 0x89, 0xC3, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0,
    0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4D, 0x01, 0xF5,
    0x4C, 0x11, 0xF9, 0x49, 0x01, 0xF5, 0x48, 0x13, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x4C, 0x03,
    0x6C, 0x24, 0x50, 0x48, 0x13, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00, 0x49, 0x01, 0xC5, 0x4C, 0x89,
    0xAC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x11, 0xD1, 0x4D, 0x0F, 0xA4, 0xD9, 0x0C, 0x4C, 0x0F,
    0xA4, 0xE9, 0x0C, 0x4C, 0x89, 0xC0, 0x49, 0x89, 0xED, 0x48, 0x89, 0x6C, 0x24, 0x68, 0x48, 0xF7,
    0xE5] ++ bytes_l1159a4_3

theorem code_l1159a4_2 : ∀ x ∈ codeRange 0x115a63 bytes_l1159a4_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15a63 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1159a4_3

def b_l1159a4_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.out 0x115a10 (movR64R64Effect 0x115a10 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[82]
    (.letOp (n := 88) (.exec 0x115a10 (fun s => s.RIP = 0x115a10) (movR64R64Effect 0x115a10 6 0) (Reg.operands [.gpr 0] [])) #v[82]
    (.letOp (n := 89) (.out 0x115a13 (movR64R64Effect 0x115a13 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 90) (.exec 0x115a13 (fun s => s.RIP = 0x115a13) (movR64R64Effect 0x115a13 0 8) (Reg.operands [.gpr 8] [])) #v[65]
    (.letOp (n := 91) (.out 0x115a16 (movR64R64Effect 0x115a16 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 92) (.exec 0x115a16 (fun s => s.RIP = 0x115a16) (movR64R64Effect 0x115a16 7 8) (Reg.operands [.gpr 8] [])) #v[65]
    (.letOp (n := 93) (.exec 0x115a19 (StorePre 0x115a19 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x115a19 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115a19 8 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 94) (.out 0x115a21 (mulR64Effect 0x115a21 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[55, 89]
    (.letOp (n := 95) (.out 0x115a21 (mulR64Effect 0x115a21 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[55, 89]
    (.letOp (n := 96) (.exec 0x115a21 (fun s => s.RIP = 0x115a21) (mulR64Effect 0x115a21 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[55, 89]
    (.letOp (n := 97) (.out 0x115a24 (movR64R64Effect 0x115a24 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[94]
    (.letOp (n := 98) (.exec 0x115a24 (fun s => s.RIP = 0x115a24) (movR64R64Effect 0x115a24 14 0) (Reg.operands [.gpr 0] [])) #v[94]
    (.letOp (n := 99) (.out 0x115a27 (movR64R64Effect 0x115a27 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[95]
    (.letOp (n := 100) (.exec 0x115a27 (fun s => s.RIP = 0x115a27) (movR64R64Effect 0x115a27 15 2) (Reg.operands [.gpr 2] [])) #v[95]
    (.letOp (n := 101) (.out 0x115a2a (movR64M64Effect 0x115a2a 8 (.base 3 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[3]
    (.letOp (n := 102) (.exec 0x115a2a (LoadPre 0x115a2a (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x115a2a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x115a2a 8 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 103) (.out 0x115a2e (movR64R64Effect 0x115a2e 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[62]
    (.letOp (n := 104) (.exec 0x115a2e (fun s => s.RIP = 0x115a2e) (movR64R64Effect 0x115a2e 0 1) (Reg.operands [.gpr 1] [])) #v[62]
    (.letOp (n := 105) (.out 0x115a31 (mulR64Effect 0x115a31 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[53, 103]
    (.letOp (n := 106) (.out 0x115a31 (mulR64Effect 0x115a31 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[53, 103]
    (.letOp (n := 107) (.exec 0x115a31 (fun s => s.RIP = 0x115a31) (mulR64Effect 0x115a31 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[53, 103]
    (.letOp (n := 108) (.out 0x115a34 (movR64R64Effect 0x115a34 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 109) (.exec 0x115a34 (fun s => s.RIP = 0x115a34) (movR64R64Effect 0x115a34 3 11) (Reg.operands [.gpr 11] [])) #v[53]
    (.letOp (n := 110) (.exec 0x115a37 (StorePre 0x115a37 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x115a37 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115a37 11 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 111) (.out 0x115a3f (movR64R64Effect 0x115a3f 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[105]
    (.letOp (n := 112) (.exec 0x115a3f (fun s => s.RIP = 0x115a3f) (movR64R64Effect 0x115a3f 13 0) (Reg.operands [.gpr 0] [])) #v[105]
    (.letOp (n := 113) (.out 0x115a42 (movR64R64Effect 0x115a42 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[106]
    (.letOp (n := 114) (.exec 0x115a42 (fun s => s.RIP = 0x115a42) (movR64R64Effect 0x115a42 1 2) (Reg.operands [.gpr 2] [])) #v[106]
    (.letOp (n := 115) (.out 0x115a45 (movR64M64Effect 0x115a45 2 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 116) (.exec 0x115a45 (LoadPre 0x115a45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x115a45 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115a45 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 117) (.exec 0x115a4a (StorePre 0x115a4a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x115a4a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115a4a 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[115, 4]
    (.letOp (n := 118) (.out 0x115a52 (movR64R64Effect 0x115a52 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[101]
    (.letOp (n := 119) (.exec 0x115a52 (fun s => s.RIP = 0x115a52) (movR64R64Effect 0x115a52 0 8) (Reg.operands [.gpr 8] [])) #v[101]
    (.letOp (n := 120) (.exec 0x115a55 (StorePre 0x115a55 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x115a55 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115a55 8 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[101, 4]
    (.letOp (n := 121) (.out 0x115a5d (mulR64Effect 0x115a5d 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[115, 118]
    (.letOp (n := 122) (.out 0x115a5d (mulR64Effect 0x115a5d 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[115, 118]
    (.letOp (n := 123) (.exec 0x115a5d (fun s => s.RIP = 0x115a5d) (mulR64Effect 0x115a5d 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[115, 118]
    (.letOp (n := 124) (.out 0x115a60 (movR64R64Effect 0x115a60 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[122]
    (.letOp (n := 125) (.exec 0x115a60 (fun s => s.RIP = 0x115a60) (movR64R64Effect 0x115a60 9 2) (Reg.operands [.gpr 2] [])) #v[122]
    (b_l1159a4_2)))))))))))))))))))))))))))))))))))))))

def bytes_l1159a4_1 : List UInt8 :=
  [0x48, 0x89, 0xC6, 0x4C, 0x89, 0xC0, 0x4C, 0x89, 0xC7, 0x4C, 0x89, 0x84, 0x24, 0x48, 0x01, 0x00,
    0x00, 0x49, 0xF7, 0xE1, 0x49, 0x89, 0xC6, 0x49, 0x89, 0xD7, 0x4C, 0x8B, 0x43, 0x20, 0x48, 0x89,
    0xC8, 0x49, 0xF7, 0xE3, 0x4C, 0x89, 0xDB, 0x4C, 0x89, 0x9C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49,
    0x89, 0xC5, 0x48, 0x89, 0xD1, 0x48, 0x8B, 0x54, 0x24, 0x48, 0x48, 0x89, 0x94, 0x24, 0xA8, 0x00,
    0x00, 0x00, 0x4C, 0x89, 0xC0, 0x4C, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x49, 0x89, 0xD1] ++ bytes_l1159a4_2

theorem code_l1159a4_1 : ∀ x ∈ codeRange 0x115a10 bytes_l1159a4_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15a10 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1159a4_2

def b_l1159a4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1159a4 (movR64M64Effect 0x1159a4 11 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 54) (.exec 0x1159a4 (LoadPre 0x1159a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1159a4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1159a4 11 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1159a9 (movR64M64Effect 0x1159a9 9 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 56) (.exec 0x1159a9 (LoadPre 0x1159a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1159a9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1159a9 9 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1159ae (StorePre 0x1159ae 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1159ae + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1159ae 9 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x1159b6 (movR64M64Effect 0x1159b6 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 59) (.exec 0x1159b6 (LoadPre 0x1159b6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1159b6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1159b6 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x1159bb (movR64M64Effect 0x1159bb 10 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 61) (.exec 0x1159bb (LoadPre 0x1159bb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1159bb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1159bb 10 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x1159c0 (movR64M64Effect 0x1159c0 1 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 63) (.exec 0x1159c0 (LoadPre 0x1159c0 (fun s => AddrMode.addr (.base 3 .none) s (0x1159c0 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1159c0 1 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 64) (.exec 0x1159c3 (StorePre 0x1159c3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x1159c3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1159c3 1 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1159cb (movR64M64Effect 0x1159cb 8 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[3]
    (.letOp (n := 66) (.exec 0x1159cb (LoadPre 0x1159cb (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1159cb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1159cb 8 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 67) (.out 0x1159cf (movR64M64Effect 0x1159cf 7 (.base 3 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 68) (.exec 0x1159cf (LoadPre 0x1159cf (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1159cf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1159cf 7 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 69) (.exec 0x1159d3 (StorePre 0x1159d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x1159d3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1159d3 7 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x1159db (movR64M64Effect 0x1159db 12 (.base 3 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[3]
    (.letOp (n := 71) (.exec 0x1159db (LoadPre 0x1159db (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1159db + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1159db 12 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 72) (.out 0x1159df (movR64R64Effect 0x1159df 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 73) (.exec 0x1159df (fun s => s.RIP = 0x1159df) (movR64R64Effect 0x1159df 0 12) (Reg.operands [.gpr 12] [])) #v[70]
    (.letOp (n := 74) (.exec 0x1159e2 (StorePre 0x1159e2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1159e2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1159e2 12 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 75) (.out 0x1159ea (mulR64Effect 0x1159ea 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[58, 72]
    (.letOp (n := 76) (.out 0x1159ea (mulR64Effect 0x1159ea 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[58, 72]
    (.letOp (n := 77) (.exec 0x1159ea (fun s => s.RIP = 0x1159ea) (mulR64Effect 0x1159ea 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[58, 72]
    (.letOp (n := 78) (.exec 0x1159ed (StorePre 0x1159ed 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1159ed + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1159ed 2 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.exec 0x1159f5 (StorePre 0x1159f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1159f5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1159f5 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 80) (.out 0x1159fa (movR64R64Effect 0x1159fa 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 81) (.exec 0x1159fa (fun s => s.RIP = 0x1159fa) (movR64R64Effect 0x1159fa 0 7) (Reg.operands [.gpr 7] [])) #v[67]
    (.letOp (n := 82) (.out 0x1159fd (mulR64Effect 0x1159fd 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[60, 80]
    (.letOp (n := 83) (.out 0x1159fd (mulR64Effect 0x1159fd 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[60, 80]
    (.letOp (n := 84) (.exec 0x1159fd (fun s => s.RIP = 0x1159fd) (mulR64Effect 0x1159fd 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[60, 80]
    (.letOp (n := 85) (.exec 0x115a00 (StorePre 0x115a00 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x115a00 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115a00 10 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 86) (.exec 0x115a08 (StorePre 0x115a08 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x115a08 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115a08 2 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[83, 4]
    (b_l1159a4_1))))))))))))))))))))))))))))))))))

def bytes_l1159a4 : List UInt8 :=
  [0x4C, 0x8B, 0x5C, 0x24, 0x40, 0x4C, 0x8B, 0x4C, 0x24, 0x38, 0x4C, 0x89, 0x8C, 0x24, 0xA0, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x6C, 0x24, 0x28, 0x4C, 0x8B, 0x54, 0x24, 0x30, 0x48, 0x8B, 0x0B, 0x48,
    0x89, 0x8C, 0x24, 0x60, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x43, 0x08, 0x48, 0x8B, 0x7B, 0x10, 0x48,
    0x89, 0xBC, 0x24, 0x30, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x63, 0x18, 0x4C, 0x89, 0xE0, 0x4C, 0x89,
    0xA4, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0x94, 0x24, 0x00, 0x01, 0x00,
    0x00, 0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0x89, 0xF8, 0x49, 0xF7, 0xE2, 0x4C, 0x89, 0x94, 0x24,
    0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00] ++ bytes_l1159a4_1

theorem code_l1159a4 : ∀ x ∈ codeRange 0x1159a4 bytes_l1159a4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x159a4 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1159a4_1

def b_l115e4d_12 : Block Op Label signature Reg.count 573 :=
  .letOp (n := 573) (.exec 0x116271 (StorePre 0x116271 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x116271 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116271 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[571, 4]
    (.letOp (n := 574) (.out 0x116276 (andR64R64Effect 0x116276 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[543, 493]
    (.letOp (n := 575) (.exec 0x116276 (fun s => s.RIP = 0x116276) (andR64R64Effect 0x116276 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[543, 493]
    (.letOp (n := 576) (.exec 0x116279 (StorePre 0x116279 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x116279 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116279 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[574, 4]
    (.letOp (n := 577) (.exec 0x11627e (StorePre 0x11627e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11627e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11627e 12 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[574, 4]
    (.letOp (n := 578) (.exec 0x116286 (StorePre 0x116286 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x116286 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116286 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[557, 4]
    (.letOp (n := 579) (.out 0x11628b (leaR64Effect 0x11628b 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 580) (.exec 0x11628b (fun s => s.RIP = 0x11628b) (leaR64Effect 0x11628b 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 581) (.out 0x116290 (movR64R64Effect 0x116290 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 582) (.exec 0x116290 (fun s => s.RIP = 0x116290) (movR64R64Effect 0x116290 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 583) (.out 0x116293 (movR64R64Effect 0x116293 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[579]
    (.letOp (n := 584) (.exec 0x116293 (fun s => s.RIP = 0x116293) (movR64R64Effect 0x116293 7 3) (Reg.operands [.gpr 3] [])) #v[579]
    (.letOp (n := 585) (.out 0x116296 (movR64R64Effect 0x116296 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[581]
    (.letOp (n := 586) (.exec 0x116296 (fun s => s.RIP = 0x116296) (movR64R64Effect 0x116296 6 14) (Reg.operands [.gpr 14] [])) #v[581]
    (.letOp (n := 587) (.out 0x116299 (callEffect (fun _ => 0x1145f0) 0x11629e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 588) (.exec 0x116299 (PushPre 0x116299 5) (callEffect (fun _ => 0x1145f0) 0x11629e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 589) (.const ⟨64, 0x11629e⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 551), (1, 497), (2, 562), (3, 579), (4, 587), (5, 557), (6, 585), (7, 583), (8, 524), (9, 441), (10, 434), (11, 443), (12, 574), (13, 568), (14, 581), (15, 571), (22, 22), (39, 39), (50, 50), (51, 51)] 590⟩ { target := .l11629e, kept := #v[], arity := rfl, guard := some (Fin.last 589) }))))))))))))))))))

def bytes_l115e4d_12 : List UInt8 :=
  [0x4C, 0x89, 0x7C, 0x24, 0x10, 0x49, 0x21, 0xDC, 0x4C, 0x89, 0x64, 0x24, 0x18, 0x4C, 0x89, 0xA4,
    0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x6C, 0x24, 0x20, 0x48, 0x8D, 0x5C, 0x24, 0x28, 0x49,
    0x89, 0xE6, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x52, 0xE3, 0xFF, 0xFF]

theorem code_l115e4d_12 : ∀ x ∈ codeRange 0x116271 bytes_l115e4d_12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x16271 45 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l115e4d_11 : Block Op Label signature Reg.count 536 :=
  .letOp (n := 536) (.out 0x11620c (andR64R64Effect 0x11620c 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[534, 493]
    (.letOp (n := 537) (.exec 0x11620c (fun s => s.RIP = 0x11620c) (andR64R64Effect 0x11620c 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[534, 493]
    (.letOp (n := 538) (.out 0x11620f (addR64R64Effect 0x11620f 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[536, 530]
    (.letOp (n := 539) (.out 0x11620f (addR64R64Effect 0x11620f 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[536, 530]
    (.letOp (n := 540) (.exec 0x11620f (fun s => s.RIP = 0x11620f) (addR64R64Effect 0x11620f 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[536, 530]
    (.letOp (n := 541) (.out 0x116212 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116212 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[531, 539]
    (.letOp (n := 542) (.exec 0x116212 (fun s => s.RIP = 0x116212) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116212 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[531, 539]
    (.letOp (n := 543) (.out 0x116216 (addR64R64Effect 0x116216 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 8] []) (.reg (.gpr 12))) #v[538, 524]
    (.letOp (n := 544) (.out 0x116216 (addR64R64Effect 0x116216 12 8) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 8] []) (.flag .CF)) #v[538, 524]
    (.letOp (n := 545) (.exec 0x116216 (fun s => s.RIP = 0x116216) (addR64R64Effect 0x116216 12 8) (Reg.operands [.gpr 12, .gpr 8] [])) #v[538, 524]
    (.letOp (n := 546) (.out 0x116219 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116219 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[541, 544]
    (.letOp (n := 547) (.exec 0x116219 (fun s => s.RIP = 0x116219) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116219 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[541, 544]
    (.letOp (n := 548) (.out 0x11621d (shldR64R64Effect 0x11621d 5 2 12 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[546, 543]
    (.letOp (n := 549) (.exec 0x11621d (fun s => s.RIP = 0x11621d) (shldR64R64Effect 0x11621d 5 2 12 12) (Reg.operands [.gpr 2, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[546, 543]
    (.letOp (n := 550) (.exec 0x116222 (StorePre 0x116222 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x116222 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116222 13 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[465, 4]
    (.letOp (n := 551) (.out 0x116227 (movR64Imm64Effect 0x116227 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 552) (.exec 0x116227 (fun s => s.RIP = 0x116227) (movR64Imm64Effect 0x116227 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 553) (.out 0x116231 (movR64M64Effect 0x116231 5 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 554) (.exec 0x116231 (LoadPre 0x116231 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x116231 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116231 5 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 555) (.out 0x116239 (andR64R64Effect 0x116239 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[553, 551]
    (.letOp (n := 556) (.exec 0x116239 (fun s => s.RIP = 0x116239) (andR64R64Effect 0x116239 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[553, 551]
    (.letOp (n := 557) (.out 0x11623c (addR64R64Effect 0x11623c 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[555, 548]
    (.letOp (n := 558) (.exec 0x11623c (fun s => s.RIP = 0x11623c) (addR64R64Effect 0x11623c 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[555, 548]
    (.letOp (n := 559) (.exec 0x11623f (StorePre 0x11623f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11623f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11623f 5 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[557, 4]
    (.letOp (n := 560) (.out 0x116247 (movR64M64Effect 0x116247 2 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 561) (.exec 0x116247 (LoadPre 0x116247 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x116247 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116247 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 562) (.out 0x11624f (andR64R64Effect 0x11624f 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[560, 493]
    (.letOp (n := 563) (.exec 0x11624f (fun s => s.RIP = 0x11624f) (andR64R64Effect 0x11624f 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[560, 493]
    (.letOp (n := 564) (.exec 0x116252 (StorePre 0x116252 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x116252 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x116252 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[562, 4]
    (.letOp (n := 565) (.exec 0x11625a (StorePre 0x11625a 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11625a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11625a 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[562, 4]
    (.letOp (n := 566) (.out 0x11625e (movR64M64Effect 0x11625e 13 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 567) (.exec 0x11625e (LoadPre 0x11625e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11625e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11625e 13 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 568) (.out 0x116266 (andR64R64Effect 0x116266 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[566, 493]
    (.letOp (n := 569) (.exec 0x116266 (fun s => s.RIP = 0x116266) (andR64R64Effect 0x116266 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[566, 493]
    (.letOp (n := 570) (.exec 0x116269 (StorePre 0x116269 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x116269 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116269 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[568, 4]
    (.letOp (n := 571) (.out 0x11626e (andR64R64Effect 0x11626e 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[526, 493]
    (.letOp (n := 572) (.exec 0x11626e (fun s => s.RIP = 0x11626e) (andR64R64Effect 0x11626e 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[526, 493]
    (b_l115e4d_12)))))))))))))))))))))))))))))))))))))

def bytes_l115e4d_11 : List UInt8 :=
  [0x49, 0x21, 0xDC, 0x49, 0x01, 0xC4, 0x48, 0x83, 0xD2, 0x00, 0x4D, 0x01, 0xC4, 0x48, 0x83, 0xD2,
    0x00, 0x4C, 0x0F, 0xA4, 0xE2, 0x0C, 0x4C, 0x89, 0x6C, 0x24, 0x18, 0x48, 0xB8, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x8B, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x21, 0xC5,
    0x48, 0x01, 0xD5, 0x48, 0x89, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x48, 0x21, 0xDA, 0x48, 0x89, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89,
    0x14, 0x24, 0x4C, 0x8B, 0xAC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0x21, 0xDD, 0x4C, 0x89, 0x6C,
    0x24, 0x08, 0x49, 0x21, 0xDF] ++ bytes_l115e4d_12

theorem code_l115e4d_11 : ∀ x ∈ codeRange 0x11620c bytes_l115e4d_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1620c 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115e4d_12

def b_l115e4d_10 : Block Op Label signature Reg.count 491 :=
  .letOp (n := 491) (.out 0x1161b6 (movR64R64Effect 0x1161b6 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[486]
    (.letOp (n := 492) (.exec 0x1161b6 (fun s => s.RIP = 0x1161b6) (movR64R64Effect 0x1161b6 0 15) (Reg.operands [.gpr 15] [])) #v[486]
    (.letOp (n := 493) (.out 0x1161b9 (movR64Imm64Effect 0x1161b9 3 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 494) (.exec 0x1161b9 (fun s => s.RIP = 0x1161b9) (movR64Imm64Effect 0x1161b9 3 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 495) (.out 0x1161c3 (andR64R64Effect 0x1161c3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[491, 493]
    (.letOp (n := 496) (.exec 0x1161c3 (fun s => s.RIP = 0x1161c3) (andR64R64Effect 0x1161c3 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[491, 493]
    (.letOp (n := 497) (.out 0x1161c6 (movR64Imm64Effect 0x1161c6 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 498) (.exec 0x1161c6 (fun s => s.RIP = 0x1161c6) (movR64Imm64Effect 0x1161c6 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 499) (.out 0x1161d0 (mulR64Effect 0x1161d0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[497, 495]
    (.letOp (n := 500) (.out 0x1161d0 (mulR64Effect 0x1161d0 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[497, 495]
    (.letOp (n := 501) (.exec 0x1161d0 (fun s => s.RIP = 0x1161d0) (mulR64Effect 0x1161d0 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[497, 495]
    (.letOp (n := 502) (.out 0x1161d3 (addR64R64Effect 0x1161d3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[452, 443]
    (.letOp (n := 503) (.out 0x1161d3 (addR64R64Effect 0x1161d3 6 11) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 11] []) (.flag .CF)) #v[452, 443]
    (.letOp (n := 504) (.exec 0x1161d3 (fun s => s.RIP = 0x1161d3) (addR64R64Effect 0x1161d3 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[452, 443]
    (.letOp (n := 505) (.out 0x1161d6 (atFlags StatusFlags.CF (adcR64R64Effect 0x1161d6 8 9)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[450, 441, 503]
    (.letOp (n := 506) (.exec 0x1161d6 (fun s => s.RIP = 0x1161d6) (atFlags StatusFlags.CF (adcR64R64Effect 0x1161d6 8 9)) (Reg.operands [.gpr 8, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[450, 441, 503]
    (.letOp (n := 507) (.out 0x1161d9 (addR64R64Effect 0x1161d9 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[502, 461]
    (.letOp (n := 508) (.out 0x1161d9 (addR64R64Effect 0x1161d9 6 12) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 12] []) (.flag .CF)) #v[502, 461]
    (.letOp (n := 509) (.exec 0x1161d9 (fun s => s.RIP = 0x1161d9) (addR64R64Effect 0x1161d9 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[502, 461]
    (.letOp (n := 510) (.out 0x1161dc (atFlags StatusFlags.CF (adcR64R64Effect 0x1161dc 8 14)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[505, 459, 508]
    (.letOp (n := 511) (.exec 0x1161dc (fun s => s.RIP = 0x1161dc) (atFlags StatusFlags.CF (adcR64R64Effect 0x1161dc 8 14)) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[505, 459, 508]
    (.letOp (n := 512) (.out 0x1161df (addR64R64Effect 0x1161df 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[507, 499]
    (.letOp (n := 513) (.out 0x1161df (addR64R64Effect 0x1161df 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[507, 499]
    (.letOp (n := 514) (.exec 0x1161df (fun s => s.RIP = 0x1161df) (addR64R64Effect 0x1161df 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[507, 499]
    (.letOp (n := 515) (.out 0x1161e2 (atFlags StatusFlags.CF (adcR64R64Effect 0x1161e2 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[510, 500, 513]
    (.letOp (n := 516) (.exec 0x1161e2 (fun s => s.RIP = 0x1161e2) (atFlags StatusFlags.CF (adcR64R64Effect 0x1161e2 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[510, 500, 513]
    (.letOp (n := 517) (.out 0x1161e5 (addR64R64Effect 0x1161e5 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[512, 434]
    (.letOp (n := 518) (.out 0x1161e5 (addR64R64Effect 0x1161e5 6 10) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 10] []) (.flag .CF)) #v[512, 434]
    (.letOp (n := 519) (.exec 0x1161e5 (fun s => s.RIP = 0x1161e5) (addR64R64Effect 0x1161e5 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[512, 434]
    (.letOp (n := 520) (.out 0x1161e8 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1161e8 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[515, 518]
    (.letOp (n := 521) (.exec 0x1161e8 (fun s => s.RIP = 0x1161e8) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1161e8 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[515, 518]
    (.letOp (n := 522) (.out 0x1161ec (shldR64R64Effect 0x1161ec 5 7 15 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[489, 486]
    (.letOp (n := 523) (.exec 0x1161ec (fun s => s.RIP = 0x1161ec) (shldR64R64Effect 0x1161ec 5 7 15 12) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[489, 486]
    (.letOp (n := 524) (.out 0x1161f1 (shldR64R64Effect 0x1161f1 5 8 6 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[520, 517]
    (.letOp (n := 525) (.exec 0x1161f1 (fun s => s.RIP = 0x1161f1) (shldR64R64Effect 0x1161f1 5 8 6 12) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[520, 517]
    (.letOp (n := 526) (.out 0x1161f6 (movR64R64Effect 0x1161f6 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[517]
    (.letOp (n := 527) (.exec 0x1161f6 (fun s => s.RIP = 0x1161f6) (movR64R64Effect 0x1161f6 15 6) (Reg.operands [.gpr 6] [])) #v[517]
    (.letOp (n := 528) (.out 0x1161f9 (movR64R64Effect 0x1161f9 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[522]
    (.letOp (n := 529) (.exec 0x1161f9 (fun s => s.RIP = 0x1161f9) (movR64R64Effect 0x1161f9 0 7) (Reg.operands [.gpr 7] [])) #v[522]
    (.letOp (n := 530) (.out 0x1161fc (mulR64Effect 0x1161fc 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[497, 528]
    (.letOp (n := 531) (.out 0x1161fc (mulR64Effect 0x1161fc 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[497, 528]
    (.letOp (n := 532) (.exec 0x1161fc (fun s => s.RIP = 0x1161fc) (mulR64Effect 0x1161fc 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[497, 528]
    (.letOp (n := 533) (.exec 0x1161ff (StorePre 0x1161ff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1161ff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1161ff 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[383, 4]
    (.letOp (n := 534) (.out 0x116204 (movR64M64Effect 0x116204 12 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 535) (.exec 0x116204 (LoadPre 0x116204 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x116204 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116204 12 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l115e4d_11)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l115e4d_10 : List UInt8 :=
  [0x4C, 0x89, 0xF8, 0x48, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD8,
    0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x4C, 0x01, 0xDE,
    0x4D, 0x11, 0xC8, 0x4C, 0x01, 0xE6, 0x4D, 0x11, 0xF0, 0x48, 0x01, 0xC6, 0x49, 0x11, 0xD0, 0x4C,
    0x01, 0xD6, 0x49, 0x83, 0xD0, 0x00, 0x4C, 0x0F, 0xA4, 0xFF, 0x0C, 0x49, 0x0F, 0xA4, 0xF0, 0x0C,
    0x49, 0x89, 0xF7, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0x6C, 0x24, 0x20, 0x4C, 0x8B,
    0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00] ++ bytes_l115e4d_11

theorem code_l115e4d_10 : ∀ x ∈ codeRange 0x1161b6 bytes_l115e4d_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x161b6 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115e4d_11

def b_l115e4d_9 : Block Op Label signature Reg.count 445 :=
  .letOp (n := 445) (.out 0x116163 (movR64M64Effect 0x116163 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 446) (.exec 0x116163 (LoadPre 0x116163 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x116163 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116163 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 447) (.out 0x116168 (mulM64Effect 0x116168 8 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[445, 4]
    (.letOp (n := 448) (.out 0x116168 (mulM64Effect 0x116168 8 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[445, 4]
    (.letOp (n := 449) (.exec 0x116168 (LoadPre 0x116168 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x116168 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x116168 8 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[445, 4]
    (.letOp (n := 450) (.out 0x116170 (movR64R64Effect 0x116170 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[448]
    (.letOp (n := 451) (.exec 0x116170 (fun s => s.RIP = 0x116170) (movR64R64Effect 0x116170 8 2) (Reg.operands [.gpr 2] [])) #v[448]
    (.letOp (n := 452) (.out 0x116173 (movR64R64Effect 0x116173 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[447]
    (.letOp (n := 453) (.exec 0x116173 (fun s => s.RIP = 0x116173) (movR64R64Effect 0x116173 6 0) (Reg.operands [.gpr 0] [])) #v[447]
    (.letOp (n := 454) (.out 0x116176 (movR64M64Effect 0x116176 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 455) (.exec 0x116176 (LoadPre 0x116176 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x116176 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116176 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 456) (.out 0x11617e (mulR64Effect 0x11617e 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[354, 454]
    (.letOp (n := 457) (.out 0x11617e (mulR64Effect 0x11617e 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[354, 454]
    (.letOp (n := 458) (.exec 0x11617e (fun s => s.RIP = 0x11617e) (mulR64Effect 0x11617e 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[354, 454]
    (.letOp (n := 459) (.out 0x116181 (movR64R64Effect 0x116181 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[457]
    (.letOp (n := 460) (.exec 0x116181 (fun s => s.RIP = 0x116181) (movR64R64Effect 0x116181 14 2) (Reg.operands [.gpr 2] [])) #v[457]
    (.letOp (n := 461) (.out 0x116184 (movR64R64Effect 0x116184 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[456]
    (.letOp (n := 462) (.exec 0x116184 (fun s => s.RIP = 0x116184) (movR64R64Effect 0x116184 12 0) (Reg.operands [.gpr 0] [])) #v[456]
    (.letOp (n := 463) (.out 0x116187 (movR64R64Effect 0x116187 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[372]
    (.letOp (n := 464) (.exec 0x116187 (fun s => s.RIP = 0x116187) (movR64R64Effect 0x116187 0 15) (Reg.operands [.gpr 15] [])) #v[372]
    (.letOp (n := 465) (.out 0x11618a (movR64R64Effect 0x11618a 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[372]
    (.letOp (n := 466) (.exec 0x11618a (fun s => s.RIP = 0x11618a) (movR64R64Effect 0x11618a 13 15) (Reg.operands [.gpr 15] [])) #v[372]
    (.letOp (n := 467) (.out 0x11618d (mulM64Effect 0x11618d 8 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[463, 4]
    (.letOp (n := 468) (.out 0x11618d (mulM64Effect 0x11618d 8 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[463, 4]
    (.letOp (n := 469) (.exec 0x11618d (LoadPre 0x11618d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x11618d + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11618d 8 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[463, 4]
    (.letOp (n := 470) (.out 0x116195 (movR64R64Effect 0x116195 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[468]
    (.letOp (n := 471) (.exec 0x116195 (fun s => s.RIP = 0x116195) (movR64R64Effect 0x116195 7 2) (Reg.operands [.gpr 2] [])) #v[468]
    (.letOp (n := 472) (.out 0x116198 (movR64R64Effect 0x116198 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[467]
    (.letOp (n := 473) (.exec 0x116198 (fun s => s.RIP = 0x116198) (movR64R64Effect 0x116198 1 0) (Reg.operands [.gpr 0] [])) #v[467]
    (.letOp (n := 474) (.out 0x11619b (movR64R64Effect 0x11619b 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[383]
    (.letOp (n := 475) (.exec 0x11619b (fun s => s.RIP = 0x11619b) (movR64R64Effect 0x11619b 0 5) (Reg.operands [.gpr 5] [])) #v[383]
    (.letOp (n := 476) (.out 0x11619e (mulM64Effect 0x11619e 8 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[474, 4]
    (.letOp (n := 477) (.out 0x11619e (mulM64Effect 0x11619e 8 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[474, 4]
    (.letOp (n := 478) (.exec 0x11619e (LoadPre 0x11619e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x11619e + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11619e 8 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[474, 4]
    (.letOp (n := 479) (.out 0x1161a6 (movR64R64Effect 0x1161a6 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[476]
    (.letOp (n := 480) (.exec 0x1161a6 (fun s => s.RIP = 0x1161a6) (movR64R64Effect 0x1161a6 15 0) (Reg.operands [.gpr 0] [])) #v[476]
    (.letOp (n := 481) (.out 0x1161a9 (addR64R64Effect 0x1161a9 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[479, 472]
    (.letOp (n := 482) (.out 0x1161a9 (addR64R64Effect 0x1161a9 15 1) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 1] []) (.flag .CF)) #v[479, 472]
    (.letOp (n := 483) (.exec 0x1161a9 (fun s => s.RIP = 0x1161a9) (addR64R64Effect 0x1161a9 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[479, 472]
    (.letOp (n := 484) (.out 0x1161ac (atFlags StatusFlags.CF (adcR64R64Effect 0x1161ac 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[470, 477, 482]
    (.letOp (n := 485) (.exec 0x1161ac (fun s => s.RIP = 0x1161ac) (atFlags StatusFlags.CF (adcR64R64Effect 0x1161ac 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[470, 477, 482]
    (.letOp (n := 486) (.out 0x1161af (addR64R64Effect 0x1161af 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[481, 407]
    (.letOp (n := 487) (.out 0x1161af (addR64R64Effect 0x1161af 15 3) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 3] []) (.flag .CF)) #v[481, 407]
    (.letOp (n := 488) (.exec 0x1161af (fun s => s.RIP = 0x1161af) (addR64R64Effect 0x1161af 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[481, 407]
    (.letOp (n := 489) (.out 0x1161b2 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1161b2 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[484, 487]
    (.letOp (n := 490) (.exec 0x1161b2 (fun s => s.RIP = 0x1161b2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1161b2 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[484, 487]
    (b_l115e4d_10))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l115e4d_9 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0xF7, 0xA4, 0x24, 0x48, 0x01, 0x00, 0x00, 0x49, 0x89, 0xD0,
    0x48, 0x89, 0xC6, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x49, 0x89,
    0xD6, 0x49, 0x89, 0xC4, 0x4C, 0x89, 0xF8, 0x4D, 0x89, 0xFD, 0x48, 0xF7, 0xA4, 0x24, 0x40, 0x01,
    0x00, 0x00, 0x48, 0x89, 0xD7, 0x48, 0x89, 0xC1, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0xA4, 0x24, 0x50,
    0x01, 0x00, 0x00, 0x49, 0x89, 0xC7, 0x49, 0x01, 0xCF, 0x48, 0x11, 0xD7, 0x49, 0x01, 0xDF, 0x48,
    0x83, 0xD7, 0x00] ++ bytes_l115e4d_10

theorem code_l115e4d_9 : ∀ x ∈ codeRange 0x116163 bytes_l115e4d_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16163 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115e4d_10

def b_l115e4d_8 : Block Op Label signature Reg.count 400 :=
  .letOp (n := 400) (.out 0x116104 (atFlags StatusFlags.CF (adcR64R64Effect 0x116104 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[395, 390, 398]
    (.letOp (n := 401) (.exec 0x116104 (fun s => s.RIP = 0x116104) (atFlags StatusFlags.CF (adcR64R64Effect 0x116104 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[395, 390, 398]
    (.letOp (n := 402) (.out 0x116107 (addR64R64Effect 0x116107 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[397, 318]
    (.letOp (n := 403) (.out 0x116107 (addR64R64Effect 0x116107 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[397, 318]
    (.letOp (n := 404) (.exec 0x116107 (fun s => s.RIP = 0x116107) (addR64R64Effect 0x116107 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[397, 318]
    (.letOp (n := 405) (.out 0x11610a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11610a 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[400, 403]
    (.letOp (n := 406) (.exec 0x11610a (fun s => s.RIP = 0x11610a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11610a 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[400, 403]
    (.letOp (n := 407) (.out 0x11610e (shldR64R64Effect 0x11610e 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[405, 402]
    (.letOp (n := 408) (.exec 0x11610e (fun s => s.RIP = 0x11610e) (shldR64R64Effect 0x11610e 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[405, 402]
    (.letOp (n := 409) (.out 0x116113 (movR64Imm64Effect 0x116113 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 410) (.exec 0x116113 (fun s => s.RIP = 0x116113) (movR64Imm64Effect 0x116113 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 411) (.out 0x11611d (andR64R64Effect 0x11611d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[402, 409]
    (.letOp (n := 412) (.exec 0x11611d (fun s => s.RIP = 0x11611d) (andR64R64Effect 0x11611d 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[402, 409]
    (.letOp (n := 413) (.out 0x116120 (movR64Imm64Effect 0x116120 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 414) (.exec 0x116120 (fun s => s.RIP = 0x116120) (movR64Imm64Effect 0x116120 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 415) (.out 0x11612a (mulR64Effect 0x11612a 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[413, 411]
    (.letOp (n := 416) (.out 0x11612a (mulR64Effect 0x11612a 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[413, 411]
    (.letOp (n := 417) (.exec 0x11612a (fun s => s.RIP = 0x11612a) (mulR64Effect 0x11612a 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[413, 411]
    (.letOp (n := 418) (.out 0x11612d (addR64M64Effect 0x11612d 8 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[361, 4]
    (.letOp (n := 419) (.out 0x11612d (addR64M64Effect 0x11612d 8 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[361, 4]
    (.letOp (n := 420) (.exec 0x11612d (LoadPre 0x11612d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11612d + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11612d 8 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[361, 4]
    (.letOp (n := 421) (.out 0x116135 (atFlags StatusFlags.CF (adcR64M64Effect 0x116135 10 (.sib 4 none 0 (.d32 0xb0)))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 10))) #v[359, 4, 419]
    (.letOp (n := 422) (.exec 0x116135 (LoadPre 0x116135 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x116135 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x116135 10 (.sib 4 none 0 (.d32 0xb0)))) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[359, 4, 419]
    (.letOp (n := 423) (.out 0x11613d (addR64R64Effect 0x11613d 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[418, 415]
    (.letOp (n := 424) (.out 0x11613d (addR64R64Effect 0x11613d 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[418, 415]
    (.letOp (n := 425) (.exec 0x11613d (fun s => s.RIP = 0x11613d) (addR64R64Effect 0x11613d 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[418, 415]
    (.letOp (n := 426) (.out 0x116140 (atFlags StatusFlags.CF (adcR64R64Effect 0x116140 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[421, 416, 424]
    (.letOp (n := 427) (.exec 0x116140 (fun s => s.RIP = 0x116140) (atFlags StatusFlags.CF (adcR64R64Effect 0x116140 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[421, 416, 424]
    (.letOp (n := 428) (.out 0x116143 (addR64R64Effect 0x116143 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[423, 341]
    (.letOp (n := 429) (.out 0x116143 (addR64R64Effect 0x116143 8 14) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 14] []) (.flag .CF)) #v[423, 341]
    (.letOp (n := 430) (.exec 0x116143 (fun s => s.RIP = 0x116143) (addR64R64Effect 0x116143 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[423, 341]
    (.letOp (n := 431) (.exec 0x116146 (StorePre 0x116146 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x116146 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x116146 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[428, 4]
    (.letOp (n := 432) (.out 0x11614e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11614e 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[426, 429]
    (.letOp (n := 433) (.exec 0x11614e (fun s => s.RIP = 0x11614e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11614e 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[426, 429]
    (.letOp (n := 434) (.out 0x116152 (shldR64R64Effect 0x116152 5 10 8 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[432, 428]
    (.letOp (n := 435) (.exec 0x116152 (fun s => s.RIP = 0x116152) (shldR64R64Effect 0x116152 5 10 8 12) (Reg.operands [.gpr 10, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[432, 428]
    (.letOp (n := 436) (.out 0x116157 (movR64R64Effect 0x116157 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[343]
    (.letOp (n := 437) (.exec 0x116157 (fun s => s.RIP = 0x116157) (movR64R64Effect 0x116157 0 12) (Reg.operands [.gpr 12] [])) #v[343]
    (.letOp (n := 438) (.out 0x11615a (mulR64Effect 0x11615a 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[387, 436]
    (.letOp (n := 439) (.out 0x11615a (mulR64Effect 0x11615a 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[387, 436]
    (.letOp (n := 440) (.exec 0x11615a (fun s => s.RIP = 0x11615a) (mulR64Effect 0x11615a 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[387, 436]
    (.letOp (n := 441) (.out 0x11615d (movR64R64Effect 0x11615d 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[439]
    (.letOp (n := 442) (.exec 0x11615d (fun s => s.RIP = 0x11615d) (movR64R64Effect 0x11615d 9 2) (Reg.operands [.gpr 2] [])) #v[439]
    (.letOp (n := 443) (.out 0x116160 (movR64R64Effect 0x116160 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[438]
    (.letOp (n := 444) (.exec 0x116160 (fun s => s.RIP = 0x116160) (movR64R64Effect 0x116160 11 0) (Reg.operands [.gpr 0] [])) #v[438]
    (b_l115e4d_9)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l115e4d_8 : List UInt8 :=
  [0x48, 0x11, 0xD3, 0x4C, 0x01, 0xD8, 0x48, 0x83, 0xD3, 0x00, 0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x48,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8, 0x48, 0xB9, 0x10, 0x3D,
    0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x4C, 0x03, 0x84, 0x24, 0xC0, 0x00, 0x00,
    0x00, 0x4C, 0x13, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC0, 0x49, 0x11, 0xD2, 0x4D,
    0x01, 0xF0, 0x4C, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0x83, 0xD2, 0x00, 0x4D, 0x0F,
    0xA4, 0xC2, 0x0C, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE1, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC3] ++ bytes_l115e4d_9

theorem code_l115e4d_8 : ∀ x ∈ codeRange 0x116104 bytes_l115e4d_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16104 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115e4d_9

def b_l115e4d_7 : Block Op Label signature Reg.count 354 :=
  .letOp (n := 354) (.out 0x1160b7 (movR64M64Effect 0x1160b7 13 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 355) (.exec 0x1160b7 (LoadPre 0x1160b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x1160b7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1160b7 13 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 356) (.out 0x1160bf (mulR64Effect 0x1160bf 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[354, 352]
    (.letOp (n := 357) (.out 0x1160bf (mulR64Effect 0x1160bf 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[354, 352]
    (.letOp (n := 358) (.exec 0x1160bf (fun s => s.RIP = 0x1160bf) (mulR64Effect 0x1160bf 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[354, 352]
    (.letOp (n := 359) (.out 0x1160c2 (movR64R64Effect 0x1160c2 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[357]
    (.letOp (n := 360) (.exec 0x1160c2 (fun s => s.RIP = 0x1160c2) (movR64R64Effect 0x1160c2 10 2) (Reg.operands [.gpr 2] [])) #v[357]
    (.letOp (n := 361) (.out 0x1160c5 (movR64R64Effect 0x1160c5 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[356]
    (.letOp (n := 362) (.exec 0x1160c5 (fun s => s.RIP = 0x1160c5) (movR64R64Effect 0x1160c5 8 0) (Reg.operands [.gpr 0] [])) #v[356]
    (.letOp (n := 363) (.out 0x1160c8 (movR64R64Effect 0x1160c8 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[269]
    (.letOp (n := 364) (.exec 0x1160c8 (fun s => s.RIP = 0x1160c8) (movR64R64Effect 0x1160c8 0 9) (Reg.operands [.gpr 9] [])) #v[269]
    (.letOp (n := 365) (.out 0x1160cb (mulR64Effect 0x1160cb 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[258, 363]
    (.letOp (n := 366) (.out 0x1160cb (mulR64Effect 0x1160cb 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[258, 363]
    (.letOp (n := 367) (.exec 0x1160cb (fun s => s.RIP = 0x1160cb) (mulR64Effect 0x1160cb 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[258, 363]
    (.letOp (n := 368) (.out 0x1160ce (movR64R64Effect 0x1160ce 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[366]
    (.letOp (n := 369) (.exec 0x1160ce (fun s => s.RIP = 0x1160ce) (movR64R64Effect 0x1160ce 1 2) (Reg.operands [.gpr 2] [])) #v[366]
    (.letOp (n := 370) (.out 0x1160d1 (movR64R64Effect 0x1160d1 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[365]
    (.letOp (n := 371) (.exec 0x1160d1 (fun s => s.RIP = 0x1160d1) (movR64R64Effect 0x1160d1 6 0) (Reg.operands [.gpr 0] [])) #v[365]
    (.letOp (n := 372) (.out 0x1160d4 (movR64M64Effect 0x1160d4 15 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 373) (.exec 0x1160d4 (LoadPre 0x1160d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1160d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1160d4 15 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 374) (.out 0x1160d9 (movR64R64Effect 0x1160d9 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[372]
    (.letOp (n := 375) (.exec 0x1160d9 (fun s => s.RIP = 0x1160d9) (movR64R64Effect 0x1160d9 0 15) (Reg.operands [.gpr 15] [])) #v[372]
    (.letOp (n := 376) (.out 0x1160dc (mulR64Effect 0x1160dc 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[273, 374]
    (.letOp (n := 377) (.out 0x1160dc (mulR64Effect 0x1160dc 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[273, 374]
    (.letOp (n := 378) (.exec 0x1160dc (fun s => s.RIP = 0x1160dc) (mulR64Effect 0x1160dc 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[273, 374]
    (.letOp (n := 379) (.out 0x1160df (movR64R64Effect 0x1160df 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[377]
    (.letOp (n := 380) (.exec 0x1160df (fun s => s.RIP = 0x1160df) (movR64R64Effect 0x1160df 3 2) (Reg.operands [.gpr 2] [])) #v[377]
    (.letOp (n := 381) (.out 0x1160e2 (movR64R64Effect 0x1160e2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[376]
    (.letOp (n := 382) (.exec 0x1160e2 (fun s => s.RIP = 0x1160e2) (movR64R64Effect 0x1160e2 7 0) (Reg.operands [.gpr 0] [])) #v[376]
    (.letOp (n := 383) (.out 0x1160e5 (movR64M64Effect 0x1160e5 5 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 384) (.exec 0x1160e5 (LoadPre 0x1160e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1160e5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1160e5 5 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 385) (.out 0x1160ed (movR64R64Effect 0x1160ed 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[383]
    (.letOp (n := 386) (.exec 0x1160ed (fun s => s.RIP = 0x1160ed) (movR64R64Effect 0x1160ed 0 5) (Reg.operands [.gpr 5] [])) #v[383]
    (.letOp (n := 387) (.out 0x1160f0 (movR64M64Effect 0x1160f0 9 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 388) (.exec 0x1160f0 (LoadPre 0x1160f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x1160f0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1160f0 9 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 389) (.out 0x1160f8 (mulR64Effect 0x1160f8 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[387, 385]
    (.letOp (n := 390) (.out 0x1160f8 (mulR64Effect 0x1160f8 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[387, 385]
    (.letOp (n := 391) (.exec 0x1160f8 (fun s => s.RIP = 0x1160f8) (mulR64Effect 0x1160f8 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[387, 385]
    (.letOp (n := 392) (.out 0x1160fb (addR64R64Effect 0x1160fb 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[381, 370]
    (.letOp (n := 393) (.out 0x1160fb (addR64R64Effect 0x1160fb 7 6) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 6] []) (.flag .CF)) #v[381, 370]
    (.letOp (n := 394) (.exec 0x1160fb (fun s => s.RIP = 0x1160fb) (addR64R64Effect 0x1160fb 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[381, 370]
    (.letOp (n := 395) (.out 0x1160fe (atFlags StatusFlags.CF (adcR64R64Effect 0x1160fe 3 1)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[379, 368, 393]
    (.letOp (n := 396) (.exec 0x1160fe (fun s => s.RIP = 0x1160fe) (atFlags StatusFlags.CF (adcR64R64Effect 0x1160fe 3 1)) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[379, 368, 393]
    (.letOp (n := 397) (.out 0x116101 (addR64R64Effect 0x116101 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[389, 392]
    (.letOp (n := 398) (.out 0x116101 (addR64R64Effect 0x116101 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[389, 392]
    (.letOp (n := 399) (.exec 0x116101 (fun s => s.RIP = 0x116101) (addR64R64Effect 0x116101 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[389, 392]
    (b_l115e4d_8))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l115e4d_7 : List UInt8 :=
  [0x4C, 0x8B, 0xAC, 0x24, 0x60, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xD2, 0x49, 0x89,
    0xC0, 0x4C, 0x89, 0xC8, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x8B, 0x7C,
    0x24, 0x70, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0xD3, 0x48, 0x89, 0xC7, 0x48, 0x8B,
    0xAC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE8, 0x4C, 0x8B, 0x8C, 0x24, 0x30, 0x01, 0x00,
    0x00, 0x49, 0xF7, 0xE1, 0x48, 0x01, 0xF7, 0x48, 0x11, 0xCB, 0x48, 0x01, 0xF8] ++ bytes_l115e4d_8

theorem code_l115e4d_7 : ∀ x ∈ codeRange 0x1160b7 bytes_l115e4d_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x160b7 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115e4d_8

def b_l115e4d_6 : Block Op Label signature Reg.count 313 :=
  .letOp (n := 313) (.out 0x11604c (addR64R64Effect 0x11604c 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[308, 241]
    (.letOp (n := 314) (.out 0x11604c (addR64R64Effect 0x11604c 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[308, 241]
    (.letOp (n := 315) (.exec 0x11604c (fun s => s.RIP = 0x11604c) (addR64R64Effect 0x11604c 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[308, 241]
    (.letOp (n := 316) (.out 0x11604f (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11604f 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[311, 314]
    (.letOp (n := 317) (.exec 0x11604f (fun s => s.RIP = 0x11604f) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11604f 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[311, 314]
    (.letOp (n := 318) (.out 0x116053 (shldR64R64Effect 0x116053 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[316, 313]
    (.letOp (n := 319) (.exec 0x116053 (fun s => s.RIP = 0x116053) (shldR64R64Effect 0x116053 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[316, 313]
    (.letOp (n := 320) (.out 0x116058 (shlR64Effect 0x116058 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[313]
    (.letOp (n := 321) (.exec 0x116058 (fun s => s.RIP = 0x116058) (shlR64Effect 0x116058 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[313]
    (.letOp (n := 322) (.out 0x11605c (movR64Imm64Effect 0x11605c 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 323) (.exec 0x11605c (fun s => s.RIP = 0x11605c) (movR64Imm64Effect 0x11605c 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 324) (.out 0x116066 (andR64R64Effect 0x116066 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[320, 322]
    (.letOp (n := 325) (.exec 0x116066 (fun s => s.RIP = 0x116066) (andR64R64Effect 0x116066 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[320, 322]
    (.letOp (n := 326) (.out 0x116069 (orR64R64Effect 0x116069 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[324, 267]
    (.letOp (n := 327) (.exec 0x116069 (fun s => s.RIP = 0x116069) (orR64R64Effect 0x116069 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[324, 267]
    (.letOp (n := 328) (.out 0x11606c (movR64Imm64Effect 0x11606c 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 329) (.exec 0x11606c (fun s => s.RIP = 0x11606c) (movR64Imm64Effect 0x11606c 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 330) (.out 0x116076 (mulR64Effect 0x116076 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[328, 326]
    (.letOp (n := 331) (.out 0x116076 (mulR64Effect 0x116076 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[328, 326]
    (.letOp (n := 332) (.exec 0x116076 (fun s => s.RIP = 0x116076) (mulR64Effect 0x116076 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[328, 326]
    (.letOp (n := 333) (.out 0x116079 (movR64R64Effect 0x116079 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[331]
    (.letOp (n := 334) (.exec 0x116079 (fun s => s.RIP = 0x116079) (movR64R64Effect 0x116079 14 2) (Reg.operands [.gpr 2] [])) #v[331]
    (.letOp (n := 335) (.out 0x11607c (addR64M64Effect 0x11607c 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[330, 4]
    (.letOp (n := 336) (.out 0x11607c (addR64M64Effect 0x11607c 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[330, 4]
    (.letOp (n := 337) (.exec 0x11607c (LoadPre 0x11607c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11607c + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11607c 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[330, 4]
    (.letOp (n := 338) (.exec 0x116084 (StorePre 0x116084 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x116084 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x116084 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[335, 4]
    (.letOp (n := 339) (.out 0x11608c (atFlags StatusFlags.CF (adcR64M64Effect 0x11608c 14 (.sib 4 none 0 (.d32 0xb0)))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 14))) #v[333, 4, 336]
    (.letOp (n := 340) (.exec 0x11608c (LoadPre 0x11608c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11608c + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11608c 14 (.sib 4 none 0 (.d32 0xb0)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[333, 4, 336]
    (.letOp (n := 341) (.out 0x116094 (shldR64R64Effect 0x116094 5 14 0 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[339, 335]
    (.letOp (n := 342) (.exec 0x116094 (fun s => s.RIP = 0x116094) (shldR64R64Effect 0x116094 5 14 0 12) (Reg.operands [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[339, 335]
    (.letOp (n := 343) (.out 0x116099 (movR64M64Effect 0x116099 12 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 344) (.exec 0x116099 (LoadPre 0x116099 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116099 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116099 12 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 345) (.out 0x11609e (movR64R64Effect 0x11609e 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[343]
    (.letOp (n := 346) (.exec 0x11609e (fun s => s.RIP = 0x11609e) (movR64R64Effect 0x11609e 0 12) (Reg.operands [.gpr 12] [])) #v[343]
    (.letOp (n := 347) (.out 0x1160a1 (mulR64Effect 0x1160a1 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[293, 345]
    (.letOp (n := 348) (.out 0x1160a1 (mulR64Effect 0x1160a1 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[293, 345]
    (.letOp (n := 349) (.exec 0x1160a1 (fun s => s.RIP = 0x1160a1) (mulR64Effect 0x1160a1 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[293, 345]
    (.letOp (n := 350) (.exec 0x1160a4 (StorePre 0x1160a4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1160a4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1160a4 2 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[348, 4]
    (.letOp (n := 351) (.exec 0x1160ac (StorePre 0x1160ac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1160ac + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1160ac 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[347, 4]
    (.letOp (n := 352) (.out 0x1160b4 (movR64R64Effect 0x1160b4 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[254]
    (.letOp (n := 353) (.exec 0x1160b4 (fun s => s.RIP = 0x1160b4) (movR64R64Effect 0x1160b4 0 8) (Reg.operands [.gpr 8] [])) #v[254]
    (b_l115e4d_7)))))))))))))))))))))))))))))))))))))))))

def bytes_l115e4d_6 : List UInt8 :=
  [0x4C, 0x01, 0xD0, 0x49, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xC1, 0xE0, 0x04,
    0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C, 0x09, 0xE8,
    0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD6,
    0x48, 0x03, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x4C, 0x13, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0x0F, 0xA4, 0xC6, 0x0C, 0x4C, 0x8B, 0x64,
    0x24, 0x68, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xC0] ++ bytes_l115e4d_7

theorem code_l115e4d_6 : ∀ x ∈ codeRange 0x11604c bytes_l115e4d_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1604c 107 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115e4d_7

def b_l115e4d_5 : Block Op Label signature Reg.count 267 :=
  .letOp (n := 267) (.out 0x115ff4 (andR32Imm8Effect 0x115ff4 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[245]
    (.letOp (n := 268) (.exec 0x115ff4 (fun s => s.RIP = 0x115ff4) (andR32Imm8Effect 0x115ff4 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[245]
    (.letOp (n := 269) (.out 0x115ff8 (movR64M64Effect 0x115ff8 9 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 270) (.exec 0x115ff8 (LoadPre 0x115ff8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x115ff8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115ff8 9 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 271) (.out 0x116000 (movR64R64Effect 0x116000 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[269]
    (.letOp (n := 272) (.exec 0x116000 (fun s => s.RIP = 0x116000) (movR64R64Effect 0x116000 0 9) (Reg.operands [.gpr 9] [])) #v[269]
    (.letOp (n := 273) (.out 0x116003 (movR64M64Effect 0x116003 3 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 274) (.exec 0x116003 (LoadPre 0x116003 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x116003 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116003 3 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 275) (.out 0x11600b (mulR64Effect 0x11600b 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[273, 271]
    (.letOp (n := 276) (.out 0x11600b (mulR64Effect 0x11600b 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[273, 271]
    (.letOp (n := 277) (.exec 0x11600b (fun s => s.RIP = 0x11600b) (mulR64Effect 0x11600b 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[273, 271]
    (.letOp (n := 278) (.out 0x11600e (movR64R64Effect 0x11600e 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[276]
    (.letOp (n := 279) (.exec 0x11600e (fun s => s.RIP = 0x11600e) (movR64R64Effect 0x11600e 11 2) (Reg.operands [.gpr 2] [])) #v[276]
    (.letOp (n := 280) (.out 0x116011 (movR64R64Effect 0x116011 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[275]
    (.letOp (n := 281) (.exec 0x116011 (fun s => s.RIP = 0x116011) (movR64R64Effect 0x116011 7 0) (Reg.operands [.gpr 0] [])) #v[275]
    (.letOp (n := 282) (.out 0x116014 (movR64M64Effect 0x116014 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 283) (.exec 0x116014 (LoadPre 0x116014 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x116014 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116014 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 284) (.out 0x116019 (mulM64Effect 0x116019 8 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[282, 4]
    (.letOp (n := 285) (.out 0x116019 (mulM64Effect 0x116019 8 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[282, 4]
    (.letOp (n := 286) (.exec 0x116019 (LoadPre 0x116019 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x116019 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x116019 8 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[282, 4]
    (.letOp (n := 287) (.out 0x116021 (movR64R64Effect 0x116021 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[285]
    (.letOp (n := 288) (.exec 0x116021 (fun s => s.RIP = 0x116021) (movR64R64Effect 0x116021 14 2) (Reg.operands [.gpr 2] [])) #v[285]
    (.letOp (n := 289) (.out 0x116024 (movR64R64Effect 0x116024 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[284]
    (.letOp (n := 290) (.exec 0x116024 (fun s => s.RIP = 0x116024) (movR64R64Effect 0x116024 12 0) (Reg.operands [.gpr 0] [])) #v[284]
    (.letOp (n := 291) (.out 0x116027 (movR64M64Effect 0x116027 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 292) (.exec 0x116027 (LoadPre 0x116027 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x116027 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116027 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 293) (.out 0x11602f (movR64M64Effect 0x11602f 5 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 294) (.exec 0x11602f (LoadPre 0x11602f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x11602f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11602f 5 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 295) (.out 0x116037 (mulR64Effect 0x116037 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[293, 291]
    (.letOp (n := 296) (.out 0x116037 (mulR64Effect 0x116037 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[293, 291]
    (.letOp (n := 297) (.exec 0x116037 (fun s => s.RIP = 0x116037) (mulR64Effect 0x116037 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[293, 291]
    (.letOp (n := 298) (.out 0x11603a (addR64R64Effect 0x11603a 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[280, 263]
    (.letOp (n := 299) (.out 0x11603a (addR64R64Effect 0x11603a 7 1) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 1] []) (.flag .CF)) #v[280, 263]
    (.letOp (n := 300) (.exec 0x11603a (fun s => s.RIP = 0x11603a) (addR64R64Effect 0x11603a 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[280, 263]
    (.letOp (n := 301) (.out 0x11603d (atFlags StatusFlags.CF (adcR64R64Effect 0x11603d 11 6)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[278, 265, 299]
    (.letOp (n := 302) (.exec 0x11603d (fun s => s.RIP = 0x11603d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11603d 11 6)) (Reg.operands [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[278, 265, 299]
    (.letOp (n := 303) (.out 0x116040 (addR64R64Effect 0x116040 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[298, 289]
    (.letOp (n := 304) (.out 0x116040 (addR64R64Effect 0x116040 7 12) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 12] []) (.flag .CF)) #v[298, 289]
    (.letOp (n := 305) (.exec 0x116040 (fun s => s.RIP = 0x116040) (addR64R64Effect 0x116040 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[298, 289]
    (.letOp (n := 306) (.out 0x116043 (atFlags StatusFlags.CF (adcR64R64Effect 0x116043 11 14)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[301, 287, 304]
    (.letOp (n := 307) (.exec 0x116043 (fun s => s.RIP = 0x116043) (atFlags StatusFlags.CF (adcR64R64Effect 0x116043 11 14)) (Reg.operands [.gpr 11, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[301, 287, 304]
    (.letOp (n := 308) (.out 0x116046 (addR64R64Effect 0x116046 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[295, 303]
    (.letOp (n := 309) (.out 0x116046 (addR64R64Effect 0x116046 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[295, 303]
    (.letOp (n := 310) (.exec 0x116046 (fun s => s.RIP = 0x116046) (addR64R64Effect 0x116046 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[295, 303]
    (.letOp (n := 311) (.out 0x116049 (atFlags StatusFlags.CF (adcR64R64Effect 0x116049 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[306, 296, 309]
    (.letOp (n := 312) (.exec 0x116049 (fun s => s.RIP = 0x116049) (atFlags StatusFlags.CF (adcR64R64Effect 0x116049 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[306, 296, 309]
    (b_l115e4d_6))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l115e4d_5 : List UInt8 :=
  [0x41, 0x83, 0xE5, 0x0F, 0x4C, 0x8B, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xC8, 0x48,
    0x8B, 0x9C, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC7,
    0x48, 0x8B, 0x44, 0x24, 0x70, 0x48, 0xF7, 0xA4, 0x24, 0x30, 0x01, 0x00, 0x00, 0x49, 0x89, 0xD6,
    0x49, 0x89, 0xC4, 0x48, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xAC, 0x24, 0x48,
    0x01, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x48, 0x01, 0xCF, 0x49, 0x11, 0xF3, 0x4C, 0x01, 0xE7, 0x4D,
    0x11, 0xF3, 0x48, 0x01, 0xF8, 0x49, 0x11, 0xD3] ++ bytes_l115e4d_6

theorem code_l115e4d_5 : ∀ x ∈ codeRange 0x115ff4 bytes_l115e4d_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15ff4 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115e4d_6

def b_l115e4d_4 : Block Op Label signature Reg.count 225 :=
  .letOp (n := 225) (.out 0x115f9c (addR64R64Effect 0x115f9c 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[220, 201]
    (.letOp (n := 226) (.out 0x115f9c (addR64R64Effect 0x115f9c 14 7) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 7] []) (.flag .CF)) #v[220, 201]
    (.letOp (n := 227) (.exec 0x115f9c (fun s => s.RIP = 0x115f9c) (addR64R64Effect 0x115f9c 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[220, 201]
    (.letOp (n := 228) (.out 0x115f9f (atFlags StatusFlags.CF (adcR64R64Effect 0x115f9f 10 9)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[223, 199, 226]
    (.letOp (n := 229) (.exec 0x115f9f (fun s => s.RIP = 0x115f9f) (atFlags StatusFlags.CF (adcR64R64Effect 0x115f9f 10 9)) (Reg.operands [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[223, 199, 226]
    (.letOp (n := 230) (.out 0x115fa2 (addR64R64Effect 0x115fa2 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[225, 207]
    (.letOp (n := 231) (.out 0x115fa2 (addR64R64Effect 0x115fa2 14 0) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 0] []) (.flag .CF)) #v[225, 207]
    (.letOp (n := 232) (.exec 0x115fa2 (fun s => s.RIP = 0x115fa2) (addR64R64Effect 0x115fa2 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[225, 207]
    (.letOp (n := 233) (.out 0x115fa5 (atFlags StatusFlags.CF (adcR64R64Effect 0x115fa5 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[228, 208, 231]
    (.letOp (n := 234) (.exec 0x115fa5 (fun s => s.RIP = 0x115fa5) (atFlags StatusFlags.CF (adcR64R64Effect 0x115fa5 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[228, 208, 231]
    (.letOp (n := 235) (.out 0x115fa8 (addR64R64Effect 0x115fa8 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[230, 157]
    (.letOp (n := 236) (.out 0x115fa8 (addR64R64Effect 0x115fa8 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[230, 157]
    (.letOp (n := 237) (.exec 0x115fa8 (fun s => s.RIP = 0x115fa8) (addR64R64Effect 0x115fa8 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[230, 157]
    (.letOp (n := 238) (.exec 0x115fab (StorePre 0x115fab 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x115fab + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115fab 14 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[235, 4]
    (.letOp (n := 239) (.out 0x115fb3 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115fb3 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[233, 236]
    (.letOp (n := 240) (.exec 0x115fb3 (fun s => s.RIP = 0x115fb3) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x115fb3 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[233, 236]
    (.letOp (n := 241) (.out 0x115fb7 (shldR64R64Effect 0x115fb7 5 10 14 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[239, 235]
    (.letOp (n := 242) (.exec 0x115fb7 (fun s => s.RIP = 0x115fb7) (shldR64R64Effect 0x115fb7 5 10 14 12) (Reg.operands [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[239, 235]
    (.letOp (n := 243) (.out 0x115fbc (movR64R64Effect 0x115fbc 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[235]
    (.letOp (n := 244) (.exec 0x115fbc (fun s => s.RIP = 0x115fbc) (movR64R64Effect 0x115fbc 13 14) (Reg.operands [.gpr 14] [])) #v[235]
    (.letOp (n := 245) (.out 0x115fbf (shrR64Effect 0x115fbf 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[243]
    (.letOp (n := 246) (.exec 0x115fbf (fun s => s.RIP = 0x115fbf) (shrR64Effect 0x115fbf 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[243]
    (.letOp (n := 247) (.out 0x115fc3 (movR64M64Effect 0x115fc3 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 248) (.exec 0x115fc3 (LoadPre 0x115fc3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x115fc3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115fc3 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 249) (.out 0x115fc8 (mulR64Effect 0x115fc8 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[112, 247]
    (.letOp (n := 250) (.out 0x115fc8 (mulR64Effect 0x115fc8 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[112, 247]
    (.letOp (n := 251) (.exec 0x115fc8 (fun s => s.RIP = 0x115fc8) (mulR64Effect 0x115fc8 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[112, 247]
    (.letOp (n := 252) (.exec 0x115fcb (StorePre 0x115fcb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x115fcb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115fcb 2 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[250, 4]
    (.letOp (n := 253) (.exec 0x115fd3 (StorePre 0x115fd3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x115fd3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115fd3 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[249, 4]
    (.letOp (n := 254) (.out 0x115fdb (movR64M64Effect 0x115fdb 8 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 255) (.exec 0x115fdb (LoadPre 0x115fdb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x115fdb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115fdb 8 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 256) (.out 0x115fe0 (movR64R64Effect 0x115fe0 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[254]
    (.letOp (n := 257) (.exec 0x115fe0 (fun s => s.RIP = 0x115fe0) (movR64R64Effect 0x115fe0 0 8) (Reg.operands [.gpr 8] [])) #v[254]
    (.letOp (n := 258) (.out 0x115fe3 (movR64M64Effect 0x115fe3 15 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 259) (.exec 0x115fe3 (LoadPre 0x115fe3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x115fe3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115fe3 15 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 260) (.out 0x115feb (mulR64Effect 0x115feb 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[258, 256]
    (.letOp (n := 261) (.out 0x115feb (mulR64Effect 0x115feb 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[258, 256]
    (.letOp (n := 262) (.exec 0x115feb (fun s => s.RIP = 0x115feb) (mulR64Effect 0x115feb 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[258, 256]
    (.letOp (n := 263) (.out 0x115fee (movR64R64Effect 0x115fee 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[260]
    (.letOp (n := 264) (.exec 0x115fee (fun s => s.RIP = 0x115fee) (movR64R64Effect 0x115fee 1 0) (Reg.operands [.gpr 0] [])) #v[260]
    (.letOp (n := 265) (.out 0x115ff1 (movR64R64Effect 0x115ff1 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[261]
    (.letOp (n := 266) (.exec 0x115ff1 (fun s => s.RIP = 0x115ff1) (movR64R64Effect 0x115ff1 6 2) (Reg.operands [.gpr 2] [])) #v[261]
    (b_l115e4d_5))))))))))))))))))))))))))))))))))))))))))

def bytes_l115e4d_4 : List UInt8 :=
  [0x49, 0x01, 0xFE, 0x4D, 0x11, 0xCA, 0x49, 0x01, 0xC6, 0x49, 0x11, 0xD2, 0x4D, 0x01, 0xDE, 0x4C,
    0x89, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x83, 0xD2, 0x00, 0x4D, 0x0F, 0xA4, 0xF2, 0x0C,
    0x4D, 0x89, 0xF5, 0x49, 0xC1, 0xED, 0x30, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0xF7, 0xE6, 0x48,
    0x89, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C,
    0x8B, 0x44, 0x24, 0x50, 0x4C, 0x89, 0xC0, 0x4C, 0x8B, 0xBC, 0x24, 0x40, 0x01, 0x00, 0x00, 0x49,
    0xF7, 0xE7, 0x48, 0x89, 0xC1, 0x48, 0x89, 0xD6] ++ bytes_l115e4d_5

theorem code_l115e4d_4 : ∀ x ∈ codeRange 0x115f9c bytes_l115e4d_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15f9c 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115e4d_5

def b_l115e4d_3 : Block Op Label signature Reg.count 178 :=
  .letOp (n := 178) (.out 0x115f54 (mulR64Effect 0x115f54 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[76, 176]
    (.letOp (n := 179) (.out 0x115f54 (mulR64Effect 0x115f54 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[76, 176]
    (.letOp (n := 180) (.exec 0x115f54 (fun s => s.RIP = 0x115f54) (mulR64Effect 0x115f54 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[76, 176]
    (.letOp (n := 181) (.out 0x115f57 (movR64R64Effect 0x115f57 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[179]
    (.letOp (n := 182) (.exec 0x115f57 (fun s => s.RIP = 0x115f57) (movR64R64Effect 0x115f57 12 2) (Reg.operands [.gpr 2] [])) #v[179]
    (.letOp (n := 183) (.out 0x115f5a (movR64R64Effect 0x115f5a 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[178]
    (.letOp (n := 184) (.exec 0x115f5a (fun s => s.RIP = 0x115f5a) (movR64R64Effect 0x115f5a 13 0) (Reg.operands [.gpr 0] [])) #v[178]
    (.letOp (n := 185) (.out 0x115f5d (movR64R64Effect 0x115f5d 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[109]
    (.letOp (n := 186) (.exec 0x115f5d (fun s => s.RIP = 0x115f5d) (movR64R64Effect 0x115f5d 0 9) (Reg.operands [.gpr 9] [])) #v[109]
    (.letOp (n := 187) (.out 0x115f60 (mulR64Effect 0x115f60 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[93, 185]
    (.letOp (n := 188) (.out 0x115f60 (mulR64Effect 0x115f60 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[93, 185]
    (.letOp (n := 189) (.exec 0x115f60 (fun s => s.RIP = 0x115f60) (mulR64Effect 0x115f60 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[93, 185]
    (.letOp (n := 190) (.out 0x115f63 (movR64R64Effect 0x115f63 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[188]
    (.letOp (n := 191) (.exec 0x115f63 (fun s => s.RIP = 0x115f63) (movR64R64Effect 0x115f63 5 2) (Reg.operands [.gpr 2] [])) #v[188]
    (.letOp (n := 192) (.out 0x115f66 (movR64R64Effect 0x115f66 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[187]
    (.letOp (n := 193) (.exec 0x115f66 (fun s => s.RIP = 0x115f66) (movR64R64Effect 0x115f66 1 0) (Reg.operands [.gpr 0] [])) #v[187]
    (.letOp (n := 194) (.out 0x115f69 (movR64R64Effect 0x115f69 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[128]
    (.letOp (n := 195) (.exec 0x115f69 (fun s => s.RIP = 0x115f69) (movR64R64Effect 0x115f69 0 8) (Reg.operands [.gpr 8] [])) #v[128]
    (.letOp (n := 196) (.out 0x115f6c (mulR64Effect 0x115f6c 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[112, 194]
    (.letOp (n := 197) (.out 0x115f6c (mulR64Effect 0x115f6c 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[112, 194]
    (.letOp (n := 198) (.exec 0x115f6c (fun s => s.RIP = 0x115f6c) (mulR64Effect 0x115f6c 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[112, 194]
    (.letOp (n := 199) (.out 0x115f6f (movR64R64Effect 0x115f6f 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[197]
    (.letOp (n := 200) (.exec 0x115f6f (fun s => s.RIP = 0x115f6f) (movR64R64Effect 0x115f6f 9 2) (Reg.operands [.gpr 2] [])) #v[197]
    (.letOp (n := 201) (.out 0x115f72 (movR64R64Effect 0x115f72 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[196]
    (.letOp (n := 202) (.exec 0x115f72 (fun s => s.RIP = 0x115f72) (movR64R64Effect 0x115f72 7 0) (Reg.operands [.gpr 0] [])) #v[196]
    (.letOp (n := 203) (.out 0x115f75 (movR64R64Effect 0x115f75 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[138]
    (.letOp (n := 204) (.exec 0x115f75 (fun s => s.RIP = 0x115f75) (movR64R64Effect 0x115f75 0 3) (Reg.operands [.gpr 3] [])) #v[138]
    (.letOp (n := 205) (.out 0x115f78 (movR64Imm64Effect 0x115f78 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 206) (.exec 0x115f78 (fun s => s.RIP = 0x115f78) (movR64Imm64Effect 0x115f78 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 207) (.out 0x115f82 (mulR64Effect 0x115f82 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[205, 203]
    (.letOp (n := 208) (.out 0x115f82 (mulR64Effect 0x115f82 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[205, 203]
    (.letOp (n := 209) (.exec 0x115f82 (fun s => s.RIP = 0x115f82) (mulR64Effect 0x115f82 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[205, 203]
    (.letOp (n := 210) (.out 0x115f85 (addR64R64Effect 0x115f85 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[174, 165]
    (.letOp (n := 211) (.out 0x115f85 (addR64R64Effect 0x115f85 14 15) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 15] []) (.flag .CF)) #v[174, 165]
    (.letOp (n := 212) (.exec 0x115f85 (fun s => s.RIP = 0x115f85) (addR64R64Effect 0x115f85 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[174, 165]
    (.letOp (n := 213) (.out 0x115f88 (atFlags StatusFlags.CF (adcR64M64Effect 0x115f88 10 (.sib 4 none 0 (.d32 0x90)))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 10))) #v[172, 4, 211]
    (.letOp (n := 214) (.exec 0x115f88 (LoadPre 0x115f88 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x115f88 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x115f88 10 (.sib 4 none 0 (.d32 0x90)))) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[172, 4, 211]
    (.letOp (n := 215) (.out 0x115f90 (addR64R64Effect 0x115f90 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[210, 183]
    (.letOp (n := 216) (.out 0x115f90 (addR64R64Effect 0x115f90 14 13) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 13] []) (.flag .CF)) #v[210, 183]
    (.letOp (n := 217) (.exec 0x115f90 (fun s => s.RIP = 0x115f90) (addR64R64Effect 0x115f90 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[210, 183]
    (.letOp (n := 218) (.out 0x115f93 (atFlags StatusFlags.CF (adcR64R64Effect 0x115f93 10 12)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[213, 181, 216]
    (.letOp (n := 219) (.exec 0x115f93 (fun s => s.RIP = 0x115f93) (atFlags StatusFlags.CF (adcR64R64Effect 0x115f93 10 12)) (Reg.operands [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[213, 181, 216]
    (.letOp (n := 220) (.out 0x115f96 (addR64R64Effect 0x115f96 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[215, 192]
    (.letOp (n := 221) (.out 0x115f96 (addR64R64Effect 0x115f96 14 1) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 1] []) (.flag .CF)) #v[215, 192]
    (.letOp (n := 222) (.exec 0x115f96 (fun s => s.RIP = 0x115f96) (addR64R64Effect 0x115f96 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[215, 192]
    (.letOp (n := 223) (.out 0x115f99 (atFlags StatusFlags.CF (adcR64R64Effect 0x115f99 10 5)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[218, 190, 221]
    (.letOp (n := 224) (.exec 0x115f99 (fun s => s.RIP = 0x115f99) (atFlags StatusFlags.CF (adcR64R64Effect 0x115f99 10 5)) (Reg.operands [.gpr 10, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[218, 190, 221]
    (b_l115e4d_4)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l115e4d_3 : List UInt8 :=
  [0x49, 0xF7, 0xE4, 0x49, 0x89, 0xD4, 0x49, 0x89, 0xC5, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0xE5, 0x48,
    0x89, 0xD5, 0x48, 0x89, 0xC1, 0x4C, 0x89, 0xC0, 0x48, 0xF7, 0xE6, 0x49, 0x89, 0xD1, 0x48, 0x89,
    0xC7, 0x48, 0x89, 0xD8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xE2, 0x4D, 0x01, 0xFE, 0x4C, 0x13, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xEE, 0x4D,
    0x11, 0xE2, 0x49, 0x01, 0xCE, 0x49, 0x11, 0xEA] ++ bytes_l115e4d_4

theorem code_l115e4d_3 : ∀ x ∈ codeRange 0x115f54 bytes_l115e4d_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15f54 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115e4d_4

def b_l115e4d_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x115ef8 (movR64R64Effect 0x115ef8 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[134]
    (.letOp (n := 137) (.exec 0x115ef8 (fun s => s.RIP = 0x115ef8) (movR64R64Effect 0x115ef8 3 2) (Reg.operands [.gpr 2] [])) #v[134]
    (.letOp (n := 138) (.out 0x115efb (shldR64R64Effect 0x115efb 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[136, 133]
    (.letOp (n := 139) (.exec 0x115efb (fun s => s.RIP = 0x115efb) (shldR64R64Effect 0x115efb 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[136, 133]
    (.letOp (n := 140) (.out 0x115f00 (movR64Imm64Effect 0x115f00 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 141) (.exec 0x115f00 (fun s => s.RIP = 0x115f00) (movR64Imm64Effect 0x115f00 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 142) (.out 0x115f0a (andR64R64Effect 0x115f0a 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[133, 140]
    (.letOp (n := 143) (.exec 0x115f0a (fun s => s.RIP = 0x115f0a) (andR64R64Effect 0x115f0a 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[133, 140]
    (.letOp (n := 144) (.out 0x115f0d (movR64Imm64Effect 0x115f0d 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 145) (.exec 0x115f0d (fun s => s.RIP = 0x115f0d) (movR64Imm64Effect 0x115f0d 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 146) (.out 0x115f17 (mulR64Effect 0x115f17 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[144, 142]
    (.letOp (n := 147) (.out 0x115f17 (mulR64Effect 0x115f17 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[144, 142]
    (.letOp (n := 148) (.exec 0x115f17 (fun s => s.RIP = 0x115f17) (mulR64Effect 0x115f17 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[144, 142]
    (.letOp (n := 149) (.out 0x115f1a (movR64R64Effect 0x115f1a 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[147]
    (.letOp (n := 150) (.exec 0x115f1a (fun s => s.RIP = 0x115f1a) (movR64R64Effect 0x115f1a 11 2) (Reg.operands [.gpr 2] [])) #v[147]
    (.letOp (n := 151) (.out 0x115f1d (addR64R64Effect 0x115f1d 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[146, 121]
    (.letOp (n := 152) (.out 0x115f1d (addR64R64Effect 0x115f1d 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[146, 121]
    (.letOp (n := 153) (.exec 0x115f1d (fun s => s.RIP = 0x115f1d) (addR64R64Effect 0x115f1d 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[146, 121]
    (.letOp (n := 154) (.exec 0x115f20 (StorePre 0x115f20 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x115f20 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115f20 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[151, 4]
    (.letOp (n := 155) (.out 0x115f28 (atFlags StatusFlags.CF (adcR64R64Effect 0x115f28 11 14)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[149, 124, 152]
    (.letOp (n := 156) (.exec 0x115f28 (fun s => s.RIP = 0x115f28) (atFlags StatusFlags.CF (adcR64R64Effect 0x115f28 11 14)) (Reg.operands [.gpr 11, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[149, 124, 152]
    (.letOp (n := 157) (.out 0x115f2b (shldR64R64Effect 0x115f2b 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[155, 151]
    (.letOp (n := 158) (.exec 0x115f2b (fun s => s.RIP = 0x115f2b) (shldR64R64Effect 0x115f2b 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[155, 151]
    (.letOp (n := 159) (.out 0x115f30 (movR64M64Effect 0x115f30 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 160) (.exec 0x115f30 (LoadPre 0x115f30 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x115f30 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115f30 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 161) (.out 0x115f35 (mulR64Effect 0x115f35 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[131, 159]
    (.letOp (n := 162) (.out 0x115f35 (mulR64Effect 0x115f35 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[131, 159]
    (.letOp (n := 163) (.exec 0x115f35 (fun s => s.RIP = 0x115f35) (mulR64Effect 0x115f35 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[131, 159]
    (.letOp (n := 164) (.exec 0x115f38 (StorePre 0x115f38 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x115f38 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115f38 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[162, 4]
    (.letOp (n := 165) (.out 0x115f40 (movR64R64Effect 0x115f40 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[161]
    (.letOp (n := 166) (.exec 0x115f40 (fun s => s.RIP = 0x115f40) (movR64R64Effect 0x115f40 15 0) (Reg.operands [.gpr 0] [])) #v[161]
    (.letOp (n := 167) (.out 0x115f43 (movR64M64Effect 0x115f43 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 168) (.exec 0x115f43 (LoadPre 0x115f43 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x115f43 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115f43 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 169) (.out 0x115f48 (mulR64Effect 0x115f48 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[65, 167]
    (.letOp (n := 170) (.out 0x115f48 (mulR64Effect 0x115f48 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[65, 167]
    (.letOp (n := 171) (.exec 0x115f48 (fun s => s.RIP = 0x115f48) (mulR64Effect 0x115f48 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[65, 167]
    (.letOp (n := 172) (.out 0x115f4b (movR64R64Effect 0x115f4b 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[170]
    (.letOp (n := 173) (.exec 0x115f4b (fun s => s.RIP = 0x115f4b) (movR64R64Effect 0x115f4b 10 2) (Reg.operands [.gpr 2] [])) #v[170]
    (.letOp (n := 174) (.out 0x115f4e (movR64R64Effect 0x115f4e 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[169]
    (.letOp (n := 175) (.exec 0x115f4e (fun s => s.RIP = 0x115f4e) (movR64R64Effect 0x115f4e 14 0) (Reg.operands [.gpr 0] [])) #v[169]
    (.letOp (n := 176) (.out 0x115f51 (movR64R64Effect 0x115f51 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 177) (.exec 0x115f51 (fun s => s.RIP = 0x115f51) (movR64R64Effect 0x115f51 0 13) (Reg.operands [.gpr 13] [])) #v[57]
    (b_l115e4d_3))))))))))))))))))))))))))))))))))))))))))

def bytes_l115e4d_2 : List UInt8 :=
  [0x48, 0x89, 0xD3, 0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE2, 0x49, 0x89, 0xD3, 0x4C, 0x01, 0xF8, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0x4D, 0x11, 0xF3, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0xF7, 0xE7,
    0x48, 0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x44, 0x24, 0x50,
    0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC6, 0x4C, 0x89, 0xE8] ++ bytes_l115e4d_3

theorem code_l115e4d_2 : ∀ x ∈ codeRange 0x115ef8 bytes_l115e4d_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15ef8 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115e4d_3

def b_l115e4d_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x115ea6 (movR64M64Effect 0x115ea6 5 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 94) (.exec 0x115ea6 (LoadPre 0x115ea6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x115ea6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115ea6 5 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x115eae (mulR64Effect 0x115eae 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[93, 90]
    (.letOp (n := 96) (.out 0x115eae (mulR64Effect 0x115eae 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[93, 90]
    (.letOp (n := 97) (.exec 0x115eae (fun s => s.RIP = 0x115eae) (mulR64Effect 0x115eae 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[93, 90]
    (.letOp (n := 98) (.out 0x115eb1 (movR64R64Effect 0x115eb1 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[96]
    (.letOp (n := 99) (.exec 0x115eb1 (fun s => s.RIP = 0x115eb1) (movR64R64Effect 0x115eb1 10 2) (Reg.operands [.gpr 2] [])) #v[96]
    (.letOp (n := 100) (.out 0x115eb4 (movR64R64Effect 0x115eb4 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[95]
    (.letOp (n := 101) (.exec 0x115eb4 (fun s => s.RIP = 0x115eb4) (movR64R64Effect 0x115eb4 11 0) (Reg.operands [.gpr 0] [])) #v[95]
    (.letOp (n := 102) (.out 0x115eb7 (addR64R64Effect 0x115eb7 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[100, 85]
    (.letOp (n := 103) (.out 0x115eb7 (addR64R64Effect 0x115eb7 11 14) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 14] []) (.flag .CF)) #v[100, 85]
    (.letOp (n := 104) (.exec 0x115eb7 (fun s => s.RIP = 0x115eb7) (addR64R64Effect 0x115eb7 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[100, 85]
    (.letOp (n := 105) (.out 0x115eba (atFlags StatusFlags.CF (adcR64R64Effect 0x115eba 10 3)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[98, 88, 103]
    (.letOp (n := 106) (.exec 0x115eba (fun s => s.RIP = 0x115eba) (atFlags StatusFlags.CF (adcR64R64Effect 0x115eba 10 3)) (Reg.operands [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[98, 88, 103]
    (.letOp (n := 107) (.out 0x115ebd (movR64R64Effect 0x115ebd 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 108) (.exec 0x115ebd (fun s => s.RIP = 0x115ebd) (movR64R64Effect 0x115ebd 0 6) (Reg.operands [.gpr 6] [])) #v[55]
    (.letOp (n := 109) (.out 0x115ec0 (movR64R64Effect 0x115ec0 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 110) (.exec 0x115ec0 (fun s => s.RIP = 0x115ec0) (movR64R64Effect 0x115ec0 9 6) (Reg.operands [.gpr 6] [])) #v[55]
    (.letOp (n := 111) (.exec 0x115ec3 (StorePre 0x115ec3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x115ec3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115ec3 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 112) (.out 0x115ec8 (movR64M64Effect 0x115ec8 6 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 113) (.exec 0x115ec8 (LoadPre 0x115ec8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x115ec8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115ec8 6 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 114) (.out 0x115ed0 (mulR64Effect 0x115ed0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[112, 107]
    (.letOp (n := 115) (.out 0x115ed0 (mulR64Effect 0x115ed0 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[112, 107]
    (.letOp (n := 116) (.exec 0x115ed0 (fun s => s.RIP = 0x115ed0) (mulR64Effect 0x115ed0 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[112, 107]
    (.letOp (n := 117) (.out 0x115ed3 (movR64R64Effect 0x115ed3 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[115]
    (.letOp (n := 118) (.exec 0x115ed3 (fun s => s.RIP = 0x115ed3) (movR64R64Effect 0x115ed3 14 2) (Reg.operands [.gpr 2] [])) #v[115]
    (.letOp (n := 119) (.out 0x115ed6 (movR64R64Effect 0x115ed6 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[114]
    (.letOp (n := 120) (.exec 0x115ed6 (fun s => s.RIP = 0x115ed6) (movR64R64Effect 0x115ed6 15 0) (Reg.operands [.gpr 0] [])) #v[114]
    (.letOp (n := 121) (.out 0x115ed9 (addR64R64Effect 0x115ed9 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[119, 102]
    (.letOp (n := 122) (.out 0x115ed9 (addR64R64Effect 0x115ed9 15 11) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 11] []) (.flag .CF)) #v[119, 102]
    (.letOp (n := 123) (.exec 0x115ed9 (fun s => s.RIP = 0x115ed9) (addR64R64Effect 0x115ed9 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[119, 102]
    (.letOp (n := 124) (.out 0x115edc (atFlags StatusFlags.CF (adcR64R64Effect 0x115edc 14 10)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[117, 105, 122]
    (.letOp (n := 125) (.exec 0x115edc (fun s => s.RIP = 0x115edc) (atFlags StatusFlags.CF (adcR64R64Effect 0x115edc 14 10)) (Reg.operands [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[117, 105, 122]
    (.letOp (n := 126) (.out 0x115edf (movR64R64Effect 0x115edf 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 127) (.exec 0x115edf (fun s => s.RIP = 0x115edf) (movR64R64Effect 0x115edf 0 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 128) (.out 0x115ee2 (movR64R64Effect 0x115ee2 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 129) (.exec 0x115ee2 (fun s => s.RIP = 0x115ee2) (movR64R64Effect 0x115ee2 8 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 130) (.exec 0x115ee5 (StorePre 0x115ee5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x115ee5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115ee5 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 131) (.out 0x115eed (movR64M64Effect 0x115eed 7 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 132) (.exec 0x115eed (LoadPre 0x115eed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x115eed + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115eed 7 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 133) (.out 0x115ef5 (mulR64Effect 0x115ef5 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[131, 126]
    (.letOp (n := 134) (.out 0x115ef5 (mulR64Effect 0x115ef5 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[131, 126]
    (.letOp (n := 135) (.exec 0x115ef5 (fun s => s.RIP = 0x115ef5) (mulR64Effect 0x115ef5 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[131, 126]
    (b_l115e4d_2)))))))))))))))))))))))))))))))))))))))))))

def bytes_l115e4d_1 : List UInt8 :=
  [0x48, 0x8B, 0xAC, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD2, 0x49, 0x89,
    0xC3, 0x4D, 0x01, 0xF3, 0x49, 0x11, 0xDA, 0x48, 0x89, 0xF0, 0x49, 0x89, 0xF1, 0x48, 0x89, 0x74,
    0x24, 0x70, 0x48, 0x8B, 0xB4, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE6, 0x49, 0x89, 0xD6,
    0x49, 0x89, 0xC7, 0x4D, 0x01, 0xDF, 0x4D, 0x11, 0xD6, 0x48, 0x89, 0xF8, 0x49, 0x89, 0xF8, 0x48,
    0x89, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xBC, 0x24, 0x40, 0x01, 0x00, 0x00, 0x48,
    0xF7, 0xE7] ++ bytes_l115e4d_2

theorem code_l115e4d_1 : ∀ x ∈ codeRange 0x115ea6 bytes_l115e4d_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15ea6 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115e4d_2

def b_l115e4d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x115e4d (movR64M64Effect 0x115e4d 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x115e4d (LoadPre 0x115e4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x115e4d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115e4d 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x115e52 (movR64M64Effect 0x115e52 6 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x115e52 (LoadPre 0x115e52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x115e52 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115e52 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x115e57 (movR64M64Effect 0x115e57 13 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 58) (.exec 0x115e57 (LoadPre 0x115e57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x115e57 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115e57 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x115e5c (movR64M64Effect 0x115e5c 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x115e5c (LoadPre 0x115e5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x115e5c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115e5c 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x115e61 (StorePre 0x115e61 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x115e61 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115e61 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x115e66 (movR64M64Effect 0x115e66 9 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 63) (.exec 0x115e66 (LoadPre 0x115e66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x115e66 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x115e66 9 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x115e6b (StorePre 0x115e6b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x115e6b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x115e6b 9 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x115e70 (movR64M64Effect 0x115e70 1 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 66) (.exec 0x115e70 (LoadPre 0x115e70 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x115e70 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115e70 1 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x115e78 (mulR64Effect 0x115e78 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[65, 59]
    (.letOp (n := 68) (.out 0x115e78 (mulR64Effect 0x115e78 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[65, 59]
    (.letOp (n := 69) (.exec 0x115e78 (fun s => s.RIP = 0x115e78) (mulR64Effect 0x115e78 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[65, 59]
    (.letOp (n := 70) (.out 0x115e7b (movR64R64Effect 0x115e7b 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[68]
    (.letOp (n := 71) (.exec 0x115e7b (fun s => s.RIP = 0x115e7b) (movR64R64Effect 0x115e7b 10 2) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 72) (.out 0x115e7e (movR64R64Effect 0x115e7e 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[67]
    (.letOp (n := 73) (.exec 0x115e7e (fun s => s.RIP = 0x115e7e) (movR64R64Effect 0x115e7e 11 0) (Reg.operands [.gpr 0] [])) #v[67]
    (.letOp (n := 74) (.out 0x115e81 (movR64R64Effect 0x115e81 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[62]
    (.letOp (n := 75) (.exec 0x115e81 (fun s => s.RIP = 0x115e81) (movR64R64Effect 0x115e81 0 9) (Reg.operands [.gpr 9] [])) #v[62]
    (.letOp (n := 76) (.out 0x115e84 (movR64M64Effect 0x115e84 12 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 77) (.exec 0x115e84 (LoadPre 0x115e84 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x115e84 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x115e84 12 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x115e8c (mulR64Effect 0x115e8c 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[76, 74]
    (.letOp (n := 79) (.out 0x115e8c (mulR64Effect 0x115e8c 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[76, 74]
    (.letOp (n := 80) (.exec 0x115e8c (fun s => s.RIP = 0x115e8c) (mulR64Effect 0x115e8c 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[76, 74]
    (.letOp (n := 81) (.out 0x115e8f (movR64R64Effect 0x115e8f 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[79]
    (.letOp (n := 82) (.exec 0x115e8f (fun s => s.RIP = 0x115e8f) (movR64R64Effect 0x115e8f 3 2) (Reg.operands [.gpr 2] [])) #v[79]
    (.letOp (n := 83) (.out 0x115e92 (movR64R64Effect 0x115e92 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[78]
    (.letOp (n := 84) (.exec 0x115e92 (fun s => s.RIP = 0x115e92) (movR64R64Effect 0x115e92 14 0) (Reg.operands [.gpr 0] [])) #v[78]
    (.letOp (n := 85) (.out 0x115e95 (addR64R64Effect 0x115e95 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[83, 72]
    (.letOp (n := 86) (.out 0x115e95 (addR64R64Effect 0x115e95 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[83, 72]
    (.letOp (n := 87) (.exec 0x115e95 (fun s => s.RIP = 0x115e95) (addR64R64Effect 0x115e95 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[83, 72]
    (.letOp (n := 88) (.out 0x115e98 (atFlags StatusFlags.CF (adcR64R64Effect 0x115e98 3 10)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[81, 70, 86]
    (.letOp (n := 89) (.exec 0x115e98 (fun s => s.RIP = 0x115e98) (atFlags StatusFlags.CF (adcR64R64Effect 0x115e98 3 10)) (Reg.operands [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[81, 70, 86]
    (.letOp (n := 90) (.out 0x115e9b (movR64R64Effect 0x115e9b 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 91) (.exec 0x115e9b (fun s => s.RIP = 0x115e9b) (movR64R64Effect 0x115e9b 0 13) (Reg.operands [.gpr 13] [])) #v[57]
    (.letOp (n := 92) (.exec 0x115e9e (StorePre 0x115e9e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x115e9e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x115e9e 13 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[57, 4]
    (b_l115e4d_1))))))))))))))))))))))))))))))))))))))))

def bytes_l115e4d : List UInt8 :=
  [0x48, 0x8B, 0x7C, 0x24, 0x48, 0x48, 0x8B, 0x74, 0x24, 0x40, 0x4C, 0x8B, 0x6C, 0x24, 0x38, 0x48,
    0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x44, 0x24, 0x68, 0x4C, 0x8B, 0x4C, 0x24, 0x30, 0x4C, 0x89,
    0x4C, 0x24, 0x50, 0x48, 0x8B, 0x8C, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89,
    0xD2, 0x49, 0x89, 0xC3, 0x4C, 0x89, 0xC8, 0x4C, 0x8B, 0xA4, 0x24, 0x30, 0x01, 0x00, 0x00, 0x49,
    0xF7, 0xE4, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC6, 0x4D, 0x01, 0xDE, 0x4C, 0x11, 0xD3, 0x4C, 0x89,
    0xE8, 0x4C, 0x89, 0xAC, 0x24, 0xD0, 0x00, 0x00, 0x00] ++ bytes_l115e4d_1

theorem code_l115e4d : ∀ x ∈ codeRange 0x115e4d bytes_l115e4d, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x15e4d 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l115e4d_1

@[cfg_block] def b_l11629e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11629e (movR64M64Effect 0x11629e 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11629e (LoadPre 0x11629e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11629e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11629e 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1162a3 (StorePre 0x1162a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1162a3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1162a3 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1162a8 (movR64M64Effect 0x1162a8 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1162a8 (LoadPre 0x1162a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1162a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1162a8 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1162ad (StorePre 0x1162ad 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1162ad + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1162ad 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1162b2 (movR64M64Effect 0x1162b2 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1162b2 (LoadPre 0x1162b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1162b2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1162b2 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1162b7 (StorePre 0x1162b7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1162b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1162b7 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1162bc (movR64M64Effect 0x1162bc 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1162bc (LoadPre 0x1162bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1162bc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1162bc 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1162c1 (movR64M64Effect 0x1162c1 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1162c1 (LoadPre 0x1162c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1162c1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1162c1 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1162c6 (StorePre 0x1162c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1162c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1162c6 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1162cb (StorePre 0x1162cb 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1162cb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1162cb 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1162cf (movR64R64Effect 0x1162cf 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1162cf (fun s => s.RIP = 0x1162cf) (movR64R64Effect 0x1162cf 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1162d2 (movR64R64Effect 0x1162d2 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1162d2 (fun s => s.RIP = 0x1162d2) (movR64R64Effect 0x1162d2 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1162d5 (callEffect (fun _ => 0x1145f0) 0x1162da) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1162d5 (PushPre 0x1162d5 5) (callEffect (fun _ => 0x1145f0) 0x1162da) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1162da⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1162da, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11629e : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x16, 0xE3, 0xFF, 0xFF]

theorem code_l11629e : ∀ x ∈ codeRange 0x11629e bytes_l11629e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1629e 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1162da : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1162da (movR64M64Effect 0x1162da 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1162da (LoadPre 0x1162da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1162da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1162da 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1162df (StorePre 0x1162df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1162df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1162df 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1162e4 (movR64M64Effect 0x1162e4 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1162e4 (LoadPre 0x1162e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1162e4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1162e4 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1162e9 (StorePre 0x1162e9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1162e9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1162e9 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1162ee (movR64M64Effect 0x1162ee 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1162ee (LoadPre 0x1162ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1162ee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1162ee 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1162f3 (StorePre 0x1162f3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1162f3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1162f3 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1162f8 (movR64M64Effect 0x1162f8 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1162f8 (LoadPre 0x1162f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1162f8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1162f8 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1162fd (movR64M64Effect 0x1162fd 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1162fd (LoadPre 0x1162fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1162fd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1162fd 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x116302 (StorePre 0x116302 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x116302 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116302 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x116307 (StorePre 0x116307 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x116307 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x116307 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11630b (movR64R64Effect 0x11630b 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11630b (fun s => s.RIP = 0x11630b) (movR64R64Effect 0x11630b 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11630e (movR64R64Effect 0x11630e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11630e (fun s => s.RIP = 0x11630e) (movR64R64Effect 0x11630e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x116311 (callEffect (fun _ => 0x1145f0) 0x116316) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x116311 (PushPre 0x116311 5) (callEffect (fun _ => 0x1145f0) 0x116316) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x116316⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l116316, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1162da : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xDA, 0xE2, 0xFF, 0xFF]

theorem code_l1162da : ∀ x ∈ codeRange 0x1162da bytes_l1162da, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x162da 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l116316_12 : Block Op Label signature Reg.count 565 :=
  .letOp (n := 565) (.exec 0x11672f (StorePre 0x11672f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11672f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11672f 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[555, 4]
    (.letOp (n := 566) (.out 0x116734 (leaR64Effect 0x116734 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 567) (.exec 0x116734 (fun s => s.RIP = 0x116734) (leaR64Effect 0x116734 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 568) (.out 0x116739 (movR64R64Effect 0x116739 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 569) (.exec 0x116739 (fun s => s.RIP = 0x116739) (movR64R64Effect 0x116739 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 570) (.out 0x11673c (movR64R64Effect 0x11673c 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[566]
    (.letOp (n := 571) (.exec 0x11673c (fun s => s.RIP = 0x11673c) (movR64R64Effect 0x11673c 7 3) (Reg.operands [.gpr 3] [])) #v[566]
    (.letOp (n := 572) (.out 0x11673f (movR64R64Effect 0x11673f 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[568]
    (.letOp (n := 573) (.exec 0x11673f (fun s => s.RIP = 0x11673f) (movR64R64Effect 0x11673f 6 14) (Reg.operands [.gpr 14] [])) #v[568]
    (.letOp (n := 574) (.out 0x116742 (callEffect (fun _ => 0x1145f0) 0x116747) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 575) (.exec 0x116742 (PushPre 0x116742 5) (callEffect (fun _ => 0x1145f0) 0x116747) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 576) (.const ⟨64, 0x116747⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 557), (1, 497), (2, 549), (3, 566), (4, 574), (5, 448), (6, 572), (7, 570), (8, 461), (9, 433), (10, 533), (11, 495), (12, 472), (13, 465), (14, 568), (15, 523), (22, 22), (39, 39), (50, 50), (51, 51)] 577⟩ { target := .l116747, kept := #v[], arity := rfl, guard := some (Fin.last 576) })))))))))))))

def bytes_l116316_12 : List UInt8 :=
  [0x48, 0x89, 0x74, 0x24, 0x20, 0x48, 0x8D, 0x5C, 0x24, 0x28, 0x49, 0x89, 0xE6, 0x48, 0x89, 0xDF,
    0x4C, 0x89, 0xF6, 0xE8, 0xA9, 0xDE, 0xFF, 0xFF]

theorem code_l116316_12 : ∀ x ∈ codeRange 0x11672f bytes_l116316_12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1672f 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l116316_11 : Block Op Label signature Reg.count 527 :=
  .letOp (n := 527) (.exec 0x1166db (StorePre 0x1166db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1166db + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1166db 13 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[465, 4]
    (.letOp (n := 528) (.out 0x1166e0 (movR64R64Effect 0x1166e0 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[523]
    (.letOp (n := 529) (.exec 0x1166e0 (fun s => s.RIP = 0x1166e0) (movR64R64Effect 0x1166e0 0 15) (Reg.operands [.gpr 15] [])) #v[523]
    (.letOp (n := 530) (.out 0x1166e3 (mulR64Effect 0x1166e3 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[497, 528]
    (.letOp (n := 531) (.out 0x1166e3 (mulR64Effect 0x1166e3 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[497, 528]
    (.letOp (n := 532) (.exec 0x1166e3 (fun s => s.RIP = 0x1166e3) (mulR64Effect 0x1166e3 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[497, 528]
    (.letOp (n := 533) (.out 0x1166e6 (andR64R64Effect 0x1166e6 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[518, 495]
    (.letOp (n := 534) (.exec 0x1166e6 (fun s => s.RIP = 0x1166e6) (andR64R64Effect 0x1166e6 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[518, 495]
    (.letOp (n := 535) (.out 0x1166e9 (movR64M64Effect 0x1166e9 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 536) (.exec 0x1166e9 (LoadPre 0x1166e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1166e9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1166e9 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 537) (.out 0x1166ee (andR64R64Effect 0x1166ee 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[535, 495]
    (.letOp (n := 538) (.exec 0x1166ee (fun s => s.RIP = 0x1166ee) (andR64R64Effect 0x1166ee 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[535, 495]
    (.letOp (n := 539) (.out 0x1166f1 (addR64R64Effect 0x1166f1 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[537, 530]
    (.letOp (n := 540) (.out 0x1166f1 (addR64R64Effect 0x1166f1 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[537, 530]
    (.letOp (n := 541) (.exec 0x1166f1 (fun s => s.RIP = 0x1166f1) (addR64R64Effect 0x1166f1 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[537, 530]
    (.letOp (n := 542) (.out 0x1166f4 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1166f4 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[531, 540]
    (.letOp (n := 543) (.exec 0x1166f4 (fun s => s.RIP = 0x1166f4) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1166f4 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[531, 540]
    (.letOp (n := 544) (.out 0x1166f8 (addR64R64Effect 0x1166f8 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[539, 525]
    (.letOp (n := 545) (.out 0x1166f8 (addR64R64Effect 0x1166f8 7 3) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 3] []) (.flag .CF)) #v[539, 525]
    (.letOp (n := 546) (.exec 0x1166f8 (fun s => s.RIP = 0x1166f8) (addR64R64Effect 0x1166f8 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[539, 525]
    (.letOp (n := 547) (.out 0x1166fb (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1166fb 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[542, 545]
    (.letOp (n := 548) (.exec 0x1166fb (fun s => s.RIP = 0x1166fb) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1166fb 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[542, 545]
    (.letOp (n := 549) (.out 0x1166ff (shldR64R64Effect 0x1166ff 5 2 7 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[547, 544]
    (.letOp (n := 550) (.exec 0x1166ff (fun s => s.RIP = 0x1166ff) (shldR64R64Effect 0x1166ff 5 2 7 12) (Reg.operands [.gpr 2, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[547, 544]
    (.letOp (n := 551) (.out 0x116704 (movR64Imm64Effect 0x116704 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 552) (.exec 0x116704 (fun s => s.RIP = 0x116704) (movR64Imm64Effect 0x116704 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 553) (.out 0x11670e (andR64R64Effect 0x11670e 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[238, 551]
    (.letOp (n := 554) (.exec 0x11670e (fun s => s.RIP = 0x11670e) (andR64R64Effect 0x11670e 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[238, 551]
    (.letOp (n := 555) (.out 0x116711 (addR64R64Effect 0x116711 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[553, 549]
    (.letOp (n := 556) (.exec 0x116711 (fun s => s.RIP = 0x116711) (addR64R64Effect 0x116711 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[553, 549]
    (.letOp (n := 557) (.out 0x116714 (movR64M64Effect 0x116714 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 558) (.exec 0x116714 (LoadPre 0x116714 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x116714 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116714 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 559) (.exec 0x116719 (StorePre 0x116719 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x116719 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x116719 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[557, 4]
    (.letOp (n := 560) (.exec 0x11671d (StorePre 0x11671d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11671d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11671d 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[461, 4]
    (.letOp (n := 561) (.exec 0x116722 (StorePre 0x116722 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x116722 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116722 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[533, 4]
    (.letOp (n := 562) (.out 0x116727 (andR64R64Effect 0x116727 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[544, 495]
    (.letOp (n := 563) (.exec 0x116727 (fun s => s.RIP = 0x116727) (andR64R64Effect 0x116727 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[544, 495]
    (.letOp (n := 564) (.exec 0x11672a (StorePre 0x11672a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11672a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11672a 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[562, 4]
    (b_l116316_12))))))))))))))))))))))))))))))))))))))

def bytes_l116316_11 : List UInt8 :=
  [0x4C, 0x89, 0x6C, 0x24, 0x18, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0xE1, 0x4D, 0x21, 0xDA, 0x48, 0x8B,
    0x7C, 0x24, 0x58, 0x4C, 0x21, 0xDF, 0x48, 0x01, 0xC7, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x01, 0xDF,
    0x48, 0x83, 0xD2, 0x00, 0x48, 0x0F, 0xA4, 0xFA, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x00, 0x00, 0x48, 0x21, 0xC6, 0x48, 0x01, 0xD6, 0x48, 0x8B, 0x44, 0x24, 0x78, 0x48, 0x89,
    0x04, 0x24, 0x4C, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x89, 0x54, 0x24, 0x10, 0x4C, 0x21, 0xDF, 0x48,
    0x89, 0x7C, 0x24, 0x18] ++ bytes_l116316_12

theorem code_l116316_11 : ∀ x ∈ codeRange 0x1166db bytes_l116316_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x166db 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116316_12

def b_l116316_10 : Block Op Label signature Reg.count 481 :=
  .letOp (n := 481) (.out 0x11668a (addR64R64Effect 0x11668a 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[479, 472]
    (.letOp (n := 482) (.out 0x11668a (addR64R64Effect 0x11668a 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[479, 472]
    (.letOp (n := 483) (.exec 0x11668a (fun s => s.RIP = 0x11668a) (addR64R64Effect 0x11668a 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[479, 472]
    (.letOp (n := 484) (.out 0x11668d (atFlags StatusFlags.CF (adcR64R64Effect 0x11668d 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[470, 477, 482]
    (.letOp (n := 485) (.exec 0x11668d (fun s => s.RIP = 0x11668d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11668d 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[470, 477, 482]
    (.letOp (n := 486) (.out 0x116690 (addR64R64Effect 0x116690 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[481, 409]
    (.letOp (n := 487) (.out 0x116690 (addR64R64Effect 0x116690 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[481, 409]
    (.letOp (n := 488) (.exec 0x116690 (fun s => s.RIP = 0x116690) (addR64R64Effect 0x116690 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[481, 409]
    (.letOp (n := 489) (.out 0x116693 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116693 15 0x0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[484, 487]
    (.letOp (n := 490) (.exec 0x116693 (fun s => s.RIP = 0x116693) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116693 15 0x0)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[484, 487]
    (.letOp (n := 491) (.out 0x116697 (movR64R64Effect 0x116697 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[486]
    (.letOp (n := 492) (.exec 0x116697 (fun s => s.RIP = 0x116697) (movR64R64Effect 0x116697 0 14) (Reg.operands [.gpr 14] [])) #v[486]
    (.letOp (n := 493) (.out 0x11669a (andR64R64Effect 0x11669a 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[491, 459]
    (.letOp (n := 494) (.exec 0x11669a (fun s => s.RIP = 0x11669a) (andR64R64Effect 0x11669a 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[491, 459]
    (.letOp (n := 495) (.out 0x11669d (movR64R64Effect 0x11669d 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[459]
    (.letOp (n := 496) (.exec 0x11669d (fun s => s.RIP = 0x11669d) (movR64R64Effect 0x11669d 11 1) (Reg.operands [.gpr 1] [])) #v[459]
    (.letOp (n := 497) (.out 0x1166a0 (movR64Imm64Effect 0x1166a0 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 498) (.exec 0x1166a0 (fun s => s.RIP = 0x1166a0) (movR64Imm64Effect 0x1166a0 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 499) (.out 0x1166aa (mulR64Effect 0x1166aa 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[497, 493]
    (.letOp (n := 500) (.out 0x1166aa (mulR64Effect 0x1166aa 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[497, 493]
    (.letOp (n := 501) (.exec 0x1166aa (fun s => s.RIP = 0x1166aa) (mulR64Effect 0x1166aa 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[497, 493]
    (.letOp (n := 502) (.out 0x1166ad (addR64R64Effect 0x1166ad 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[455, 448]
    (.letOp (n := 503) (.out 0x1166ad (addR64R64Effect 0x1166ad 10 5) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 5] []) (.flag .CF)) #v[455, 448]
    (.letOp (n := 504) (.exec 0x1166ad (fun s => s.RIP = 0x1166ad) (addR64R64Effect 0x1166ad 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[455, 448]
    (.letOp (n := 505) (.out 0x1166b0 (atFlags StatusFlags.CF (adcR64M64Effect 0x1166b0 3 (.sib 4 none 0 (.d8 0x68)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[457, 4, 503]
    (.letOp (n := 506) (.exec 0x1166b0 (LoadPre 0x1166b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1166b0 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1166b0 3 (.sib 4 none 0 (.d8 0x68)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[457, 4, 503]
    (.letOp (n := 507) (.out 0x1166b5 (addR64M64Effect 0x1166b5 10 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[502, 4]
    (.letOp (n := 508) (.out 0x1166b5 (addR64M64Effect 0x1166b5 10 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[502, 4]
    (.letOp (n := 509) (.exec 0x1166b5 (LoadPre 0x1166b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1166b5 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1166b5 10 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[502, 4]
    (.letOp (n := 510) (.out 0x1166ba (atFlags StatusFlags.CF (adcR64M64Effect 0x1166ba 3 (.sib 4 none 0 (.d8 0x50)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[505, 4, 508]
    (.letOp (n := 511) (.exec 0x1166ba (LoadPre 0x1166ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1166ba + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1166ba 3 (.sib 4 none 0 (.d8 0x50)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[505, 4, 508]
    (.letOp (n := 512) (.out 0x1166bf (addR64R64Effect 0x1166bf 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[507, 499]
    (.letOp (n := 513) (.out 0x1166bf (addR64R64Effect 0x1166bf 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[507, 499]
    (.letOp (n := 514) (.exec 0x1166bf (fun s => s.RIP = 0x1166bf) (addR64R64Effect 0x1166bf 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[507, 499]
    (.letOp (n := 515) (.out 0x1166c2 (atFlags StatusFlags.CF (adcR64R64Effect 0x1166c2 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[510, 500, 513]
    (.letOp (n := 516) (.exec 0x1166c2 (fun s => s.RIP = 0x1166c2) (atFlags StatusFlags.CF (adcR64R64Effect 0x1166c2 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[510, 500, 513]
    (.letOp (n := 517) (.exec 0x1166c5 (StorePre 0x1166c5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1166c5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1166c5 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[389, 4]
    (.letOp (n := 518) (.out 0x1166ca (addR64R64Effect 0x1166ca 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[512, 433]
    (.letOp (n := 519) (.out 0x1166ca (addR64R64Effect 0x1166ca 10 9) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 9] []) (.flag .CF)) #v[512, 433]
    (.letOp (n := 520) (.exec 0x1166ca (fun s => s.RIP = 0x1166ca) (addR64R64Effect 0x1166ca 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[512, 433]
    (.letOp (n := 521) (.out 0x1166cd (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1166cd 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[515, 519]
    (.letOp (n := 522) (.exec 0x1166cd (fun s => s.RIP = 0x1166cd) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1166cd 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[515, 519]
    (.letOp (n := 523) (.out 0x1166d1 (shldR64R64Effect 0x1166d1 5 15 14 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[489, 486]
    (.letOp (n := 524) (.exec 0x1166d1 (fun s => s.RIP = 0x1166d1) (shldR64R64Effect 0x1166d1 5 15 14 12) (Reg.operands [.gpr 15, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[489, 486]
    (.letOp (n := 525) (.out 0x1166d6 (shldR64R64Effect 0x1166d6 5 3 10 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[521, 518]
    (.letOp (n := 526) (.exec 0x1166d6 (fun s => s.RIP = 0x1166d6) (shldR64R64Effect 0x1166d6 5 3 10 12) (Reg.operands [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[521, 518]
    (b_l116316_11))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116316_10 : List UInt8 :=
  [0x4D, 0x01, 0xE6, 0x49, 0x11, 0xD7, 0x4D, 0x01, 0xDE, 0x49, 0x83, 0xD7, 0x00, 0x4C, 0x89, 0xF0,
    0x48, 0x21, 0xC8, 0x49, 0x89, 0xCB, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE1, 0x49, 0x01, 0xEA, 0x48, 0x13, 0x5C, 0x24, 0x68, 0x4C, 0x03, 0x54, 0x24, 0x60,
    0x48, 0x13, 0x5C, 0x24, 0x50, 0x49, 0x01, 0xC2, 0x48, 0x11, 0xD3, 0x48, 0x89, 0x7C, 0x24, 0x20,
    0x4D, 0x01, 0xCA, 0x48, 0x83, 0xD3, 0x00, 0x4D, 0x0F, 0xA4, 0xF7, 0x0C, 0x4C, 0x0F, 0xA4, 0xD3,
    0x0C] ++ bytes_l116316_11

theorem code_l116316_10 : ∀ x ∈ codeRange 0x11668a bytes_l116316_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1668a 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116316_11

def b_l116316_9 : Block Op Label signature Reg.count 440 :=
  .letOp (n := 440) (.exec 0x116630 (StorePre 0x116630 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x116630 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116630 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[438, 4]
    (.letOp (n := 441) (.exec 0x116635 (StorePre 0x116635 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x116635 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116635 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[437, 4]
    (.letOp (n := 442) (.out 0x11663a (movR64M64Effect 0x11663a 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 443) (.exec 0x11663a (LoadPre 0x11663a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11663a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11663a 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 444) (.out 0x116642 (mulM64Effect 0x116642 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[442, 4]
    (.letOp (n := 445) (.out 0x116642 (mulM64Effect 0x116642 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[442, 4]
    (.letOp (n := 446) (.exec 0x116642 (LoadPre 0x116642 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116642 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x116642 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[442, 4]
    (.letOp (n := 447) (.exec 0x116647 (StorePre 0x116647 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116647 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116647 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[445, 4]
    (.letOp (n := 448) (.out 0x11664c (movR64R64Effect 0x11664c 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[444]
    (.letOp (n := 449) (.exec 0x11664c (fun s => s.RIP = 0x11664c) (movR64R64Effect 0x11664c 5 0) (Reg.operands [.gpr 0] [])) #v[444]
    (.letOp (n := 450) (.out 0x11664f (movR64M64Effect 0x11664f 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 451) (.exec 0x11664f (LoadPre 0x11664f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11664f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11664f 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 452) (.out 0x116657 (mulM64Effect 0x116657 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[450, 4]
    (.letOp (n := 453) (.out 0x116657 (mulM64Effect 0x116657 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[450, 4]
    (.letOp (n := 454) (.exec 0x116657 (LoadPre 0x116657 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x116657 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x116657 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[450, 4]
    (.letOp (n := 455) (.out 0x11665c (movR64R64Effect 0x11665c 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[452]
    (.letOp (n := 456) (.exec 0x11665c (fun s => s.RIP = 0x11665c) (movR64R64Effect 0x11665c 10 0) (Reg.operands [.gpr 0] [])) #v[452]
    (.letOp (n := 457) (.out 0x11665f (movR64R64Effect 0x11665f 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[453]
    (.letOp (n := 458) (.exec 0x11665f (fun s => s.RIP = 0x11665f) (movR64R64Effect 0x11665f 3 2) (Reg.operands [.gpr 2] [])) #v[453]
    (.letOp (n := 459) (.out 0x116662 (movR64R64Effect 0x116662 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[369]
    (.letOp (n := 460) (.exec 0x116662 (fun s => s.RIP = 0x116662) (movR64R64Effect 0x116662 1 15) (Reg.operands [.gpr 15] [])) #v[369]
    (.letOp (n := 461) (.out 0x116665 (andR64R64Effect 0x116665 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[428, 369]
    (.letOp (n := 462) (.exec 0x116665 (fun s => s.RIP = 0x116665) (andR64R64Effect 0x116665 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[428, 369]
    (.letOp (n := 463) (.out 0x116668 (movR64M64Effect 0x116668 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 464) (.exec 0x116668 (LoadPre 0x116668 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x116668 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116668 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 465) (.out 0x116670 (movR64M64Effect 0x116670 13 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 466) (.exec 0x116670 (LoadPre 0x116670 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x116670 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116670 13 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 467) (.out 0x116678 (mulR64Effect 0x116678 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[465, 463]
    (.letOp (n := 468) (.out 0x116678 (mulR64Effect 0x116678 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[465, 463]
    (.letOp (n := 469) (.exec 0x116678 (fun s => s.RIP = 0x116678) (mulR64Effect 0x116678 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[465, 463]
    (.letOp (n := 470) (.out 0x11667b (movR64R64Effect 0x11667b 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[468]
    (.letOp (n := 471) (.exec 0x11667b (fun s => s.RIP = 0x11667b) (movR64R64Effect 0x11667b 15 2) (Reg.operands [.gpr 2] [])) #v[468]
    (.letOp (n := 472) (.out 0x11667e (movR64R64Effect 0x11667e 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[467]
    (.letOp (n := 473) (.exec 0x11667e (fun s => s.RIP = 0x11667e) (movR64R64Effect 0x11667e 12 0) (Reg.operands [.gpr 0] [])) #v[467]
    (.letOp (n := 474) (.out 0x116681 (movR64R64Effect 0x116681 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[374]
    (.letOp (n := 475) (.exec 0x116681 (fun s => s.RIP = 0x116681) (movR64R64Effect 0x116681 0 14) (Reg.operands [.gpr 14] [])) #v[374]
    (.letOp (n := 476) (.out 0x116684 (mulR64Effect 0x116684 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[389, 474]
    (.letOp (n := 477) (.out 0x116684 (mulR64Effect 0x116684 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[389, 474]
    (.letOp (n := 478) (.exec 0x116684 (fun s => s.RIP = 0x116684) (mulR64Effect 0x116684 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[389, 474]
    (.letOp (n := 479) (.out 0x116687 (movR64R64Effect 0x116687 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[476]
    (.letOp (n := 480) (.exec 0x116687 (fun s => s.RIP = 0x116687) (movR64R64Effect 0x116687 14 0) (Reg.operands [.gpr 0] [])) #v[476]
    (b_l116316_10)))))))))))))))))))))))))))))))))))))))))

def bytes_l116316_9 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x68, 0x48, 0x89, 0x54, 0x24, 0x68, 0x48, 0x89, 0xC5, 0x48,
    0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x70, 0x49, 0x89, 0xC2, 0x48,
    0x89, 0xD3, 0x4C, 0x89, 0xF9, 0x4D, 0x21, 0xF8, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x4C, 0x8B, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xD7, 0x49, 0x89,
    0xC4, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xC6] ++ bytes_l116316_10

theorem code_l116316_9 : ∀ x ∈ codeRange 0x116630 bytes_l116316_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16630 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116316_10

def b_l116316_8 : Block Op Label signature Reg.count 391 :=
  .letOp (n := 391) (.out 0x1165de (mulR64Effect 0x1165de 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[389, 387]
    (.letOp (n := 392) (.out 0x1165de (mulR64Effect 0x1165de 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[389, 387]
    (.letOp (n := 393) (.exec 0x1165de (fun s => s.RIP = 0x1165de) (mulR64Effect 0x1165de 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[389, 387]
    (.letOp (n := 394) (.out 0x1165e1 (addR64R64Effect 0x1165e1 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[391, 383]
    (.letOp (n := 395) (.out 0x1165e1 (addR64R64Effect 0x1165e1 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[391, 383]
    (.letOp (n := 396) (.exec 0x1165e1 (fun s => s.RIP = 0x1165e1) (addR64R64Effect 0x1165e1 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[391, 383]
    (.letOp (n := 397) (.out 0x1165e4 (atFlags StatusFlags.CF (adcR64R64Effect 0x1165e4 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[381, 392, 395]
    (.letOp (n := 398) (.exec 0x1165e4 (fun s => s.RIP = 0x1165e4) (atFlags StatusFlags.CF (adcR64R64Effect 0x1165e4 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[381, 392, 395]
    (.letOp (n := 399) (.out 0x1165e7 (addR64R64Effect 0x1165e7 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[394, 365]
    (.letOp (n := 400) (.out 0x1165e7 (addR64R64Effect 0x1165e7 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[394, 365]
    (.letOp (n := 401) (.exec 0x1165e7 (fun s => s.RIP = 0x1165e7) (addR64R64Effect 0x1165e7 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[394, 365]
    (.letOp (n := 402) (.out 0x1165ea (atFlags StatusFlags.CF (adcR64R64Effect 0x1165ea 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[397, 367, 400]
    (.letOp (n := 403) (.exec 0x1165ea (fun s => s.RIP = 0x1165ea) (atFlags StatusFlags.CF (adcR64R64Effect 0x1165ea 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[397, 367, 400]
    (.letOp (n := 404) (.out 0x1165ed (addR64R64Effect 0x1165ed 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[399, 318]
    (.letOp (n := 405) (.out 0x1165ed (addR64R64Effect 0x1165ed 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[399, 318]
    (.letOp (n := 406) (.exec 0x1165ed (fun s => s.RIP = 0x1165ed) (addR64R64Effect 0x1165ed 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[399, 318]
    (.letOp (n := 407) (.out 0x1165f0 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1165f0 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[402, 405]
    (.letOp (n := 408) (.exec 0x1165f0 (fun s => s.RIP = 0x1165f0) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1165f0 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[402, 405]
    (.letOp (n := 409) (.out 0x1165f4 (shldR64R64Effect 0x1165f4 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[407, 404]
    (.letOp (n := 410) (.exec 0x1165f4 (fun s => s.RIP = 0x1165f4) (shldR64R64Effect 0x1165f4 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[407, 404]
    (.letOp (n := 411) (.out 0x1165f9 (andR64R64Effect 0x1165f9 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[404, 369]
    (.letOp (n := 412) (.exec 0x1165f9 (fun s => s.RIP = 0x1165f9) (andR64R64Effect 0x1165f9 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[404, 369]
    (.letOp (n := 413) (.out 0x1165fc (movR64Imm64Effect 0x1165fc 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 414) (.exec 0x1165fc (fun s => s.RIP = 0x1165fc) (movR64Imm64Effect 0x1165fc 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 415) (.out 0x116606 (mulR64Effect 0x116606 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[413, 411]
    (.letOp (n := 416) (.out 0x116606 (mulR64Effect 0x116606 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[413, 411]
    (.letOp (n := 417) (.exec 0x116606 (fun s => s.RIP = 0x116606) (mulR64Effect 0x116606 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[413, 411]
    (.letOp (n := 418) (.out 0x116609 (addR64M64Effect 0x116609 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[358, 4]
    (.letOp (n := 419) (.out 0x116609 (addR64M64Effect 0x116609 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[358, 4]
    (.letOp (n := 420) (.exec 0x116609 (LoadPre 0x116609 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x116609 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x116609 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[358, 4]
    (.letOp (n := 421) (.out 0x116611 (atFlags StatusFlags.CF (adcR64M64Effect 0x116611 9 (.sib 4 none 0 (.d8 0x60)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[356, 4, 419]
    (.letOp (n := 422) (.exec 0x116611 (LoadPre 0x116611 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x116611 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x116611 9 (.sib 4 none 0 (.d8 0x60)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[356, 4, 419]
    (.letOp (n := 423) (.out 0x116616 (addR64R64Effect 0x116616 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[418, 415]
    (.letOp (n := 424) (.out 0x116616 (addR64R64Effect 0x116616 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[418, 415]
    (.letOp (n := 425) (.exec 0x116616 (fun s => s.RIP = 0x116616) (addR64R64Effect 0x116616 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[418, 415]
    (.letOp (n := 426) (.out 0x116619 (atFlags StatusFlags.CF (adcR64R64Effect 0x116619 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[421, 416, 424]
    (.letOp (n := 427) (.exec 0x116619 (fun s => s.RIP = 0x116619) (atFlags StatusFlags.CF (adcR64R64Effect 0x116619 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[421, 416, 424]
    (.letOp (n := 428) (.out 0x11661c (addR64R64Effect 0x11661c 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[423, 340]
    (.letOp (n := 429) (.out 0x11661c (addR64R64Effect 0x11661c 8 3) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 3] []) (.flag .CF)) #v[423, 340]
    (.letOp (n := 430) (.exec 0x11661c (fun s => s.RIP = 0x11661c) (addR64R64Effect 0x11661c 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[423, 340]
    (.letOp (n := 431) (.out 0x11661f (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11661f 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[426, 429]
    (.letOp (n := 432) (.exec 0x11661f (fun s => s.RIP = 0x11661f) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11661f 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[426, 429]
    (.letOp (n := 433) (.out 0x116623 (shldR64R64Effect 0x116623 5 9 8 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[431, 428]
    (.letOp (n := 434) (.exec 0x116623 (fun s => s.RIP = 0x116623) (shldR64R64Effect 0x116623 5 9 8 12) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[431, 428]
    (.letOp (n := 435) (.out 0x116628 (movR64R64Effect 0x116628 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[385]
    (.letOp (n := 436) (.exec 0x116628 (fun s => s.RIP = 0x116628) (movR64R64Effect 0x116628 0 1) (Reg.operands [.gpr 1] [])) #v[385]
    (.letOp (n := 437) (.out 0x11662b (mulM64Effect 0x11662b 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[435, 4]
    (.letOp (n := 438) (.out 0x11662b (mulM64Effect 0x11662b 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[435, 4]
    (.letOp (n := 439) (.exec 0x11662b (LoadPre 0x11662b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11662b + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11662b 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[435, 4]
    (b_l116316_9)))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116316_8 : List UInt8 :=
  [0x48, 0xF7, 0xE7, 0x48, 0x01, 0xE8, 0x49, 0x11, 0xD3, 0x4C, 0x01, 0xE0, 0x4D, 0x11, 0xEB, 0x4C,
    0x01, 0xD0, 0x49, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x4C, 0x21, 0xF8, 0x48, 0xBA,
    0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x03, 0x84, 0x24, 0x80,
    0x00, 0x00, 0x00, 0x4C, 0x13, 0x4C, 0x24, 0x60, 0x49, 0x01, 0xC0, 0x49, 0x11, 0xD1, 0x49, 0x01,
    0xD8, 0x49, 0x83, 0xD1, 0x00, 0x4D, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0x64,
    0x24, 0x50] ++ bytes_l116316_9

theorem code_l116316_8 : ∀ x ∈ codeRange 0x1165de bytes_l116316_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x165de 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116316_9

def b_l116316_7 : Block Op Label signature Reg.count 350 :=
  .letOp (n := 350) (.exec 0x116581 (StorePre 0x116581 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x116581 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x116581 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[346, 4]
    (.letOp (n := 351) (.out 0x116589 (movR64R64Effect 0x116589 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[249]
    (.letOp (n := 352) (.exec 0x116589 (fun s => s.RIP = 0x116589) (movR64R64Effect 0x116589 0 9) (Reg.operands [.gpr 9] [])) #v[249]
    (.letOp (n := 353) (.out 0x11658c (mulM64Effect 0x11658c 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[351, 4]
    (.letOp (n := 354) (.out 0x11658c (mulM64Effect 0x11658c 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[351, 4]
    (.letOp (n := 355) (.exec 0x11658c (LoadPre 0x11658c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11658c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11658c 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[351, 4]
    (.letOp (n := 356) (.out 0x116591 (movR64R64Effect 0x116591 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[354]
    (.letOp (n := 357) (.exec 0x116591 (fun s => s.RIP = 0x116591) (movR64R64Effect 0x116591 9 2) (Reg.operands [.gpr 2] [])) #v[354]
    (.letOp (n := 358) (.out 0x116594 (movR64R64Effect 0x116594 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[353]
    (.letOp (n := 359) (.exec 0x116594 (fun s => s.RIP = 0x116594) (movR64R64Effect 0x116594 8 0) (Reg.operands [.gpr 0] [])) #v[353]
    (.letOp (n := 360) (.out 0x116597 (movR64R64Effect 0x116597 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[258]
    (.letOp (n := 361) (.exec 0x116597 (fun s => s.RIP = 0x116597) (movR64R64Effect 0x116597 0 5) (Reg.operands [.gpr 5] [])) #v[258]
    (.letOp (n := 362) (.out 0x11659a (mulM64Effect 0x11659a 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[360, 4]
    (.letOp (n := 363) (.out 0x11659a (mulM64Effect 0x11659a 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[360, 4]
    (.letOp (n := 364) (.exec 0x11659a (LoadPre 0x11659a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11659a + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11659a 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[360, 4]
    (.letOp (n := 365) (.out 0x11659f (movR64R64Effect 0x11659f 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[362]
    (.letOp (n := 366) (.exec 0x11659f (fun s => s.RIP = 0x11659f) (movR64R64Effect 0x11659f 12 0) (Reg.operands [.gpr 0] [])) #v[362]
    (.letOp (n := 367) (.out 0x1165a2 (movR64R64Effect 0x1165a2 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[363]
    (.letOp (n := 368) (.exec 0x1165a2 (fun s => s.RIP = 0x1165a2) (movR64R64Effect 0x1165a2 13 2) (Reg.operands [.gpr 2] [])) #v[363]
    (.letOp (n := 369) (.out 0x1165a5 (movR64Imm64Effect 0x1165a5 15 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 370) (.exec 0x1165a5 (fun s => s.RIP = 0x1165a5) (movR64Imm64Effect 0x1165a5 15 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 371) (.out 0x1165af (andR64R64Effect 0x1165af 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[342, 369]
    (.letOp (n := 372) (.exec 0x1165af (fun s => s.RIP = 0x1165af) (andR64R64Effect 0x1165af 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[342, 369]
    (.letOp (n := 373) (.exec 0x1165b2 (StorePre 0x1165b2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1165b2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1165b2 11 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[371, 4]
    (.letOp (n := 374) (.out 0x1165b7 (movR64M64Effect 0x1165b7 14 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 375) (.exec 0x1165b7 (LoadPre 0x1165b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1165b7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1165b7 14 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 376) (.out 0x1165bf (movR64R64Effect 0x1165bf 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[374]
    (.letOp (n := 377) (.exec 0x1165bf (fun s => s.RIP = 0x1165bf) (movR64R64Effect 0x1165bf 0 14) (Reg.operands [.gpr 14] [])) #v[374]
    (.letOp (n := 378) (.out 0x1165c2 (mulR64Effect 0x1165c2 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[282, 376]
    (.letOp (n := 379) (.out 0x1165c2 (mulR64Effect 0x1165c2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[282, 376]
    (.letOp (n := 380) (.exec 0x1165c2 (fun s => s.RIP = 0x1165c2) (mulR64Effect 0x1165c2 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[282, 376]
    (.letOp (n := 381) (.out 0x1165c5 (movR64R64Effect 0x1165c5 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[379]
    (.letOp (n := 382) (.exec 0x1165c5 (fun s => s.RIP = 0x1165c5) (movR64R64Effect 0x1165c5 11 2) (Reg.operands [.gpr 2] [])) #v[379]
    (.letOp (n := 383) (.out 0x1165c8 (movR64R64Effect 0x1165c8 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[378]
    (.letOp (n := 384) (.exec 0x1165c8 (fun s => s.RIP = 0x1165c8) (movR64R64Effect 0x1165c8 5 0) (Reg.operands [.gpr 0] [])) #v[378]
    (.letOp (n := 385) (.out 0x1165cb (movR64M64Effect 0x1165cb 1 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 386) (.exec 0x1165cb (LoadPre 0x1165cb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1165cb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1165cb 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 387) (.out 0x1165d3 (movR64R64Effect 0x1165d3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[385]
    (.letOp (n := 388) (.exec 0x1165d3 (fun s => s.RIP = 0x1165d3) (movR64R64Effect 0x1165d3 0 1) (Reg.operands [.gpr 1] [])) #v[385]
    (.letOp (n := 389) (.out 0x1165d6 (movR64M64Effect 0x1165d6 7 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 390) (.exec 0x1165d6 (LoadPre 0x1165d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1165d6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1165d6 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l116316_8)))))))))))))))))))))))))))))))))))))))))

def bytes_l116316_7 : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0x64, 0x24, 0x68,
    0x49, 0x89, 0xD1, 0x49, 0x89, 0xC0, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0x64, 0x24, 0x70, 0x49, 0x89,
    0xC4, 0x49, 0x89, 0xD5, 0x49, 0xBF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4D, 0x21,
    0xFB, 0x4C, 0x89, 0x5C, 0x24, 0x78, 0x4C, 0x8B, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xF0, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0x8C, 0x24, 0xD0, 0x00,
    0x00, 0x00, 0x48, 0x89, 0xC8, 0x48, 0x8B, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] ++ bytes_l116316_8

theorem code_l116316_7 : ∀ x ∈ codeRange 0x116581 bytes_l116316_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16581 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116316_8

def b_l116316_6 : Block Op Label signature Reg.count 306 :=
  .letOp (n := 306) (.out 0x116529 (atFlags StatusFlags.CF (adcR64R64Effect 0x116529 10 15)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[301, 276, 304]
    (.letOp (n := 307) (.exec 0x116529 (fun s => s.RIP = 0x116529) (atFlags StatusFlags.CF (adcR64R64Effect 0x116529 10 15)) (Reg.operands [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[301, 276, 304]
    (.letOp (n := 308) (.out 0x11652c (addR64R64Effect 0x11652c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[303, 267]
    (.letOp (n := 309) (.out 0x11652c (addR64R64Effect 0x11652c 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[303, 267]
    (.letOp (n := 310) (.exec 0x11652c (fun s => s.RIP = 0x11652c) (addR64R64Effect 0x11652c 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[303, 267]
    (.letOp (n := 311) (.out 0x11652f (atFlags StatusFlags.CF (adcR64R64Effect 0x11652f 10 11)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[306, 265, 309]
    (.letOp (n := 312) (.exec 0x11652f (fun s => s.RIP = 0x11652f) (atFlags StatusFlags.CF (adcR64R64Effect 0x11652f 10 11)) (Reg.operands [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[306, 265, 309]
    (.letOp (n := 313) (.out 0x116532 (addR64R64Effect 0x116532 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[308, 243]
    (.letOp (n := 314) (.out 0x116532 (addR64R64Effect 0x116532 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[308, 243]
    (.letOp (n := 315) (.exec 0x116532 (fun s => s.RIP = 0x116532) (addR64R64Effect 0x116532 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[308, 243]
    (.letOp (n := 316) (.out 0x116535 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116535 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[311, 314]
    (.letOp (n := 317) (.exec 0x116535 (fun s => s.RIP = 0x116535) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116535 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[311, 314]
    (.letOp (n := 318) (.out 0x116539 (shldR64R64Effect 0x116539 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[316, 313]
    (.letOp (n := 319) (.exec 0x116539 (fun s => s.RIP = 0x116539) (shldR64R64Effect 0x116539 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[316, 313]
    (.letOp (n := 320) (.out 0x11653e (shlR64Effect 0x11653e 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[313]
    (.letOp (n := 321) (.exec 0x11653e (fun s => s.RIP = 0x11653e) (shlR64Effect 0x11653e 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[313]
    (.letOp (n := 322) (.out 0x116542 (movR64Imm64Effect 0x116542 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 323) (.exec 0x116542 (fun s => s.RIP = 0x116542) (movR64Imm64Effect 0x116542 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 324) (.out 0x11654c (andR64R64Effect 0x11654c 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[320, 322]
    (.letOp (n := 325) (.exec 0x11654c (fun s => s.RIP = 0x11654c) (andR64R64Effect 0x11654c 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[320, 322]
    (.letOp (n := 326) (.out 0x11654f (orR64R64Effect 0x11654f 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[324, 278]
    (.letOp (n := 327) (.exec 0x11654f (fun s => s.RIP = 0x11654f) (orR64R64Effect 0x11654f 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[324, 278]
    (.letOp (n := 328) (.out 0x116552 (movR64Imm64Effect 0x116552 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 329) (.exec 0x116552 (fun s => s.RIP = 0x116552) (movR64Imm64Effect 0x116552 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 330) (.out 0x11655c (mulR64Effect 0x11655c 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[328, 326]
    (.letOp (n := 331) (.out 0x11655c (mulR64Effect 0x11655c 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[328, 326]
    (.letOp (n := 332) (.exec 0x11655c (fun s => s.RIP = 0x11655c) (mulR64Effect 0x11655c 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[328, 326]
    (.letOp (n := 333) (.out 0x11655f (movR64R64Effect 0x11655f 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[331]
    (.letOp (n := 334) (.exec 0x11655f (fun s => s.RIP = 0x11655f) (movR64R64Effect 0x11655f 3 2) (Reg.operands [.gpr 2] [])) #v[331]
    (.letOp (n := 335) (.out 0x116562 (addR64M64Effect 0x116562 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[330, 4]
    (.letOp (n := 336) (.out 0x116562 (addR64M64Effect 0x116562 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[330, 4]
    (.letOp (n := 337) (.exec 0x116562 (LoadPre 0x116562 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x116562 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x116562 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[330, 4]
    (.letOp (n := 338) (.out 0x116567 (atFlags StatusFlags.CF (adcR64M64Effect 0x116567 3 (.sib 4 none 0 (.d8 0x78)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[333, 4, 336]
    (.letOp (n := 339) (.exec 0x116567 (LoadPre 0x116567 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x116567 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x116567 3 (.sib 4 none 0 (.d8 0x78)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[333, 4, 336]
    (.letOp (n := 340) (.out 0x11656c (shldR64R64Effect 0x11656c 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[338, 335]
    (.letOp (n := 341) (.exec 0x11656c (fun s => s.RIP = 0x11656c) (shldR64R64Effect 0x11656c 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[338, 335]
    (.letOp (n := 342) (.out 0x116571 (movR64R64Effect 0x116571 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[335]
    (.letOp (n := 343) (.exec 0x116571 (fun s => s.RIP = 0x116571) (movR64R64Effect 0x116571 11 0) (Reg.operands [.gpr 0] [])) #v[335]
    (.letOp (n := 344) (.out 0x116574 (movR64R64Effect 0x116574 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[291]
    (.letOp (n := 345) (.exec 0x116574 (fun s => s.RIP = 0x116574) (movR64R64Effect 0x116574 0 1) (Reg.operands [.gpr 1] [])) #v[291]
    (.letOp (n := 346) (.out 0x116577 (mulM64Effect 0x116577 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[344, 4]
    (.letOp (n := 347) (.out 0x116577 (mulM64Effect 0x116577 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[344, 4]
    (.letOp (n := 348) (.exec 0x116577 (LoadPre 0x116577 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x116577 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x116577 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[344, 4]
    (.letOp (n := 349) (.exec 0x11657c (StorePre 0x11657c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11657c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11657c 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[347, 4]
    (b_l116316_7))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116316_6 : List UInt8 :=
  [0x4D, 0x11, 0xFA, 0x48, 0x01, 0xD8, 0x4D, 0x11, 0xDA, 0x4C, 0x01, 0xC0, 0x49, 0x83, 0xD2, 0x00,
    0x49, 0x0F, 0xA4, 0xC2, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x4C, 0x09, 0xE8, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD3, 0x48, 0x03, 0x44, 0x24, 0x60, 0x48, 0x13,
    0x5C, 0x24, 0x78, 0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xC8, 0x48, 0xF7,
    0x64, 0x24, 0x50, 0x48, 0x89, 0x54, 0x24, 0x60] ++ bytes_l116316_7

theorem code_l116316_6 : ∀ x ∈ codeRange 0x116529 bytes_l116316_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16529 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116316_7

def b_l116316_5 : Block Op Label signature Reg.count 260 :=
  .letOp (n := 260) (.out 0x1164d3 (movR64R64Effect 0x1164d3 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[258]
    (.letOp (n := 261) (.exec 0x1164d3 (fun s => s.RIP = 0x1164d3) (movR64R64Effect 0x1164d3 0 5) (Reg.operands [.gpr 5] [])) #v[258]
    (.letOp (n := 262) (.out 0x1164d6 (mulR64Effect 0x1164d6 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[164, 260]
    (.letOp (n := 263) (.out 0x1164d6 (mulR64Effect 0x1164d6 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[164, 260]
    (.letOp (n := 264) (.exec 0x1164d6 (fun s => s.RIP = 0x1164d6) (mulR64Effect 0x1164d6 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[164, 260]
    (.letOp (n := 265) (.out 0x1164d9 (movR64R64Effect 0x1164d9 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[263]
    (.letOp (n := 266) (.exec 0x1164d9 (fun s => s.RIP = 0x1164d9) (movR64R64Effect 0x1164d9 11 2) (Reg.operands [.gpr 2] [])) #v[263]
    (.letOp (n := 267) (.out 0x1164dc (movR64R64Effect 0x1164dc 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[262]
    (.letOp (n := 268) (.exec 0x1164dc (fun s => s.RIP = 0x1164dc) (movR64R64Effect 0x1164dc 3 0) (Reg.operands [.gpr 0] [])) #v[262]
    (.letOp (n := 269) (.out 0x1164df (movR64M64Effect 0x1164df 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 270) (.exec 0x1164df (LoadPre 0x1164df (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1164df + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1164df 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 271) (.out 0x1164e7 (mulR64Effect 0x1164e7 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[173, 269]
    (.letOp (n := 272) (.out 0x1164e7 (mulR64Effect 0x1164e7 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[173, 269]
    (.letOp (n := 273) (.exec 0x1164e7 (fun s => s.RIP = 0x1164e7) (mulR64Effect 0x1164e7 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[173, 269]
    (.letOp (n := 274) (.out 0x1164ea (movR64R64Effect 0x1164ea 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[271]
    (.letOp (n := 275) (.exec 0x1164ea (fun s => s.RIP = 0x1164ea) (movR64R64Effect 0x1164ea 14 0) (Reg.operands [.gpr 0] [])) #v[271]
    (.letOp (n := 276) (.out 0x1164ed (movR64R64Effect 0x1164ed 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[272]
    (.letOp (n := 277) (.exec 0x1164ed (fun s => s.RIP = 0x1164ed) (movR64R64Effect 0x1164ed 15 2) (Reg.operands [.gpr 2] [])) #v[272]
    (.letOp (n := 278) (.out 0x1164f0 (andR32Imm8Effect 0x1164f0 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[247]
    (.letOp (n := 279) (.exec 0x1164f0 (fun s => s.RIP = 0x1164f0) (andR32Imm8Effect 0x1164f0 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[247]
    (.letOp (n := 280) (.out 0x1164f4 (movR64M64Effect 0x1164f4 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 281) (.exec 0x1164f4 (LoadPre 0x1164f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1164f4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1164f4 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 282) (.out 0x1164fc (movR64M64Effect 0x1164fc 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 283) (.exec 0x1164fc (LoadPre 0x1164fc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1164fc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1164fc 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 284) (.out 0x116504 (mulR64Effect 0x116504 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[282, 280]
    (.letOp (n := 285) (.out 0x116504 (mulR64Effect 0x116504 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[282, 280]
    (.letOp (n := 286) (.exec 0x116504 (fun s => s.RIP = 0x116504) (mulR64Effect 0x116504 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[282, 280]
    (.letOp (n := 287) (.out 0x116507 (movR64R64Effect 0x116507 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[285]
    (.letOp (n := 288) (.exec 0x116507 (fun s => s.RIP = 0x116507) (movR64R64Effect 0x116507 10 2) (Reg.operands [.gpr 2] [])) #v[285]
    (.letOp (n := 289) (.out 0x11650a (movR64R64Effect 0x11650a 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[284]
    (.letOp (n := 290) (.exec 0x11650a (fun s => s.RIP = 0x11650a) (movR64R64Effect 0x11650a 12 0) (Reg.operands [.gpr 0] [])) #v[284]
    (.letOp (n := 291) (.out 0x11650d (movR64M64Effect 0x11650d 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 292) (.exec 0x11650d (LoadPre 0x11650d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11650d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11650d 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 293) (.out 0x116515 (movR64R64Effect 0x116515 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[291]
    (.letOp (n := 294) (.exec 0x116515 (fun s => s.RIP = 0x116515) (movR64R64Effect 0x116515 0 1) (Reg.operands [.gpr 1] [])) #v[291]
    (.letOp (n := 295) (.out 0x116518 (mulM64Effect 0x116518 8 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[293, 4]
    (.letOp (n := 296) (.out 0x116518 (mulM64Effect 0x116518 8 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[293, 4]
    (.letOp (n := 297) (.exec 0x116518 (LoadPre 0x116518 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x116518 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x116518 8 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[293, 4]
    (.letOp (n := 298) (.out 0x116520 (addR64R64Effect 0x116520 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[295, 289]
    (.letOp (n := 299) (.out 0x116520 (addR64R64Effect 0x116520 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[295, 289]
    (.letOp (n := 300) (.exec 0x116520 (fun s => s.RIP = 0x116520) (addR64R64Effect 0x116520 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[295, 289]
    (.letOp (n := 301) (.out 0x116523 (atFlags StatusFlags.CF (adcR64R64Effect 0x116523 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[287, 296, 299]
    (.letOp (n := 302) (.exec 0x116523 (fun s => s.RIP = 0x116523) (atFlags StatusFlags.CF (adcR64R64Effect 0x116523 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[287, 296, 299]
    (.letOp (n := 303) (.out 0x116526 (addR64R64Effect 0x116526 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[298, 274]
    (.letOp (n := 304) (.out 0x116526 (addR64R64Effect 0x116526 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[298, 274]
    (.letOp (n := 305) (.exec 0x116526 (fun s => s.RIP = 0x116526) (addR64R64Effect 0x116526 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[298, 274]
    (b_l116316_6))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116316_5 : List UInt8 :=
  [0x48, 0x89, 0xE8, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC3, 0x48, 0x8B, 0x84, 0x24,
    0xA8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xC6, 0x49, 0x89, 0xD7, 0x41, 0x83, 0xE5,
    0x0F, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xBC, 0x24, 0x88, 0x00, 0x00,
    0x00, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00,
    0x00, 0x00, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0xA4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xE0,
    0x49, 0x11, 0xD2, 0x4C, 0x01, 0xF0] ++ bytes_l116316_6

theorem code_l116316_5 : ∀ x ∈ codeRange 0x1164d3 bytes_l116316_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x164d3 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116316_6

def b_l116316_4 : Block Op Label signature Reg.count 216 :=
  .letOp (n := 216) (.out 0x116477 (atFlags StatusFlags.CF (adcR64R64Effect 0x116477 8 15)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[187, 178, 214]
    (.letOp (n := 217) (.exec 0x116477 (fun s => s.RIP = 0x116477) (atFlags StatusFlags.CF (adcR64R64Effect 0x116477 8 15)) (Reg.operands [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[187, 178, 214]
    (.letOp (n := 218) (.out 0x11647a (addR64R64Effect 0x11647a 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[213, 196]
    (.letOp (n := 219) (.out 0x11647a (addR64R64Effect 0x11647a 6 5) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 5] []) (.flag .CF)) #v[213, 196]
    (.letOp (n := 220) (.exec 0x11647a (fun s => s.RIP = 0x11647a) (addR64R64Effect 0x11647a 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[213, 196]
    (.letOp (n := 221) (.out 0x11647d (atFlags StatusFlags.CF (adcR64R64Effect 0x11647d 8 11)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[216, 198, 219]
    (.letOp (n := 222) (.exec 0x11647d (fun s => s.RIP = 0x11647d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11647d 8 11)) (Reg.operands [.gpr 8, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[216, 198, 219]
    (.letOp (n := 223) (.out 0x116480 (addR64M64Effect 0x116480 6 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[218, 4]
    (.letOp (n := 224) (.out 0x116480 (addR64M64Effect 0x116480 6 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[218, 4]
    (.letOp (n := 225) (.exec 0x116480 (LoadPre 0x116480 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x116480 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x116480 6 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[218, 4]
    (.letOp (n := 226) (.out 0x116488 (atFlags StatusFlags.CF (adcR64M64Effect 0x116488 8 (.sib 4 none 0 (.d32 0x80)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[221, 4, 224]
    (.letOp (n := 227) (.exec 0x116488 (LoadPre 0x116488 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x116488 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x116488 8 (.sib 4 none 0 (.d32 0x80)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[221, 4, 224]
    (.letOp (n := 228) (.out 0x116490 (addR64M64Effect 0x116490 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[223, 4]
    (.letOp (n := 229) (.out 0x116490 (addR64M64Effect 0x116490 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[223, 4]
    (.letOp (n := 230) (.exec 0x116490 (LoadPre 0x116490 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x116490 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x116490 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[223, 4]
    (.letOp (n := 231) (.out 0x116495 (atFlags StatusFlags.CF (adcR64M64Effect 0x116495 8 (.sib 4 none 0 (.d8 0x78)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[226, 4, 229]
    (.letOp (n := 232) (.exec 0x116495 (LoadPre 0x116495 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x116495 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x116495 8 (.sib 4 none 0 (.d8 0x78)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[226, 4, 229]
    (.letOp (n := 233) (.out 0x11649a (addR64R64Effect 0x11649a 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[228, 208]
    (.letOp (n := 234) (.out 0x11649a (addR64R64Effect 0x11649a 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[228, 208]
    (.letOp (n := 235) (.exec 0x11649a (fun s => s.RIP = 0x11649a) (addR64R64Effect 0x11649a 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[228, 208]
    (.letOp (n := 236) (.out 0x11649d (atFlags StatusFlags.CF (adcR64R64Effect 0x11649d 8 9)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[231, 211, 234]
    (.letOp (n := 237) (.exec 0x11649d (fun s => s.RIP = 0x11649d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11649d 8 9)) (Reg.operands [.gpr 8, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[231, 211, 234]
    (.letOp (n := 238) (.out 0x1164a0 (addR64R64Effect 0x1164a0 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[233, 151]
    (.letOp (n := 239) (.out 0x1164a0 (addR64R64Effect 0x1164a0 6 7) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 7] []) (.flag .CF)) #v[233, 151]
    (.letOp (n := 240) (.exec 0x1164a0 (fun s => s.RIP = 0x1164a0) (addR64R64Effect 0x1164a0 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[233, 151]
    (.letOp (n := 241) (.out 0x1164a3 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1164a3 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[236, 239]
    (.letOp (n := 242) (.exec 0x1164a3 (fun s => s.RIP = 0x1164a3) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1164a3 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[236, 239]
    (.letOp (n := 243) (.out 0x1164a7 (shldR64R64Effect 0x1164a7 5 8 6 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[241, 238]
    (.letOp (n := 244) (.exec 0x1164a7 (fun s => s.RIP = 0x1164a7) (shldR64R64Effect 0x1164a7 5 8 6 12) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[241, 238]
    (.letOp (n := 245) (.out 0x1164ac (movR64R64Effect 0x1164ac 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[238]
    (.letOp (n := 246) (.exec 0x1164ac (fun s => s.RIP = 0x1164ac) (movR64R64Effect 0x1164ac 13 6) (Reg.operands [.gpr 6] [])) #v[238]
    (.letOp (n := 247) (.out 0x1164af (shrR64Effect 0x1164af 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[245]
    (.letOp (n := 248) (.exec 0x1164af (fun s => s.RIP = 0x1164af) (shrR64Effect 0x1164af 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[245]
    (.letOp (n := 249) (.out 0x1164b3 (movR64M64Effect 0x1164b3 9 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 250) (.exec 0x1164b3 (LoadPre 0x1164b3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1164b3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1164b3 9 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 251) (.out 0x1164bb (movR64R64Effect 0x1164bb 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[249]
    (.letOp (n := 252) (.exec 0x1164bb (fun s => s.RIP = 0x1164bb) (movR64R64Effect 0x1164bb 0 9) (Reg.operands [.gpr 9] [])) #v[249]
    (.letOp (n := 253) (.out 0x1164be (mulR64Effect 0x1164be 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[155, 251]
    (.letOp (n := 254) (.out 0x1164be (mulR64Effect 0x1164be 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[155, 251]
    (.letOp (n := 255) (.exec 0x1164be (fun s => s.RIP = 0x1164be) (mulR64Effect 0x1164be 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[155, 251]
    (.letOp (n := 256) (.exec 0x1164c1 (StorePre 0x1164c1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1164c1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1164c1 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[254, 4]
    (.letOp (n := 257) (.exec 0x1164c6 (StorePre 0x1164c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1164c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1164c6 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[253, 4]
    (.letOp (n := 258) (.out 0x1164cb (movR64M64Effect 0x1164cb 5 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 259) (.exec 0x1164cb (LoadPre 0x1164cb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1164cb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1164cb 5 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l116316_5))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116316_4 : List UInt8 :=
  [0x4D, 0x11, 0xF8, 0x48, 0x01, 0xEE, 0x4D, 0x11, 0xD8, 0x48, 0x03, 0xB4, 0x24, 0x08, 0x01, 0x00,
    0x00, 0x4C, 0x13, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x03, 0x74, 0x24, 0x60, 0x4C, 0x13,
    0x44, 0x24, 0x78, 0x48, 0x01, 0xC6, 0x4D, 0x11, 0xC8, 0x48, 0x01, 0xFE, 0x49, 0x83, 0xD0, 0x00,
    0x49, 0x0F, 0xA4, 0xF0, 0x0C, 0x49, 0x89, 0xF5, 0x49, 0xC1, 0xED, 0x30, 0x4C, 0x8B, 0x8C, 0x24,
    0xA0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xC8, 0x49, 0xF7, 0xE4, 0x48, 0x89, 0x54, 0x24, 0x78, 0x48,
    0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00] ++ bytes_l116316_5

theorem code_l116316_4 : ∀ x ∈ codeRange 0x116477 bytes_l116316_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16477 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116316_5

def b_l116316_3 : Block Op Label signature Reg.count 171 :=
  .letOp (n := 171) (.out 0x11642b (movR64R64Effect 0x11642b 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 172) (.exec 0x11642b (fun s => s.RIP = 0x11642b) (movR64R64Effect 0x11642b 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 173) (.out 0x11642e (movR64M64Effect 0x11642e 14 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 174) (.exec 0x11642e (LoadPre 0x11642e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11642e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11642e 14 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 175) (.out 0x116433 (mulR64Effect 0x116433 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[173, 171]
    (.letOp (n := 176) (.out 0x116433 (mulR64Effect 0x116433 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[173, 171]
    (.letOp (n := 177) (.exec 0x116433 (fun s => s.RIP = 0x116433) (mulR64Effect 0x116433 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[173, 171]
    (.letOp (n := 178) (.out 0x116436 (movR64R64Effect 0x116436 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[176]
    (.letOp (n := 179) (.exec 0x116436 (fun s => s.RIP = 0x116436) (movR64R64Effect 0x116436 15 2) (Reg.operands [.gpr 2] [])) #v[176]
    (.letOp (n := 180) (.out 0x116439 (movR64R64Effect 0x116439 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[175]
    (.letOp (n := 181) (.exec 0x116439 (fun s => s.RIP = 0x116439) (movR64R64Effect 0x116439 13 0) (Reg.operands [.gpr 0] [])) #v[175]
    (.letOp (n := 182) (.out 0x11643c (movR64R64Effect 0x11643c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[84]
    (.letOp (n := 183) (.exec 0x11643c (fun s => s.RIP = 0x11643c) (movR64R64Effect 0x11643c 0 6) (Reg.operands [.gpr 6] [])) #v[84]
    (.letOp (n := 184) (.out 0x11643f (mulM64Effect 0x11643f 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[182, 4]
    (.letOp (n := 185) (.out 0x11643f (mulM64Effect 0x11643f 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[182, 4]
    (.letOp (n := 186) (.exec 0x11643f (LoadPre 0x11643f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11643f + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11643f 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[182, 4]
    (.letOp (n := 187) (.out 0x116447 (movR64R64Effect 0x116447 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[185]
    (.letOp (n := 188) (.exec 0x116447 (fun s => s.RIP = 0x116447) (movR64R64Effect 0x116447 8 2) (Reg.operands [.gpr 2] [])) #v[185]
    (.letOp (n := 189) (.out 0x11644a (movR64R64Effect 0x11644a 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[184]
    (.letOp (n := 190) (.exec 0x11644a (fun s => s.RIP = 0x11644a) (movR64R64Effect 0x11644a 6 0) (Reg.operands [.gpr 0] [])) #v[184]
    (.letOp (n := 191) (.out 0x11644d (movR64R64Effect 0x11644d 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[96]
    (.letOp (n := 192) (.exec 0x11644d (fun s => s.RIP = 0x11644d) (movR64R64Effect 0x11644d 0 5) (Reg.operands [.gpr 5] [])) #v[96]
    (.letOp (n := 193) (.out 0x116450 (mulR64Effect 0x116450 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[53, 191]
    (.letOp (n := 194) (.out 0x116450 (mulR64Effect 0x116450 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[53, 191]
    (.letOp (n := 195) (.exec 0x116450 (fun s => s.RIP = 0x116450) (mulR64Effect 0x116450 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[53, 191]
    (.letOp (n := 196) (.out 0x116453 (movR64R64Effect 0x116453 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[193]
    (.letOp (n := 197) (.exec 0x116453 (fun s => s.RIP = 0x116453) (movR64R64Effect 0x116453 5 0) (Reg.operands [.gpr 0] [])) #v[193]
    (.letOp (n := 198) (.out 0x116456 (movR64R64Effect 0x116456 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[194]
    (.letOp (n := 199) (.exec 0x116456 (fun s => s.RIP = 0x116456) (movR64R64Effect 0x116456 11 2) (Reg.operands [.gpr 2] [])) #v[194]
    (.letOp (n := 200) (.out 0x116459 (shrR64Effect 0x116459 4 9 52) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[115]
    (.letOp (n := 201) (.exec 0x116459 (fun s => s.RIP = 0x116459) (shrR64Effect 0x116459 4 9 52) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 202) (.out 0x11645d (movR64Imm64Effect 0x11645d 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 203) (.exec 0x11645d (fun s => s.RIP = 0x11645d) (movR64Imm64Effect 0x11645d 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 204) (.out 0x116467 (imulR64R64Effect 0x116467 4 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[200, 202]
    (.letOp (n := 205) (.exec 0x116467 (fun s => s.RIP = 0x116467) (imulR64R64Effect 0x116467 4 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[200, 202]
    (.letOp (n := 206) (.out 0x11646b (movR64R64Effect 0x11646b 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[149]
    (.letOp (n := 207) (.exec 0x11646b (fun s => s.RIP = 0x11646b) (movR64R64Effect 0x11646b 0 10) (Reg.operands [.gpr 10] [])) #v[149]
    (.letOp (n := 208) (.out 0x11646e (mulR64Effect 0x11646e 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[202, 206]
    (.letOp (n := 209) (.out 0x11646e (mulR64Effect 0x11646e 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[202, 206]
    (.letOp (n := 210) (.exec 0x11646e (fun s => s.RIP = 0x11646e) (mulR64Effect 0x11646e 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[202, 206]
    (.letOp (n := 211) (.out 0x116471 (addR64R64Effect 0x116471 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[204, 209]
    (.letOp (n := 212) (.exec 0x116471 (fun s => s.RIP = 0x116471) (addR64R64Effect 0x116471 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[204, 209]
    (.letOp (n := 213) (.out 0x116474 (addR64R64Effect 0x116474 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[189, 180]
    (.letOp (n := 214) (.out 0x116474 (addR64R64Effect 0x116474 6 13) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 13] []) (.flag .CF)) #v[189, 180]
    (.letOp (n := 215) (.exec 0x116474 (fun s => s.RIP = 0x116474) (addR64R64Effect 0x116474 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[189, 180]
    (b_l116316_4)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116316_3 : List UInt8 :=
  [0x4C, 0x89, 0xF8, 0x4C, 0x8B, 0x74, 0x24, 0x70, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD7, 0x49, 0x89,
    0xC5, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0xA4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD0, 0x48,
    0x89, 0xC6, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE3, 0x48, 0x89, 0xC5, 0x49, 0x89, 0xD3, 0x49, 0xC1,
    0xE9, 0x34, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xC9,
    0x4C, 0x89, 0xD0, 0x48, 0xF7, 0xE1, 0x49, 0x01, 0xD1, 0x4C, 0x01, 0xEE] ++ bytes_l116316_4

theorem code_l116316_3 : ∀ x ∈ codeRange 0x11642b bytes_l116316_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1642b 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116316_4

def b_l116316_2 : Block Op Label signature Reg.count 131 :=
  .letOp (n := 131) (.out 0x1163ce (atFlags StatusFlags.CF (adcR64R64Effect 0x1163ce 7 14)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[103, 92, 129]
    (.letOp (n := 132) (.exec 0x1163ce (fun s => s.RIP = 0x1163ce) (atFlags StatusFlags.CF (adcR64R64Effect 0x1163ce 7 14)) (Reg.operands [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[103, 92, 129]
    (.letOp (n := 133) (.out 0x1163d1 (addR64R64Effect 0x1163d1 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[128, 77]
    (.letOp (n := 134) (.out 0x1163d1 (addR64R64Effect 0x1163d1 13 3) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 3] []) (.flag .CF)) #v[128, 77]
    (.letOp (n := 135) (.exec 0x1163d1 (fun s => s.RIP = 0x1163d1) (addR64R64Effect 0x1163d1 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[128, 77]
    (.letOp (n := 136) (.out 0x1163d4 (atFlags StatusFlags.CF (adcR64R64Effect 0x1163d4 7 12)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[131, 79, 134]
    (.letOp (n := 137) (.exec 0x1163d4 (fun s => s.RIP = 0x1163d4) (atFlags StatusFlags.CF (adcR64R64Effect 0x1163d4 7 12)) (Reg.operands [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[131, 79, 134]
    (.letOp (n := 138) (.out 0x1163d7 (addR64M64Effect 0x1163d7 13 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[133, 4]
    (.letOp (n := 139) (.out 0x1163d7 (addR64M64Effect 0x1163d7 13 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[133, 4]
    (.letOp (n := 140) (.exec 0x1163d7 (LoadPre 0x1163d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1163d7 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1163d7 13 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[133, 4]
    (.letOp (n := 141) (.out 0x1163dc (atFlags StatusFlags.CF (adcR64M64Effect 0x1163dc 7 (.sib 4 none 0 (.d8 0x58)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[136, 4, 139]
    (.letOp (n := 142) (.exec 0x1163dc (LoadPre 0x1163dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1163dc + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1163dc 7 (.sib 4 none 0 (.d8 0x58)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[136, 4, 139]
    (.letOp (n := 143) (.out 0x1163e1 (addR64R64Effect 0x1163e1 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[138, 125]
    (.letOp (n := 144) (.out 0x1163e1 (addR64R64Effect 0x1163e1 13 0) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 0] []) (.flag .CF)) #v[138, 125]
    (.letOp (n := 145) (.exec 0x1163e1 (fun s => s.RIP = 0x1163e1) (addR64R64Effect 0x1163e1 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[138, 125]
    (.letOp (n := 146) (.exec 0x1163e4 (StorePre 0x1163e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1163e4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1163e4 13 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[143, 4]
    (.letOp (n := 147) (.out 0x1163e9 (atFlags StatusFlags.CF (adcR64R64Effect 0x1163e9 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[141, 126, 144]
    (.letOp (n := 148) (.exec 0x1163e9 (fun s => s.RIP = 0x1163e9) (atFlags StatusFlags.CF (adcR64R64Effect 0x1163e9 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[141, 126, 144]
    (.letOp (n := 149) (.out 0x1163ec (shrdR64R64Effect 0x1163ec 5 10 9 52) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[117, 115]
    (.letOp (n := 150) (.exec 0x1163ec (fun s => s.RIP = 0x1163ec) (shrdR64R64Effect 0x1163ec 5 10 9 52) (Reg.operands [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[117, 115]
    (.letOp (n := 151) (.out 0x1163f1 (shldR64R64Effect 0x1163f1 5 7 13 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[147, 143]
    (.letOp (n := 152) (.exec 0x1163f1 (fun s => s.RIP = 0x1163f1) (shldR64R64Effect 0x1163f1 5 7 13 12) (Reg.operands [.gpr 7, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[147, 143]
    (.letOp (n := 153) (.out 0x1163f6 (movR64R64Effect 0x1163f6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[107]
    (.letOp (n := 154) (.exec 0x1163f6 (fun s => s.RIP = 0x1163f6) (movR64R64Effect 0x1163f6 0 1) (Reg.operands [.gpr 1] [])) #v[107]
    (.letOp (n := 155) (.out 0x1163f9 (movR64M64Effect 0x1163f9 12 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 156) (.exec 0x1163f9 (LoadPre 0x1163f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1163f9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1163f9 12 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 157) (.out 0x1163fe (mulR64Effect 0x1163fe 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[155, 153]
    (.letOp (n := 158) (.out 0x1163fe (mulR64Effect 0x1163fe 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[155, 153]
    (.letOp (n := 159) (.exec 0x1163fe (fun s => s.RIP = 0x1163fe) (mulR64Effect 0x1163fe 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[155, 153]
    (.letOp (n := 160) (.exec 0x116401 (StorePre 0x116401 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x116401 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116401 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[158, 4]
    (.letOp (n := 161) (.exec 0x116406 (StorePre 0x116406 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x116406 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116406 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[157, 4]
    (.letOp (n := 162) (.out 0x11640b (movR64M64Effect 0x11640b 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 163) (.exec 0x11640b (LoadPre 0x11640b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11640b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11640b 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 164) (.out 0x116413 (movR64M64Effect 0x116413 3 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 165) (.exec 0x116413 (LoadPre 0x116413 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116413 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116413 3 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 166) (.out 0x116418 (mulR64Effect 0x116418 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[164, 162]
    (.letOp (n := 167) (.out 0x116418 (mulR64Effect 0x116418 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[164, 162]
    (.letOp (n := 168) (.exec 0x116418 (fun s => s.RIP = 0x116418) (mulR64Effect 0x116418 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[164, 162]
    (.letOp (n := 169) (.exec 0x11641b (StorePre 0x11641b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11641b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11641b 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[167, 4]
    (.letOp (n := 170) (.exec 0x116423 (StorePre 0x116423 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x116423 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x116423 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[166, 4]
    (b_l116316_3))))))))))))))))))))))))))))))))))))))))

def bytes_l116316_2 : List UInt8 :=
  [0x4C, 0x11, 0xF7, 0x49, 0x01, 0xDD, 0x4C, 0x11, 0xE7, 0x4C, 0x03, 0x6C, 0x24, 0x78, 0x48, 0x13,
    0x7C, 0x24, 0x58, 0x49, 0x01, 0xC5, 0x4C, 0x89, 0x6C, 0x24, 0x58, 0x48, 0x11, 0xD7, 0x4D, 0x0F,
    0xAC, 0xCA, 0x34, 0x4C, 0x0F, 0xA4, 0xEF, 0x0C, 0x48, 0x89, 0xC8, 0x4C, 0x8B, 0x64, 0x24, 0x50,
    0x49, 0xF7, 0xE4, 0x48, 0x89, 0x54, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x84,
    0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x5C, 0x24, 0x68, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0x94,
    0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] ++ bytes_l116316_3

theorem code_l116316_2 : ∀ x ∈ codeRange 0x1163ce bytes_l116316_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x163ce 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116316_3

def b_l116316_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.out 0x116375 (movR64R64Effect 0x116375 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 88) (.exec 0x116375 (fun s => s.RIP = 0x116375) (movR64R64Effect 0x116375 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 89) (.out 0x116378 (mulR64Effect 0x116378 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[81, 87]
    (.letOp (n := 90) (.out 0x116378 (mulR64Effect 0x116378 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[81, 87]
    (.letOp (n := 91) (.exec 0x116378 (fun s => s.RIP = 0x116378) (mulR64Effect 0x116378 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[81, 87]
    (.letOp (n := 92) (.out 0x11637b (movR64R64Effect 0x11637b 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[90]
    (.letOp (n := 93) (.exec 0x11637b (fun s => s.RIP = 0x11637b) (movR64R64Effect 0x11637b 14 2) (Reg.operands [.gpr 2] [])) #v[90]
    (.letOp (n := 94) (.out 0x11637e (movR64R64Effect 0x11637e 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[89]
    (.letOp (n := 95) (.exec 0x11637e (fun s => s.RIP = 0x11637e) (movR64R64Effect 0x11637e 8 0) (Reg.operands [.gpr 0] [])) #v[89]
    (.letOp (n := 96) (.out 0x116381 (movR64M64Effect 0x116381 5 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 97) (.exec 0x116381 (LoadPre 0x116381 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x116381 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116381 5 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 98) (.out 0x116389 (movR64R64Effect 0x116389 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[96]
    (.letOp (n := 99) (.exec 0x116389 (fun s => s.RIP = 0x116389) (movR64R64Effect 0x116389 0 5) (Reg.operands [.gpr 5] [])) #v[96]
    (.letOp (n := 100) (.out 0x11638c (mulR64Effect 0x11638c 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[55, 98]
    (.letOp (n := 101) (.out 0x11638c (mulR64Effect 0x11638c 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[55, 98]
    (.letOp (n := 102) (.exec 0x11638c (fun s => s.RIP = 0x11638c) (mulR64Effect 0x11638c 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[55, 98]
    (.letOp (n := 103) (.out 0x11638f (movR64R64Effect 0x11638f 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[101]
    (.letOp (n := 104) (.exec 0x11638f (fun s => s.RIP = 0x11638f) (movR64R64Effect 0x11638f 7 2) (Reg.operands [.gpr 2] [])) #v[101]
    (.letOp (n := 105) (.out 0x116392 (movR64R64Effect 0x116392 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[100]
    (.letOp (n := 106) (.exec 0x116392 (fun s => s.RIP = 0x116392) (movR64R64Effect 0x116392 13 0) (Reg.operands [.gpr 0] [])) #v[100]
    (.letOp (n := 107) (.out 0x116395 (movR64M64Effect 0x116395 1 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 108) (.exec 0x116395 (LoadPre 0x116395 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x116395 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116395 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 109) (.out 0x11639d (movR64R64Effect 0x11639d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[107]
    (.letOp (n := 110) (.exec 0x11639d (fun s => s.RIP = 0x11639d) (movR64R64Effect 0x11639d 0 1) (Reg.operands [.gpr 1] [])) #v[107]
    (.letOp (n := 111) (.out 0x1163a0 (mulR64Effect 0x1163a0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[53, 109]
    (.letOp (n := 112) (.out 0x1163a0 (mulR64Effect 0x1163a0 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[53, 109]
    (.letOp (n := 113) (.exec 0x1163a0 (fun s => s.RIP = 0x1163a0) (mulR64Effect 0x1163a0 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[53, 109]
    (.letOp (n := 114) (.exec 0x1163a3 (StorePre 0x1163a3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1163a3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1163a3 11 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 115) (.out 0x1163ab (movR64R64Effect 0x1163ab 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[112]
    (.letOp (n := 116) (.exec 0x1163ab (fun s => s.RIP = 0x1163ab) (movR64R64Effect 0x1163ab 9 2) (Reg.operands [.gpr 2] [])) #v[112]
    (.letOp (n := 117) (.out 0x1163ae (movR64R64Effect 0x1163ae 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[111]
    (.letOp (n := 118) (.exec 0x1163ae (fun s => s.RIP = 0x1163ae) (movR64R64Effect 0x1163ae 10 0) (Reg.operands [.gpr 0] [])) #v[111]
    (.letOp (n := 119) (.out 0x1163b1 (movR64Imm64Effect 0x1163b1 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 120) (.exec 0x1163b1 (fun s => s.RIP = 0x1163b1) (movR64Imm64Effect 0x1163b1 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 121) (.out 0x1163bb (andR64R64Effect 0x1163bb 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[111, 119]
    (.letOp (n := 122) (.exec 0x1163bb (fun s => s.RIP = 0x1163bb) (andR64R64Effect 0x1163bb 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[111, 119]
    (.letOp (n := 123) (.out 0x1163be (movR64Imm64Effect 0x1163be 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 124) (.exec 0x1163be (fun s => s.RIP = 0x1163be) (movR64Imm64Effect 0x1163be 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 125) (.out 0x1163c8 (mulR64Effect 0x1163c8 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[123, 121]
    (.letOp (n := 126) (.out 0x1163c8 (mulR64Effect 0x1163c8 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[123, 121]
    (.letOp (n := 127) (.exec 0x1163c8 (fun s => s.RIP = 0x1163c8) (mulR64Effect 0x1163c8 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[123, 121]
    (.letOp (n := 128) (.out 0x1163cb (addR64R64Effect 0x1163cb 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[105, 94]
    (.letOp (n := 129) (.out 0x1163cb (addR64R64Effect 0x1163cb 13 8) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 8] []) (.flag .CF)) #v[105, 94]
    (.letOp (n := 130) (.exec 0x1163cb (fun s => s.RIP = 0x1163cb) (addR64R64Effect 0x1163cb 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[105, 94]
    (b_l116316_2))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116316_1 : List UInt8 :=
  [0x4C, 0x89, 0xE8, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC0, 0x48, 0x8B, 0xAC, 0x24,
    0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC5,
    0x48, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE3, 0x4C, 0x89,
    0x9C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC2, 0x48, 0xBA, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4D, 0x01, 0xC5] ++ bytes_l116316_2

theorem code_l116316_1 : ∀ x ∈ codeRange 0x116375 bytes_l116316_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16375 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116316_2

def b_l116316 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x116316 (movR64M64Effect 0x116316 11 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 54) (.exec 0x116316 (LoadPre 0x116316 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x116316 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116316 11 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11631b (movR64M64Effect 0x11631b 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x11631b (LoadPre 0x11631b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11631b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11631b 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x116320 (StorePre 0x116320 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x116320 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x116320 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x116328 (movR64M64Effect 0x116328 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x116328 (LoadPre 0x116328 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x116328 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116328 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x11632d (StorePre 0x11632d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11632d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11632d 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x116332 (movR64M64Effect 0x116332 6 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x116332 (LoadPre 0x116332 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x116332 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116332 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x116337 (StorePre 0x116337 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116337 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116337 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x11633c (movR64R64Effect 0x11633c 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 65) (.exec 0x11633c (fun s => s.RIP = 0x11633c) (movR64R64Effect 0x11633c 0 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 66) (.out 0x11633f (mulR64Effect 0x11633f 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[58, 64]
    (.letOp (n := 67) (.out 0x11633f (mulR64Effect 0x11633f 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[58, 64]
    (.letOp (n := 68) (.exec 0x11633f (fun s => s.RIP = 0x11633f) (mulR64Effect 0x11633f 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[58, 64]
    (.letOp (n := 69) (.exec 0x116342 (StorePre 0x116342 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x116342 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116342 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.exec 0x116347 (StorePre 0x116347 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x116347 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116347 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 71) (.exec 0x11634c (StorePre 0x11634c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11634c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11634c 15 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 72) (.out 0x116354 (movR64R64Effect 0x116354 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 73) (.exec 0x116354 (fun s => s.RIP = 0x116354) (movR64R64Effect 0x116354 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 74) (.out 0x116357 (mulR64Effect 0x116357 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[61, 72]
    (.letOp (n := 75) (.out 0x116357 (mulR64Effect 0x116357 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[61, 72]
    (.letOp (n := 76) (.exec 0x116357 (fun s => s.RIP = 0x116357) (mulR64Effect 0x116357 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[61, 72]
    (.letOp (n := 77) (.out 0x11635a (movR64R64Effect 0x11635a 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[74]
    (.letOp (n := 78) (.exec 0x11635a (fun s => s.RIP = 0x11635a) (movR64R64Effect 0x11635a 3 0) (Reg.operands [.gpr 0] [])) #v[74]
    (.letOp (n := 79) (.out 0x11635d (movR64R64Effect 0x11635d 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[75]
    (.letOp (n := 80) (.exec 0x11635d (fun s => s.RIP = 0x11635d) (movR64R64Effect 0x11635d 12 2) (Reg.operands [.gpr 2] [])) #v[75]
    (.letOp (n := 81) (.out 0x116360 (movR64M64Effect 0x116360 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 82) (.exec 0x116360 (LoadPre 0x116360 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x116360 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116360 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.exec 0x116365 (StorePre 0x116365 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x116365 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116365 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 84) (.out 0x11636a (movR64R64Effect 0x11636a 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 85) (.exec 0x11636a (fun s => s.RIP = 0x11636a) (movR64R64Effect 0x11636a 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 86) (.exec 0x11636d (StorePre 0x11636d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11636d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11636d 13 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (b_l116316_1))))))))))))))))))))))))))))))))))

def bytes_l116316 : List UInt8 :=
  [0x4C, 0x8B, 0x5C, 0x24, 0x48, 0x48, 0x8B, 0x7C, 0x24, 0x40, 0x48, 0x89, 0xBC, 0x24, 0x88, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x48, 0x89, 0x4C, 0x24, 0x50, 0x48, 0x8B, 0x74, 0x24,
    0x30, 0x48, 0x89, 0x74, 0x24, 0x68, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0x54, 0x24,
    0x58, 0x48, 0x89, 0x44, 0x24, 0x78, 0x4C, 0x89, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xF8, 0x48, 0xF7, 0xE6, 0x48, 0x89, 0xC3, 0x49, 0x89, 0xD4, 0x48, 0x8B, 0x4C, 0x24, 0x38, 0x48,
    0x89, 0x4C, 0x24, 0x70, 0x4C, 0x89, 0xEE, 0x4C, 0x89, 0xAC, 0x24, 0xB0, 0x00, 0x00, 0x00] ++ bytes_l116316_1

theorem code_l116316 : ∀ x ∈ codeRange 0x116316 bytes_l116316, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16316 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116316_1

@[cfg_block] def b_l116747 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x116747 (movR64M64Effect 0x116747 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x116747 (LoadPre 0x116747 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x116747 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116747 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11674c (StorePre 0x11674c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11674c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11674c 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x116751 (movR64M64Effect 0x116751 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x116751 (LoadPre 0x116751 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x116751 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116751 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x116756 (StorePre 0x116756 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x116756 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116756 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11675b (movR64M64Effect 0x11675b 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11675b (LoadPre 0x11675b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11675b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11675b 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x116760 (StorePre 0x116760 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x116760 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116760 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x116765 (movR64M64Effect 0x116765 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x116765 (LoadPre 0x116765 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x116765 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116765 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11676a (movR64M64Effect 0x11676a 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11676a (LoadPre 0x11676a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11676a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11676a 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11676f (StorePre 0x11676f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11676f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11676f 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x116774 (StorePre 0x116774 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x116774 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x116774 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x116778 (movR64R64Effect 0x116778 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x116778 (fun s => s.RIP = 0x116778) (movR64R64Effect 0x116778 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11677b (movR64R64Effect 0x11677b 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11677b (fun s => s.RIP = 0x11677b) (movR64R64Effect 0x11677b 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11677e (callEffect (fun _ => 0x1145f0) 0x116783) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11677e (PushPre 0x11677e 5) (callEffect (fun _ => 0x1145f0) 0x116783) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x116783⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l116783, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l116747 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x6D, 0xDE, 0xFF, 0xFF]

theorem code_l116747 : ∀ x ∈ codeRange 0x116747 bytes_l116747, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x16747 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116783 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x116783 (movR64M64Effect 0x116783 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x116783 (LoadPre 0x116783 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x116783 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116783 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x116788 (StorePre 0x116788 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x116788 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116788 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11678d (movR64M64Effect 0x11678d 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11678d (LoadPre 0x11678d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11678d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11678d 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x116792 (StorePre 0x116792 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x116792 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116792 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x116797 (movR64M64Effect 0x116797 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x116797 (LoadPre 0x116797 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x116797 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116797 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11679c (StorePre 0x11679c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11679c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11679c 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1167a1 (movR64M64Effect 0x1167a1 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1167a1 (LoadPre 0x1167a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1167a1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1167a1 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1167a6 (movR64M64Effect 0x1167a6 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1167a6 (LoadPre 0x1167a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1167a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1167a6 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1167ab (StorePre 0x1167ab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1167ab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1167ab 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1167b0 (StorePre 0x1167b0 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1167b0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1167b0 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1167b4 (movR64R64Effect 0x1167b4 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1167b4 (fun s => s.RIP = 0x1167b4) (movR64R64Effect 0x1167b4 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1167b7 (movR64R64Effect 0x1167b7 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1167b7 (fun s => s.RIP = 0x1167b7) (movR64R64Effect 0x1167b7 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1167ba (callEffect (fun _ => 0x1145f0) 0x1167bf) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1167ba (PushPre 0x1167ba 5) (callEffect (fun _ => 0x1145f0) 0x1167bf) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1167bf⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1167bf, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l116783 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x31, 0xDE, 0xFF, 0xFF]

theorem code_l116783 : ∀ x ∈ codeRange 0x116783 bytes_l116783, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x16783 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l1167bf_12 : Block Op Label signature Reg.count 569 :=
  .letOp (n := 569) (.out 0x116bca (movR64R64Effect 0x116bca 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 570) (.exec 0x116bca (fun s => s.RIP = 0x116bca) (movR64R64Effect 0x116bca 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 571) (.out 0x116bcd (movR64R64Effect 0x116bcd 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[567]
    (.letOp (n := 572) (.exec 0x116bcd (fun s => s.RIP = 0x116bcd) (movR64R64Effect 0x116bcd 7 3) (Reg.operands [.gpr 3] [])) #v[567]
    (.letOp (n := 573) (.out 0x116bd0 (movR64R64Effect 0x116bd0 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[569]
    (.letOp (n := 574) (.exec 0x116bd0 (fun s => s.RIP = 0x116bd0) (movR64R64Effect 0x116bd0 6 14) (Reg.operands [.gpr 14] [])) #v[569]
    (.letOp (n := 575) (.out 0x116bd3 (callEffect (fun _ => 0x1145f0) 0x116bd8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 576) (.exec 0x116bd3 (PushPre 0x116bd3 5) (callEffect (fun _ => 0x1145f0) 0x116bd8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 577) (.const ⟨64, 0x116bd8⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 558), (1, 498), (2, 550), (3, 567), (4, 575), (5, 487), (6, 573), (7, 571), (8, 462), (9, 563), (10, 534), (11, 496), (12, 473), (13, 459), (14, 569), (15, 392), (22, 22), (39, 39), (50, 50), (51, 51)] 578⟩ { target := .l116bd8, kept := #v[], arity := rfl, guard := some (Fin.last 577) }))))))))))

def bytes_l1167bf_12 : List UInt8 :=
  [0x49, 0x89, 0xE6, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x18, 0xDA, 0xFF, 0xFF]

theorem code_l1167bf_12 : ∀ x ∈ codeRange 0x116bca bytes_l1167bf_12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x16bca 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l1167bf_11 : Block Op Label signature Reg.count 531 :=
  .letOp (n := 531) (.out 0x116b71 (mulR64Effect 0x116b71 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[498, 529]
    (.letOp (n := 532) (.out 0x116b71 (mulR64Effect 0x116b71 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[498, 529]
    (.letOp (n := 533) (.exec 0x116b71 (fun s => s.RIP = 0x116b71) (mulR64Effect 0x116b71 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[498, 529]
    (.letOp (n := 534) (.out 0x116b74 (andR64R64Effect 0x116b74 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[519, 496]
    (.letOp (n := 535) (.exec 0x116b74 (fun s => s.RIP = 0x116b74) (andR64R64Effect 0x116b74 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[519, 496]
    (.letOp (n := 536) (.out 0x116b77 (movR64M64Effect 0x116b77 9 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 537) (.exec 0x116b77 (LoadPre 0x116b77 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x116b77 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116b77 9 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 538) (.out 0x116b7f (andR64R64Effect 0x116b7f 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[536, 496]
    (.letOp (n := 539) (.exec 0x116b7f (fun s => s.RIP = 0x116b7f) (andR64R64Effect 0x116b7f 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[536, 496]
    (.letOp (n := 540) (.out 0x116b82 (addR64R64Effect 0x116b82 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[538, 531]
    (.letOp (n := 541) (.out 0x116b82 (addR64R64Effect 0x116b82 9 0) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 0] []) (.flag .CF)) #v[538, 531]
    (.letOp (n := 542) (.exec 0x116b82 (fun s => s.RIP = 0x116b82) (addR64R64Effect 0x116b82 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[538, 531]
    (.letOp (n := 543) (.out 0x116b85 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116b85 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[532, 541]
    (.letOp (n := 544) (.exec 0x116b85 (fun s => s.RIP = 0x116b85) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116b85 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[532, 541]
    (.letOp (n := 545) (.out 0x116b89 (addR64R64Effect 0x116b89 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[540, 526]
    (.letOp (n := 546) (.out 0x116b89 (addR64R64Effect 0x116b89 9 3) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 3] []) (.flag .CF)) #v[540, 526]
    (.letOp (n := 547) (.exec 0x116b89 (fun s => s.RIP = 0x116b89) (addR64R64Effect 0x116b89 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[540, 526]
    (.letOp (n := 548) (.out 0x116b8c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116b8c 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[543, 546]
    (.letOp (n := 549) (.exec 0x116b8c (fun s => s.RIP = 0x116b8c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116b8c 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[543, 546]
    (.letOp (n := 550) (.out 0x116b90 (shldR64R64Effect 0x116b90 5 2 9 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[548, 545]
    (.letOp (n := 551) (.exec 0x116b90 (fun s => s.RIP = 0x116b90) (shldR64R64Effect 0x116b90 5 2 9 12) (Reg.operands [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[548, 545]
    (.letOp (n := 552) (.out 0x116b95 (movR64Imm64Effect 0x116b95 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 553) (.exec 0x116b95 (fun s => s.RIP = 0x116b95) (movR64Imm64Effect 0x116b95 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 554) (.out 0x116b9f (andR64R64Effect 0x116b9f 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[241, 552]
    (.letOp (n := 555) (.exec 0x116b9f (fun s => s.RIP = 0x116b9f) (andR64R64Effect 0x116b9f 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[241, 552]
    (.letOp (n := 556) (.out 0x116ba2 (addR64R64Effect 0x116ba2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[554, 550]
    (.letOp (n := 557) (.exec 0x116ba2 (fun s => s.RIP = 0x116ba2) (addR64R64Effect 0x116ba2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[554, 550]
    (.letOp (n := 558) (.out 0x116ba5 (movR64M64Effect 0x116ba5 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 559) (.exec 0x116ba5 (LoadPre 0x116ba5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x116ba5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116ba5 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 560) (.exec 0x116baa (StorePre 0x116baa 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x116baa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x116baa 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[558, 4]
    (.letOp (n := 561) (.exec 0x116bae (StorePre 0x116bae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x116bae + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116bae 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[462, 4]
    (.letOp (n := 562) (.exec 0x116bb3 (StorePre 0x116bb3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x116bb3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116bb3 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[534, 4]
    (.letOp (n := 563) (.out 0x116bb8 (andR64R64Effect 0x116bb8 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[545, 496]
    (.letOp (n := 564) (.exec 0x116bb8 (fun s => s.RIP = 0x116bb8) (andR64R64Effect 0x116bb8 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[545, 496]
    (.letOp (n := 565) (.exec 0x116bbb (StorePre 0x116bbb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x116bbb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116bbb 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[563, 4]
    (.letOp (n := 566) (.exec 0x116bc0 (StorePre 0x116bc0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x116bc0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116bc0 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[556, 4]
    (.letOp (n := 567) (.out 0x116bc5 (leaR64Effect 0x116bc5 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 568) (.exec 0x116bc5 (fun s => s.RIP = 0x116bc5) (leaR64Effect 0x116bc5 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1167bf_12))))))))))))))))))))))))))))))))))))))

def bytes_l1167bf_11 : List UInt8 :=
  [0x48, 0xF7, 0xE1, 0x4D, 0x21, 0xDA, 0x4C, 0x8B, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4D, 0x21,
    0xD9, 0x49, 0x01, 0xC1, 0x48, 0x83, 0xD2, 0x00, 0x49, 0x01, 0xD9, 0x48, 0x83, 0xD2, 0x00, 0x4C,
    0x0F, 0xA4, 0xCA, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x21,
    0xC6, 0x48, 0x01, 0xD6, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x89, 0x04, 0x24, 0x4C, 0x89, 0x44,
    0x24, 0x08, 0x4C, 0x89, 0x54, 0x24, 0x10, 0x4D, 0x21, 0xD9, 0x4C, 0x89, 0x4C, 0x24, 0x18, 0x48,
    0x89, 0x74, 0x24, 0x20, 0x48, 0x8D, 0x5C, 0x24, 0x28] ++ bytes_l1167bf_12

theorem code_l1167bf_11 : ∀ x ∈ codeRange 0x116b71 bytes_l1167bf_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16b71 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1167bf_12

def b_l1167bf_10 : Block Op Label signature Reg.count 487 :=
  .letOp (n := 487) (.out 0x116b1e (addR64R64Effect 0x116b1e 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[482, 412]
    (.letOp (n := 488) (.out 0x116b1e (addR64R64Effect 0x116b1e 5 11) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 11] []) (.flag .CF)) #v[482, 412]
    (.letOp (n := 489) (.exec 0x116b1e (fun s => s.RIP = 0x116b1e) (addR64R64Effect 0x116b1e 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[482, 412]
    (.letOp (n := 490) (.out 0x116b21 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116b21 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[485, 488]
    (.letOp (n := 491) (.exec 0x116b21 (fun s => s.RIP = 0x116b21) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116b21 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[485, 488]
    (.letOp (n := 492) (.out 0x116b25 (movR64R64Effect 0x116b25 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[487]
    (.letOp (n := 493) (.exec 0x116b25 (fun s => s.RIP = 0x116b25) (movR64R64Effect 0x116b25 0 5) (Reg.operands [.gpr 5] [])) #v[487]
    (.letOp (n := 494) (.out 0x116b28 (andR64R64Effect 0x116b28 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[492, 464]
    (.letOp (n := 495) (.exec 0x116b28 (fun s => s.RIP = 0x116b28) (andR64R64Effect 0x116b28 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[492, 464]
    (.letOp (n := 496) (.out 0x116b2b (movR64R64Effect 0x116b2b 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[464]
    (.letOp (n := 497) (.exec 0x116b2b (fun s => s.RIP = 0x116b2b) (movR64R64Effect 0x116b2b 11 1) (Reg.operands [.gpr 1] [])) #v[464]
    (.letOp (n := 498) (.out 0x116b2e (movR64Imm64Effect 0x116b2e 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 499) (.exec 0x116b2e (fun s => s.RIP = 0x116b2e) (movR64Imm64Effect 0x116b2e 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 500) (.out 0x116b38 (mulR64Effect 0x116b38 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[498, 494]
    (.letOp (n := 501) (.out 0x116b38 (mulR64Effect 0x116b38 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[498, 494]
    (.letOp (n := 502) (.exec 0x116b38 (fun s => s.RIP = 0x116b38) (mulR64Effect 0x116b38 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[498, 494]
    (.letOp (n := 503) (.out 0x116b3b (addR64M64Effect 0x116b3b 10 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[452, 4]
    (.letOp (n := 504) (.out 0x116b3b (addR64M64Effect 0x116b3b 10 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[452, 4]
    (.letOp (n := 505) (.exec 0x116b3b (LoadPre 0x116b3b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x116b3b + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x116b3b 10 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[452, 4]
    (.letOp (n := 506) (.out 0x116b40 (atFlags StatusFlags.CF (adcR64M64Effect 0x116b40 3 (.sib 4 none 0 (.d8 0x70)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[450, 4, 504]
    (.letOp (n := 507) (.exec 0x116b40 (LoadPre 0x116b40 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x116b40 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x116b40 3 (.sib 4 none 0 (.d8 0x70)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[450, 4, 504]
    (.letOp (n := 508) (.out 0x116b45 (addR64R64Effect 0x116b45 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[503, 459]
    (.letOp (n := 509) (.out 0x116b45 (addR64R64Effect 0x116b45 10 13) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 13] []) (.flag .CF)) #v[503, 459]
    (.letOp (n := 510) (.exec 0x116b45 (fun s => s.RIP = 0x116b45) (addR64R64Effect 0x116b45 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[503, 459]
    (.letOp (n := 511) (.out 0x116b48 (atFlags StatusFlags.CF (adcR64M64Effect 0x116b48 3 (.sib 4 none 0 (.d8 0x68)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[506, 4, 509]
    (.letOp (n := 512) (.exec 0x116b48 (LoadPre 0x116b48 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116b48 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x116b48 3 (.sib 4 none 0 (.d8 0x68)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[506, 4, 509]
    (.letOp (n := 513) (.out 0x116b4d (addR64R64Effect 0x116b4d 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[508, 500]
    (.letOp (n := 514) (.out 0x116b4d (addR64R64Effect 0x116b4d 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[508, 500]
    (.letOp (n := 515) (.exec 0x116b4d (fun s => s.RIP = 0x116b4d) (addR64R64Effect 0x116b4d 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[508, 500]
    (.letOp (n := 516) (.out 0x116b50 (atFlags StatusFlags.CF (adcR64R64Effect 0x116b50 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[511, 501, 514]
    (.letOp (n := 517) (.exec 0x116b50 (fun s => s.RIP = 0x116b50) (atFlags StatusFlags.CF (adcR64R64Effect 0x116b50 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[511, 501, 514]
    (.letOp (n := 518) (.exec 0x116b53 (StorePre 0x116b53 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x116b53 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116b53 15 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[392, 4]
    (.letOp (n := 519) (.out 0x116b58 (addR64R64Effect 0x116b58 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[513, 436]
    (.letOp (n := 520) (.out 0x116b58 (addR64R64Effect 0x116b58 10 9) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 9] []) (.flag .CF)) #v[513, 436]
    (.letOp (n := 521) (.exec 0x116b58 (fun s => s.RIP = 0x116b58) (addR64R64Effect 0x116b58 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[513, 436]
    (.letOp (n := 522) (.out 0x116b5b (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116b5b 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[516, 520]
    (.letOp (n := 523) (.exec 0x116b5b (fun s => s.RIP = 0x116b5b) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116b5b 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[516, 520]
    (.letOp (n := 524) (.out 0x116b5f (shldR64R64Effect 0x116b5f 5 14 5 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[490, 487]
    (.letOp (n := 525) (.exec 0x116b5f (fun s => s.RIP = 0x116b5f) (shldR64R64Effect 0x116b5f 5 14 5 12) (Reg.operands [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[490, 487]
    (.letOp (n := 526) (.out 0x116b64 (shldR64R64Effect 0x116b64 5 3 10 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[522, 519]
    (.letOp (n := 527) (.exec 0x116b64 (fun s => s.RIP = 0x116b64) (shldR64R64Effect 0x116b64 5 3 10 12) (Reg.operands [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[522, 519]
    (.letOp (n := 528) (.exec 0x116b69 (StorePre 0x116b69 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x116b69 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116b69 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[382, 4]
    (.letOp (n := 529) (.out 0x116b6e (movR64R64Effect 0x116b6e 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[524]
    (.letOp (n := 530) (.exec 0x116b6e (fun s => s.RIP = 0x116b6e) (movR64R64Effect 0x116b6e 0 14) (Reg.operands [.gpr 14] [])) #v[524]
    (b_l1167bf_11))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1167bf_10 : List UInt8 :=
  [0x4C, 0x01, 0xDD, 0x49, 0x83, 0xD6, 0x00, 0x48, 0x89, 0xE8, 0x48, 0x21, 0xC8, 0x49, 0x89, 0xCB,
    0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x4C, 0x03, 0x54,
    0x24, 0x60, 0x48, 0x13, 0x5C, 0x24, 0x70, 0x4D, 0x01, 0xEA, 0x48, 0x13, 0x5C, 0x24, 0x68, 0x49,
    0x01, 0xC2, 0x48, 0x11, 0xD3, 0x4C, 0x89, 0x7C, 0x24, 0x20, 0x4D, 0x01, 0xCA, 0x48, 0x83, 0xD3,
    0x00, 0x49, 0x0F, 0xA4, 0xEE, 0x0C, 0x4C, 0x0F, 0xA4, 0xD3, 0x0C, 0x48, 0x89, 0x7C, 0x24, 0x18,
    0x4C, 0x89, 0xF0] ++ bytes_l1167bf_11

theorem code_l1167bf_10 : ∀ x ∈ codeRange 0x116b1e bytes_l1167bf_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16b1e 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1167bf_11

def b_l1167bf_9 : Block Op Label signature Reg.count 444 :=
  .letOp (n := 444) (.exec 0x116ac6 (StorePre 0x116ac6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x116ac6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116ac6 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[440, 4]
    (.letOp (n := 445) (.out 0x116acb (movR64M64Effect 0x116acb 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 446) (.exec 0x116acb (LoadPre 0x116acb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x116acb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116acb 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 447) (.out 0x116ad3 (mulM64Effect 0x116ad3 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[445, 4]
    (.letOp (n := 448) (.out 0x116ad3 (mulM64Effect 0x116ad3 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[445, 4]
    (.letOp (n := 449) (.exec 0x116ad3 (LoadPre 0x116ad3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x116ad3 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x116ad3 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[445, 4]
    (.letOp (n := 450) (.out 0x116ad8 (movR64R64Effect 0x116ad8 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[448]
    (.letOp (n := 451) (.exec 0x116ad8 (fun s => s.RIP = 0x116ad8) (movR64R64Effect 0x116ad8 3 2) (Reg.operands [.gpr 2] [])) #v[448]
    (.letOp (n := 452) (.out 0x116adb (movR64R64Effect 0x116adb 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[447]
    (.letOp (n := 453) (.exec 0x116adb (fun s => s.RIP = 0x116adb) (movR64R64Effect 0x116adb 10 0) (Reg.operands [.gpr 0] [])) #v[447]
    (.letOp (n := 454) (.out 0x116ade (movR64M64Effect 0x116ade 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 455) (.exec 0x116ade (LoadPre 0x116ade (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x116ade + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116ade 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 456) (.out 0x116ae6 (mulM64Effect 0x116ae6 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[454, 4]
    (.letOp (n := 457) (.out 0x116ae6 (mulM64Effect 0x116ae6 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[454, 4]
    (.letOp (n := 458) (.exec 0x116ae6 (LoadPre 0x116ae6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116ae6 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x116ae6 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[454, 4]
    (.letOp (n := 459) (.out 0x116aeb (movR64R64Effect 0x116aeb 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[456]
    (.letOp (n := 460) (.exec 0x116aeb (fun s => s.RIP = 0x116aeb) (movR64R64Effect 0x116aeb 13 0) (Reg.operands [.gpr 0] [])) #v[456]
    (.letOp (n := 461) (.exec 0x116aee (StorePre 0x116aee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116aee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116aee 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[457, 4]
    (.letOp (n := 462) (.out 0x116af3 (andR64R64Effect 0x116af3 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[431, 372]
    (.letOp (n := 463) (.exec 0x116af3 (fun s => s.RIP = 0x116af3) (andR64R64Effect 0x116af3 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[431, 372]
    (.letOp (n := 464) (.out 0x116af6 (movR64R64Effect 0x116af6 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[372]
    (.letOp (n := 465) (.exec 0x116af6 (fun s => s.RIP = 0x116af6) (movR64R64Effect 0x116af6 1 14) (Reg.operands [.gpr 14] [])) #v[372]
    (.letOp (n := 466) (.out 0x116af9 (movR64M64Effect 0x116af9 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 467) (.exec 0x116af9 (LoadPre 0x116af9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x116af9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116af9 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 468) (.out 0x116b01 (mulR64Effect 0x116b01 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[382, 466]
    (.letOp (n := 469) (.out 0x116b01 (mulR64Effect 0x116b01 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[382, 466]
    (.letOp (n := 470) (.exec 0x116b01 (fun s => s.RIP = 0x116b01) (mulR64Effect 0x116b01 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[382, 466]
    (.letOp (n := 471) (.out 0x116b04 (movR64R64Effect 0x116b04 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[469]
    (.letOp (n := 472) (.exec 0x116b04 (fun s => s.RIP = 0x116b04) (movR64R64Effect 0x116b04 14 2) (Reg.operands [.gpr 2] [])) #v[469]
    (.letOp (n := 473) (.out 0x116b07 (movR64R64Effect 0x116b07 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[468]
    (.letOp (n := 474) (.exec 0x116b07 (fun s => s.RIP = 0x116b07) (movR64R64Effect 0x116b07 12 0) (Reg.operands [.gpr 0] [])) #v[468]
    (.letOp (n := 475) (.out 0x116b0a (movR64M64Effect 0x116b0a 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 476) (.exec 0x116b0a (LoadPre 0x116b0a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x116b0a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116b0a 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 477) (.out 0x116b12 (mulR64Effect 0x116b12 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[392, 475]
    (.letOp (n := 478) (.out 0x116b12 (mulR64Effect 0x116b12 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[392, 475]
    (.letOp (n := 479) (.exec 0x116b12 (fun s => s.RIP = 0x116b12) (mulR64Effect 0x116b12 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[392, 475]
    (.letOp (n := 480) (.out 0x116b15 (movR64R64Effect 0x116b15 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[477]
    (.letOp (n := 481) (.exec 0x116b15 (fun s => s.RIP = 0x116b15) (movR64R64Effect 0x116b15 5 0) (Reg.operands [.gpr 0] [])) #v[477]
    (.letOp (n := 482) (.out 0x116b18 (addR64R64Effect 0x116b18 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[480, 473]
    (.letOp (n := 483) (.out 0x116b18 (addR64R64Effect 0x116b18 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[480, 473]
    (.letOp (n := 484) (.exec 0x116b18 (fun s => s.RIP = 0x116b18) (addR64R64Effect 0x116b18 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[480, 473]
    (.letOp (n := 485) (.out 0x116b1b (atFlags StatusFlags.CF (adcR64R64Effect 0x116b1b 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[471, 478, 483]
    (.letOp (n := 486) (.exec 0x116b1b (fun s => s.RIP = 0x116b1b) (atFlags StatusFlags.CF (adcR64R64Effect 0x116b1b 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[471, 478, 483]
    (b_l1167bf_10)))))))))))))))))))))))))))))))))))))))))))

def bytes_l1167bf_9 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64,
    0x24, 0x50, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC2, 0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0x64, 0x24, 0x68, 0x49, 0x89, 0xC5, 0x48, 0x89, 0x54, 0x24, 0x68, 0x4D, 0x21, 0xF0,
    0x4C, 0x89, 0xF1, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x49, 0x89,
    0xD6, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE7, 0x48,
    0x89, 0xC5, 0x4C, 0x01, 0xE5, 0x49, 0x11, 0xD6] ++ bytes_l1167bf_10

theorem code_l1167bf_9 : ∀ x ∈ codeRange 0x116ac6 bytes_l1167bf_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16ac6 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1167bf_10

def b_l1167bf_8 : Block Op Label signature Reg.count 397 :=
  .letOp (n := 397) (.out 0x116a72 (addR64R64Effect 0x116a72 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[386, 368]
    (.letOp (n := 398) (.out 0x116a72 (addR64R64Effect 0x116a72 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[386, 368]
    (.letOp (n := 399) (.exec 0x116a72 (fun s => s.RIP = 0x116a72) (addR64R64Effect 0x116a72 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[386, 368]
    (.letOp (n := 400) (.out 0x116a75 (atFlags StatusFlags.CF (adcR64R64Effect 0x116a75 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[384, 370, 398]
    (.letOp (n := 401) (.exec 0x116a75 (fun s => s.RIP = 0x116a75) (atFlags StatusFlags.CF (adcR64R64Effect 0x116a75 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[384, 370, 398]
    (.letOp (n := 402) (.out 0x116a78 (addR64R64Effect 0x116a78 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[394, 397]
    (.letOp (n := 403) (.out 0x116a78 (addR64R64Effect 0x116a78 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[394, 397]
    (.letOp (n := 404) (.exec 0x116a78 (fun s => s.RIP = 0x116a78) (addR64R64Effect 0x116a78 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[394, 397]
    (.letOp (n := 405) (.out 0x116a7b (atFlags StatusFlags.CF (adcR64R64Effect 0x116a7b 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[400, 395, 403]
    (.letOp (n := 406) (.exec 0x116a7b (fun s => s.RIP = 0x116a7b) (atFlags StatusFlags.CF (adcR64R64Effect 0x116a7b 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[400, 395, 403]
    (.letOp (n := 407) (.out 0x116a7e (addR64R64Effect 0x116a7e 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[402, 321]
    (.letOp (n := 408) (.out 0x116a7e (addR64R64Effect 0x116a7e 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[402, 321]
    (.letOp (n := 409) (.exec 0x116a7e (fun s => s.RIP = 0x116a7e) (addR64R64Effect 0x116a7e 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[402, 321]
    (.letOp (n := 410) (.out 0x116a81 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116a81 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[405, 408]
    (.letOp (n := 411) (.exec 0x116a81 (fun s => s.RIP = 0x116a81) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116a81 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[405, 408]
    (.letOp (n := 412) (.out 0x116a85 (shldR64R64Effect 0x116a85 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[410, 407]
    (.letOp (n := 413) (.exec 0x116a85 (fun s => s.RIP = 0x116a85) (shldR64R64Effect 0x116a85 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[410, 407]
    (.letOp (n := 414) (.out 0x116a8a (andR64R64Effect 0x116a8a 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[407, 372]
    (.letOp (n := 415) (.exec 0x116a8a (fun s => s.RIP = 0x116a8a) (andR64R64Effect 0x116a8a 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[407, 372]
    (.letOp (n := 416) (.out 0x116a8d (movR64Imm64Effect 0x116a8d 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 417) (.exec 0x116a8d (fun s => s.RIP = 0x116a8d) (movR64Imm64Effect 0x116a8d 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 418) (.out 0x116a97 (mulR64Effect 0x116a97 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[416, 414]
    (.letOp (n := 419) (.out 0x116a97 (mulR64Effect 0x116a97 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[416, 414]
    (.letOp (n := 420) (.exec 0x116a97 (fun s => s.RIP = 0x116a97) (mulR64Effect 0x116a97 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[416, 414]
    (.letOp (n := 421) (.out 0x116a9a (addR64M64Effect 0x116a9a 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[361, 4]
    (.letOp (n := 422) (.out 0x116a9a (addR64M64Effect 0x116a9a 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[361, 4]
    (.letOp (n := 423) (.exec 0x116a9a (LoadPre 0x116a9a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x116a9a + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x116a9a 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[361, 4]
    (.letOp (n := 424) (.out 0x116aa2 (atFlags StatusFlags.CF (adcR64M64Effect 0x116aa2 9 (.sib 4 none 0 (.d8 0x60)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[359, 4, 422]
    (.letOp (n := 425) (.exec 0x116aa2 (LoadPre 0x116aa2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x116aa2 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x116aa2 9 (.sib 4 none 0 (.d8 0x60)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[359, 4, 422]
    (.letOp (n := 426) (.out 0x116aa7 (addR64R64Effect 0x116aa7 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[421, 418]
    (.letOp (n := 427) (.out 0x116aa7 (addR64R64Effect 0x116aa7 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[421, 418]
    (.letOp (n := 428) (.exec 0x116aa7 (fun s => s.RIP = 0x116aa7) (addR64R64Effect 0x116aa7 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[421, 418]
    (.letOp (n := 429) (.out 0x116aaa (atFlags StatusFlags.CF (adcR64R64Effect 0x116aaa 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[424, 419, 427]
    (.letOp (n := 430) (.exec 0x116aaa (fun s => s.RIP = 0x116aaa) (atFlags StatusFlags.CF (adcR64R64Effect 0x116aaa 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[424, 419, 427]
    (.letOp (n := 431) (.out 0x116aad (addR64R64Effect 0x116aad 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[426, 343]
    (.letOp (n := 432) (.out 0x116aad (addR64R64Effect 0x116aad 8 3) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 3] []) (.flag .CF)) #v[426, 343]
    (.letOp (n := 433) (.exec 0x116aad (fun s => s.RIP = 0x116aad) (addR64R64Effect 0x116aad 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[426, 343]
    (.letOp (n := 434) (.out 0x116ab0 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116ab0 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[429, 432]
    (.letOp (n := 435) (.exec 0x116ab0 (fun s => s.RIP = 0x116ab0) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116ab0 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[429, 432]
    (.letOp (n := 436) (.out 0x116ab4 (shldR64R64Effect 0x116ab4 5 9 8 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[434, 431]
    (.letOp (n := 437) (.exec 0x116ab4 (fun s => s.RIP = 0x116ab4) (shldR64R64Effect 0x116ab4 5 9 8 12) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[434, 431]
    (.letOp (n := 438) (.out 0x116ab9 (movR64R64Effect 0x116ab9 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[388]
    (.letOp (n := 439) (.exec 0x116ab9 (fun s => s.RIP = 0x116ab9) (movR64R64Effect 0x116ab9 0 1) (Reg.operands [.gpr 1] [])) #v[388]
    (.letOp (n := 440) (.out 0x116abc (mulM64Effect 0x116abc 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[438, 4]
    (.letOp (n := 441) (.out 0x116abc (mulM64Effect 0x116abc 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[438, 4]
    (.letOp (n := 442) (.exec 0x116abc (LoadPre 0x116abc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x116abc + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x116abc 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[438, 4]
    (.letOp (n := 443) (.exec 0x116ac1 (StorePre 0x116ac1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x116ac1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116ac1 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[441, 4]
    (b_l1167bf_9)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1167bf_8 : List UInt8 :=
  [0x4C, 0x01, 0xE5, 0x4D, 0x11, 0xEB, 0x48, 0x01, 0xE8, 0x49, 0x11, 0xD3, 0x4C, 0x01, 0xD0, 0x49,
    0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x4C, 0x21, 0xF0, 0x48, 0xBA, 0x10, 0x3D, 0x00,
    0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x03, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x4C, 0x13, 0x4C, 0x24, 0x60, 0x49, 0x01, 0xC0, 0x49, 0x11, 0xD1, 0x49, 0x01, 0xD8, 0x49, 0x83,
    0xD1, 0x00, 0x4D, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0x64, 0x24, 0x70, 0x48,
    0x89, 0x54, 0x24, 0x70] ++ bytes_l1167bf_9

theorem code_l1167bf_8 : ∀ x ∈ codeRange 0x116a72 bytes_l1167bf_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16a72 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1167bf_9

def b_l1167bf_7 : Block Op Label signature Reg.count 354 :=
  .letOp (n := 354) (.out 0x116a12 (movR64M64Effect 0x116a12 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 355) (.exec 0x116a12 (LoadPre 0x116a12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x116a12 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116a12 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 356) (.out 0x116a1a (mulR64Effect 0x116a1a 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[263, 354]
    (.letOp (n := 357) (.out 0x116a1a (mulR64Effect 0x116a1a 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[263, 354]
    (.letOp (n := 358) (.exec 0x116a1a (fun s => s.RIP = 0x116a1a) (mulR64Effect 0x116a1a 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[263, 354]
    (.letOp (n := 359) (.out 0x116a1d (movR64R64Effect 0x116a1d 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[357]
    (.letOp (n := 360) (.exec 0x116a1d (fun s => s.RIP = 0x116a1d) (movR64R64Effect 0x116a1d 9 2) (Reg.operands [.gpr 2] [])) #v[357]
    (.letOp (n := 361) (.out 0x116a20 (movR64R64Effect 0x116a20 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[356]
    (.letOp (n := 362) (.exec 0x116a20 (fun s => s.RIP = 0x116a20) (movR64R64Effect 0x116a20 8 0) (Reg.operands [.gpr 0] [])) #v[356]
    (.letOp (n := 363) (.out 0x116a23 (movR64M64Effect 0x116a23 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 364) (.exec 0x116a23 (LoadPre 0x116a23 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x116a23 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116a23 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 365) (.out 0x116a2b (mulM64Effect 0x116a2b 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[363, 4]
    (.letOp (n := 366) (.out 0x116a2b (mulM64Effect 0x116a2b 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[363, 4]
    (.letOp (n := 367) (.exec 0x116a2b (LoadPre 0x116a2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116a2b + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x116a2b 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[363, 4]
    (.letOp (n := 368) (.out 0x116a30 (movR64R64Effect 0x116a30 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[365]
    (.letOp (n := 369) (.exec 0x116a30 (fun s => s.RIP = 0x116a30) (movR64R64Effect 0x116a30 12 0) (Reg.operands [.gpr 0] [])) #v[365]
    (.letOp (n := 370) (.out 0x116a33 (movR64R64Effect 0x116a33 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[366]
    (.letOp (n := 371) (.exec 0x116a33 (fun s => s.RIP = 0x116a33) (movR64R64Effect 0x116a33 13 2) (Reg.operands [.gpr 2] [])) #v[366]
    (.letOp (n := 372) (.out 0x116a36 (movR64Imm64Effect 0x116a36 14 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 373) (.exec 0x116a36 (fun s => s.RIP = 0x116a36) (movR64Imm64Effect 0x116a36 14 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 374) (.out 0x116a40 (andR64R64Effect 0x116a40 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[345, 372]
    (.letOp (n := 375) (.exec 0x116a40 (fun s => s.RIP = 0x116a40) (andR64R64Effect 0x116a40 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[345, 372]
    (.letOp (n := 376) (.exec 0x116a43 (StorePre 0x116a43 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x116a43 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116a43 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[374, 4]
    (.letOp (n := 377) (.out 0x116a48 (movR64M64Effect 0x116a48 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 378) (.exec 0x116a48 (LoadPre 0x116a48 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x116a48 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116a48 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 379) (.out 0x116a50 (mulR64Effect 0x116a50 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[285, 377]
    (.letOp (n := 380) (.out 0x116a50 (mulR64Effect 0x116a50 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[285, 377]
    (.letOp (n := 381) (.exec 0x116a50 (fun s => s.RIP = 0x116a50) (mulR64Effect 0x116a50 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[285, 377]
    (.letOp (n := 382) (.out 0x116a53 (movR64R64Effect 0x116a53 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[285]
    (.letOp (n := 383) (.exec 0x116a53 (fun s => s.RIP = 0x116a53) (movR64R64Effect 0x116a53 7 5) (Reg.operands [.gpr 5] [])) #v[285]
    (.letOp (n := 384) (.out 0x116a56 (movR64R64Effect 0x116a56 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[380]
    (.letOp (n := 385) (.exec 0x116a56 (fun s => s.RIP = 0x116a56) (movR64R64Effect 0x116a56 11 2) (Reg.operands [.gpr 2] [])) #v[380]
    (.letOp (n := 386) (.out 0x116a59 (movR64R64Effect 0x116a59 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[379]
    (.letOp (n := 387) (.exec 0x116a59 (fun s => s.RIP = 0x116a59) (movR64R64Effect 0x116a59 5 0) (Reg.operands [.gpr 0] [])) #v[379]
    (.letOp (n := 388) (.out 0x116a5c (movR64M64Effect 0x116a5c 1 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 389) (.exec 0x116a5c (LoadPre 0x116a5c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x116a5c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116a5c 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 390) (.out 0x116a64 (movR64R64Effect 0x116a64 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[388]
    (.letOp (n := 391) (.exec 0x116a64 (fun s => s.RIP = 0x116a64) (movR64R64Effect 0x116a64 0 1) (Reg.operands [.gpr 1] [])) #v[388]
    (.letOp (n := 392) (.out 0x116a67 (movR64M64Effect 0x116a67 15 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 393) (.exec 0x116a67 (LoadPre 0x116a67 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x116a67 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116a67 15 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 394) (.out 0x116a6f (mulR64Effect 0x116a6f 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[392, 390]
    (.letOp (n := 395) (.out 0x116a6f (mulR64Effect 0x116a6f 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[392, 390]
    (.letOp (n := 396) (.exec 0x116a6f (fun s => s.RIP = 0x116a6f) (mulR64Effect 0x116a6f 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[392, 390]
    (b_l1167bf_8)))))))))))))))))))))))))))))))))))))))))))

def bytes_l1167bf_7 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xD1, 0x49, 0x89,
    0xC0, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x68, 0x49, 0x89,
    0xC4, 0x49, 0x89, 0xD5, 0x49, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21,
    0xF7, 0x48, 0x89, 0x7C, 0x24, 0x58, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xE5, 0x48, 0x89, 0xEF, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0x8C, 0x24, 0xD0, 0x00,
    0x00, 0x00, 0x48, 0x89, 0xC8, 0x4C, 0x8B, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE7] ++ bytes_l1167bf_8

theorem code_l1167bf_7 : ∀ x ∈ codeRange 0x116a12 bytes_l1167bf_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16a12 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1167bf_8

def b_l1167bf_6 : Block Op Label signature Reg.count 311 :=
  .letOp (n := 311) (.out 0x1169b7 (addR64R64Effect 0x1169b7 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[298, 306]
    (.letOp (n := 312) (.out 0x1169b7 (addR64R64Effect 0x1169b7 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[298, 306]
    (.letOp (n := 313) (.exec 0x1169b7 (fun s => s.RIP = 0x1169b7) (addR64R64Effect 0x1169b7 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[298, 306]
    (.letOp (n := 314) (.out 0x1169ba (atFlags StatusFlags.CF (adcR64R64Effect 0x1169ba 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[309, 299, 312]
    (.letOp (n := 315) (.exec 0x1169ba (fun s => s.RIP = 0x1169ba) (atFlags StatusFlags.CF (adcR64R64Effect 0x1169ba 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[309, 299, 312]
    (.letOp (n := 316) (.out 0x1169bd (addR64R64Effect 0x1169bd 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[311, 246]
    (.letOp (n := 317) (.out 0x1169bd (addR64R64Effect 0x1169bd 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[311, 246]
    (.letOp (n := 318) (.exec 0x1169bd (fun s => s.RIP = 0x1169bd) (addR64R64Effect 0x1169bd 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[311, 246]
    (.letOp (n := 319) (.out 0x1169c0 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1169c0 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[314, 317]
    (.letOp (n := 320) (.exec 0x1169c0 (fun s => s.RIP = 0x1169c0) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1169c0 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[314, 317]
    (.letOp (n := 321) (.out 0x1169c4 (shldR64R64Effect 0x1169c4 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[319, 316]
    (.letOp (n := 322) (.exec 0x1169c4 (fun s => s.RIP = 0x1169c4) (shldR64R64Effect 0x1169c4 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[319, 316]
    (.letOp (n := 323) (.out 0x1169c9 (shlR64Effect 0x1169c9 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[316]
    (.letOp (n := 324) (.exec 0x1169c9 (fun s => s.RIP = 0x1169c9) (shlR64Effect 0x1169c9 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[316]
    (.letOp (n := 325) (.out 0x1169cd (movR64Imm64Effect 0x1169cd 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 326) (.exec 0x1169cd (fun s => s.RIP = 0x1169cd) (movR64Imm64Effect 0x1169cd 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 327) (.out 0x1169d7 (andR64R64Effect 0x1169d7 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[323, 325]
    (.letOp (n := 328) (.exec 0x1169d7 (fun s => s.RIP = 0x1169d7) (andR64R64Effect 0x1169d7 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[323, 325]
    (.letOp (n := 329) (.out 0x1169da (orR64R64Effect 0x1169da 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[327, 272]
    (.letOp (n := 330) (.exec 0x1169da (fun s => s.RIP = 0x1169da) (orR64R64Effect 0x1169da 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[327, 272]
    (.letOp (n := 331) (.out 0x1169dd (movR64Imm64Effect 0x1169dd 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 332) (.exec 0x1169dd (fun s => s.RIP = 0x1169dd) (movR64Imm64Effect 0x1169dd 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 333) (.out 0x1169e7 (mulR64Effect 0x1169e7 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[331, 329]
    (.letOp (n := 334) (.out 0x1169e7 (mulR64Effect 0x1169e7 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[331, 329]
    (.letOp (n := 335) (.exec 0x1169e7 (fun s => s.RIP = 0x1169e7) (mulR64Effect 0x1169e7 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[331, 329]
    (.letOp (n := 336) (.out 0x1169ea (movR64R64Effect 0x1169ea 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[334]
    (.letOp (n := 337) (.exec 0x1169ea (fun s => s.RIP = 0x1169ea) (movR64R64Effect 0x1169ea 3 2) (Reg.operands [.gpr 2] [])) #v[334]
    (.letOp (n := 338) (.out 0x1169ed (addR64M64Effect 0x1169ed 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[333, 4]
    (.letOp (n := 339) (.out 0x1169ed (addR64M64Effect 0x1169ed 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[333, 4]
    (.letOp (n := 340) (.exec 0x1169ed (LoadPre 0x1169ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1169ed + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1169ed 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[333, 4]
    (.letOp (n := 341) (.out 0x1169f2 (atFlags StatusFlags.CF (adcR64M64Effect 0x1169f2 3 (.sib 4 none 0 (.d8 0x58)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[336, 4, 339]
    (.letOp (n := 342) (.exec 0x1169f2 (LoadPre 0x1169f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1169f2 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1169f2 3 (.sib 4 none 0 (.d8 0x58)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[336, 4, 339]
    (.letOp (n := 343) (.out 0x1169f7 (shldR64R64Effect 0x1169f7 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[341, 338]
    (.letOp (n := 344) (.exec 0x1169f7 (fun s => s.RIP = 0x1169f7) (shldR64R64Effect 0x1169f7 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[341, 338]
    (.letOp (n := 345) (.out 0x1169fc (movR64R64Effect 0x1169fc 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[338]
    (.letOp (n := 346) (.exec 0x1169fc (fun s => s.RIP = 0x1169fc) (movR64R64Effect 0x1169fc 7 0) (Reg.operands [.gpr 0] [])) #v[338]
    (.letOp (n := 347) (.out 0x1169ff (movR64R64Effect 0x1169ff 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[294]
    (.letOp (n := 348) (.exec 0x1169ff (fun s => s.RIP = 0x1169ff) (movR64R64Effect 0x1169ff 0 1) (Reg.operands [.gpr 1] [])) #v[294]
    (.letOp (n := 349) (.out 0x116a02 (mulR64Effect 0x116a02 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[254, 347]
    (.letOp (n := 350) (.out 0x116a02 (mulR64Effect 0x116a02 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[254, 347]
    (.letOp (n := 351) (.exec 0x116a02 (fun s => s.RIP = 0x116a02) (mulR64Effect 0x116a02 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[254, 347]
    (.letOp (n := 352) (.exec 0x116a05 (StorePre 0x116a05 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x116a05 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116a05 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[350, 4]
    (.letOp (n := 353) (.exec 0x116a0a (StorePre 0x116a0a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x116a0a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x116a0a 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[349, 4]
    (b_l1167bf_7)))))))))))))))))))))))))))))))))))))))))))

def bytes_l1167bf_6 : List UInt8 :=
  [0x4C, 0x01, 0xF0, 0x49, 0x11, 0xD2, 0x48, 0x01, 0xF8, 0x49, 0x83, 0xD2, 0x00, 0x49, 0x0F, 0xA4,
    0xC2, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00,
    0x48, 0x21, 0xD0, 0x4C, 0x09, 0xE8, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD3, 0x48, 0x03, 0x44, 0x24, 0x60, 0x48, 0x13, 0x5C, 0x24, 0x58,
    0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0x89, 0xC7, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE1, 0x48, 0x89,
    0x54, 0x24, 0x60, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] ++ bytes_l1167bf_7

theorem code_l1167bf_6 : ∀ x ∈ codeRange 0x1169b7 bytes_l1167bf_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x169b7 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1167bf_7

def b_l1167bf_5 : Block Op Label signature Reg.count 265 :=
  .letOp (n := 265) (.out 0x116964 (mulR64Effect 0x116964 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[263, 261]
    (.letOp (n := 266) (.out 0x116964 (mulR64Effect 0x116964 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[263, 261]
    (.letOp (n := 267) (.exec 0x116964 (fun s => s.RIP = 0x116964) (mulR64Effect 0x116964 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[263, 261]
    (.letOp (n := 268) (.out 0x116967 (movR64R64Effect 0x116967 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[265]
    (.letOp (n := 269) (.exec 0x116967 (fun s => s.RIP = 0x116967) (movR64R64Effect 0x116967 11 0) (Reg.operands [.gpr 0] [])) #v[265]
    (.letOp (n := 270) (.out 0x11696a (movR64R64Effect 0x11696a 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[266]
    (.letOp (n := 271) (.exec 0x11696a (fun s => s.RIP = 0x11696a) (movR64R64Effect 0x11696a 3 2) (Reg.operands [.gpr 2] [])) #v[266]
    (.letOp (n := 272) (.out 0x11696d (andR32Imm8Effect 0x11696d 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[250]
    (.letOp (n := 273) (.exec 0x11696d (fun s => s.RIP = 0x11696d) (andR32Imm8Effect 0x11696d 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[250]
    (.letOp (n := 274) (.out 0x116971 (movR64M64Effect 0x116971 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 275) (.exec 0x116971 (LoadPre 0x116971 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x116971 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116971 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 276) (.out 0x116979 (mulR64Effect 0x116979 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[177, 274]
    (.letOp (n := 277) (.out 0x116979 (mulR64Effect 0x116979 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[177, 274]
    (.letOp (n := 278) (.exec 0x116979 (fun s => s.RIP = 0x116979) (mulR64Effect 0x116979 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[177, 274]
    (.letOp (n := 279) (.out 0x11697c (movR64R64Effect 0x11697c 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[277]
    (.letOp (n := 280) (.exec 0x11697c (fun s => s.RIP = 0x11697c) (movR64R64Effect 0x11697c 10 2) (Reg.operands [.gpr 2] [])) #v[277]
    (.letOp (n := 281) (.out 0x11697f (movR64R64Effect 0x11697f 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[276]
    (.letOp (n := 282) (.exec 0x11697f (fun s => s.RIP = 0x11697f) (movR64R64Effect 0x11697f 14 0) (Reg.operands [.gpr 0] [])) #v[276]
    (.letOp (n := 283) (.out 0x116982 (movR64M64Effect 0x116982 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 284) (.exec 0x116982 (LoadPre 0x116982 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x116982 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116982 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 285) (.out 0x11698a (movR64M64Effect 0x11698a 5 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 286) (.exec 0x11698a (LoadPre 0x11698a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11698a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11698a 5 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 287) (.out 0x11698f (mulR64Effect 0x11698f 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[285, 283]
    (.letOp (n := 288) (.out 0x11698f (mulR64Effect 0x11698f 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[285, 283]
    (.letOp (n := 289) (.exec 0x11698f (fun s => s.RIP = 0x11698f) (mulR64Effect 0x11698f 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[285, 283]
    (.letOp (n := 290) (.out 0x116992 (movR64R64Effect 0x116992 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[288]
    (.letOp (n := 291) (.exec 0x116992 (fun s => s.RIP = 0x116992) (movR64R64Effect 0x116992 15 2) (Reg.operands [.gpr 2] [])) #v[288]
    (.letOp (n := 292) (.out 0x116995 (movR64R64Effect 0x116995 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[287]
    (.letOp (n := 293) (.exec 0x116995 (fun s => s.RIP = 0x116995) (movR64R64Effect 0x116995 12 0) (Reg.operands [.gpr 0] [])) #v[287]
    (.letOp (n := 294) (.out 0x116998 (movR64M64Effect 0x116998 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 295) (.exec 0x116998 (LoadPre 0x116998 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x116998 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116998 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 296) (.out 0x1169a0 (movR64R64Effect 0x1169a0 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[294]
    (.letOp (n := 297) (.exec 0x1169a0 (fun s => s.RIP = 0x1169a0) (movR64R64Effect 0x1169a0 0 1) (Reg.operands [.gpr 1] [])) #v[294]
    (.letOp (n := 298) (.out 0x1169a3 (mulM64Effect 0x1169a3 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[296, 4]
    (.letOp (n := 299) (.out 0x1169a3 (mulM64Effect 0x1169a3 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[296, 4]
    (.letOp (n := 300) (.exec 0x1169a3 (LoadPre 0x1169a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1169a3 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1169a3 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[296, 4]
    (.letOp (n := 301) (.out 0x1169ab (addR64R64Effect 0x1169ab 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[281, 268]
    (.letOp (n := 302) (.out 0x1169ab (addR64R64Effect 0x1169ab 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[281, 268]
    (.letOp (n := 303) (.exec 0x1169ab (fun s => s.RIP = 0x1169ab) (addR64R64Effect 0x1169ab 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[281, 268]
    (.letOp (n := 304) (.out 0x1169ae (atFlags StatusFlags.CF (adcR64R64Effect 0x1169ae 10 3)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[279, 270, 302]
    (.letOp (n := 305) (.exec 0x1169ae (fun s => s.RIP = 0x1169ae) (atFlags StatusFlags.CF (adcR64R64Effect 0x1169ae 10 3)) (Reg.operands [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[279, 270, 302]
    (.letOp (n := 306) (.out 0x1169b1 (addR64R64Effect 0x1169b1 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[301, 292]
    (.letOp (n := 307) (.out 0x1169b1 (addR64R64Effect 0x1169b1 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[301, 292]
    (.letOp (n := 308) (.exec 0x1169b1 (fun s => s.RIP = 0x1169b1) (addR64R64Effect 0x1169b1 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[301, 292]
    (.letOp (n := 309) (.out 0x1169b4 (atFlags StatusFlags.CF (adcR64R64Effect 0x1169b4 10 15)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[304, 290, 307]
    (.letOp (n := 310) (.exec 0x1169b4 (fun s => s.RIP = 0x1169b4) (atFlags StatusFlags.CF (adcR64R64Effect 0x1169b4 10 15)) (Reg.operands [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[304, 290, 307]
    (b_l1167bf_6))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1167bf_5 : List UInt8 :=
  [0x49, 0xF7, 0xE0, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xD3, 0x41, 0x83, 0xE5, 0x0F, 0x48, 0x8B, 0x84,
    0x24, 0xA8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC6, 0x48, 0x8B,
    0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x6C, 0x24, 0x78, 0x48, 0xF7, 0xE5, 0x49, 0x89,
    0xD7, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x48,
    0xF7, 0xA4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xDE, 0x49, 0x11, 0xDA, 0x4D, 0x01, 0xE6,
    0x4D, 0x11, 0xFA] ++ bytes_l1167bf_6

theorem code_l1167bf_5 : ∀ x ∈ codeRange 0x116964 bytes_l1167bf_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16964 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1167bf_6

def b_l1167bf_4 : Block Op Label signature Reg.count 221 :=
  .letOp (n := 221) (.out 0x116912 (addR64R64Effect 0x116912 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[216, 183]
    (.letOp (n := 222) (.out 0x116912 (addR64R64Effect 0x116912 6 15) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 15] []) (.flag .CF)) #v[216, 183]
    (.letOp (n := 223) (.exec 0x116912 (fun s => s.RIP = 0x116912) (addR64R64Effect 0x116912 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[216, 183]
    (.letOp (n := 224) (.out 0x116915 (atFlags StatusFlags.CF (adcR64M64Effect 0x116915 7 (.sib 4 none 0 (.d32 0x80)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[219, 4, 222]
    (.letOp (n := 225) (.exec 0x116915 (LoadPre 0x116915 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x116915 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x116915 7 (.sib 4 none 0 (.d32 0x80)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[219, 4, 222]
    (.letOp (n := 226) (.out 0x11691d (addR64R64Effect 0x11691d 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[221, 192]
    (.letOp (n := 227) (.out 0x11691d (addR64R64Effect 0x11691d 6 13) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 13] []) (.flag .CF)) #v[221, 192]
    (.letOp (n := 228) (.exec 0x11691d (fun s => s.RIP = 0x11691d) (addR64R64Effect 0x11691d 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[221, 192]
    (.letOp (n := 229) (.out 0x116920 (atFlags StatusFlags.CF (adcR64R64Effect 0x116920 7 12)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[224, 190, 227]
    (.letOp (n := 230) (.exec 0x116920 (fun s => s.RIP = 0x116920) (atFlags StatusFlags.CF (adcR64R64Effect 0x116920 7 12)) (Reg.operands [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[224, 190, 227]
    (.letOp (n := 231) (.out 0x116923 (addR64R64Effect 0x116923 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[226, 199]
    (.letOp (n := 232) (.out 0x116923 (addR64R64Effect 0x116923 6 11) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 11] []) (.flag .CF)) #v[226, 199]
    (.letOp (n := 233) (.exec 0x116923 (fun s => s.RIP = 0x116923) (addR64R64Effect 0x116923 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[226, 199]
    (.letOp (n := 234) (.out 0x116926 (atFlags StatusFlags.CF (adcR64R64Effect 0x116926 7 3)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[229, 201, 232]
    (.letOp (n := 235) (.exec 0x116926 (fun s => s.RIP = 0x116926) (atFlags StatusFlags.CF (adcR64R64Effect 0x116926 7 3)) (Reg.operands [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[229, 201, 232]
    (.letOp (n := 236) (.out 0x116929 (addR64R64Effect 0x116929 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[231, 211]
    (.letOp (n := 237) (.out 0x116929 (addR64R64Effect 0x116929 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[231, 211]
    (.letOp (n := 238) (.exec 0x116929 (fun s => s.RIP = 0x116929) (addR64R64Effect 0x116929 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[231, 211]
    (.letOp (n := 239) (.out 0x11692c (atFlags StatusFlags.CF (adcR64R64Effect 0x11692c 7 8)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[234, 214, 237]
    (.letOp (n := 240) (.exec 0x11692c (fun s => s.RIP = 0x11692c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11692c 7 8)) (Reg.operands [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[234, 214, 237]
    (.letOp (n := 241) (.out 0x11692f (addR64R64Effect 0x11692f 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[236, 157]
    (.letOp (n := 242) (.out 0x11692f (addR64R64Effect 0x11692f 6 9) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 9] []) (.flag .CF)) #v[236, 157]
    (.letOp (n := 243) (.exec 0x11692f (fun s => s.RIP = 0x11692f) (addR64R64Effect 0x11692f 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[236, 157]
    (.letOp (n := 244) (.out 0x116932 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116932 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[239, 242]
    (.letOp (n := 245) (.exec 0x116932 (fun s => s.RIP = 0x116932) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116932 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[239, 242]
    (.letOp (n := 246) (.out 0x116936 (shldR64R64Effect 0x116936 5 7 6 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[244, 241]
    (.letOp (n := 247) (.exec 0x116936 (fun s => s.RIP = 0x116936) (shldR64R64Effect 0x116936 5 7 6 12) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[244, 241]
    (.letOp (n := 248) (.out 0x11693b (movR64R64Effect 0x11693b 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[241]
    (.letOp (n := 249) (.exec 0x11693b (fun s => s.RIP = 0x11693b) (movR64R64Effect 0x11693b 13 6) (Reg.operands [.gpr 6] [])) #v[241]
    (.letOp (n := 250) (.out 0x11693e (shrR64Effect 0x11693e 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[248]
    (.letOp (n := 251) (.exec 0x11693e (fun s => s.RIP = 0x11693e) (shrR64Effect 0x11693e 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[248]
    (.letOp (n := 252) (.out 0x116942 (movR64R64Effect 0x116942 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[109]
    (.letOp (n := 253) (.exec 0x116942 (fun s => s.RIP = 0x116942) (movR64R64Effect 0x116942 0 5) (Reg.operands [.gpr 5] [])) #v[109]
    (.letOp (n := 254) (.out 0x116945 (movR64M64Effect 0x116945 9 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 255) (.exec 0x116945 (LoadPre 0x116945 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x116945 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116945 9 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 256) (.out 0x11694a (mulR64Effect 0x11694a 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[254, 252]
    (.letOp (n := 257) (.out 0x11694a (mulR64Effect 0x11694a 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[254, 252]
    (.letOp (n := 258) (.exec 0x11694a (fun s => s.RIP = 0x11694a) (mulR64Effect 0x11694a 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[254, 252]
    (.letOp (n := 259) (.exec 0x11694d (StorePre 0x11694d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11694d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11694d 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[257, 4]
    (.letOp (n := 260) (.exec 0x116952 (StorePre 0x116952 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x116952 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116952 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[256, 4]
    (.letOp (n := 261) (.out 0x116957 (movR64M64Effect 0x116957 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 262) (.exec 0x116957 (LoadPre 0x116957 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x116957 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116957 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 263) (.out 0x11695f (movR64M64Effect 0x11695f 8 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 264) (.exec 0x11695f (LoadPre 0x11695f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11695f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11695f 8 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1167bf_5))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1167bf_4 : List UInt8 :=
  [0x4C, 0x01, 0xFE, 0x48, 0x13, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xEE, 0x4C, 0x11,
    0xE7, 0x4C, 0x01, 0xDE, 0x48, 0x11, 0xDF, 0x48, 0x01, 0xC6, 0x4C, 0x11, 0xC7, 0x4C, 0x01, 0xCE,
    0x48, 0x83, 0xD7, 0x00, 0x48, 0x0F, 0xA4, 0xF7, 0x0C, 0x49, 0x89, 0xF5, 0x49, 0xC1, 0xED, 0x30,
    0x48, 0x89, 0xE8, 0x4C, 0x8B, 0x4C, 0x24, 0x70, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x54, 0x24, 0x58,
    0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x44,
    0x24, 0x50] ++ bytes_l1167bf_5

theorem code_l1167bf_4 : ∀ x ∈ codeRange 0x116912 bytes_l1167bf_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16912 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1167bf_5

def b_l1167bf_3 : Block Op Label signature Reg.count 177 :=
  .letOp (n := 177) (.out 0x1168c2 (movR64M64Effect 0x1168c2 14 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 178) (.exec 0x1168c2 (LoadPre 0x1168c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1168c2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1168c2 14 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 179) (.out 0x1168c7 (mulR64Effect 0x1168c7 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[177, 175]
    (.letOp (n := 180) (.out 0x1168c7 (mulR64Effect 0x1168c7 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[177, 175]
    (.letOp (n := 181) (.exec 0x1168c7 (fun s => s.RIP = 0x1168c7) (mulR64Effect 0x1168c7 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[177, 175]
    (.letOp (n := 182) (.exec 0x1168ca (StorePre 0x1168ca 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1168ca + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1168ca 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[180, 4]
    (.letOp (n := 183) (.out 0x1168d2 (movR64R64Effect 0x1168d2 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[179]
    (.letOp (n := 184) (.exec 0x1168d2 (fun s => s.RIP = 0x1168d2) (movR64R64Effect 0x1168d2 15 0) (Reg.operands [.gpr 0] [])) #v[179]
    (.letOp (n := 185) (.out 0x1168d5 (movR64R64Effect 0x1168d5 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[93]
    (.letOp (n := 186) (.exec 0x1168d5 (fun s => s.RIP = 0x1168d5) (movR64R64Effect 0x1168d5 0 13) (Reg.operands [.gpr 13] [])) #v[93]
    (.letOp (n := 187) (.out 0x1168d8 (mulR64Effect 0x1168d8 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[55, 185]
    (.letOp (n := 188) (.out 0x1168d8 (mulR64Effect 0x1168d8 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[55, 185]
    (.letOp (n := 189) (.exec 0x1168d8 (fun s => s.RIP = 0x1168d8) (mulR64Effect 0x1168d8 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[55, 185]
    (.letOp (n := 190) (.out 0x1168db (movR64R64Effect 0x1168db 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[188]
    (.letOp (n := 191) (.exec 0x1168db (fun s => s.RIP = 0x1168db) (movR64R64Effect 0x1168db 12 2) (Reg.operands [.gpr 2] [])) #v[188]
    (.letOp (n := 192) (.out 0x1168de (movR64R64Effect 0x1168de 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[187]
    (.letOp (n := 193) (.exec 0x1168de (fun s => s.RIP = 0x1168de) (movR64R64Effect 0x1168de 13 0) (Reg.operands [.gpr 0] [])) #v[187]
    (.letOp (n := 194) (.out 0x1168e1 (movR64R64Effect 0x1168e1 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[109]
    (.letOp (n := 195) (.exec 0x1168e1 (fun s => s.RIP = 0x1168e1) (movR64R64Effect 0x1168e1 0 5) (Reg.operands [.gpr 5] [])) #v[109]
    (.letOp (n := 196) (.out 0x1168e4 (mulR64Effect 0x1168e4 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[53, 194]
    (.letOp (n := 197) (.out 0x1168e4 (mulR64Effect 0x1168e4 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[53, 194]
    (.letOp (n := 198) (.exec 0x1168e4 (fun s => s.RIP = 0x1168e4) (mulR64Effect 0x1168e4 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[53, 194]
    (.letOp (n := 199) (.out 0x1168e7 (movR64R64Effect 0x1168e7 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[196]
    (.letOp (n := 200) (.exec 0x1168e7 (fun s => s.RIP = 0x1168e7) (movR64R64Effect 0x1168e7 11 0) (Reg.operands [.gpr 0] [])) #v[196]
    (.letOp (n := 201) (.out 0x1168ea (movR64R64Effect 0x1168ea 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[197]
    (.letOp (n := 202) (.exec 0x1168ea (fun s => s.RIP = 0x1168ea) (movR64R64Effect 0x1168ea 3 2) (Reg.operands [.gpr 2] [])) #v[197]
    (.letOp (n := 203) (.out 0x1168ed (shrR64Effect 0x1168ed 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[134]
    (.letOp (n := 204) (.exec 0x1168ed (fun s => s.RIP = 0x1168ed) (shrR64Effect 0x1168ed 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[134]
    (.letOp (n := 205) (.out 0x1168f1 (movR64Imm64Effect 0x1168f1 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 206) (.exec 0x1168f1 (fun s => s.RIP = 0x1168f1) (movR64Imm64Effect 0x1168f1 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 207) (.out 0x1168fb (imulR64R64Effect 0x1168fb 4 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[203, 205]
    (.letOp (n := 208) (.exec 0x1168fb (fun s => s.RIP = 0x1168fb) (imulR64R64Effect 0x1168fb 4 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[203, 205]
    (.letOp (n := 209) (.out 0x1168ff (movR64R64Effect 0x1168ff 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[138]
    (.letOp (n := 210) (.exec 0x1168ff (fun s => s.RIP = 0x1168ff) (movR64R64Effect 0x1168ff 0 10) (Reg.operands [.gpr 10] [])) #v[138]
    (.letOp (n := 211) (.out 0x116902 (mulR64Effect 0x116902 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[205, 209]
    (.letOp (n := 212) (.out 0x116902 (mulR64Effect 0x116902 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[205, 209]
    (.letOp (n := 213) (.exec 0x116902 (fun s => s.RIP = 0x116902) (mulR64Effect 0x116902 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[205, 209]
    (.letOp (n := 214) (.out 0x116905 (addR64R64Effect 0x116905 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[207, 212]
    (.letOp (n := 215) (.exec 0x116905 (fun s => s.RIP = 0x116905) (addR64R64Effect 0x116905 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[207, 212]
    (.letOp (n := 216) (.out 0x116908 (addR64M64Effect 0x116908 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[173, 4]
    (.letOp (n := 217) (.out 0x116908 (addR64M64Effect 0x116908 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[173, 4]
    (.letOp (n := 218) (.exec 0x116908 (LoadPre 0x116908 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x116908 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x116908 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[173, 4]
    (.letOp (n := 219) (.out 0x11690d (atFlags StatusFlags.CF (adcR64M64Effect 0x11690d 7 (.sib 4 none 0 (.d8 0x58)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[171, 4, 217]
    (.letOp (n := 220) (.exec 0x11690d (LoadPre 0x11690d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11690d + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11690d 7 (.sib 4 none 0 (.d8 0x58)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[171, 4, 217]
    (b_l1167bf_4))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1167bf_3 : List UInt8 :=
  [0x4C, 0x8B, 0x74, 0x24, 0x68, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x49, 0x89, 0xC7, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE4, 0x49, 0x89, 0xD4, 0x49, 0x89, 0xC5, 0x48,
    0x89, 0xE8, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xD3, 0x49, 0xC1, 0xE8, 0x34, 0x48,
    0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xC1, 0x4C, 0x89, 0xD0,
    0x48, 0xF7, 0xE1, 0x49, 0x01, 0xD0, 0x48, 0x03, 0x74, 0x24, 0x60, 0x48, 0x13, 0x7C, 0x24, 0x58] ++ bytes_l1167bf_4

theorem code_l1167bf_3 : ∀ x ∈ codeRange 0x1168c2 bytes_l1167bf_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x168c2 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1167bf_4

def b_l1167bf_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x116867 (movR64R64Effect 0x116867 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[131]
    (.letOp (n := 137) (.exec 0x116867 (fun s => s.RIP = 0x116867) (movR64R64Effect 0x116867 10 2) (Reg.operands [.gpr 2] [])) #v[131]
    (.letOp (n := 138) (.out 0x11686a (shldR64R64Effect 0x11686a 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[136, 130]
    (.letOp (n := 139) (.exec 0x11686a (fun s => s.RIP = 0x11686a) (shldR64R64Effect 0x11686a 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[136, 130]
    (.letOp (n := 140) (.out 0x11686f (movR64Imm64Effect 0x11686f 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 141) (.exec 0x11686f (fun s => s.RIP = 0x11686f) (movR64Imm64Effect 0x11686f 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 142) (.out 0x116879 (andR64R64Effect 0x116879 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[130, 140]
    (.letOp (n := 143) (.exec 0x116879 (fun s => s.RIP = 0x116879) (andR64R64Effect 0x116879 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[130, 140]
    (.letOp (n := 144) (.out 0x11687c (movR64Imm64Effect 0x11687c 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 145) (.exec 0x11687c (fun s => s.RIP = 0x11687c) (movR64Imm64Effect 0x11687c 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 146) (.out 0x116886 (mulR64Effect 0x116886 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[144, 142]
    (.letOp (n := 147) (.out 0x116886 (mulR64Effect 0x116886 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[144, 142]
    (.letOp (n := 148) (.exec 0x116886 (fun s => s.RIP = 0x116886) (mulR64Effect 0x116886 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[144, 142]
    (.letOp (n := 149) (.out 0x116889 (movR64R64Effect 0x116889 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[147]
    (.letOp (n := 150) (.exec 0x116889 (fun s => s.RIP = 0x116889) (movR64R64Effect 0x116889 9 2) (Reg.operands [.gpr 2] [])) #v[147]
    (.letOp (n := 151) (.out 0x11688c (addR64R64Effect 0x11688c 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[146, 121]
    (.letOp (n := 152) (.out 0x11688c (addR64R64Effect 0x11688c 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[146, 121]
    (.letOp (n := 153) (.exec 0x11688c (fun s => s.RIP = 0x11688c) (addR64R64Effect 0x11688c 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[146, 121]
    (.letOp (n := 154) (.exec 0x11688f (StorePre 0x11688f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11688f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11688f 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[151, 4]
    (.letOp (n := 155) (.out 0x116897 (atFlags StatusFlags.CF (adcR64R64Effect 0x116897 9 7)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[149, 124, 152]
    (.letOp (n := 156) (.exec 0x116897 (fun s => s.RIP = 0x116897) (atFlags StatusFlags.CF (adcR64R64Effect 0x116897 9 7)) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[149, 124, 152]
    (.letOp (n := 157) (.out 0x11689a (shldR64R64Effect 0x11689a 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[155, 151]
    (.letOp (n := 158) (.exec 0x11689a (fun s => s.RIP = 0x11689a) (shldR64R64Effect 0x11689a 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[155, 151]
    (.letOp (n := 159) (.out 0x11689f (movR64R64Effect 0x11689f 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[126]
    (.letOp (n := 160) (.exec 0x11689f (fun s => s.RIP = 0x11689f) (movR64R64Effect 0x11689f 0 1) (Reg.operands [.gpr 1] [])) #v[126]
    (.letOp (n := 161) (.out 0x1168a2 (mulM64Effect 0x1168a2 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[159, 4]
    (.letOp (n := 162) (.out 0x1168a2 (mulM64Effect 0x1168a2 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[159, 4]
    (.letOp (n := 163) (.exec 0x1168a2 (LoadPre 0x1168a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1168a2 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1168a2 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[159, 4]
    (.letOp (n := 164) (.exec 0x1168a7 (StorePre 0x1168a7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1168a7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1168a7 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[162, 4]
    (.letOp (n := 165) (.exec 0x1168ac (StorePre 0x1168ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1168ac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1168ac 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[161, 4]
    (.letOp (n := 166) (.out 0x1168b1 (movR64R64Effect 0x1168b1 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 167) (.exec 0x1168b1 (fun s => s.RIP = 0x1168b1) (movR64R64Effect 0x1168b1 0 14) (Reg.operands [.gpr 14] [])) #v[66]
    (.letOp (n := 168) (.out 0x1168b4 (mulM64Effect 0x1168b4 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[166, 4]
    (.letOp (n := 169) (.out 0x1168b4 (mulM64Effect 0x1168b4 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[166, 4]
    (.letOp (n := 170) (.exec 0x1168b4 (LoadPre 0x1168b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1168b4 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1168b4 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[166, 4]
    (.letOp (n := 171) (.out 0x1168b9 (movR64R64Effect 0x1168b9 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[169]
    (.letOp (n := 172) (.exec 0x1168b9 (fun s => s.RIP = 0x1168b9) (movR64R64Effect 0x1168b9 7 2) (Reg.operands [.gpr 2] [])) #v[169]
    (.letOp (n := 173) (.out 0x1168bc (movR64R64Effect 0x1168bc 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[168]
    (.letOp (n := 174) (.exec 0x1168bc (fun s => s.RIP = 0x1168bc) (movR64R64Effect 0x1168bc 6 0) (Reg.operands [.gpr 0] [])) #v[168]
    (.letOp (n := 175) (.out 0x1168bf (movR64R64Effect 0x1168bf 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[77]
    (.letOp (n := 176) (.exec 0x1168bf (fun s => s.RIP = 0x1168bf) (movR64R64Effect 0x1168bf 0 15) (Reg.operands [.gpr 15] [])) #v[77]
    (b_l1167bf_3)))))))))))))))))))))))))))))))))))))))))

def bytes_l1167bf_2 : List UInt8 :=
  [0x49, 0x89, 0xD2, 0x49, 0x0F, 0xA4, 0xC2, 0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE2, 0x49, 0x89, 0xD1, 0x4C, 0x01, 0xD8, 0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00,
    0x49, 0x11, 0xF9, 0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0x64, 0x24, 0x70,
    0x48, 0x89, 0x54, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x60, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0x64,
    0x24, 0x50, 0x48, 0x89, 0xD7, 0x48, 0x89, 0xC6, 0x4C, 0x89, 0xF8] ++ bytes_l1167bf_3

theorem code_l1167bf_2 : ∀ x ∈ codeRange 0x116867 bytes_l1167bf_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16867 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1167bf_3

def b_l1167bf_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x116815 (movR64M64Effect 0x116815 13 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 94) (.exec 0x116815 (LoadPre 0x116815 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x116815 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116815 13 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x11681d (movR64R64Effect 0x11681d 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[93]
    (.letOp (n := 96) (.exec 0x11681d (fun s => s.RIP = 0x11681d) (movR64R64Effect 0x11681d 0 13) (Reg.operands [.gpr 13] [])) #v[93]
    (.letOp (n := 97) (.out 0x116820 (mulR64Effect 0x116820 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[57, 95]
    (.letOp (n := 98) (.out 0x116820 (mulR64Effect 0x116820 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[57, 95]
    (.letOp (n := 99) (.exec 0x116820 (fun s => s.RIP = 0x116820) (mulR64Effect 0x116820 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[57, 95]
    (.letOp (n := 100) (.out 0x116823 (movR64R64Effect 0x116823 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[98]
    (.letOp (n := 101) (.exec 0x116823 (fun s => s.RIP = 0x116823) (movR64R64Effect 0x116823 1 2) (Reg.operands [.gpr 2] [])) #v[98]
    (.letOp (n := 102) (.out 0x116826 (movR64R64Effect 0x116826 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[97]
    (.letOp (n := 103) (.exec 0x116826 (fun s => s.RIP = 0x116826) (movR64R64Effect 0x116826 6 0) (Reg.operands [.gpr 0] [])) #v[97]
    (.letOp (n := 104) (.out 0x116829 (addR64R64Effect 0x116829 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[102, 88]
    (.letOp (n := 105) (.out 0x116829 (addR64R64Effect 0x116829 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[102, 88]
    (.letOp (n := 106) (.exec 0x116829 (fun s => s.RIP = 0x116829) (addR64R64Effect 0x116829 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[102, 88]
    (.letOp (n := 107) (.out 0x11682c (atFlags StatusFlags.CF (adcR64R64Effect 0x11682c 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[100, 91, 105]
    (.letOp (n := 108) (.exec 0x11682c (fun s => s.RIP = 0x11682c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11682c 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[100, 91, 105]
    (.letOp (n := 109) (.out 0x11682f (movR64M64Effect 0x11682f 5 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 110) (.exec 0x11682f (LoadPre 0x11682f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11682f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11682f 5 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 111) (.out 0x116837 (movR64R64Effect 0x116837 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[109]
    (.letOp (n := 112) (.exec 0x116837 (fun s => s.RIP = 0x116837) (movR64R64Effect 0x116837 0 5) (Reg.operands [.gpr 5] [])) #v[109]
    (.letOp (n := 113) (.out 0x11683a (mulR64Effect 0x11683a 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[55, 111]
    (.letOp (n := 114) (.out 0x11683a (mulR64Effect 0x11683a 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[55, 111]
    (.letOp (n := 115) (.exec 0x11683a (fun s => s.RIP = 0x11683a) (mulR64Effect 0x11683a 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[55, 111]
    (.letOp (n := 116) (.exec 0x11683d (StorePre 0x11683d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11683d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11683d 12 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 117) (.out 0x116842 (movR64R64Effect 0x116842 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[114]
    (.letOp (n := 118) (.exec 0x116842 (fun s => s.RIP = 0x116842) (movR64R64Effect 0x116842 7 2) (Reg.operands [.gpr 2] [])) #v[114]
    (.letOp (n := 119) (.out 0x116845 (movR64R64Effect 0x116845 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[113]
    (.letOp (n := 120) (.exec 0x116845 (fun s => s.RIP = 0x116845) (movR64R64Effect 0x116845 11 0) (Reg.operands [.gpr 0] [])) #v[113]
    (.letOp (n := 121) (.out 0x116848 (addR64R64Effect 0x116848 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[119, 104]
    (.letOp (n := 122) (.out 0x116848 (addR64R64Effect 0x116848 11 6) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 6] []) (.flag .CF)) #v[119, 104]
    (.letOp (n := 123) (.exec 0x116848 (fun s => s.RIP = 0x116848) (addR64R64Effect 0x116848 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[119, 104]
    (.letOp (n := 124) (.out 0x11684b (atFlags StatusFlags.CF (adcR64R64Effect 0x11684b 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[117, 107, 122]
    (.letOp (n := 125) (.exec 0x11684b (fun s => s.RIP = 0x11684b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11684b 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[117, 107, 122]
    (.letOp (n := 126) (.out 0x11684e (movR64M64Effect 0x11684e 1 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 127) (.exec 0x11684e (LoadPre 0x11684e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11684e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11684e 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 128) (.out 0x116856 (movR64R64Effect 0x116856 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[126]
    (.letOp (n := 129) (.exec 0x116856 (fun s => s.RIP = 0x116856) (movR64R64Effect 0x116856 0 1) (Reg.operands [.gpr 1] [])) #v[126]
    (.letOp (n := 130) (.out 0x116859 (mulR64Effect 0x116859 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[53, 128]
    (.letOp (n := 131) (.out 0x116859 (mulR64Effect 0x116859 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[53, 128]
    (.letOp (n := 132) (.exec 0x116859 (fun s => s.RIP = 0x116859) (mulR64Effect 0x116859 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[53, 128]
    (.letOp (n := 133) (.exec 0x11685c (StorePre 0x11685c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11685c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11685c 3 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 134) (.out 0x116864 (movR64R64Effect 0x116864 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[131]
    (.letOp (n := 135) (.exec 0x116864 (fun s => s.RIP = 0x116864) (movR64R64Effect 0x116864 8 2) (Reg.operands [.gpr 2] [])) #v[131]
    (b_l1167bf_2)))))))))))))))))))))))))))))))))))))))))))

def bytes_l1167bf_1 : List UInt8 :=
  [0x4C, 0x8B, 0xAC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE3, 0x48, 0x89,
    0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x01, 0xC6, 0x48, 0x11, 0xF9, 0x48, 0x8B, 0xAC, 0x24, 0xA0, 0x00,
    0x00, 0x00, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE4, 0x4C, 0x89, 0x64, 0x24, 0x78, 0x48, 0x89, 0xD7,
    0x49, 0x89, 0xC3, 0x49, 0x01, 0xF3, 0x48, 0x11, 0xCF, 0x48, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49,
    0x89, 0xD0] ++ bytes_l1167bf_2

theorem code_l1167bf_1 : ∀ x ∈ codeRange 0x116815 bytes_l1167bf_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16815 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1167bf_2

def b_l1167bf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1167bf (movR64M64Effect 0x1167bf 3 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x1167bf (LoadPre 0x1167bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1167bf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1167bf 3 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1167c4 (movR64M64Effect 0x1167c4 12 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 56) (.exec 0x1167c4 (LoadPre 0x1167c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1167c4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1167c4 12 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1167c9 (movR64M64Effect 0x1167c9 11 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 58) (.exec 0x1167c9 (LoadPre 0x1167c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1167c9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1167c9 11 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x1167ce (StorePre 0x1167ce 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1167ce + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1167ce 11 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x1167d3 (movR64M64Effect 0x1167d3 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 61) (.exec 0x1167d3 (LoadPre 0x1167d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1167d3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1167d3 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x1167d8 (StorePre 0x1167d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1167d8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1167d8 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x1167dd (movR64M64Effect 0x1167dd 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x1167dd (LoadPre 0x1167dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1167dd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1167dd 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x1167e2 (StorePre 0x1167e2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1167e2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1167e2 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x1167e7 (movR64M64Effect 0x1167e7 14 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 67) (.exec 0x1167e7 (LoadPre 0x1167e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1167e7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1167e7 14 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x1167ef (movR64R64Effect 0x1167ef 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 69) (.exec 0x1167ef (fun s => s.RIP = 0x1167ef) (movR64R64Effect 0x1167ef 0 14) (Reg.operands [.gpr 14] [])) #v[66]
    (.letOp (n := 70) (.out 0x1167f2 (mulR64Effect 0x1167f2 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[60, 68]
    (.letOp (n := 71) (.out 0x1167f2 (mulR64Effect 0x1167f2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[60, 68]
    (.letOp (n := 72) (.exec 0x1167f2 (fun s => s.RIP = 0x1167f2) (mulR64Effect 0x1167f2 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[60, 68]
    (.letOp (n := 73) (.out 0x1167f5 (movR64R64Effect 0x1167f5 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[71]
    (.letOp (n := 74) (.exec 0x1167f5 (fun s => s.RIP = 0x1167f5) (movR64R64Effect 0x1167f5 1 2) (Reg.operands [.gpr 2] [])) #v[71]
    (.letOp (n := 75) (.out 0x1167f8 (movR64R64Effect 0x1167f8 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[70]
    (.letOp (n := 76) (.exec 0x1167f8 (fun s => s.RIP = 0x1167f8) (movR64R64Effect 0x1167f8 6 0) (Reg.operands [.gpr 0] [])) #v[70]
    (.letOp (n := 77) (.out 0x1167fb (movR64M64Effect 0x1167fb 15 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 78) (.exec 0x1167fb (LoadPre 0x1167fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1167fb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1167fb 15 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x116803 (movR64R64Effect 0x116803 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[77]
    (.letOp (n := 80) (.exec 0x116803 (fun s => s.RIP = 0x116803) (movR64R64Effect 0x116803 0 15) (Reg.operands [.gpr 15] [])) #v[77]
    (.letOp (n := 81) (.out 0x116806 (mulR64Effect 0x116806 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[63, 79]
    (.letOp (n := 82) (.out 0x116806 (mulR64Effect 0x116806 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[63, 79]
    (.letOp (n := 83) (.exec 0x116806 (fun s => s.RIP = 0x116806) (mulR64Effect 0x116806 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[63, 79]
    (.letOp (n := 84) (.out 0x116809 (movR64R64Effect 0x116809 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[82]
    (.letOp (n := 85) (.exec 0x116809 (fun s => s.RIP = 0x116809) (movR64R64Effect 0x116809 7 2) (Reg.operands [.gpr 2] [])) #v[82]
    (.letOp (n := 86) (.out 0x11680c (movR64R64Effect 0x11680c 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[81]
    (.letOp (n := 87) (.exec 0x11680c (fun s => s.RIP = 0x11680c) (movR64R64Effect 0x11680c 8 0) (Reg.operands [.gpr 0] [])) #v[81]
    (.letOp (n := 88) (.out 0x11680f (addR64R64Effect 0x11680f 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[86, 75]
    (.letOp (n := 89) (.out 0x11680f (addR64R64Effect 0x11680f 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[86, 75]
    (.letOp (n := 90) (.exec 0x11680f (fun s => s.RIP = 0x11680f) (addR64R64Effect 0x11680f 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[86, 75]
    (.letOp (n := 91) (.out 0x116812 (atFlags StatusFlags.CF (adcR64R64Effect 0x116812 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[84, 73, 89]
    (.letOp (n := 92) (.exec 0x116812 (fun s => s.RIP = 0x116812) (atFlags StatusFlags.CF (adcR64R64Effect 0x116812 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[84, 73, 89]
    (b_l1167bf_1))))))))))))))))))))))))))))))))))))))))

def bytes_l1167bf : List UInt8 :=
  [0x48, 0x8B, 0x5C, 0x24, 0x48, 0x4C, 0x8B, 0x64, 0x24, 0x40, 0x4C, 0x8B, 0x5C, 0x24, 0x38, 0x4C,
    0x89, 0x5C, 0x24, 0x68, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x48, 0x89, 0x4C, 0x24, 0x70, 0x48, 0x8B,
    0x7C, 0x24, 0x30, 0x48, 0x89, 0x7C, 0x24, 0x50, 0x4C, 0x8B, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x8B, 0xBC, 0x24,
    0xD0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0,
    0x49, 0x01, 0xF0, 0x48, 0x11, 0xCF] ++ bytes_l1167bf_1

theorem code_l1167bf : ∀ x ∈ codeRange 0x1167bf bytes_l1167bf, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x167bf 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1167bf_1

@[cfg_block] def b_l116bd8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x116bd8 (movR64M64Effect 0x116bd8 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x116bd8 (LoadPre 0x116bd8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x116bd8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116bd8 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x116bdd (StorePre 0x116bdd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x116bdd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116bdd 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x116be2 (movR64M64Effect 0x116be2 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x116be2 (LoadPre 0x116be2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x116be2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116be2 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x116be7 (StorePre 0x116be7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x116be7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116be7 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x116bec (movR64M64Effect 0x116bec 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x116bec (LoadPre 0x116bec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x116bec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116bec 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x116bf1 (StorePre 0x116bf1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x116bf1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116bf1 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x116bf6 (movR64M64Effect 0x116bf6 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x116bf6 (LoadPre 0x116bf6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x116bf6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116bf6 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x116bfb (movR64M64Effect 0x116bfb 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x116bfb (LoadPre 0x116bfb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x116bfb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116bfb 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x116c00 (StorePre 0x116c00 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x116c00 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116c00 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x116c05 (StorePre 0x116c05 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x116c05 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x116c05 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x116c09 (movR64R64Effect 0x116c09 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x116c09 (fun s => s.RIP = 0x116c09) (movR64R64Effect 0x116c09 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x116c0c (movR64R64Effect 0x116c0c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x116c0c (fun s => s.RIP = 0x116c0c) (movR64R64Effect 0x116c0c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x116c0f (callEffect (fun _ => 0x1145f0) 0x116c14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x116c0f (PushPre 0x116c0f 5) (callEffect (fun _ => 0x1145f0) 0x116c14) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x116c14⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l116c14, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l116bd8 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xDC, 0xD9, 0xFF, 0xFF]

theorem code_l116bd8 : ∀ x ∈ codeRange 0x116bd8 bytes_l116bd8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x16bd8 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l116c14_12 : Block Op Label signature Reg.count 573 :=
  .letOp (n := 573) (.exec 0x117014 (StorePre 0x117014 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117014 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117014 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[571, 4]
    (.letOp (n := 574) (.out 0x117019 (movR64R64Effect 0x117019 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[571]
    (.letOp (n := 575) (.exec 0x117019 (fun s => s.RIP = 0x117019) (movR64R64Effect 0x117019 13 3) (Reg.operands [.gpr 3] [])) #v[571]
    (.letOp (n := 576) (.out 0x11701c (andR64R64Effect 0x11701c 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[543, 532]
    (.letOp (n := 577) (.exec 0x11701c (fun s => s.RIP = 0x11701c) (andR64R64Effect 0x11701c 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[543, 532]
    (.letOp (n := 578) (.exec 0x11701f (StorePre 0x11701f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11701f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11701f 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[576, 4]
    (.letOp (n := 579) (.out 0x117024 (movR64R64Effect 0x117024 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[576]
    (.letOp (n := 580) (.exec 0x117024 (fun s => s.RIP = 0x117024) (movR64R64Effect 0x117024 3 7) (Reg.operands [.gpr 7] [])) #v[576]
    (.letOp (n := 581) (.exec 0x117027 (StorePre 0x117027 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117027 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117027 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[559, 4]
    (.letOp (n := 582) (.out 0x11702c (leaR64Effect 0x11702c 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 583) (.exec 0x11702c (fun s => s.RIP = 0x11702c) (leaR64Effect 0x11702c 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 584) (.out 0x117031 (movR64R64Effect 0x117031 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 585) (.exec 0x117031 (fun s => s.RIP = 0x117031) (movR64R64Effect 0x117031 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 586) (.out 0x117034 (movR64R64Effect 0x117034 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[582]
    (.letOp (n := 587) (.exec 0x117034 (fun s => s.RIP = 0x117034) (movR64R64Effect 0x117034 7 5) (Reg.operands [.gpr 5] [])) #v[582]
    (.letOp (n := 588) (.out 0x117037 (movR64R64Effect 0x117037 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[584]
    (.letOp (n := 589) (.exec 0x117037 (fun s => s.RIP = 0x117037) (movR64R64Effect 0x117037 6 14) (Reg.operands [.gpr 14] [])) #v[584]
    (.letOp (n := 590) (.out 0x11703a (callEffect (fun _ => 0x1145f0) 0x11703f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 591) (.exec 0x11703a (PushPre 0x11703a 5) (callEffect (fun _ => 0x1145f0) 0x11703f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 592) (.const ⟨64, 0x11703f⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 551), (1, 564), (2, 559), (3, 579), (4, 590), (5, 582), (6, 588), (7, 586), (8, 532), (9, 493), (10, 459), (11, 505), (12, 473), (13, 574), (14, 584), (15, 568), (22, 22), (39, 39), (50, 50), (51, 51)] 593⟩ { target := .l11703f, kept := #v[], arity := rfl, guard := some (Fin.last 592) })))))))))))))))))))))

def bytes_l116c14_12 : List UInt8 :=
  [0x48, 0x89, 0x5C, 0x24, 0x10, 0x49, 0x89, 0xDD, 0x4C, 0x21, 0xC7, 0x48, 0x89, 0x7C, 0x24, 0x18,
    0x48, 0x89, 0xFB, 0x48, 0x89, 0x54, 0x24, 0x20, 0x48, 0x8D, 0x6C, 0x24, 0x28, 0x49, 0x89, 0xE6,
    0x48, 0x89, 0xEF, 0x4C, 0x89, 0xF6, 0xE8, 0xB1, 0xD5, 0xFF, 0xFF]

theorem code_l116c14_12 : ∀ x ∈ codeRange 0x117014 bytes_l116c14_12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17014 43 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l116c14_11 : Block Op Label signature Reg.count 536 :=
  .letOp (n := 536) (.out 0x116fc0 (andR64R64Effect 0x116fc0 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[534, 532]
    (.letOp (n := 537) (.exec 0x116fc0 (fun s => s.RIP = 0x116fc0) (andR64R64Effect 0x116fc0 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[534, 532]
    (.letOp (n := 538) (.out 0x116fc3 (addR64R64Effect 0x116fc3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[529, 536]
    (.letOp (n := 539) (.out 0x116fc3 (addR64R64Effect 0x116fc3 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[529, 536]
    (.letOp (n := 540) (.exec 0x116fc3 (fun s => s.RIP = 0x116fc3) (addR64R64Effect 0x116fc3 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[529, 536]
    (.letOp (n := 541) (.out 0x116fc6 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116fc6 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[527, 539]
    (.letOp (n := 542) (.exec 0x116fc6 (fun s => s.RIP = 0x116fc6) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116fc6 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[527, 539]
    (.letOp (n := 543) (.out 0x116fca (addR64R64Effect 0x116fca 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[538, 522]
    (.letOp (n := 544) (.out 0x116fca (addR64R64Effect 0x116fca 7 6) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 6] []) (.flag .CF)) #v[538, 522]
    (.letOp (n := 545) (.exec 0x116fca (fun s => s.RIP = 0x116fca) (addR64R64Effect 0x116fca 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[538, 522]
    (.letOp (n := 546) (.out 0x116fcd (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116fcd 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[541, 544]
    (.letOp (n := 547) (.exec 0x116fcd (fun s => s.RIP = 0x116fcd) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116fcd 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[541, 544]
    (.letOp (n := 548) (.out 0x116fd1 (shldR64R64Effect 0x116fd1 5 2 7 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[546, 543]
    (.letOp (n := 549) (.exec 0x116fd1 (fun s => s.RIP = 0x116fd1) (shldR64R64Effect 0x116fd1 5 2 7 12) (Reg.operands [.gpr 2, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[546, 543]
    (.letOp (n := 550) (.exec 0x116fd6 (StorePre 0x116fd6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x116fd6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116fd6 10 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[459, 4]
    (.letOp (n := 551) (.out 0x116fdb (movR64Imm64Effect 0x116fdb 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 552) (.exec 0x116fdb (fun s => s.RIP = 0x116fdb) (movR64Imm64Effect 0x116fdb 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 553) (.out 0x116fe5 (movR64M64Effect 0x116fe5 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 554) (.exec 0x116fe5 (LoadPre 0x116fe5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x116fe5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116fe5 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 555) (.out 0x116fea (andR64R64Effect 0x116fea 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[553, 551]
    (.letOp (n := 556) (.exec 0x116fea (fun s => s.RIP = 0x116fea) (andR64R64Effect 0x116fea 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[553, 551]
    (.letOp (n := 557) (.out 0x116fed (addR64R64Effect 0x116fed 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[555, 548]
    (.letOp (n := 558) (.exec 0x116fed (fun s => s.RIP = 0x116fed) (addR64R64Effect 0x116fed 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[555, 548]
    (.letOp (n := 559) (.out 0x116ff0 (movR64R64Effect 0x116ff0 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[557]
    (.letOp (n := 560) (.exec 0x116ff0 (fun s => s.RIP = 0x116ff0) (movR64R64Effect 0x116ff0 2 1) (Reg.operands [.gpr 1] [])) #v[557]
    (.letOp (n := 561) (.exec 0x116ff3 (StorePre 0x116ff3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x116ff3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116ff3 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[557, 4]
    (.letOp (n := 562) (.out 0x116ff8 (movR64M64Effect 0x116ff8 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 563) (.exec 0x116ff8 (LoadPre 0x116ff8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x116ff8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116ff8 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 564) (.out 0x116ffd (andR64R64Effect 0x116ffd 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[562, 532]
    (.letOp (n := 565) (.exec 0x116ffd (fun s => s.RIP = 0x116ffd) (andR64R64Effect 0x116ffd 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[562, 532]
    (.letOp (n := 566) (.exec 0x117000 (StorePre 0x117000 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x117000 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117000 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[564, 4]
    (.letOp (n := 567) (.exec 0x117005 (StorePre 0x117005 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117005 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117005 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[564, 4]
    (.letOp (n := 568) (.out 0x117009 (andR64R64Effect 0x117009 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[424, 532]
    (.letOp (n := 569) (.exec 0x117009 (fun s => s.RIP = 0x117009) (andR64R64Effect 0x117009 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[424, 532]
    (.letOp (n := 570) (.exec 0x11700c (StorePre 0x11700c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11700c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11700c 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[568, 4]
    (.letOp (n := 571) (.out 0x117011 (andR64R64Effect 0x117011 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[515, 532]
    (.letOp (n := 572) (.exec 0x117011 (fun s => s.RIP = 0x117011) (andR64R64Effect 0x117011 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[515, 532]
    (b_l116c14_12)))))))))))))))))))))))))))))))))))))

def bytes_l116c14_11 : List UInt8 :=
  [0x4C, 0x21, 0xC0, 0x48, 0x01, 0xC7, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x01, 0xF7, 0x48, 0x83, 0xD2,
    0x00, 0x48, 0x0F, 0xA4, 0xFA, 0x0C, 0x4C, 0x89, 0x54, 0x24, 0x18, 0x48, 0xB8, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x50, 0x48, 0x21, 0xC1, 0x48, 0x01, 0xD1,
    0x48, 0x89, 0xCA, 0x48, 0x89, 0x4C, 0x24, 0x50, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0x4C, 0x21, 0xC1,
    0x48, 0x89, 0x4C, 0x24, 0x58, 0x48, 0x89, 0x0C, 0x24, 0x4D, 0x21, 0xC7, 0x4C, 0x89, 0x7C, 0x24,
    0x08, 0x4C, 0x21, 0xC3] ++ bytes_l116c14_12

theorem code_l116c14_11 : ∀ x ∈ codeRange 0x116fc0 bytes_l116c14_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16fc0 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116c14_12

def b_l116c14_10 : Block Op Label signature Reg.count 491 :=
  .letOp (n := 491) (.out 0x116f6b (andR64R64Effect 0x116f6b 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[487, 489]
    (.letOp (n := 492) (.exec 0x116f6b (fun s => s.RIP = 0x116f6b) (andR64R64Effect 0x116f6b 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[487, 489]
    (.letOp (n := 493) (.out 0x116f6e (movR64Imm64Effect 0x116f6e 9 0x1000003d10) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 494) (.exec 0x116f6e (fun s => s.RIP = 0x116f6e) (movR64Imm64Effect 0x116f6e 9 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 495) (.out 0x116f78 (mulR64Effect 0x116f78 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[493, 491]
    (.letOp (n := 496) (.out 0x116f78 (mulR64Effect 0x116f78 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[493, 491]
    (.letOp (n := 497) (.exec 0x116f78 (fun s => s.RIP = 0x116f78) (mulR64Effect 0x116f78 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[493, 491]
    (.letOp (n := 498) (.out 0x116f7b (movR64R64Effect 0x116f7b 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[495]
    (.letOp (n := 499) (.exec 0x116f7b (fun s => s.RIP = 0x116f7b) (movR64R64Effect 0x116f7b 3 0) (Reg.operands [.gpr 0] [])) #v[495]
    (.letOp (n := 500) (.out 0x116f7e (addR64R64Effect 0x116f7e 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[446, 437]
    (.letOp (n := 501) (.out 0x116f7e (addR64R64Effect 0x116f7e 11 14) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 14] []) (.flag .CF)) #v[446, 437]
    (.letOp (n := 502) (.exec 0x116f7e (fun s => s.RIP = 0x116f7e) (addR64R64Effect 0x116f7e 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[446, 437]
    (.letOp (n := 503) (.out 0x116f81 (atFlags StatusFlags.CF (adcR64M64Effect 0x116f81 6 (.sib 4 none 0 (.d8 0x68)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[444, 4, 501]
    (.letOp (n := 504) (.exec 0x116f81 (LoadPre 0x116f81 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116f81 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x116f81 6 (.sib 4 none 0 (.d8 0x68)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[444, 4, 501]
    (.letOp (n := 505) (.out 0x116f86 (addR64R64Effect 0x116f86 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[500, 455]
    (.letOp (n := 506) (.out 0x116f86 (addR64R64Effect 0x116f86 11 1) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 1] []) (.flag .CF)) #v[500, 455]
    (.letOp (n := 507) (.exec 0x116f86 (fun s => s.RIP = 0x116f86) (addR64R64Effect 0x116f86 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[500, 455]
    (.letOp (n := 508) (.out 0x116f89 (atFlags StatusFlags.CF (adcR64R64Effect 0x116f89 6 13)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[503, 453, 506]
    (.letOp (n := 509) (.exec 0x116f89 (fun s => s.RIP = 0x116f89) (atFlags StatusFlags.CF (adcR64R64Effect 0x116f89 6 13)) (Reg.operands [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[503, 453, 506]
    (.letOp (n := 510) (.out 0x116f8c (addR64R64Effect 0x116f8c 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[498, 505]
    (.letOp (n := 511) (.out 0x116f8c (addR64R64Effect 0x116f8c 3 11) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 11] []) (.flag .CF)) #v[498, 505]
    (.letOp (n := 512) (.exec 0x116f8c (fun s => s.RIP = 0x116f8c) (addR64R64Effect 0x116f8c 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[498, 505]
    (.letOp (n := 513) (.out 0x116f8f (atFlags StatusFlags.CF (adcR64R64Effect 0x116f8f 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[508, 496, 511]
    (.letOp (n := 514) (.exec 0x116f8f (fun s => s.RIP = 0x116f8f) (atFlags StatusFlags.CF (adcR64R64Effect 0x116f8f 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[508, 496, 511]
    (.letOp (n := 515) (.out 0x116f92 (addR64R64Effect 0x116f92 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[510, 429]
    (.letOp (n := 516) (.out 0x116f92 (addR64R64Effect 0x116f92 3 7) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 7] []) (.flag .CF)) #v[510, 429]
    (.letOp (n := 517) (.exec 0x116f92 (fun s => s.RIP = 0x116f92) (addR64R64Effect 0x116f92 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[510, 429]
    (.letOp (n := 518) (.out 0x116f95 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116f95 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[513, 516]
    (.letOp (n := 519) (.exec 0x116f95 (fun s => s.RIP = 0x116f95) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116f95 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[513, 516]
    (.letOp (n := 520) (.out 0x116f99 (shldR64R64Effect 0x116f99 5 8 5 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[485, 482]
    (.letOp (n := 521) (.exec 0x116f99 (fun s => s.RIP = 0x116f99) (shldR64R64Effect 0x116f99 5 8 5 12) (Reg.operands [.gpr 8, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[485, 482]
    (.letOp (n := 522) (.out 0x116f9e (shldR64R64Effect 0x116f9e 5 6 3 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[518, 515]
    (.letOp (n := 523) (.exec 0x116f9e (fun s => s.RIP = 0x116f9e) (shldR64R64Effect 0x116f9e 5 6 3 12) (Reg.operands [.gpr 6, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[518, 515]
    (.letOp (n := 524) (.out 0x116fa3 (movR64R64Effect 0x116fa3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[520]
    (.letOp (n := 525) (.exec 0x116fa3 (fun s => s.RIP = 0x116fa3) (movR64R64Effect 0x116fa3 0 8) (Reg.operands [.gpr 8] [])) #v[520]
    (.letOp (n := 526) (.out 0x116fa6 (mulR64Effect 0x116fa6 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[493, 524]
    (.letOp (n := 527) (.out 0x116fa6 (mulR64Effect 0x116fa6 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[493, 524]
    (.letOp (n := 528) (.exec 0x116fa6 (fun s => s.RIP = 0x116fa6) (mulR64Effect 0x116fa6 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[493, 524]
    (.letOp (n := 529) (.out 0x116fa9 (movR64R64Effect 0x116fa9 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[526]
    (.letOp (n := 530) (.exec 0x116fa9 (fun s => s.RIP = 0x116fa9) (movR64R64Effect 0x116fa9 7 0) (Reg.operands [.gpr 0] [])) #v[526]
    (.letOp (n := 531) (.exec 0x116fac (StorePre 0x116fac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x116fac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116fac 12 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[473, 4]
    (.letOp (n := 532) (.out 0x116fb1 (movR64Imm64Effect 0x116fb1 8 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 533) (.exec 0x116fb1 (fun s => s.RIP = 0x116fb1) (movR64Imm64Effect 0x116fb1 8 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 534) (.out 0x116fbb (movR64M64Effect 0x116fbb 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 535) (.exec 0x116fbb (LoadPre 0x116fbb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x116fbb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116fbb 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l116c14_11)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116c14_10 : List UInt8 :=
  [0x48, 0x21, 0xD0, 0x49, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE1,
    0x48, 0x89, 0xC3, 0x4D, 0x01, 0xF3, 0x48, 0x13, 0x74, 0x24, 0x68, 0x49, 0x01, 0xCB, 0x4C, 0x11,
    0xEE, 0x4C, 0x01, 0xDB, 0x48, 0x11, 0xD6, 0x48, 0x01, 0xFB, 0x48, 0x83, 0xD6, 0x00, 0x49, 0x0F,
    0xA4, 0xE8, 0x0C, 0x48, 0x0F, 0xA4, 0xDE, 0x0C, 0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE1, 0x48, 0x89,
    0xC7, 0x4C, 0x89, 0x64, 0x24, 0x20, 0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x48, 0x8B, 0x44, 0x24, 0x78] ++ bytes_l116c14_11

theorem code_l116c14_10 : ∀ x ∈ codeRange 0x116f6b bytes_l116c14_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16f6b 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116c14_11

def b_l116c14_9 : Block Op Label signature Reg.count 446 :=
  .letOp (n := 446) (.out 0x116f16 (movR64R64Effect 0x116f16 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[441]
    (.letOp (n := 447) (.exec 0x116f16 (fun s => s.RIP = 0x116f16) (movR64R64Effect 0x116f16 11 0) (Reg.operands [.gpr 0] [])) #v[441]
    (.letOp (n := 448) (.out 0x116f19 (movR64M64Effect 0x116f19 0 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 449) (.exec 0x116f19 (LoadPre 0x116f19 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x116f19 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116f19 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 450) (.out 0x116f21 (mulM64Effect 0x116f21 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[448, 4]
    (.letOp (n := 451) (.out 0x116f21 (mulM64Effect 0x116f21 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[448, 4]
    (.letOp (n := 452) (.exec 0x116f21 (LoadPre 0x116f21 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x116f21 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x116f21 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[448, 4]
    (.letOp (n := 453) (.out 0x116f26 (movR64R64Effect 0x116f26 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[451]
    (.letOp (n := 454) (.exec 0x116f26 (fun s => s.RIP = 0x116f26) (movR64R64Effect 0x116f26 13 2) (Reg.operands [.gpr 2] [])) #v[451]
    (.letOp (n := 455) (.out 0x116f29 (movR64R64Effect 0x116f29 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[450]
    (.letOp (n := 456) (.exec 0x116f29 (fun s => s.RIP = 0x116f29) (movR64R64Effect 0x116f29 1 0) (Reg.operands [.gpr 0] [])) #v[450]
    (.letOp (n := 457) (.out 0x116f2c (movR64R64Effect 0x116f2c 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[359]
    (.letOp (n := 458) (.exec 0x116f2c (fun s => s.RIP = 0x116f2c) (movR64R64Effect 0x116f2c 0 12) (Reg.operands [.gpr 12] [])) #v[359]
    (.letOp (n := 459) (.out 0x116f2f (movR64M64Effect 0x116f2f 10 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 460) (.exec 0x116f2f (LoadPre 0x116f2f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x116f2f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116f2f 10 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 461) (.out 0x116f37 (mulR64Effect 0x116f37 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[459, 457]
    (.letOp (n := 462) (.out 0x116f37 (mulR64Effect 0x116f37 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[459, 457]
    (.letOp (n := 463) (.exec 0x116f37 (fun s => s.RIP = 0x116f37) (mulR64Effect 0x116f37 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[459, 457]
    (.letOp (n := 464) (.out 0x116f3a (movR64R64Effect 0x116f3a 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[462]
    (.letOp (n := 465) (.exec 0x116f3a (fun s => s.RIP = 0x116f3a) (movR64R64Effect 0x116f3a 8 2) (Reg.operands [.gpr 2] [])) #v[462]
    (.letOp (n := 466) (.out 0x116f3d (movR64R64Effect 0x116f3d 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[461]
    (.letOp (n := 467) (.exec 0x116f3d (fun s => s.RIP = 0x116f3d) (movR64R64Effect 0x116f3d 3 0) (Reg.operands [.gpr 0] [])) #v[461]
    (.letOp (n := 468) (.out 0x116f40 (movR64M64Effect 0x116f40 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 469) (.exec 0x116f40 (LoadPre 0x116f40 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x116f40 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116f40 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 470) (.out 0x116f48 (mulR64Effect 0x116f48 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[291, 468]
    (.letOp (n := 471) (.out 0x116f48 (mulR64Effect 0x116f48 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[291, 468]
    (.letOp (n := 472) (.exec 0x116f48 (fun s => s.RIP = 0x116f48) (mulR64Effect 0x116f48 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[291, 468]
    (.letOp (n := 473) (.out 0x116f4b (movR64R64Effect 0x116f4b 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 5] []) (.reg (.gpr 12))) #v[291]
    (.letOp (n := 474) (.exec 0x116f4b (fun s => s.RIP = 0x116f4b) (movR64R64Effect 0x116f4b 12 5) (Reg.operands [.gpr 5] [])) #v[291]
    (.letOp (n := 475) (.out 0x116f4e (movR64R64Effect 0x116f4e 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[470]
    (.letOp (n := 476) (.exec 0x116f4e (fun s => s.RIP = 0x116f4e) (movR64R64Effect 0x116f4e 5 0) (Reg.operands [.gpr 0] [])) #v[470]
    (.letOp (n := 477) (.out 0x116f51 (addR64R64Effect 0x116f51 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[475, 466]
    (.letOp (n := 478) (.out 0x116f51 (addR64R64Effect 0x116f51 5 3) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 3] []) (.flag .CF)) #v[475, 466]
    (.letOp (n := 479) (.exec 0x116f51 (fun s => s.RIP = 0x116f51) (addR64R64Effect 0x116f51 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[475, 466]
    (.letOp (n := 480) (.out 0x116f54 (atFlags StatusFlags.CF (adcR64R64Effect 0x116f54 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[464, 471, 478]
    (.letOp (n := 481) (.exec 0x116f54 (fun s => s.RIP = 0x116f54) (atFlags StatusFlags.CF (adcR64R64Effect 0x116f54 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[464, 471, 478]
    (.letOp (n := 482) (.out 0x116f57 (addR64R64Effect 0x116f57 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[477, 401]
    (.letOp (n := 483) (.out 0x116f57 (addR64R64Effect 0x116f57 5 9) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 9] []) (.flag .CF)) #v[477, 401]
    (.letOp (n := 484) (.exec 0x116f57 (fun s => s.RIP = 0x116f57) (addR64R64Effect 0x116f57 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[477, 401]
    (.letOp (n := 485) (.out 0x116f5a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116f5a 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[480, 483]
    (.letOp (n := 486) (.exec 0x116f5a (fun s => s.RIP = 0x116f5a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116f5a 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[480, 483]
    (.letOp (n := 487) (.out 0x116f5e (movR64R64Effect 0x116f5e 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[482]
    (.letOp (n := 488) (.exec 0x116f5e (fun s => s.RIP = 0x116f5e) (movR64R64Effect 0x116f5e 0 5) (Reg.operands [.gpr 5] [])) #v[482]
    (.letOp (n := 489) (.out 0x116f61 (movR64Imm64Effect 0x116f61 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 490) (.exec 0x116f61 (fun s => s.RIP = 0x116f61) (movR64Imm64Effect 0x116f61 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l116c14_10)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116c14_9 : List UInt8 :=
  [0x49, 0x89, 0xC3, 0x48, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x70,
    0x49, 0x89, 0xD5, 0x48, 0x89, 0xC1, 0x4C, 0x89, 0xE0, 0x4C, 0x8B, 0x94, 0x24, 0xC0, 0x00, 0x00,
    0x00, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD0, 0x48, 0x89, 0xC3, 0x48, 0x8B, 0x84, 0x24, 0x00, 0x01,
    0x00, 0x00, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xEC, 0x48, 0x89, 0xC5, 0x48, 0x01, 0xDD, 0x49, 0x11,
    0xD0, 0x4C, 0x01, 0xCD, 0x49, 0x83, 0xD0, 0x00, 0x48, 0x89, 0xE8, 0x48, 0xBA, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x0F, 0x00] ++ bytes_l116c14_10

theorem code_l116c14_9 : ∀ x ∈ codeRange 0x116f16 bytes_l116c14_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16f16 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116c14_10

def b_l116c14_8 : Block Op Label signature Reg.count 401 :=
  .letOp (n := 401) (.out 0x116eb6 (shldR64R64Effect 0x116eb6 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[399, 396]
    (.letOp (n := 402) (.exec 0x116eb6 (fun s => s.RIP = 0x116eb6) (shldR64R64Effect 0x116eb6 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[399, 396]
    (.letOp (n := 403) (.out 0x116ebb (movR64Imm64Effect 0x116ebb 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 404) (.exec 0x116ebb (fun s => s.RIP = 0x116ebb) (movR64Imm64Effect 0x116ebb 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 405) (.out 0x116ec5 (andR64R64Effect 0x116ec5 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[396, 403]
    (.letOp (n := 406) (.exec 0x116ec5 (fun s => s.RIP = 0x116ec5) (andR64R64Effect 0x116ec5 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[396, 403]
    (.letOp (n := 407) (.out 0x116ec8 (movR64Imm64Effect 0x116ec8 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 408) (.exec 0x116ec8 (fun s => s.RIP = 0x116ec8) (movR64Imm64Effect 0x116ec8 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 409) (.out 0x116ed2 (mulR64Effect 0x116ed2 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[407, 405]
    (.letOp (n := 410) (.out 0x116ed2 (mulR64Effect 0x116ed2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[407, 405]
    (.letOp (n := 411) (.exec 0x116ed2 (fun s => s.RIP = 0x116ed2) (mulR64Effect 0x116ed2 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[407, 405]
    (.letOp (n := 412) (.out 0x116ed5 (movR64R64Effect 0x116ed5 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[409]
    (.letOp (n := 413) (.exec 0x116ed5 (fun s => s.RIP = 0x116ed5) (movR64R64Effect 0x116ed5 15 0) (Reg.operands [.gpr 0] [])) #v[409]
    (.letOp (n := 414) (.out 0x116ed8 (addR64M64Effect 0x116ed8 14 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[357, 4]
    (.letOp (n := 415) (.out 0x116ed8 (addR64M64Effect 0x116ed8 14 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 4] []) (.flag .CF)) #v[357, 4]
    (.letOp (n := 416) (.exec 0x116ed8 (LoadPre 0x116ed8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x116ed8 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x116ed8 14 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[357, 4]
    (.letOp (n := 417) (.out 0x116ee0 (atFlags StatusFlags.CF (adcR64M64Effect 0x116ee0 7 (.sib 4 none 0 (.d32 0x80)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[355, 4, 415]
    (.letOp (n := 418) (.exec 0x116ee0 (LoadPre 0x116ee0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x116ee0 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x116ee0 7 (.sib 4 none 0 (.d32 0x80)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[355, 4, 415]
    (.letOp (n := 419) (.out 0x116ee8 (addR64R64Effect 0x116ee8 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[412, 414]
    (.letOp (n := 420) (.out 0x116ee8 (addR64R64Effect 0x116ee8 15 14) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 14] []) (.flag .CF)) #v[412, 414]
    (.letOp (n := 421) (.exec 0x116ee8 (fun s => s.RIP = 0x116ee8) (addR64R64Effect 0x116ee8 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[412, 414]
    (.letOp (n := 422) (.out 0x116eeb (atFlags StatusFlags.CF (adcR64R64Effect 0x116eeb 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[417, 410, 420]
    (.letOp (n := 423) (.exec 0x116eeb (fun s => s.RIP = 0x116eeb) (atFlags StatusFlags.CF (adcR64R64Effect 0x116eeb 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[417, 410, 420]
    (.letOp (n := 424) (.out 0x116eee (addR64R64Effect 0x116eee 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[419, 337]
    (.letOp (n := 425) (.out 0x116eee (addR64R64Effect 0x116eee 15 13) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 13] []) (.flag .CF)) #v[419, 337]
    (.letOp (n := 426) (.exec 0x116eee (fun s => s.RIP = 0x116eee) (addR64R64Effect 0x116eee 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[419, 337]
    (.letOp (n := 427) (.out 0x116ef1 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116ef1 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[422, 425]
    (.letOp (n := 428) (.exec 0x116ef1 (fun s => s.RIP = 0x116ef1) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116ef1 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[422, 425]
    (.letOp (n := 429) (.out 0x116ef5 (shldR64R64Effect 0x116ef5 5 7 15 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[427, 424]
    (.letOp (n := 430) (.exec 0x116ef5 (fun s => s.RIP = 0x116ef5) (shldR64R64Effect 0x116ef5 5 7 15 12) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[427, 424]
    (.letOp (n := 431) (.out 0x116efa (movR64R64Effect 0x116efa 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[379]
    (.letOp (n := 432) (.exec 0x116efa (fun s => s.RIP = 0x116efa) (movR64R64Effect 0x116efa 0 6) (Reg.operands [.gpr 6] [])) #v[379]
    (.letOp (n := 433) (.out 0x116efd (mulR64Effect 0x116efd 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[341, 431]
    (.letOp (n := 434) (.out 0x116efd (mulR64Effect 0x116efd 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[341, 431]
    (.letOp (n := 435) (.exec 0x116efd (fun s => s.RIP = 0x116efd) (mulR64Effect 0x116efd 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[341, 431]
    (.letOp (n := 436) (.exec 0x116f00 (StorePre 0x116f00 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116f00 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116f00 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[434, 4]
    (.letOp (n := 437) (.out 0x116f05 (movR64R64Effect 0x116f05 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[433]
    (.letOp (n := 438) (.exec 0x116f05 (fun s => s.RIP = 0x116f05) (movR64R64Effect 0x116f05 14 0) (Reg.operands [.gpr 0] [])) #v[433]
    (.letOp (n := 439) (.out 0x116f08 (movR64M64Effect 0x116f08 0 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 440) (.exec 0x116f08 (LoadPre 0x116f08 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x116f08 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116f08 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 441) (.out 0x116f10 (mulR64Effect 0x116f10 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[350, 439]
    (.letOp (n := 442) (.out 0x116f10 (mulR64Effect 0x116f10 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[350, 439]
    (.letOp (n := 443) (.exec 0x116f10 (fun s => s.RIP = 0x116f10) (mulR64Effect 0x116f10 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[350, 439]
    (.letOp (n := 444) (.out 0x116f13 (movR64R64Effect 0x116f13 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[442]
    (.letOp (n := 445) (.exec 0x116f13 (fun s => s.RIP = 0x116f13) (movR64R64Effect 0x116f13 6 2) (Reg.operands [.gpr 2] [])) #v[442]
    (b_l116c14_9)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116c14_8 : List UInt8 :=
  [0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48,
    0x21, 0xC8, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49,
    0x89, 0xC7, 0x4C, 0x03, 0xB4, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0x13, 0xBC, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x4D, 0x01, 0xF7, 0x48, 0x11, 0xD7, 0x4D, 0x01, 0xEF, 0x48, 0x83, 0xD7, 0x00, 0x4C,
    0x0F, 0xA4, 0xFF, 0x0C, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0x54, 0x24, 0x68, 0x49,
    0x89, 0xC6, 0x48, 0x8B, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE3, 0x48, 0x89, 0xD6] ++ bytes_l116c14_9

theorem code_l116c14_8 : ∀ x ∈ codeRange 0x116eb6 bytes_l116c14_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16eb6 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116c14_9

def b_l116c14_7 : Block Op Label signature Reg.count 355 :=
  .letOp (n := 355) (.out 0x116e6d (movR64R64Effect 0x116e6d 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[353]
    (.letOp (n := 356) (.exec 0x116e6d (fun s => s.RIP = 0x116e6d) (movR64R64Effect 0x116e6d 7 2) (Reg.operands [.gpr 2] [])) #v[353]
    (.letOp (n := 357) (.out 0x116e70 (movR64R64Effect 0x116e70 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[352]
    (.letOp (n := 358) (.exec 0x116e70 (fun s => s.RIP = 0x116e70) (movR64R64Effect 0x116e70 14 0) (Reg.operands [.gpr 0] [])) #v[352]
    (.letOp (n := 359) (.out 0x116e73 (movR64M64Effect 0x116e73 12 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 360) (.exec 0x116e73 (LoadPre 0x116e73 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x116e73 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116e73 12 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 361) (.out 0x116e7b (movR64R64Effect 0x116e7b 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[359]
    (.letOp (n := 362) (.exec 0x116e7b (fun s => s.RIP = 0x116e7b) (movR64R64Effect 0x116e7b 0 12) (Reg.operands [.gpr 12] [])) #v[359]
    (.letOp (n := 363) (.out 0x116e7e (mulM64Effect 0x116e7e 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[361, 4]
    (.letOp (n := 364) (.out 0x116e7e (mulM64Effect 0x116e7e 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[361, 4]
    (.letOp (n := 365) (.exec 0x116e7e (LoadPre 0x116e7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x116e7e + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x116e7e 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[361, 4]
    (.letOp (n := 366) (.out 0x116e83 (movR64R64Effect 0x116e83 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[364]
    (.letOp (n := 367) (.exec 0x116e83 (fun s => s.RIP = 0x116e83) (movR64R64Effect 0x116e83 1 2) (Reg.operands [.gpr 2] [])) #v[364]
    (.letOp (n := 368) (.out 0x116e86 (movR64R64Effect 0x116e86 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[363]
    (.letOp (n := 369) (.exec 0x116e86 (fun s => s.RIP = 0x116e86) (movR64R64Effect 0x116e86 3 0) (Reg.operands [.gpr 0] [])) #v[363]
    (.letOp (n := 370) (.out 0x116e89 (movR64R64Effect 0x116e89 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[265]
    (.letOp (n := 371) (.exec 0x116e89 (fun s => s.RIP = 0x116e89) (movR64R64Effect 0x116e89 0 6) (Reg.operands [.gpr 6] [])) #v[265]
    (.letOp (n := 372) (.out 0x116e8c (mulR64Effect 0x116e8c 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[278, 370]
    (.letOp (n := 373) (.out 0x116e8c (mulR64Effect 0x116e8c 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[278, 370]
    (.letOp (n := 374) (.exec 0x116e8c (fun s => s.RIP = 0x116e8c) (mulR64Effect 0x116e8c 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[278, 370]
    (.letOp (n := 375) (.out 0x116e8f (movR64R64Effect 0x116e8f 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[373]
    (.letOp (n := 376) (.exec 0x116e8f (fun s => s.RIP = 0x116e8f) (movR64R64Effect 0x116e8f 9 2) (Reg.operands [.gpr 2] [])) #v[373]
    (.letOp (n := 377) (.out 0x116e92 (movR64R64Effect 0x116e92 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[372]
    (.letOp (n := 378) (.exec 0x116e92 (fun s => s.RIP = 0x116e92) (movR64R64Effect 0x116e92 15 0) (Reg.operands [.gpr 0] [])) #v[372]
    (.letOp (n := 379) (.out 0x116e95 (movR64M64Effect 0x116e95 6 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 380) (.exec 0x116e95 (LoadPre 0x116e95 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x116e95 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116e95 6 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 381) (.out 0x116e9d (movR64R64Effect 0x116e9d 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[379]
    (.letOp (n := 382) (.exec 0x116e9d (fun s => s.RIP = 0x116e9d) (movR64R64Effect 0x116e9d 0 6) (Reg.operands [.gpr 6] [])) #v[379]
    (.letOp (n := 383) (.out 0x116ea0 (mulR64Effect 0x116ea0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[291, 381]
    (.letOp (n := 384) (.out 0x116ea0 (mulR64Effect 0x116ea0 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[291, 381]
    (.letOp (n := 385) (.exec 0x116ea0 (fun s => s.RIP = 0x116ea0) (mulR64Effect 0x116ea0 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[291, 381]
    (.letOp (n := 386) (.out 0x116ea3 (addR64R64Effect 0x116ea3 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[377, 368]
    (.letOp (n := 387) (.out 0x116ea3 (addR64R64Effect 0x116ea3 15 3) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 3] []) (.flag .CF)) #v[377, 368]
    (.letOp (n := 388) (.exec 0x116ea3 (fun s => s.RIP = 0x116ea3) (addR64R64Effect 0x116ea3 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[377, 368]
    (.letOp (n := 389) (.out 0x116ea6 (atFlags StatusFlags.CF (adcR64R64Effect 0x116ea6 9 1)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[375, 366, 387]
    (.letOp (n := 390) (.exec 0x116ea6 (fun s => s.RIP = 0x116ea6) (atFlags StatusFlags.CF (adcR64R64Effect 0x116ea6 9 1)) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[375, 366, 387]
    (.letOp (n := 391) (.out 0x116ea9 (addR64R64Effect 0x116ea9 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[383, 386]
    (.letOp (n := 392) (.out 0x116ea9 (addR64R64Effect 0x116ea9 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[383, 386]
    (.letOp (n := 393) (.exec 0x116ea9 (fun s => s.RIP = 0x116ea9) (addR64R64Effect 0x116ea9 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[383, 386]
    (.letOp (n := 394) (.out 0x116eac (atFlags StatusFlags.CF (adcR64R64Effect 0x116eac 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[389, 384, 392]
    (.letOp (n := 395) (.exec 0x116eac (fun s => s.RIP = 0x116eac) (atFlags StatusFlags.CF (adcR64R64Effect 0x116eac 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[389, 384, 392]
    (.letOp (n := 396) (.out 0x116eaf (addR64R64Effect 0x116eaf 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[391, 316]
    (.letOp (n := 397) (.out 0x116eaf (addR64R64Effect 0x116eaf 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[391, 316]
    (.letOp (n := 398) (.exec 0x116eaf (fun s => s.RIP = 0x116eaf) (addR64R64Effect 0x116eaf 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[391, 316]
    (.letOp (n := 399) (.out 0x116eb2 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116eb2 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[394, 397]
    (.letOp (n := 400) (.exec 0x116eb2 (fun s => s.RIP = 0x116eb2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116eb2 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[394, 397]
    (b_l116c14_8))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116c14_7 : List UInt8 :=
  [0x48, 0x89, 0xD7, 0x49, 0x89, 0xC6, 0x4C, 0x8B, 0xA4, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xE0, 0x48, 0xF7, 0x64, 0x24, 0x70, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC3, 0x48, 0x89, 0xF0, 0x49,
    0xF7, 0xE1, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0xB4, 0x24, 0x38, 0x01, 0x00, 0x00,
    0x48, 0x89, 0xF0, 0x48, 0xF7, 0xE5, 0x49, 0x01, 0xDF, 0x49, 0x11, 0xC9, 0x4C, 0x01, 0xF8, 0x49,
    0x11, 0xD1, 0x4C, 0x01, 0xC0, 0x49, 0x83, 0xD1, 0x00] ++ bytes_l116c14_8

theorem code_l116c14_7 : ∀ x ∈ codeRange 0x116e6d bytes_l116c14_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16e6d 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116c14_8

def b_l116c14_6 : Block Op Label signature Reg.count 314 :=
  .letOp (n := 314) (.out 0x116e03 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116e03 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[309, 312]
    (.letOp (n := 315) (.exec 0x116e03 (fun s => s.RIP = 0x116e03) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116e03 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[309, 312]
    (.letOp (n := 316) (.out 0x116e07 (shldR64R64Effect 0x116e07 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[314, 311]
    (.letOp (n := 317) (.exec 0x116e07 (fun s => s.RIP = 0x116e07) (shldR64R64Effect 0x116e07 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[314, 311]
    (.letOp (n := 318) (.out 0x116e0c (shlR64Effect 0x116e0c 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[311]
    (.letOp (n := 319) (.exec 0x116e0c (fun s => s.RIP = 0x116e0c) (shlR64Effect 0x116e0c 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[311]
    (.letOp (n := 320) (.out 0x116e10 (movR64Imm64Effect 0x116e10 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 321) (.exec 0x116e10 (fun s => s.RIP = 0x116e10) (movR64Imm64Effect 0x116e10 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 322) (.out 0x116e1a (andR64R64Effect 0x116e1a 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[318, 320]
    (.letOp (n := 323) (.exec 0x116e1a (fun s => s.RIP = 0x116e1a) (andR64R64Effect 0x116e1a 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[318, 320]
    (.letOp (n := 324) (.out 0x116e1d (orR64R64Effect 0x116e1d 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[322, 263]
    (.letOp (n := 325) (.exec 0x116e1d (fun s => s.RIP = 0x116e1d) (orR64R64Effect 0x116e1d 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[322, 263]
    (.letOp (n := 326) (.out 0x116e20 (movR64Imm64Effect 0x116e20 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 327) (.exec 0x116e20 (fun s => s.RIP = 0x116e20) (movR64Imm64Effect 0x116e20 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 328) (.out 0x116e2a (mulR64Effect 0x116e2a 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[326, 324]
    (.letOp (n := 329) (.out 0x116e2a (mulR64Effect 0x116e2a 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[326, 324]
    (.letOp (n := 330) (.exec 0x116e2a (fun s => s.RIP = 0x116e2a) (mulR64Effect 0x116e2a 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[326, 324]
    (.letOp (n := 331) (.out 0x116e2d (addR64M64Effect 0x116e2d 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[328, 4]
    (.letOp (n := 332) (.out 0x116e2d (addR64M64Effect 0x116e2d 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[328, 4]
    (.letOp (n := 333) (.exec 0x116e2d (LoadPre 0x116e2d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x116e2d + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x116e2d 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[328, 4]
    (.letOp (n := 334) (.exec 0x116e32 (StorePre 0x116e32 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x116e32 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116e32 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[331, 4]
    (.letOp (n := 335) (.out 0x116e37 (atFlags StatusFlags.CF (adcR64R64Effect 0x116e37 13 2)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[251, 329, 332]
    (.letOp (n := 336) (.exec 0x116e37 (fun s => s.RIP = 0x116e37) (atFlags StatusFlags.CF (adcR64R64Effect 0x116e37 13 2)) (Reg.operands [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[251, 329, 332]
    (.letOp (n := 337) (.out 0x116e3a (shldR64R64Effect 0x116e3a 5 13 0 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[335, 331]
    (.letOp (n := 338) (.exec 0x116e3a (fun s => s.RIP = 0x116e3a) (shldR64R64Effect 0x116e3a 5 13 0 12) (Reg.operands [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[335, 331]
    (.letOp (n := 339) (.out 0x116e3f (movR64R64Effect 0x116e3f 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[287]
    (.letOp (n := 340) (.exec 0x116e3f (fun s => s.RIP = 0x116e3f) (movR64R64Effect 0x116e3f 0 12) (Reg.operands [.gpr 12] [])) #v[287]
    (.letOp (n := 341) (.out 0x116e42 (movR64M64Effect 0x116e42 10 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 342) (.exec 0x116e42 (LoadPre 0x116e42 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116e42 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116e42 10 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 343) (.out 0x116e47 (mulR64Effect 0x116e47 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[341, 339]
    (.letOp (n := 344) (.out 0x116e47 (mulR64Effect 0x116e47 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[341, 339]
    (.letOp (n := 345) (.exec 0x116e47 (fun s => s.RIP = 0x116e47) (mulR64Effect 0x116e47 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[341, 339]
    (.letOp (n := 346) (.exec 0x116e4a (StorePre 0x116e4a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x116e4a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x116e4a 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[344, 4]
    (.letOp (n := 347) (.exec 0x116e52 (StorePre 0x116e52 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x116e52 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x116e52 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[343, 4]
    (.letOp (n := 348) (.out 0x116e5a (movR64M64Effect 0x116e5a 0 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 349) (.exec 0x116e5a (LoadPre 0x116e5a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x116e5a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116e5a 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 350) (.out 0x116e62 (movR64M64Effect 0x116e62 11 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 351) (.exec 0x116e62 (LoadPre 0x116e62 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x116e62 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116e62 11 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 352) (.out 0x116e6a (mulR64Effect 0x116e6a 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[350, 348]
    (.letOp (n := 353) (.out 0x116e6a (mulR64Effect 0x116e6a 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[350, 348]
    (.letOp (n := 354) (.exec 0x116e6a (fun s => s.RIP = 0x116e6a) (mulR64Effect 0x116e6a 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[350, 348]
    (b_l116c14_7)))))))))))))))))))))))))))))))))))))))))

def bytes_l116c14_6 : List UInt8 :=
  [0x49, 0x83, 0xD0, 0x00, 0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xB9, 0xF0,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C, 0x09, 0xF8, 0x48, 0xB9, 0xD1,
    0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x03, 0x44, 0x24, 0x58, 0x48,
    0x89, 0x44, 0x24, 0x58, 0x49, 0x11, 0xD5, 0x49, 0x0F, 0xA4, 0xC5, 0x0C, 0x4C, 0x89, 0xE0, 0x4C,
    0x8B, 0x54, 0x24, 0x68, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x4C,
    0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE3] ++ bytes_l116c14_7

theorem code_l116c14_6 : ∀ x ∈ codeRange 0x116e03 bytes_l116c14_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16e03 106 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116c14_7

def b_l116c14_5 : Block Op Label signature Reg.count 267 :=
  .letOp (n := 267) (.out 0x116db4 (movR64R64Effect 0x116db4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[265]
    (.letOp (n := 268) (.exec 0x116db4 (fun s => s.RIP = 0x116db4) (movR64R64Effect 0x116db4 0 6) (Reg.operands [.gpr 6] [])) #v[265]
    (.letOp (n := 269) (.out 0x116db7 (mulM64Effect 0x116db7 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[267, 4]
    (.letOp (n := 270) (.out 0x116db7 (mulM64Effect 0x116db7 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[267, 4]
    (.letOp (n := 271) (.exec 0x116db7 (LoadPre 0x116db7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x116db7 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x116db7 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[267, 4]
    (.letOp (n := 272) (.out 0x116dbc (movR64R64Effect 0x116dbc 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[270]
    (.letOp (n := 273) (.exec 0x116dbc (fun s => s.RIP = 0x116dbc) (movR64R64Effect 0x116dbc 8 2) (Reg.operands [.gpr 2] [])) #v[270]
    (.letOp (n := 274) (.out 0x116dbf (movR64R64Effect 0x116dbf 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[269]
    (.letOp (n := 275) (.exec 0x116dbf (fun s => s.RIP = 0x116dbf) (movR64R64Effect 0x116dbf 11 0) (Reg.operands [.gpr 0] [])) #v[269]
    (.letOp (n := 276) (.out 0x116dc2 (movR64M64Effect 0x116dc2 0 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 277) (.exec 0x116dc2 (LoadPre 0x116dc2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x116dc2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116dc2 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 278) (.out 0x116dca (movR64M64Effect 0x116dca 9 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 279) (.exec 0x116dca (LoadPre 0x116dca (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x116dca + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116dca 9 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 280) (.out 0x116dd2 (mulR64Effect 0x116dd2 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[278, 276]
    (.letOp (n := 281) (.out 0x116dd2 (mulR64Effect 0x116dd2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[278, 276]
    (.letOp (n := 282) (.exec 0x116dd2 (fun s => s.RIP = 0x116dd2) (mulR64Effect 0x116dd2 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[278, 276]
    (.letOp (n := 283) (.out 0x116dd5 (movR64R64Effect 0x116dd5 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[281]
    (.letOp (n := 284) (.exec 0x116dd5 (fun s => s.RIP = 0x116dd5) (movR64R64Effect 0x116dd5 3 2) (Reg.operands [.gpr 2] [])) #v[281]
    (.letOp (n := 285) (.out 0x116dd8 (movR64R64Effect 0x116dd8 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[280]
    (.letOp (n := 286) (.exec 0x116dd8 (fun s => s.RIP = 0x116dd8) (movR64R64Effect 0x116dd8 14 0) (Reg.operands [.gpr 0] [])) #v[280]
    (.letOp (n := 287) (.out 0x116ddb (movR64M64Effect 0x116ddb 12 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 288) (.exec 0x116ddb (LoadPre 0x116ddb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x116ddb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116ddb 12 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 289) (.out 0x116de3 (movR64R64Effect 0x116de3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[287]
    (.letOp (n := 290) (.exec 0x116de3 (fun s => s.RIP = 0x116de3) (movR64R64Effect 0x116de3 0 12) (Reg.operands [.gpr 12] [])) #v[287]
    (.letOp (n := 291) (.out 0x116de6 (movR64M64Effect 0x116de6 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 292) (.exec 0x116de6 (LoadPre 0x116de6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x116de6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116de6 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 293) (.out 0x116deb (mulR64Effect 0x116deb 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[291, 289]
    (.letOp (n := 294) (.out 0x116deb (mulR64Effect 0x116deb 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[291, 289]
    (.letOp (n := 295) (.exec 0x116deb (fun s => s.RIP = 0x116deb) (mulR64Effect 0x116deb 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[291, 289]
    (.letOp (n := 296) (.out 0x116dee (addR64R64Effect 0x116dee 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[274, 259]
    (.letOp (n := 297) (.out 0x116dee (addR64R64Effect 0x116dee 11 1) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 1] []) (.flag .CF)) #v[274, 259]
    (.letOp (n := 298) (.exec 0x116dee (fun s => s.RIP = 0x116dee) (addR64R64Effect 0x116dee 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[274, 259]
    (.letOp (n := 299) (.out 0x116df1 (atFlags StatusFlags.CF (adcR64R64Effect 0x116df1 8 10)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[272, 261, 297]
    (.letOp (n := 300) (.exec 0x116df1 (fun s => s.RIP = 0x116df1) (atFlags StatusFlags.CF (adcR64R64Effect 0x116df1 8 10)) (Reg.operands [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[272, 261, 297]
    (.letOp (n := 301) (.out 0x116df4 (addR64R64Effect 0x116df4 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[296, 285]
    (.letOp (n := 302) (.out 0x116df4 (addR64R64Effect 0x116df4 11 14) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 14] []) (.flag .CF)) #v[296, 285]
    (.letOp (n := 303) (.exec 0x116df4 (fun s => s.RIP = 0x116df4) (addR64R64Effect 0x116df4 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[296, 285]
    (.letOp (n := 304) (.out 0x116df7 (atFlags StatusFlags.CF (adcR64R64Effect 0x116df7 8 3)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[299, 283, 302]
    (.letOp (n := 305) (.exec 0x116df7 (fun s => s.RIP = 0x116df7) (atFlags StatusFlags.CF (adcR64R64Effect 0x116df7 8 3)) (Reg.operands [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[299, 283, 302]
    (.letOp (n := 306) (.out 0x116dfa (addR64R64Effect 0x116dfa 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[293, 301]
    (.letOp (n := 307) (.out 0x116dfa (addR64R64Effect 0x116dfa 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[293, 301]
    (.letOp (n := 308) (.exec 0x116dfa (fun s => s.RIP = 0x116dfa) (addR64R64Effect 0x116dfa 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[293, 301]
    (.letOp (n := 309) (.out 0x116dfd (atFlags StatusFlags.CF (adcR64R64Effect 0x116dfd 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[304, 294, 307]
    (.letOp (n := 310) (.exec 0x116dfd (fun s => s.RIP = 0x116dfd) (atFlags StatusFlags.CF (adcR64R64Effect 0x116dfd 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[304, 294, 307]
    (.letOp (n := 311) (.out 0x116e00 (addR64R64Effect 0x116e00 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[306, 242]
    (.letOp (n := 312) (.out 0x116e00 (addR64R64Effect 0x116e00 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[306, 242]
    (.letOp (n := 313) (.exec 0x116e00 (fun s => s.RIP = 0x116e00) (addR64R64Effect 0x116e00 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[306, 242]
    (b_l116c14_6)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116c14_5 : List UInt8 :=
  [0x48, 0x89, 0xF0, 0x48, 0xF7, 0x64, 0x24, 0x70, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC3, 0x48, 0x8B,
    0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x49, 0xF7,
    0xE1, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC6, 0x4C, 0x8B, 0xA4, 0x24, 0x20, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0xE0, 0x48, 0x8B, 0x6C, 0x24, 0x60, 0x48, 0xF7, 0xE5, 0x49, 0x01, 0xCB, 0x4D, 0x11, 0xD0,
    0x4D, 0x01, 0xF3, 0x49, 0x11, 0xD8, 0x4C, 0x01, 0xD8, 0x49, 0x11, 0xD0, 0x48, 0x01, 0xF8] ++ bytes_l116c14_6

theorem code_l116c14_5 : ∀ x ∈ codeRange 0x116db4 bytes_l116c14_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16db4 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116c14_6

def b_l116c14_4 : Block Op Label signature Reg.count 224 :=
  .letOp (n := 224) (.out 0x116d5e (addR64R64Effect 0x116d5e 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[219, 192]
    (.letOp (n := 225) (.out 0x116d5e (addR64R64Effect 0x116d5e 10 3) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 3] []) (.flag .CF)) #v[219, 192]
    (.letOp (n := 226) (.exec 0x116d5e (fun s => s.RIP = 0x116d5e) (addR64R64Effect 0x116d5e 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[219, 192]
    (.letOp (n := 227) (.out 0x116d61 (atFlags StatusFlags.CF (adcR64R64Effect 0x116d61 7 5)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[222, 194, 225]
    (.letOp (n := 228) (.exec 0x116d61 (fun s => s.RIP = 0x116d61) (atFlags StatusFlags.CF (adcR64R64Effect 0x116d61 7 5)) (Reg.operands [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[222, 194, 225]
    (.letOp (n := 229) (.out 0x116d64 (movR64R64Effect 0x116d64 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[204]
    (.letOp (n := 230) (.exec 0x116d64 (fun s => s.RIP = 0x116d64) (movR64R64Effect 0x116d64 15 0) (Reg.operands [.gpr 0] [])) #v[204]
    (.letOp (n := 231) (.out 0x116d67 (addR64R64Effect 0x116d67 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[229, 224]
    (.letOp (n := 232) (.out 0x116d67 (addR64R64Effect 0x116d67 15 10) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 10] []) (.flag .CF)) #v[229, 224]
    (.letOp (n := 233) (.exec 0x116d67 (fun s => s.RIP = 0x116d67) (addR64R64Effect 0x116d67 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[229, 224]
    (.letOp (n := 234) (.out 0x116d6a (atFlags StatusFlags.CF (adcR64R64Effect 0x116d6a 7 8)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[227, 207, 232]
    (.letOp (n := 235) (.exec 0x116d6a (fun s => s.RIP = 0x116d6a) (atFlags StatusFlags.CF (adcR64R64Effect 0x116d6a 7 8)) (Reg.operands [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[227, 207, 232]
    (.letOp (n := 236) (.out 0x116d6d (addR64R64Effect 0x116d6d 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[231, 149]
    (.letOp (n := 237) (.out 0x116d6d (addR64R64Effect 0x116d6d 15 6) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 6] []) (.flag .CF)) #v[231, 149]
    (.letOp (n := 238) (.exec 0x116d6d (fun s => s.RIP = 0x116d6d) (addR64R64Effect 0x116d6d 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[231, 149]
    (.letOp (n := 239) (.exec 0x116d70 (StorePre 0x116d70 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x116d70 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116d70 15 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[236, 4]
    (.letOp (n := 240) (.out 0x116d75 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116d75 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[234, 237]
    (.letOp (n := 241) (.exec 0x116d75 (fun s => s.RIP = 0x116d75) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x116d75 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[234, 237]
    (.letOp (n := 242) (.out 0x116d79 (shldR64R64Effect 0x116d79 5 7 15 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[240, 236]
    (.letOp (n := 243) (.exec 0x116d79 (fun s => s.RIP = 0x116d79) (shldR64R64Effect 0x116d79 5 7 15 12) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[240, 236]
    (.letOp (n := 244) (.out 0x116d7e (shrR64Effect 0x116d7e 4 15 48) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[236]
    (.letOp (n := 245) (.exec 0x116d7e (fun s => s.RIP = 0x116d7e) (shrR64Effect 0x116d7e 4 15 48) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[236]
    (.letOp (n := 246) (.out 0x116d82 (movR64R64Effect 0x116d82 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[187]
    (.letOp (n := 247) (.exec 0x116d82 (fun s => s.RIP = 0x116d82) (movR64R64Effect 0x116d82 0 14) (Reg.operands [.gpr 14] [])) #v[187]
    (.letOp (n := 248) (.out 0x116d85 (mulM64Effect 0x116d85 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[246, 4]
    (.letOp (n := 249) (.out 0x116d85 (mulM64Effect 0x116d85 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[246, 4]
    (.letOp (n := 250) (.exec 0x116d85 (LoadPre 0x116d85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116d85 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x116d85 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[246, 4]
    (.letOp (n := 251) (.out 0x116d8a (movR64R64Effect 0x116d8a 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[249]
    (.letOp (n := 252) (.exec 0x116d8a (fun s => s.RIP = 0x116d8a) (movR64R64Effect 0x116d8a 13 2) (Reg.operands [.gpr 2] [])) #v[249]
    (.letOp (n := 253) (.exec 0x116d8d (StorePre 0x116d8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x116d8d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116d8d 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[248, 4]
    (.letOp (n := 254) (.out 0x116d92 (movR64M64Effect 0x116d92 0 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 255) (.exec 0x116d92 (LoadPre 0x116d92 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x116d92 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116d92 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 256) (.out 0x116d9a (mulM64Effect 0x116d9a 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[254, 4]
    (.letOp (n := 257) (.out 0x116d9a (mulM64Effect 0x116d9a 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[254, 4]
    (.letOp (n := 258) (.exec 0x116d9a (LoadPre 0x116d9a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x116d9a + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x116d9a 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[254, 4]
    (.letOp (n := 259) (.out 0x116da2 (movR64R64Effect 0x116da2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[256]
    (.letOp (n := 260) (.exec 0x116da2 (fun s => s.RIP = 0x116da2) (movR64R64Effect 0x116da2 1 0) (Reg.operands [.gpr 0] [])) #v[256]
    (.letOp (n := 261) (.out 0x116da5 (movR64R64Effect 0x116da5 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[257]
    (.letOp (n := 262) (.exec 0x116da5 (fun s => s.RIP = 0x116da5) (movR64R64Effect 0x116da5 10 2) (Reg.operands [.gpr 2] [])) #v[257]
    (.letOp (n := 263) (.out 0x116da8 (andR32Imm8Effect 0x116da8 4 15 0xf) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[244]
    (.letOp (n := 264) (.exec 0x116da8 (fun s => s.RIP = 0x116da8) (andR32Imm8Effect 0x116da8 4 15 0xf) (Reg.operands [.gpr 15] [])) #v[244]
    (.letOp (n := 265) (.out 0x116dac (movR64M64Effect 0x116dac 6 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 266) (.exec 0x116dac (LoadPre 0x116dac (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x116dac + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116dac 6 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l116c14_5)))))))))))))))))))))))))))))))))))))))))))

def bytes_l116c14_4 : List UInt8 :=
  [0x49, 0x01, 0xDA, 0x48, 0x11, 0xEF, 0x49, 0x89, 0xC7, 0x4D, 0x01, 0xD7, 0x4C, 0x11, 0xC7, 0x49,
    0x01, 0xF7, 0x4C, 0x89, 0x7C, 0x24, 0x50, 0x48, 0x83, 0xD7, 0x00, 0x4C, 0x0F, 0xA4, 0xFF, 0x0C,
    0x49, 0xC1, 0xEF, 0x30, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0x64, 0x24, 0x68, 0x49, 0x89, 0xD5, 0x48,
    0x89, 0x44, 0x24, 0x58, 0x48, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24,
    0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC1, 0x49, 0x89, 0xD2, 0x41, 0x83, 0xE7, 0x0F, 0x48, 0x8B,
    0xB4, 0x24, 0x00, 0x01, 0x00, 0x00] ++ bytes_l116c14_5

theorem code_l116c14_4 : ∀ x ∈ codeRange 0x116d5e bytes_l116c14_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16d5e 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116c14_5

def b_l116c14_3 : Block Op Label signature Reg.count 178 :=
  .letOp (n := 178) (.out 0x116d15 (mulR64Effect 0x116d15 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[55, 176]
    (.letOp (n := 179) (.out 0x116d15 (mulR64Effect 0x116d15 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[55, 176]
    (.letOp (n := 180) (.exec 0x116d15 (fun s => s.RIP = 0x116d15) (mulR64Effect 0x116d15 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[55, 176]
    (.letOp (n := 181) (.out 0x116d18 (movR64R64Effect 0x116d18 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[179]
    (.letOp (n := 182) (.exec 0x116d18 (fun s => s.RIP = 0x116d18) (movR64R64Effect 0x116d18 15 2) (Reg.operands [.gpr 2] [])) #v[179]
    (.letOp (n := 183) (.out 0x116d1b (movR64R64Effect 0x116d1b 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[178]
    (.letOp (n := 184) (.exec 0x116d1b (fun s => s.RIP = 0x116d1b) (movR64R64Effect 0x116d1b 13 0) (Reg.operands [.gpr 0] [])) #v[178]
    (.letOp (n := 185) (.out 0x116d1e (movR64R64Effect 0x116d1e 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[105]
    (.letOp (n := 186) (.exec 0x116d1e (fun s => s.RIP = 0x116d1e) (movR64R64Effect 0x116d1e 0 3) (Reg.operands [.gpr 3] [])) #v[105]
    (.letOp (n := 187) (.out 0x116d21 (movR64R64Effect 0x116d21 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 3] []) (.reg (.gpr 14))) #v[105]
    (.letOp (n := 188) (.exec 0x116d21 (fun s => s.RIP = 0x116d21) (movR64R64Effect 0x116d21 14 3) (Reg.operands [.gpr 3] [])) #v[105]
    (.letOp (n := 189) (.out 0x116d24 (mulR64Effect 0x116d24 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[53, 185]
    (.letOp (n := 190) (.out 0x116d24 (mulR64Effect 0x116d24 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[53, 185]
    (.letOp (n := 191) (.exec 0x116d24 (fun s => s.RIP = 0x116d24) (mulR64Effect 0x116d24 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[53, 185]
    (.letOp (n := 192) (.out 0x116d27 (movR64R64Effect 0x116d27 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[189]
    (.letOp (n := 193) (.exec 0x116d27 (fun s => s.RIP = 0x116d27) (movR64R64Effect 0x116d27 3 0) (Reg.operands [.gpr 0] [])) #v[189]
    (.letOp (n := 194) (.out 0x116d2a (movR64R64Effect 0x116d2a 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[190]
    (.letOp (n := 195) (.exec 0x116d2a (fun s => s.RIP = 0x116d2a) (movR64R64Effect 0x116d2a 5 2) (Reg.operands [.gpr 2] [])) #v[190]
    (.letOp (n := 196) (.out 0x116d2d (shrR64Effect 0x116d2d 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[128]
    (.letOp (n := 197) (.exec 0x116d2d (fun s => s.RIP = 0x116d2d) (shrR64Effect 0x116d2d 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[128]
    (.letOp (n := 198) (.out 0x116d31 (movR64Imm64Effect 0x116d31 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 199) (.exec 0x116d31 (fun s => s.RIP = 0x116d31) (movR64Imm64Effect 0x116d31 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 200) (.out 0x116d3b (imulR64R64Effect 0x116d3b 4 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[196, 198]
    (.letOp (n := 201) (.exec 0x116d3b (fun s => s.RIP = 0x116d3b) (imulR64R64Effect 0x116d3b 4 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[196, 198]
    (.letOp (n := 202) (.out 0x116d3f (movR64R64Effect 0x116d3f 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[132]
    (.letOp (n := 203) (.exec 0x116d3f (fun s => s.RIP = 0x116d3f) (movR64R64Effect 0x116d3f 0 11) (Reg.operands [.gpr 11] [])) #v[132]
    (.letOp (n := 204) (.out 0x116d42 (mulR64Effect 0x116d42 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[198, 202]
    (.letOp (n := 205) (.out 0x116d42 (mulR64Effect 0x116d42 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[198, 202]
    (.letOp (n := 206) (.exec 0x116d42 (fun s => s.RIP = 0x116d42) (mulR64Effect 0x116d42 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[198, 202]
    (.letOp (n := 207) (.out 0x116d45 (addR64R64Effect 0x116d45 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[200, 205]
    (.letOp (n := 208) (.exec 0x116d45 (fun s => s.RIP = 0x116d45) (addR64R64Effect 0x116d45 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[200, 205]
    (.letOp (n := 209) (.out 0x116d48 (addR64M64Effect 0x116d48 10 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[165, 4]
    (.letOp (n := 210) (.out 0x116d48 (addR64M64Effect 0x116d48 10 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[165, 4]
    (.letOp (n := 211) (.exec 0x116d48 (LoadPre 0x116d48 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x116d48 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x116d48 10 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[165, 4]
    (.letOp (n := 212) (.out 0x116d4d (atFlags StatusFlags.CF (adcR64M64Effect 0x116d4d 7 (.sib 4 none 0 (.d8 0x50)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[163, 4, 210]
    (.letOp (n := 213) (.exec 0x116d4d (LoadPre 0x116d4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x116d4d + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x116d4d 7 (.sib 4 none 0 (.d8 0x50)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[163, 4, 210]
    (.letOp (n := 214) (.out 0x116d52 (addR64R64Effect 0x116d52 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[209, 174]
    (.letOp (n := 215) (.out 0x116d52 (addR64R64Effect 0x116d52 10 12) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 12] []) (.flag .CF)) #v[209, 174]
    (.letOp (n := 216) (.exec 0x116d52 (fun s => s.RIP = 0x116d52) (addR64R64Effect 0x116d52 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[209, 174]
    (.letOp (n := 217) (.out 0x116d55 (atFlags StatusFlags.CF (adcR64R64Effect 0x116d55 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[212, 172, 215]
    (.letOp (n := 218) (.exec 0x116d55 (fun s => s.RIP = 0x116d55) (atFlags StatusFlags.CF (adcR64R64Effect 0x116d55 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[212, 172, 215]
    (.letOp (n := 219) (.out 0x116d58 (addR64R64Effect 0x116d58 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[214, 183]
    (.letOp (n := 220) (.out 0x116d58 (addR64R64Effect 0x116d58 10 13) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 13] []) (.flag .CF)) #v[214, 183]
    (.letOp (n := 221) (.exec 0x116d58 (fun s => s.RIP = 0x116d58) (addR64R64Effect 0x116d58 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[214, 183]
    (.letOp (n := 222) (.out 0x116d5b (atFlags StatusFlags.CF (adcR64R64Effect 0x116d5b 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[217, 181, 220]
    (.letOp (n := 223) (.exec 0x116d5b (fun s => s.RIP = 0x116d5b) (atFlags StatusFlags.CF (adcR64R64Effect 0x116d5b 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[217, 181, 220]
    (b_l116c14_4))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116c14_3 : List UInt8 :=
  [0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC5, 0x48, 0x89, 0xD8, 0x49, 0x89, 0xDE, 0x49,
    0xF7, 0xE1, 0x48, 0x89, 0xC3, 0x48, 0x89, 0xD5, 0x49, 0xC1, 0xE8, 0x34, 0x48, 0xBA, 0x10, 0x3D,
    0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xC2, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0xE2,
    0x49, 0x01, 0xD0, 0x4C, 0x03, 0x54, 0x24, 0x58, 0x48, 0x13, 0x7C, 0x24, 0x50, 0x4D, 0x01, 0xE2,
    0x48, 0x11, 0xCF, 0x4D, 0x01, 0xEA, 0x4C, 0x11, 0xFF] ++ bytes_l116c14_4

theorem code_l116c14_3 : ∀ x ∈ codeRange 0x116d15 bytes_l116c14_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16d15 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116c14_4

def b_l116c14_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x116cc8 (andR64R64Effect 0x116cc8 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[125, 134]
    (.letOp (n := 137) (.exec 0x116cc8 (fun s => s.RIP = 0x116cc8) (andR64R64Effect 0x116cc8 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[125, 134]
    (.letOp (n := 138) (.out 0x116ccb (movR64Imm64Effect 0x116ccb 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 139) (.exec 0x116ccb (fun s => s.RIP = 0x116ccb) (movR64Imm64Effect 0x116ccb 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 140) (.out 0x116cd5 (mulR64Effect 0x116cd5 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[138, 136]
    (.letOp (n := 141) (.out 0x116cd5 (mulR64Effect 0x116cd5 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[138, 136]
    (.letOp (n := 142) (.exec 0x116cd5 (fun s => s.RIP = 0x116cd5) (mulR64Effect 0x116cd5 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[138, 136]
    (.letOp (n := 143) (.out 0x116cd8 (addR64R64Effect 0x116cd8 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[140, 115]
    (.letOp (n := 144) (.out 0x116cd8 (addR64R64Effect 0x116cd8 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[140, 115]
    (.letOp (n := 145) (.exec 0x116cd8 (fun s => s.RIP = 0x116cd8) (addR64R64Effect 0x116cd8 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[140, 115]
    (.letOp (n := 146) (.exec 0x116cdb (StorePre 0x116cdb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x116cdb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116cdb 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[143, 4]
    (.letOp (n := 147) (.out 0x116ce0 (atFlags StatusFlags.CF (adcR64R64Effect 0x116ce0 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[118, 141, 144]
    (.letOp (n := 148) (.exec 0x116ce0 (fun s => s.RIP = 0x116ce0) (atFlags StatusFlags.CF (adcR64R64Effect 0x116ce0 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[118, 141, 144]
    (.letOp (n := 149) (.out 0x116ce3 (shldR64R64Effect 0x116ce3 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[147, 143]
    (.letOp (n := 150) (.exec 0x116ce3 (fun s => s.RIP = 0x116ce3) (shldR64R64Effect 0x116ce3 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[147, 143]
    (.letOp (n := 151) (.out 0x116ce8 (movR64R64Effect 0x116ce8 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[120]
    (.letOp (n := 152) (.exec 0x116ce8 (fun s => s.RIP = 0x116ce8) (movR64R64Effect 0x116ce8 0 1) (Reg.operands [.gpr 1] [])) #v[120]
    (.letOp (n := 153) (.out 0x116ceb (mulM64Effect 0x116ceb 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[151, 4]
    (.letOp (n := 154) (.out 0x116ceb (mulM64Effect 0x116ceb 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[151, 4]
    (.letOp (n := 155) (.exec 0x116ceb (LoadPre 0x116ceb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116ceb + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x116ceb 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[151, 4]
    (.letOp (n := 156) (.exec 0x116cf0 (StorePre 0x116cf0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x116cf0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116cf0 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[154, 4]
    (.letOp (n := 157) (.exec 0x116cf5 (StorePre 0x116cf5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x116cf5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116cf5 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[153, 4]
    (.letOp (n := 158) (.out 0x116cfa (movR64R64Effect 0x116cfa 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[64]
    (.letOp (n := 159) (.exec 0x116cfa (fun s => s.RIP = 0x116cfa) (movR64R64Effect 0x116cfa 0 10) (Reg.operands [.gpr 10] [])) #v[64]
    (.letOp (n := 160) (.out 0x116cfd (mulR64Effect 0x116cfd 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[62, 158]
    (.letOp (n := 161) (.out 0x116cfd (mulR64Effect 0x116cfd 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[62, 158]
    (.letOp (n := 162) (.exec 0x116cfd (fun s => s.RIP = 0x116cfd) (mulR64Effect 0x116cfd 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[62, 158]
    (.letOp (n := 163) (.out 0x116d00 (movR64R64Effect 0x116d00 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[161]
    (.letOp (n := 164) (.exec 0x116d00 (fun s => s.RIP = 0x116d00) (movR64R64Effect 0x116d00 7 2) (Reg.operands [.gpr 2] [])) #v[161]
    (.letOp (n := 165) (.out 0x116d03 (movR64R64Effect 0x116d03 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[160]
    (.letOp (n := 166) (.exec 0x116d03 (fun s => s.RIP = 0x116d03) (movR64R64Effect 0x116d03 10 0) (Reg.operands [.gpr 0] [])) #v[160]
    (.letOp (n := 167) (.out 0x116d06 (movR64R64Effect 0x116d06 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[75]
    (.letOp (n := 168) (.exec 0x116d06 (fun s => s.RIP = 0x116d06) (movR64R64Effect 0x116d06 0 15) (Reg.operands [.gpr 15] [])) #v[75]
    (.letOp (n := 169) (.out 0x116d09 (mulR64Effect 0x116d09 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[57, 167]
    (.letOp (n := 170) (.out 0x116d09 (mulR64Effect 0x116d09 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[57, 167]
    (.letOp (n := 171) (.exec 0x116d09 (fun s => s.RIP = 0x116d09) (mulR64Effect 0x116d09 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[57, 167]
    (.letOp (n := 172) (.out 0x116d0c (movR64R64Effect 0x116d0c 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[170]
    (.letOp (n := 173) (.exec 0x116d0c (fun s => s.RIP = 0x116d0c) (movR64R64Effect 0x116d0c 1 2) (Reg.operands [.gpr 2] [])) #v[170]
    (.letOp (n := 174) (.out 0x116d0f (movR64R64Effect 0x116d0f 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[169]
    (.letOp (n := 175) (.exec 0x116d0f (fun s => s.RIP = 0x116d0f) (movR64R64Effect 0x116d0f 12 0) (Reg.operands [.gpr 0] [])) #v[169]
    (.letOp (n := 176) (.out 0x116d12 (movR64R64Effect 0x116d12 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[90]
    (.letOp (n := 177) (.exec 0x116d12 (fun s => s.RIP = 0x116d12) (movR64R64Effect 0x116d12 0 13) (Reg.operands [.gpr 13] [])) #v[90]
    (b_l116c14_3))))))))))))))))))))))))))))))))))))))))))

def bytes_l116c14_2 : List UInt8 :=
  [0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x48, 0x01, 0xF8, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x11, 0xD6, 0x48, 0x0F, 0xA4, 0xC6, 0x0C,
    0x48, 0x89, 0xC8, 0x48, 0xF7, 0x64, 0x24, 0x68, 0x48, 0x89, 0x54, 0x24, 0x50, 0x48, 0x89, 0x44,
    0x24, 0x58, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC2, 0x4C, 0x89,
    0xF8, 0x49, 0xF7, 0xE4, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC4, 0x4C, 0x89, 0xE8] ++ bytes_l116c14_3

theorem code_l116c14_2 : ∀ x ∈ codeRange 0x116cc8 bytes_l116c14_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16cc8 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116c14_3

def b_l116c14_1 : Block Op Label signature Reg.count 94 :=
  .letOp (n := 94) (.out 0x116c70 (mulR64Effect 0x116c70 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[57, 92]
    (.letOp (n := 95) (.out 0x116c70 (mulR64Effect 0x116c70 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[57, 92]
    (.letOp (n := 96) (.exec 0x116c70 (fun s => s.RIP = 0x116c70) (mulR64Effect 0x116c70 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[57, 92]
    (.letOp (n := 97) (.exec 0x116c73 (StorePre 0x116c73 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x116c73 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116c73 12 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 98) (.out 0x116c78 (movR64R64Effect 0x116c78 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[94]
    (.letOp (n := 99) (.exec 0x116c78 (fun s => s.RIP = 0x116c78) (movR64R64Effect 0x116c78 1 0) (Reg.operands [.gpr 0] [])) #v[94]
    (.letOp (n := 100) (.out 0x116c7b (addR64R64Effect 0x116c7b 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[98, 85]
    (.letOp (n := 101) (.out 0x116c7b (addR64R64Effect 0x116c7b 1 7) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 7] []) (.flag .CF)) #v[98, 85]
    (.letOp (n := 102) (.exec 0x116c7b (fun s => s.RIP = 0x116c7b) (addR64R64Effect 0x116c7b 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[98, 85]
    (.letOp (n := 103) (.out 0x116c7e (atFlags StatusFlags.CF (adcR64R64Effect 0x116c7e 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[88, 95, 101]
    (.letOp (n := 104) (.exec 0x116c7e (fun s => s.RIP = 0x116c7e) (atFlags StatusFlags.CF (adcR64R64Effect 0x116c7e 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[88, 95, 101]
    (.letOp (n := 105) (.out 0x116c81 (movR64M64Effect 0x116c81 3 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 106) (.exec 0x116c81 (LoadPre 0x116c81 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x116c81 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116c81 3 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 107) (.out 0x116c89 (movR64R64Effect 0x116c89 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[105]
    (.letOp (n := 108) (.exec 0x116c89 (fun s => s.RIP = 0x116c89) (movR64R64Effect 0x116c89 0 3) (Reg.operands [.gpr 3] [])) #v[105]
    (.letOp (n := 109) (.out 0x116c8c (mulR64Effect 0x116c8c 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[55, 107]
    (.letOp (n := 110) (.out 0x116c8c (mulR64Effect 0x116c8c 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[55, 107]
    (.letOp (n := 111) (.exec 0x116c8c (fun s => s.RIP = 0x116c8c) (mulR64Effect 0x116c8c 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[55, 107]
    (.letOp (n := 112) (.exec 0x116c8f (StorePre 0x116c8f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x116c8f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x116c8f 14 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 113) (.out 0x116c97 (movR64R64Effect 0x116c97 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[109]
    (.letOp (n := 114) (.exec 0x116c97 (fun s => s.RIP = 0x116c97) (movR64R64Effect 0x116c97 7 0) (Reg.operands [.gpr 0] [])) #v[109]
    (.letOp (n := 115) (.out 0x116c9a (addR64R64Effect 0x116c9a 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[113, 100]
    (.letOp (n := 116) (.out 0x116c9a (addR64R64Effect 0x116c9a 7 1) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 1] []) (.flag .CF)) #v[113, 100]
    (.letOp (n := 117) (.exec 0x116c9a (fun s => s.RIP = 0x116c9a) (addR64R64Effect 0x116c9a 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[113, 100]
    (.letOp (n := 118) (.out 0x116c9d (atFlags StatusFlags.CF (adcR64R64Effect 0x116c9d 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[103, 110, 116]
    (.letOp (n := 119) (.exec 0x116c9d (fun s => s.RIP = 0x116c9d) (atFlags StatusFlags.CF (adcR64R64Effect 0x116c9d 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[103, 110, 116]
    (.letOp (n := 120) (.out 0x116ca0 (movR64M64Effect 0x116ca0 1 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 121) (.exec 0x116ca0 (LoadPre 0x116ca0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x116ca0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116ca0 1 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 122) (.out 0x116ca8 (movR64R64Effect 0x116ca8 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[120]
    (.letOp (n := 123) (.exec 0x116ca8 (fun s => s.RIP = 0x116ca8) (movR64R64Effect 0x116ca8 0 1) (Reg.operands [.gpr 1] [])) #v[120]
    (.letOp (n := 124) (.exec 0x116cab (StorePre 0x116cab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x116cab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116cab 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 125) (.out 0x116cb0 (mulR64Effect 0x116cb0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[53, 122]
    (.letOp (n := 126) (.out 0x116cb0 (mulR64Effect 0x116cb0 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[53, 122]
    (.letOp (n := 127) (.exec 0x116cb0 (fun s => s.RIP = 0x116cb0) (mulR64Effect 0x116cb0 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[53, 122]
    (.letOp (n := 128) (.out 0x116cb3 (movR64R64Effect 0x116cb3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[126]
    (.letOp (n := 129) (.exec 0x116cb3 (fun s => s.RIP = 0x116cb3) (movR64R64Effect 0x116cb3 8 2) (Reg.operands [.gpr 2] [])) #v[126]
    (.letOp (n := 130) (.out 0x116cb6 (movR64R64Effect 0x116cb6 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[126]
    (.letOp (n := 131) (.exec 0x116cb6 (fun s => s.RIP = 0x116cb6) (movR64R64Effect 0x116cb6 11 2) (Reg.operands [.gpr 2] [])) #v[126]
    (.letOp (n := 132) (.out 0x116cb9 (shldR64R64Effect 0x116cb9 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[130, 125]
    (.letOp (n := 133) (.exec 0x116cb9 (fun s => s.RIP = 0x116cb9) (shldR64R64Effect 0x116cb9 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[130, 125]
    (.letOp (n := 134) (.out 0x116cbe (movR64Imm64Effect 0x116cbe 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 135) (.exec 0x116cbe (fun s => s.RIP = 0x116cbe) (movR64Imm64Effect 0x116cbe 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l116c14_2))))))))))))))))))))))))))))))))))))))))))

def bytes_l116c14_1 : List UInt8 :=
  [0x49, 0xF7, 0xE4, 0x4C, 0x89, 0x64, 0x24, 0x70, 0x48, 0x89, 0xC1, 0x48, 0x01, 0xF9, 0x48, 0x11,
    0xD6, 0x48, 0x8B, 0x9C, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE6, 0x4C,
    0x89, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x48, 0x01, 0xCF, 0x48, 0x11, 0xD6,
    0x48, 0x8B, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x4C, 0x89, 0x4C, 0x24, 0x60,
    0x49, 0xF7, 0xE1, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xD3, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xBA,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] ++ bytes_l116c14_2

theorem code_l116c14_1 : ∀ x ∈ codeRange 0x116c70 bytes_l116c14_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16c70 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116c14_2

def b_l116c14 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x116c14 (movR64M64Effect 0x116c14 9 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 54) (.exec 0x116c14 (LoadPre 0x116c14 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x116c14 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116c14 9 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x116c19 (movR64M64Effect 0x116c19 14 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 56) (.exec 0x116c19 (LoadPre 0x116c19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x116c19 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116c19 14 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x116c1e (movR64M64Effect 0x116c1e 12 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 58) (.exec 0x116c1e (LoadPre 0x116c1e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x116c1e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116c1e 12 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x116c23 (movR64M64Effect 0x116c23 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x116c23 (LoadPre 0x116c23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x116c23 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116c23 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x116c28 (StorePre 0x116c28 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x116c28 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x116c28 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x116c2d (movR64M64Effect 0x116c2d 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 63) (.exec 0x116c2d (LoadPre 0x116c2d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x116c2d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x116c2d 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x116c32 (movR64M64Effect 0x116c32 10 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 65) (.exec 0x116c32 (LoadPre 0x116c32 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x116c32 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116c32 10 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x116c3a (movR64R64Effect 0x116c3a 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[64]
    (.letOp (n := 67) (.exec 0x116c3a (fun s => s.RIP = 0x116c3a) (movR64R64Effect 0x116c3a 0 10) (Reg.operands [.gpr 10] [])) #v[64]
    (.letOp (n := 68) (.out 0x116c3d (mulR64Effect 0x116c3d 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[59, 66]
    (.letOp (n := 69) (.out 0x116c3d (mulR64Effect 0x116c3d 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[59, 66]
    (.letOp (n := 70) (.exec 0x116c3d (fun s => s.RIP = 0x116c3d) (mulR64Effect 0x116c3d 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[59, 66]
    (.letOp (n := 71) (.out 0x116c40 (movR64R64Effect 0x116c40 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[69]
    (.letOp (n := 72) (.exec 0x116c40 (fun s => s.RIP = 0x116c40) (movR64R64Effect 0x116c40 6 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 73) (.out 0x116c43 (movR64R64Effect 0x116c43 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[68]
    (.letOp (n := 74) (.exec 0x116c43 (fun s => s.RIP = 0x116c43) (movR64R64Effect 0x116c43 1 0) (Reg.operands [.gpr 0] [])) #v[68]
    (.letOp (n := 75) (.out 0x116c46 (movR64M64Effect 0x116c46 15 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 76) (.exec 0x116c46 (LoadPre 0x116c46 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x116c46 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116c46 15 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x116c4e (movR64R64Effect 0x116c4e 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[75]
    (.letOp (n := 78) (.exec 0x116c4e (fun s => s.RIP = 0x116c4e) (movR64R64Effect 0x116c4e 0 15) (Reg.operands [.gpr 15] [])) #v[75]
    (.letOp (n := 79) (.out 0x116c51 (mulR64Effect 0x116c51 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[62, 77]
    (.letOp (n := 80) (.out 0x116c51 (mulR64Effect 0x116c51 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[62, 77]
    (.letOp (n := 81) (.exec 0x116c51 (fun s => s.RIP = 0x116c51) (mulR64Effect 0x116c51 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[62, 77]
    (.letOp (n := 82) (.exec 0x116c54 (StorePre 0x116c54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x116c54 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x116c54 5 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 83) (.out 0x116c5c (movR64R64Effect 0x116c5c 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[79]
    (.letOp (n := 84) (.exec 0x116c5c (fun s => s.RIP = 0x116c5c) (movR64R64Effect 0x116c5c 7 0) (Reg.operands [.gpr 0] [])) #v[79]
    (.letOp (n := 85) (.out 0x116c5f (addR64R64Effect 0x116c5f 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[83, 73]
    (.letOp (n := 86) (.out 0x116c5f (addR64R64Effect 0x116c5f 7 1) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 1] []) (.flag .CF)) #v[83, 73]
    (.letOp (n := 87) (.exec 0x116c5f (fun s => s.RIP = 0x116c5f) (addR64R64Effect 0x116c5f 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[83, 73]
    (.letOp (n := 88) (.out 0x116c62 (atFlags StatusFlags.CF (adcR64R64Effect 0x116c62 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[71, 80, 86]
    (.letOp (n := 89) (.exec 0x116c62 (fun s => s.RIP = 0x116c62) (atFlags StatusFlags.CF (adcR64R64Effect 0x116c62 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[71, 80, 86]
    (.letOp (n := 90) (.out 0x116c65 (movR64M64Effect 0x116c65 13 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 91) (.exec 0x116c65 (LoadPre 0x116c65 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x116c65 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x116c65 13 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.out 0x116c6d (movR64R64Effect 0x116c6d 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[90]
    (.letOp (n := 93) (.exec 0x116c6d (fun s => s.RIP = 0x116c6d) (movR64R64Effect 0x116c6d 0 13) (Reg.operands [.gpr 13] [])) #v[90]
    (b_l116c14_1)))))))))))))))))))))))))))))))))))))))))

def bytes_l116c14 : List UInt8 :=
  [0x4C, 0x8B, 0x4C, 0x24, 0x48, 0x4C, 0x8B, 0x74, 0x24, 0x40, 0x4C, 0x8B, 0x64, 0x24, 0x38, 0x48,
    0x8B, 0x4C, 0x24, 0x28, 0x48, 0x89, 0x4C, 0x24, 0x68, 0x48, 0x8B, 0x6C, 0x24, 0x30, 0x4C, 0x8B,
    0x94, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD6, 0x48,
    0x89, 0xC1, 0x4C, 0x8B, 0xBC, 0x24, 0x38, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0xE5,
    0x48, 0x89, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x48, 0x01, 0xCF, 0x48, 0x11,
    0xD6, 0x4C, 0x8B, 0xAC, 0x24, 0x20, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE8] ++ bytes_l116c14_1

theorem code_l116c14 : ∀ x ∈ codeRange 0x116c14 bytes_l116c14, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x16c14 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116c14_1

@[cfg_block] def b_l11703f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11703f (movR64M64Effect 0x11703f 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11703f (LoadPre 0x11703f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11703f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11703f 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117044 (StorePre 0x117044 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117044 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117044 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117049 (movR64M64Effect 0x117049 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117049 (LoadPre 0x117049 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117049 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117049 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11704e (StorePre 0x11704e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11704e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11704e 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117053 (movR64M64Effect 0x117053 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117053 (LoadPre 0x117053 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117053 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117053 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117058 (StorePre 0x117058 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117058 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117058 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11705d (movR64M64Effect 0x11705d 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11705d (LoadPre 0x11705d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11705d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11705d 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117062 (movR64M64Effect 0x117062 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117062 (LoadPre 0x117062 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117062 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117062 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117067 (StorePre 0x117067 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117067 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117067 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11706c (StorePre 0x11706c 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11706c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11706c 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117070 (movR64R64Effect 0x117070 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 69) (.exec 0x117070 (fun s => s.RIP = 0x117070) (movR64R64Effect 0x117070 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 70) (.out 0x117073 (movR64R64Effect 0x117073 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117073 (fun s => s.RIP = 0x117073) (movR64R64Effect 0x117073 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117076 (callEffect (fun _ => 0x1145f0) 0x11707b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117076 (PushPre 0x117076 5) (callEffect (fun _ => 0x1145f0) 0x11707b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11707b⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11707b, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11703f : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xF6, 0xE8, 0x75, 0xD5, 0xFF, 0xFF]

theorem code_l11703f : ∀ x ∈ codeRange 0x11703f bytes_l11703f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1703f 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11707b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11707b (movR64M64Effect 0x11707b 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11707b (LoadPre 0x11707b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11707b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11707b 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117080 (StorePre 0x117080 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117080 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117080 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117085 (movR64M64Effect 0x117085 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117085 (LoadPre 0x117085 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117085 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117085 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11708a (StorePre 0x11708a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11708a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11708a 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11708f (movR64M64Effect 0x11708f 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11708f (LoadPre 0x11708f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11708f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11708f 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117094 (StorePre 0x117094 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117094 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117094 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117099 (movR64M64Effect 0x117099 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117099 (LoadPre 0x117099 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117099 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117099 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11709e (movR64M64Effect 0x11709e 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11709e (LoadPre 0x11709e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11709e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11709e 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1170a3 (StorePre 0x1170a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1170a3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1170a3 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1170a8 (StorePre 0x1170a8 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1170a8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1170a8 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1170ac (movR64R64Effect 0x1170ac 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 69) (.exec 0x1170ac (fun s => s.RIP = 0x1170ac) (movR64R64Effect 0x1170ac 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 70) (.out 0x1170af (movR64R64Effect 0x1170af 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1170af (fun s => s.RIP = 0x1170af) (movR64R64Effect 0x1170af 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1170b2 (callEffect (fun _ => 0x1145f0) 0x1170b7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1170b2 (PushPre 0x1170b2 5) (callEffect (fun _ => 0x1145f0) 0x1170b7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1170b7⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1170b7, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11707b : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xF6, 0xE8, 0x39, 0xD5, 0xFF, 0xFF]

theorem code_l11707b : ∀ x ∈ codeRange 0x11707b bytes_l11707b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1707b 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1170b7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1170b7 (movR64M64Effect 0x1170b7 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1170b7 (LoadPre 0x1170b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1170b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1170b7 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1170bc (StorePre 0x1170bc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1170bc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1170bc 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1170c1 (movR64M64Effect 0x1170c1 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1170c1 (LoadPre 0x1170c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1170c1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1170c1 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1170c6 (StorePre 0x1170c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1170c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1170c6 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1170cb (movR64M64Effect 0x1170cb 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1170cb (LoadPre 0x1170cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1170cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1170cb 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1170d0 (StorePre 0x1170d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1170d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1170d0 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1170d5 (movR64M64Effect 0x1170d5 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1170d5 (LoadPre 0x1170d5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1170d5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1170d5 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1170da (movR64M64Effect 0x1170da 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1170da (LoadPre 0x1170da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1170da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1170da 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1170df (StorePre 0x1170df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1170df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1170df 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1170e4 (StorePre 0x1170e4 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1170e4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1170e4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1170e8 (movR64R64Effect 0x1170e8 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 69) (.exec 0x1170e8 (fun s => s.RIP = 0x1170e8) (movR64R64Effect 0x1170e8 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 70) (.out 0x1170eb (movR64R64Effect 0x1170eb 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1170eb (fun s => s.RIP = 0x1170eb) (movR64R64Effect 0x1170eb 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1170ee (callEffect (fun _ => 0x1145f0) 0x1170f3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1170ee (PushPre 0x1170ee 5) (callEffect (fun _ => 0x1145f0) 0x1170f3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1170f3⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1170f3, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1170b7 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xF6, 0xE8, 0xFD, 0xD4, 0xFF, 0xFF]

theorem code_l1170b7 : ∀ x ∈ codeRange 0x1170b7 bytes_l1170b7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x170b7 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1170f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1170f3 (movR64M64Effect 0x1170f3 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1170f3 (LoadPre 0x1170f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1170f3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1170f3 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1170f8 (StorePre 0x1170f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1170f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1170f8 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1170fd (movR64M64Effect 0x1170fd 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1170fd (LoadPre 0x1170fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1170fd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1170fd 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117102 (StorePre 0x117102 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117102 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117102 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117107 (movR64M64Effect 0x117107 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117107 (LoadPre 0x117107 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117107 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117107 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11710c (StorePre 0x11710c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11710c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11710c 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117111 (movR64M64Effect 0x117111 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117111 (LoadPre 0x117111 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117111 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117111 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117116 (movR64M64Effect 0x117116 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117116 (LoadPre 0x117116 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117116 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117116 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11711b (StorePre 0x11711b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11711b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11711b 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117120 (StorePre 0x117120 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117120 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117120 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117124 (movR64R64Effect 0x117124 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 69) (.exec 0x117124 (fun s => s.RIP = 0x117124) (movR64R64Effect 0x117124 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 70) (.out 0x117127 (movR64R64Effect 0x117127 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117127 (fun s => s.RIP = 0x117127) (movR64R64Effect 0x117127 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11712a (callEffect (fun _ => 0x1145f0) 0x11712f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11712a (PushPre 0x11712a 5) (callEffect (fun _ => 0x1145f0) 0x11712f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11712f⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11712f, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1170f3 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xF6, 0xE8, 0xC1, 0xD4, 0xFF, 0xFF]

theorem code_l1170f3 : ∀ x ∈ codeRange 0x1170f3 bytes_l1170f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x170f3 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11712f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11712f (movR64M64Effect 0x11712f 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11712f (LoadPre 0x11712f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11712f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11712f 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117134 (StorePre 0x117134 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117134 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117134 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117139 (movR64M64Effect 0x117139 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117139 (LoadPre 0x117139 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117139 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117139 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11713e (StorePre 0x11713e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11713e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11713e 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117143 (movR64M64Effect 0x117143 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117143 (LoadPre 0x117143 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117143 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117143 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117148 (StorePre 0x117148 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117148 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117148 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11714d (movR64M64Effect 0x11714d 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11714d (LoadPre 0x11714d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11714d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11714d 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117152 (movR64M64Effect 0x117152 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117152 (LoadPre 0x117152 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117152 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117152 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117157 (StorePre 0x117157 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117157 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117157 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11715c (StorePre 0x11715c 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11715c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11715c 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117160 (movR64R64Effect 0x117160 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 69) (.exec 0x117160 (fun s => s.RIP = 0x117160) (movR64R64Effect 0x117160 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 70) (.out 0x117163 (movR64R64Effect 0x117163 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117163 (fun s => s.RIP = 0x117163) (movR64R64Effect 0x117163 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117166 (callEffect (fun _ => 0x1145f0) 0x11716b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117166 (PushPre 0x117166 5) (callEffect (fun _ => 0x1145f0) 0x11716b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11716b⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11716b, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11712f : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xF6, 0xE8, 0x85, 0xD4, 0xFF, 0xFF]

theorem code_l11712f : ∀ x ∈ codeRange 0x11712f bytes_l11712f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1712f 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11716b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11716b (movR64M64Effect 0x11716b 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11716b (LoadPre 0x11716b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11716b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11716b 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117170 (StorePre 0x117170 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117170 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117170 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117175 (movR64M64Effect 0x117175 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117175 (LoadPre 0x117175 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117175 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117175 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11717a (StorePre 0x11717a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11717a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11717a 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11717f (movR64M64Effect 0x11717f 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11717f (LoadPre 0x11717f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11717f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11717f 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117184 (StorePre 0x117184 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117184 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117184 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117189 (movR64M64Effect 0x117189 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117189 (LoadPre 0x117189 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117189 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117189 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11718e (movR64M64Effect 0x11718e 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11718e (LoadPre 0x11718e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11718e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11718e 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117193 (StorePre 0x117193 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117193 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117193 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117198 (StorePre 0x117198 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117198 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117198 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11719c (movR64R64Effect 0x11719c 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 69) (.exec 0x11719c (fun s => s.RIP = 0x11719c) (movR64R64Effect 0x11719c 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 70) (.out 0x11719f (movR64R64Effect 0x11719f 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11719f (fun s => s.RIP = 0x11719f) (movR64R64Effect 0x11719f 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1171a2 (callEffect (fun _ => 0x1145f0) 0x1171a7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1171a2 (PushPre 0x1171a2 5) (callEffect (fun _ => 0x1145f0) 0x1171a7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1171a7⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1171a7, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11716b : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xF6, 0xE8, 0x49, 0xD4, 0xFF, 0xFF]

theorem code_l11716b : ∀ x ∈ codeRange 0x11716b bytes_l11716b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1716b 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1171a7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1171a7 (movR64M64Effect 0x1171a7 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1171a7 (LoadPre 0x1171a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1171a7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1171a7 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1171ac (StorePre 0x1171ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1171ac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1171ac 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1171b1 (movR64M64Effect 0x1171b1 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1171b1 (LoadPre 0x1171b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1171b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1171b1 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1171b6 (StorePre 0x1171b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1171b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1171b6 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1171bb (movR64M64Effect 0x1171bb 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1171bb (LoadPre 0x1171bb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1171bb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1171bb 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1171c0 (StorePre 0x1171c0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1171c0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1171c0 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1171c5 (movR64M64Effect 0x1171c5 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1171c5 (LoadPre 0x1171c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1171c5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1171c5 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1171ca (movR64M64Effect 0x1171ca 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1171ca (LoadPre 0x1171ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1171ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1171ca 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1171cf (StorePre 0x1171cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1171cf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1171cf 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1171d4 (StorePre 0x1171d4 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1171d4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1171d4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1171d8 (movR64R64Effect 0x1171d8 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 69) (.exec 0x1171d8 (fun s => s.RIP = 0x1171d8) (movR64R64Effect 0x1171d8 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 70) (.out 0x1171db (movR64R64Effect 0x1171db 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1171db (fun s => s.RIP = 0x1171db) (movR64R64Effect 0x1171db 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1171de (callEffect (fun _ => 0x1145f0) 0x1171e3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1171de (PushPre 0x1171de 5) (callEffect (fun _ => 0x1145f0) 0x1171e3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1171e3⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1171e3, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1171a7 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xF6, 0xE8, 0x0D, 0xD4, 0xFF, 0xFF]

theorem code_l1171a7 : ∀ x ∈ codeRange 0x1171a7 bytes_l1171a7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x171a7 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1171e3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1171e3 (movR64M64Effect 0x1171e3 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1171e3 (LoadPre 0x1171e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1171e3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1171e3 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1171e8 (StorePre 0x1171e8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1171e8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1171e8 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1171ed (movR64M64Effect 0x1171ed 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1171ed (LoadPre 0x1171ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1171ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1171ed 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1171f2 (StorePre 0x1171f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1171f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1171f2 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1171f7 (movR64M64Effect 0x1171f7 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1171f7 (LoadPre 0x1171f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1171f7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1171f7 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1171fc (StorePre 0x1171fc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1171fc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1171fc 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117201 (movR64M64Effect 0x117201 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117201 (LoadPre 0x117201 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117201 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117201 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117206 (movR64M64Effect 0x117206 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117206 (LoadPre 0x117206 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117206 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117206 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11720b (StorePre 0x11720b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11720b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11720b 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117210 (StorePre 0x117210 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117210 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117210 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117214 (movR64R64Effect 0x117214 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 69) (.exec 0x117214 (fun s => s.RIP = 0x117214) (movR64R64Effect 0x117214 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 70) (.out 0x117217 (movR64R64Effect 0x117217 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117217 (fun s => s.RIP = 0x117217) (movR64R64Effect 0x117217 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11721a (callEffect (fun _ => 0x1145f0) 0x11721f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11721a (PushPre 0x11721a 5) (callEffect (fun _ => 0x1145f0) 0x11721f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11721f⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11721f, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1171e3 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xF6, 0xE8, 0xD1, 0xD3, 0xFF, 0xFF]

theorem code_l1171e3 : ∀ x ∈ codeRange 0x1171e3 bytes_l1171e3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x171e3 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11721f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11721f (movR64M64Effect 0x11721f 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11721f (LoadPre 0x11721f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11721f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11721f 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117224 (StorePre 0x117224 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117224 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117224 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117229 (movR64M64Effect 0x117229 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117229 (LoadPre 0x117229 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117229 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117229 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11722e (StorePre 0x11722e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11722e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11722e 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117233 (movR64M64Effect 0x117233 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117233 (LoadPre 0x117233 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117233 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117233 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117238 (StorePre 0x117238 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117238 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117238 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11723d (movR64M64Effect 0x11723d 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11723d (LoadPre 0x11723d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11723d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11723d 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117242 (movR64M64Effect 0x117242 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117242 (LoadPre 0x117242 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117242 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117242 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117247 (StorePre 0x117247 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117247 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117247 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11724c (StorePre 0x11724c 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11724c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11724c 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117250 (movR64R64Effect 0x117250 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 69) (.exec 0x117250 (fun s => s.RIP = 0x117250) (movR64R64Effect 0x117250 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 70) (.out 0x117253 (movR64R64Effect 0x117253 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117253 (fun s => s.RIP = 0x117253) (movR64R64Effect 0x117253 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117256 (callEffect (fun _ => 0x1145f0) 0x11725b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117256 (PushPre 0x117256 5) (callEffect (fun _ => 0x1145f0) 0x11725b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11725b⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11725b, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11721f : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xF6, 0xE8, 0x95, 0xD3, 0xFF, 0xFF]

theorem code_l11721f : ∀ x ∈ codeRange 0x11721f bytes_l11721f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1721f 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11725b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11725b (movR64M64Effect 0x11725b 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11725b (LoadPre 0x11725b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11725b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11725b 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117260 (StorePre 0x117260 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117260 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117260 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117265 (movR64M64Effect 0x117265 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117265 (LoadPre 0x117265 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117265 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117265 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11726a (StorePre 0x11726a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11726a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11726a 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11726f (movR64M64Effect 0x11726f 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11726f (LoadPre 0x11726f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11726f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11726f 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117274 (StorePre 0x117274 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117274 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117274 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117279 (movR64M64Effect 0x117279 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117279 (LoadPre 0x117279 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117279 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117279 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11727e (movR64M64Effect 0x11727e 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11727e (LoadPre 0x11727e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11727e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11727e 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117283 (StorePre 0x117283 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117283 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117283 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117288 (StorePre 0x117288 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117288 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117288 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11728c (movR64R64Effect 0x11728c 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 69) (.exec 0x11728c (fun s => s.RIP = 0x11728c) (movR64R64Effect 0x11728c 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 70) (.out 0x11728f (movR64R64Effect 0x11728f 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11728f (fun s => s.RIP = 0x11728f) (movR64R64Effect 0x11728f 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117292 (callEffect (fun _ => 0x1145f0) 0x117297) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117292 (PushPre 0x117292 5) (callEffect (fun _ => 0x1145f0) 0x117297) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117297⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117297, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11725b : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xF6, 0xE8, 0x59, 0xD3, 0xFF, 0xFF]

theorem code_l11725b : ∀ x ∈ codeRange 0x11725b bytes_l11725b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1725b 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l117297_12 : Block Op Label signature Reg.count 572 :=
  .letOp (n := 572) (.exec 0x1176a8 (StorePre 0x1176a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1176a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1176a8 13 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[570, 4]
    (.letOp (n := 573) (.exec 0x1176b0 (StorePre 0x1176b0 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1176b0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1176b0 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 13, .gpr 4] [])) #v[570, 4]
    (.letOp (n := 574) (.out 0x1176b4 (movR64M64Effect 0x1176b4 13 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 575) (.exec 0x1176b4 (LoadPre 0x1176b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1176b4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1176b4 13 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 576) (.out 0x1176bc (andR64R64Effect 0x1176bc 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[574, 502]
    (.letOp (n := 577) (.exec 0x1176bc (fun s => s.RIP = 0x1176bc) (andR64R64Effect 0x1176bc 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[574, 502]
    (.letOp (n := 578) (.exec 0x1176bf (StorePre 0x1176bf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1176bf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1176bf 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[576, 4]
    (.letOp (n := 579) (.out 0x1176c4 (andR64R64Effect 0x1176c4 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[535, 502]
    (.letOp (n := 580) (.exec 0x1176c4 (fun s => s.RIP = 0x1176c4) (andR64R64Effect 0x1176c4 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[535, 502]
    (.letOp (n := 581) (.exec 0x1176c7 (StorePre 0x1176c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1176c7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1176c7 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[579, 4]
    (.letOp (n := 582) (.out 0x1176cc (movR64R64Effect 0x1176cc 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[579]
    (.letOp (n := 583) (.exec 0x1176cc (fun s => s.RIP = 0x1176cc) (movR64R64Effect 0x1176cc 5 9) (Reg.operands [.gpr 9] [])) #v[579]
    (.letOp (n := 584) (.out 0x1176cf (andR64R64Effect 0x1176cf 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[552, 502]
    (.letOp (n := 585) (.exec 0x1176cf (fun s => s.RIP = 0x1176cf) (andR64R64Effect 0x1176cf 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[552, 502]
    (.letOp (n := 586) (.exec 0x1176d2 (StorePre 0x1176d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1176d2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1176d2 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[584, 4]
    (.letOp (n := 587) (.out 0x1176d7 (movR64R64Effect 0x1176d7 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 1] []) (.reg (.gpr 15))) #v[584]
    (.letOp (n := 588) (.exec 0x1176d7 (fun s => s.RIP = 0x1176d7) (movR64R64Effect 0x1176d7 15 1) (Reg.operands [.gpr 1] [])) #v[584]
    (.letOp (n := 589) (.exec 0x1176da (StorePre 0x1176da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1176da + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1176da 12 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[566, 4]
    (.letOp (n := 590) (.out 0x1176df (leaR64Effect 0x1176df 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 591) (.exec 0x1176df (fun s => s.RIP = 0x1176df) (leaR64Effect 0x1176df 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 592) (.out 0x1176e4 (movR64R64Effect 0x1176e4 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 593) (.exec 0x1176e4 (fun s => s.RIP = 0x1176e4) (movR64R64Effect 0x1176e4 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 594) (.out 0x1176e7 (movR64R64Effect 0x1176e7 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[590]
    (.letOp (n := 595) (.exec 0x1176e7 (fun s => s.RIP = 0x1176e7) (movR64R64Effect 0x1176e7 7 3) (Reg.operands [.gpr 3] [])) #v[590]
    (.letOp (n := 596) (.out 0x1176ea (movR64R64Effect 0x1176ea 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[592]
    (.letOp (n := 597) (.exec 0x1176ea (fun s => s.RIP = 0x1176ea) (movR64R64Effect 0x1176ea 6 14) (Reg.operands [.gpr 14] [])) #v[592]
    (.letOp (n := 598) (.out 0x1176ed (callEffect (fun _ => 0x1145f0) 0x1176f2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 599) (.exec 0x1176ed (PushPre 0x1176ed 5) (callEffect (fun _ => 0x1145f0) 0x1176f2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 600) (.const ⟨64, 0x1176f2⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 560), (1, 584), (2, 557), (3, 590), (4, 598), (5, 582), (6, 596), (7, 594), (8, 531), (9, 579), (10, 472), (11, 466), (12, 566), (13, 576), (14, 592), (15, 587), (22, 22), (39, 39), (50, 50), (51, 51)] 601⟩ { target := .l1176f2, kept := #v[], arity := rfl, guard := some (Fin.last 600) }))))))))))))))))))))))))))))))

def bytes_l117297_12 : List UInt8 :=
  [0x4C, 0x89, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x2C, 0x24, 0x4C, 0x8B, 0xAC, 0x24,
    0xC0, 0x00, 0x00, 0x00, 0x4D, 0x21, 0xFD, 0x4C, 0x89, 0x6C, 0x24, 0x08, 0x4D, 0x21, 0xF9, 0x4C,
    0x89, 0x4C, 0x24, 0x10, 0x4C, 0x89, 0xCD, 0x4C, 0x21, 0xF9, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x49,
    0x89, 0xCF, 0x4C, 0x89, 0x64, 0x24, 0x20, 0x48, 0x8D, 0x5C, 0x24, 0x28, 0x49, 0x89, 0xE6, 0x48,
    0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xFE, 0xCE, 0xFF, 0xFF]

theorem code_l117297_12 : ∀ x ∈ codeRange 0x1176a8 bytes_l117297_12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x176a8 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l117297_11 : Block Op Label signature Reg.count 531 :=
  .letOp (n := 531) (.out 0x117650 (shldR64R64Effect 0x117650 5 8 3 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[498, 495]
    (.letOp (n := 532) (.exec 0x117650 (fun s => s.RIP = 0x117650) (shldR64R64Effect 0x117650 5 8 3 12) (Reg.operands [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[498, 495]
    (.letOp (n := 533) (.out 0x117655 (shldR64R64Effect 0x117655 5 6 13 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[529, 526]
    (.letOp (n := 534) (.exec 0x117655 (fun s => s.RIP = 0x117655) (shldR64R64Effect 0x117655 5 6 13 12) (Reg.operands [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[529, 526]
    (.letOp (n := 535) (.out 0x11765a (movR64R64Effect 0x11765a 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 13] []) (.reg (.gpr 9))) #v[526]
    (.letOp (n := 536) (.exec 0x11765a (fun s => s.RIP = 0x11765a) (movR64R64Effect 0x11765a 9 13) (Reg.operands [.gpr 13] [])) #v[526]
    (.letOp (n := 537) (.out 0x11765d (movR64R64Effect 0x11765d 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[531]
    (.letOp (n := 538) (.exec 0x11765d (fun s => s.RIP = 0x11765d) (movR64R64Effect 0x11765d 0 8) (Reg.operands [.gpr 8] [])) #v[531]
    (.letOp (n := 539) (.out 0x117660 (mulR64Effect 0x117660 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[506, 537]
    (.letOp (n := 540) (.out 0x117660 (mulR64Effect 0x117660 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[506, 537]
    (.letOp (n := 541) (.exec 0x117660 (fun s => s.RIP = 0x117660) (mulR64Effect 0x117660 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[506, 537]
    (.letOp (n := 542) (.exec 0x117663 (StorePre 0x117663 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117663 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117663 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[486, 4]
    (.letOp (n := 543) (.out 0x117668 (movR64M64Effect 0x117668 1 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 544) (.exec 0x117668 (LoadPre 0x117668 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x117668 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117668 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 545) (.out 0x11766d (andR64R64Effect 0x11766d 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[543, 502]
    (.letOp (n := 546) (.exec 0x11766d (fun s => s.RIP = 0x11766d) (andR64R64Effect 0x11766d 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[543, 502]
    (.letOp (n := 547) (.out 0x117670 (addR64R64Effect 0x117670 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[545, 539]
    (.letOp (n := 548) (.out 0x117670 (addR64R64Effect 0x117670 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[545, 539]
    (.letOp (n := 549) (.exec 0x117670 (fun s => s.RIP = 0x117670) (addR64R64Effect 0x117670 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[545, 539]
    (.letOp (n := 550) (.out 0x117673 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117673 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[540, 548]
    (.letOp (n := 551) (.exec 0x117673 (fun s => s.RIP = 0x117673) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117673 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[540, 548]
    (.letOp (n := 552) (.out 0x117677 (addR64R64Effect 0x117677 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[547, 533]
    (.letOp (n := 553) (.out 0x117677 (addR64R64Effect 0x117677 1 6) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 6] []) (.flag .CF)) #v[547, 533]
    (.letOp (n := 554) (.exec 0x117677 (fun s => s.RIP = 0x117677) (addR64R64Effect 0x117677 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[547, 533]
    (.letOp (n := 555) (.out 0x11767a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11767a 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[550, 553]
    (.letOp (n := 556) (.exec 0x11767a (fun s => s.RIP = 0x11767a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11767a 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[550, 553]
    (.letOp (n := 557) (.out 0x11767e (shldR64R64Effect 0x11767e 5 2 1 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[555, 552]
    (.letOp (n := 558) (.exec 0x11767e (fun s => s.RIP = 0x11767e) (shldR64R64Effect 0x11767e 5 2 1 12) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[555, 552]
    (.letOp (n := 559) (.exec 0x117683 (StorePre 0x117683 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117683 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117683 10 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[472, 4]
    (.letOp (n := 560) (.out 0x117688 (movR64Imm64Effect 0x117688 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 561) (.exec 0x117688 (fun s => s.RIP = 0x117688) (movR64Imm64Effect 0x117688 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 562) (.out 0x117692 (movR64M64Effect 0x117692 12 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 563) (.exec 0x117692 (LoadPre 0x117692 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x117692 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117692 12 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 564) (.out 0x117697 (andR64R64Effect 0x117697 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[562, 560]
    (.letOp (n := 565) (.exec 0x117697 (fun s => s.RIP = 0x117697) (andR64R64Effect 0x117697 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[562, 560]
    (.letOp (n := 566) (.out 0x11769a (addR64R64Effect 0x11769a 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[564, 557]
    (.letOp (n := 567) (.exec 0x11769a (fun s => s.RIP = 0x11769a) (addR64R64Effect 0x11769a 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[564, 557]
    (.letOp (n := 568) (.out 0x11769d (movR64M64Effect 0x11769d 13 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 569) (.exec 0x11769d (LoadPre 0x11769d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11769d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11769d 13 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 570) (.out 0x1176a5 (andR64R64Effect 0x1176a5 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[568, 502]
    (.letOp (n := 571) (.exec 0x1176a5 (fun s => s.RIP = 0x1176a5) (andR64R64Effect 0x1176a5 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[568, 502]
    (b_l117297_12)))))))))))))))))))))))))))))))))))))))))

def bytes_l117297_11 : List UInt8 :=
  [0x49, 0x0F, 0xA4, 0xD8, 0x0C, 0x4C, 0x0F, 0xA4, 0xEE, 0x0C, 0x4D, 0x89, 0xE9, 0x4C, 0x89, 0xC0,
    0x48, 0xF7, 0xE7, 0x48, 0x89, 0x6C, 0x24, 0x20, 0x48, 0x8B, 0x4C, 0x24, 0x68, 0x4C, 0x21, 0xF9,
    0x48, 0x01, 0xC1, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x01, 0xF1, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x0F,
    0xA4, 0xCA, 0x0C, 0x4C, 0x89, 0x54, 0x24, 0x18, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x00, 0x00, 0x4C, 0x8B, 0x64, 0x24, 0x70, 0x49, 0x21, 0xC4, 0x49, 0x01, 0xD4, 0x4C, 0x8B, 0xAC,
    0x24, 0x88, 0x00, 0x00, 0x00, 0x4D, 0x21, 0xFD] ++ bytes_l117297_12

theorem code_l117297_11 : ∀ x ∈ codeRange 0x117650 bytes_l117297_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17650 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117297_12

def b_l117297_10 : Block Op Label signature Reg.count 483 :=
  .letOp (n := 483) (.out 0x117602 (mulR64Effect 0x117602 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[395, 481]
    (.letOp (n := 484) (.out 0x117602 (mulR64Effect 0x117602 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[395, 481]
    (.letOp (n := 485) (.exec 0x117602 (fun s => s.RIP = 0x117602) (mulR64Effect 0x117602 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[395, 481]
    (.letOp (n := 486) (.out 0x117605 (movR64R64Effect 0x117605 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[395]
    (.letOp (n := 487) (.exec 0x117605 (fun s => s.RIP = 0x117605) (movR64R64Effect 0x117605 5 9) (Reg.operands [.gpr 9] [])) #v[395]
    (.letOp (n := 488) (.out 0x117608 (movR64R64Effect 0x117608 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[483]
    (.letOp (n := 489) (.exec 0x117608 (fun s => s.RIP = 0x117608) (movR64R64Effect 0x117608 3 0) (Reg.operands [.gpr 0] [])) #v[483]
    (.letOp (n := 490) (.out 0x11760b (addR64R64Effect 0x11760b 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[488, 479]
    (.letOp (n := 491) (.out 0x11760b (addR64R64Effect 0x11760b 3 15) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 15] []) (.flag .CF)) #v[488, 479]
    (.letOp (n := 492) (.exec 0x11760b (fun s => s.RIP = 0x11760b) (addR64R64Effect 0x11760b 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[488, 479]
    (.letOp (n := 493) (.out 0x11760e (atFlags StatusFlags.CF (adcR64R64Effect 0x11760e 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[477, 484, 491]
    (.letOp (n := 494) (.exec 0x11760e (fun s => s.RIP = 0x11760e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11760e 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[477, 484, 491]
    (.letOp (n := 495) (.out 0x117611 (addR64R64Effect 0x117611 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[490, 415]
    (.letOp (n := 496) (.out 0x117611 (addR64R64Effect 0x117611 3 7) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 7] []) (.flag .CF)) #v[490, 415]
    (.letOp (n := 497) (.exec 0x117611 (fun s => s.RIP = 0x117611) (addR64R64Effect 0x117611 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[490, 415]
    (.letOp (n := 498) (.out 0x117614 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117614 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[493, 496]
    (.letOp (n := 499) (.exec 0x117614 (fun s => s.RIP = 0x117614) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117614 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[493, 496]
    (.letOp (n := 500) (.out 0x117618 (movR64R64Effect 0x117618 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[495]
    (.letOp (n := 501) (.exec 0x117618 (fun s => s.RIP = 0x117618) (movR64R64Effect 0x117618 0 3) (Reg.operands [.gpr 3] [])) #v[495]
    (.letOp (n := 502) (.out 0x11761b (movR64Imm64Effect 0x11761b 15 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 503) (.exec 0x11761b (fun s => s.RIP = 0x11761b) (movR64Imm64Effect 0x11761b 15 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 504) (.out 0x117625 (andR64R64Effect 0x117625 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[500, 502]
    (.letOp (n := 505) (.exec 0x117625 (fun s => s.RIP = 0x117625) (andR64R64Effect 0x117625 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[500, 502]
    (.letOp (n := 506) (.out 0x117628 (movR64Imm64Effect 0x117628 7 0x1000003d10) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 507) (.exec 0x117628 (fun s => s.RIP = 0x117628) (movR64Imm64Effect 0x117628 7 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 508) (.out 0x117632 (mulR64Effect 0x117632 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[506, 504]
    (.letOp (n := 509) (.out 0x117632 (mulR64Effect 0x117632 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[506, 504]
    (.letOp (n := 510) (.exec 0x117632 (fun s => s.RIP = 0x117632) (mulR64Effect 0x117632 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[506, 504]
    (.letOp (n := 511) (.out 0x117635 (addR64R64Effect 0x117635 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[459, 450]
    (.letOp (n := 512) (.out 0x117635 (addR64R64Effect 0x117635 13 12) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 12] []) (.flag .CF)) #v[459, 450]
    (.letOp (n := 513) (.exec 0x117635 (fun s => s.RIP = 0x117635) (addR64R64Effect 0x117635 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[459, 450]
    (.letOp (n := 514) (.out 0x117638 (atFlags StatusFlags.CF (adcR64M64Effect 0x117638 6 (.sib 4 none 0 (.d8 0x60)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[457, 4, 512]
    (.letOp (n := 515) (.exec 0x117638 (LoadPre 0x117638 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x117638 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x117638 6 (.sib 4 none 0 (.d8 0x60)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[457, 4, 512]
    (.letOp (n := 516) (.out 0x11763d (addR64R64Effect 0x11763d 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[511, 468]
    (.letOp (n := 517) (.out 0x11763d (addR64R64Effect 0x11763d 13 14) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 14] []) (.flag .CF)) #v[511, 468]
    (.letOp (n := 518) (.exec 0x11763d (fun s => s.RIP = 0x11763d) (addR64R64Effect 0x11763d 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[511, 468]
    (.letOp (n := 519) (.out 0x117640 (atFlags StatusFlags.CF (adcR64R64Effect 0x117640 6 11)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[514, 466, 517]
    (.letOp (n := 520) (.exec 0x117640 (fun s => s.RIP = 0x117640) (atFlags StatusFlags.CF (adcR64R64Effect 0x117640 6 11)) (Reg.operands [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[514, 466, 517]
    (.letOp (n := 521) (.out 0x117643 (addR64R64Effect 0x117643 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[516, 508]
    (.letOp (n := 522) (.out 0x117643 (addR64R64Effect 0x117643 13 0) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 0] []) (.flag .CF)) #v[516, 508]
    (.letOp (n := 523) (.exec 0x117643 (fun s => s.RIP = 0x117643) (addR64R64Effect 0x117643 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[516, 508]
    (.letOp (n := 524) (.out 0x117646 (atFlags StatusFlags.CF (adcR64R64Effect 0x117646 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[519, 509, 522]
    (.letOp (n := 525) (.exec 0x117646 (fun s => s.RIP = 0x117646) (atFlags StatusFlags.CF (adcR64R64Effect 0x117646 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[519, 509, 522]
    (.letOp (n := 526) (.out 0x117649 (addR64R64Effect 0x117649 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[521, 442]
    (.letOp (n := 527) (.out 0x117649 (addR64R64Effect 0x117649 13 1) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 1] []) (.flag .CF)) #v[521, 442]
    (.letOp (n := 528) (.exec 0x117649 (fun s => s.RIP = 0x117649) (addR64R64Effect 0x117649 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[521, 442]
    (.letOp (n := 529) (.out 0x11764c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11764c 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[524, 527]
    (.letOp (n := 530) (.exec 0x11764c (fun s => s.RIP = 0x11764c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11764c 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[524, 527]
    (b_l117297_11))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l117297_10 : List UInt8 :=
  [0x49, 0xF7, 0xE1, 0x4C, 0x89, 0xCD, 0x48, 0x89, 0xC3, 0x4C, 0x01, 0xFB, 0x49, 0x11, 0xD0, 0x48,
    0x01, 0xFB, 0x49, 0x83, 0xD0, 0x00, 0x48, 0x89, 0xD8, 0x49, 0xBF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xF8, 0x48, 0xBF, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE7, 0x4D, 0x01, 0xE5, 0x48, 0x13, 0x74, 0x24, 0x60, 0x4D, 0x01, 0xF5, 0x4C, 0x11,
    0xDE, 0x49, 0x01, 0xC5, 0x48, 0x11, 0xD6, 0x49, 0x01, 0xCD, 0x48, 0x83, 0xD6, 0x00] ++ bytes_l117297_11

theorem code_l117297_10 : ∀ x ∈ codeRange 0x117602 bytes_l117297_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17602 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117297_11

def b_l117297_9 : Block Op Label signature Reg.count 440 :=
  .letOp (n := 440) (.out 0x1175a9 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1175a9 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[434, 437]
    (.letOp (n := 441) (.exec 0x1175a9 (fun s => s.RIP = 0x1175a9) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1175a9 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[434, 437]
    (.letOp (n := 442) (.out 0x1175ad (shldR64R64Effect 0x1175ad 5 1 15 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[440, 436]
    (.letOp (n := 443) (.exec 0x1175ad (fun s => s.RIP = 0x1175ad) (shldR64R64Effect 0x1175ad 5 1 15 12) (Reg.operands [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[440, 436]
    (.letOp (n := 444) (.out 0x1175b2 (movR64R64Effect 0x1175b2 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[391]
    (.letOp (n := 445) (.exec 0x1175b2 (fun s => s.RIP = 0x1175b2) (movR64R64Effect 0x1175b2 0 12) (Reg.operands [.gpr 12] [])) #v[391]
    (.letOp (n := 446) (.out 0x1175b5 (mulM64Effect 0x1175b5 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[444, 4]
    (.letOp (n := 447) (.out 0x1175b5 (mulM64Effect 0x1175b5 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[444, 4]
    (.letOp (n := 448) (.exec 0x1175b5 (LoadPre 0x1175b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1175b5 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1175b5 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[444, 4]
    (.letOp (n := 449) (.exec 0x1175ba (StorePre 0x1175ba 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1175ba + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1175ba 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[447, 4]
    (.letOp (n := 450) (.out 0x1175bf (movR64R64Effect 0x1175bf 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[446]
    (.letOp (n := 451) (.exec 0x1175bf (fun s => s.RIP = 0x1175bf) (movR64R64Effect 0x1175bf 12 0) (Reg.operands [.gpr 0] [])) #v[446]
    (.letOp (n := 452) (.out 0x1175c2 (movR64M64Effect 0x1175c2 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 453) (.exec 0x1175c2 (LoadPre 0x1175c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1175c2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1175c2 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 454) (.out 0x1175ca (mulR64Effect 0x1175ca 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[362, 452]
    (.letOp (n := 455) (.out 0x1175ca (mulR64Effect 0x1175ca 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[362, 452]
    (.letOp (n := 456) (.exec 0x1175ca (fun s => s.RIP = 0x1175ca) (mulR64Effect 0x1175ca 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[362, 452]
    (.letOp (n := 457) (.out 0x1175cd (movR64R64Effect 0x1175cd 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[455]
    (.letOp (n := 458) (.exec 0x1175cd (fun s => s.RIP = 0x1175cd) (movR64R64Effect 0x1175cd 6 2) (Reg.operands [.gpr 2] [])) #v[455]
    (.letOp (n := 459) (.out 0x1175d0 (movR64R64Effect 0x1175d0 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[454]
    (.letOp (n := 460) (.exec 0x1175d0 (fun s => s.RIP = 0x1175d0) (movR64R64Effect 0x1175d0 13 0) (Reg.operands [.gpr 0] [])) #v[454]
    (.letOp (n := 461) (.out 0x1175d3 (movR64M64Effect 0x1175d3 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 462) (.exec 0x1175d3 (LoadPre 0x1175d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1175d3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1175d3 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 463) (.out 0x1175d8 (mulM64Effect 0x1175d8 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[461, 4]
    (.letOp (n := 464) (.out 0x1175d8 (mulM64Effect 0x1175d8 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[461, 4]
    (.letOp (n := 465) (.exec 0x1175d8 (LoadPre 0x1175d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1175d8 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1175d8 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[461, 4]
    (.letOp (n := 466) (.out 0x1175e0 (movR64R64Effect 0x1175e0 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[464]
    (.letOp (n := 467) (.exec 0x1175e0 (fun s => s.RIP = 0x1175e0) (movR64R64Effect 0x1175e0 11 2) (Reg.operands [.gpr 2] [])) #v[464]
    (.letOp (n := 468) (.out 0x1175e3 (movR64R64Effect 0x1175e3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[463]
    (.letOp (n := 469) (.exec 0x1175e3 (fun s => s.RIP = 0x1175e3) (movR64R64Effect 0x1175e3 14 0) (Reg.operands [.gpr 0] [])) #v[463]
    (.letOp (n := 470) (.out 0x1175e6 (movR64R64Effect 0x1175e6 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[371]
    (.letOp (n := 471) (.exec 0x1175e6 (fun s => s.RIP = 0x1175e6) (movR64R64Effect 0x1175e6 0 5) (Reg.operands [.gpr 5] [])) #v[371]
    (.letOp (n := 472) (.out 0x1175e9 (movR64M64Effect 0x1175e9 10 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 473) (.exec 0x1175e9 (LoadPre 0x1175e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1175e9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1175e9 10 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 474) (.out 0x1175f1 (mulR64Effect 0x1175f1 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[472, 470]
    (.letOp (n := 475) (.out 0x1175f1 (mulR64Effect 0x1175f1 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[472, 470]
    (.letOp (n := 476) (.exec 0x1175f1 (fun s => s.RIP = 0x1175f1) (mulR64Effect 0x1175f1 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[472, 470]
    (.letOp (n := 477) (.out 0x1175f4 (movR64R64Effect 0x1175f4 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[475]
    (.letOp (n := 478) (.exec 0x1175f4 (fun s => s.RIP = 0x1175f4) (movR64R64Effect 0x1175f4 8 2) (Reg.operands [.gpr 2] [])) #v[475]
    (.letOp (n := 479) (.out 0x1175f7 (movR64R64Effect 0x1175f7 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[474]
    (.letOp (n := 480) (.exec 0x1175f7 (fun s => s.RIP = 0x1175f7) (movR64R64Effect 0x1175f7 15 0) (Reg.operands [.gpr 0] [])) #v[474]
    (.letOp (n := 481) (.out 0x1175fa (movR64M64Effect 0x1175fa 0 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 482) (.exec 0x1175fa (LoadPre 0x1175fa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1175fa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1175fa 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l117297_10)))))))))))))))))))))))))))))))))))))))))))

def bytes_l117297_9 : List UInt8 :=
  [0x48, 0x83, 0xD1, 0x00, 0x4C, 0x0F, 0xA4, 0xF9, 0x0C, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0x64, 0x24,
    0x60, 0x48, 0x89, 0x54, 0x24, 0x60, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC5, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48,
    0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD3, 0x49, 0x89, 0xC6, 0x48, 0x89, 0xE8,
    0x4C, 0x8B, 0x94, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD0, 0x49, 0x89,
    0xC7, 0x48, 0x8B, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] ++ bytes_l117297_10

theorem code_l117297_9 : ∀ x ∈ codeRange 0x1175a9 bytes_l117297_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x175a9 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117297_10

def b_l117297_8 : Block Op Label signature Reg.count 393 :=
  .letOp (n := 393) (.out 0x11754d (movR64R64Effect 0x11754d 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[391]
    (.letOp (n := 394) (.exec 0x11754d (fun s => s.RIP = 0x11754d) (movR64R64Effect 0x11754d 0 12) (Reg.operands [.gpr 12] [])) #v[391]
    (.letOp (n := 395) (.out 0x117550 (movR64M64Effect 0x117550 9 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 396) (.exec 0x117550 (LoadPre 0x117550 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x117550 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117550 9 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 397) (.out 0x117558 (mulR64Effect 0x117558 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[395, 393]
    (.letOp (n := 398) (.out 0x117558 (mulR64Effect 0x117558 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[395, 393]
    (.letOp (n := 399) (.exec 0x117558 (fun s => s.RIP = 0x117558) (mulR64Effect 0x117558 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[395, 393]
    (.letOp (n := 400) (.out 0x11755b (addR64R64Effect 0x11755b 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[389, 380]
    (.letOp (n := 401) (.out 0x11755b (addR64R64Effect 0x11755b 14 3) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 3] []) (.flag .CF)) #v[389, 380]
    (.letOp (n := 402) (.exec 0x11755b (fun s => s.RIP = 0x11755b) (addR64R64Effect 0x11755b 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[389, 380]
    (.letOp (n := 403) (.out 0x11755e (atFlags StatusFlags.CF (adcR64R64Effect 0x11755e 7 11)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[387, 378, 401]
    (.letOp (n := 404) (.exec 0x11755e (fun s => s.RIP = 0x11755e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11755e 7 11)) (Reg.operands [.gpr 7, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[387, 378, 401]
    (.letOp (n := 405) (.out 0x117561 (addR64R64Effect 0x117561 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[397, 400]
    (.letOp (n := 406) (.out 0x117561 (addR64R64Effect 0x117561 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[397, 400]
    (.letOp (n := 407) (.exec 0x117561 (fun s => s.RIP = 0x117561) (addR64R64Effect 0x117561 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[397, 400]
    (.letOp (n := 408) (.out 0x117564 (atFlags StatusFlags.CF (adcR64R64Effect 0x117564 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[403, 398, 406]
    (.letOp (n := 409) (.exec 0x117564 (fun s => s.RIP = 0x117564) (atFlags StatusFlags.CF (adcR64R64Effect 0x117564 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[403, 398, 406]
    (.letOp (n := 410) (.out 0x117567 (addR64R64Effect 0x117567 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[405, 327]
    (.letOp (n := 411) (.out 0x117567 (addR64R64Effect 0x117567 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[405, 327]
    (.letOp (n := 412) (.exec 0x117567 (fun s => s.RIP = 0x117567) (addR64R64Effect 0x117567 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[405, 327]
    (.letOp (n := 413) (.out 0x11756a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11756a 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[408, 411]
    (.letOp (n := 414) (.exec 0x11756a (fun s => s.RIP = 0x11756a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11756a 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[408, 411]
    (.letOp (n := 415) (.out 0x11756e (shldR64R64Effect 0x11756e 5 7 0 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[413, 410]
    (.letOp (n := 416) (.exec 0x11756e (fun s => s.RIP = 0x11756e) (shldR64R64Effect 0x11756e 5 7 0 12) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[413, 410]
    (.letOp (n := 417) (.out 0x117573 (movR64Imm64Effect 0x117573 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 418) (.exec 0x117573 (fun s => s.RIP = 0x117573) (movR64Imm64Effect 0x117573 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 419) (.out 0x11757d (andR64R64Effect 0x11757d 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[410, 417]
    (.letOp (n := 420) (.exec 0x11757d (fun s => s.RIP = 0x11757d) (andR64R64Effect 0x11757d 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[410, 417]
    (.letOp (n := 421) (.out 0x117580 (movR64Imm64Effect 0x117580 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 422) (.exec 0x117580 (fun s => s.RIP = 0x117580) (movR64Imm64Effect 0x117580 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 423) (.out 0x11758a (mulR64Effect 0x11758a 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[421, 419]
    (.letOp (n := 424) (.out 0x11758a (mulR64Effect 0x11758a 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[421, 419]
    (.letOp (n := 425) (.exec 0x11758a (fun s => s.RIP = 0x11758a) (mulR64Effect 0x11758a 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[421, 419]
    (.letOp (n := 426) (.out 0x11758d (addR64R64Effect 0x11758d 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[369, 358]
    (.letOp (n := 427) (.out 0x11758d (addR64R64Effect 0x11758d 15 13) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 13] []) (.flag .CF)) #v[369, 358]
    (.letOp (n := 428) (.exec 0x11758d (fun s => s.RIP = 0x11758d) (addR64R64Effect 0x11758d 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[369, 358]
    (.letOp (n := 429) (.out 0x117590 (atFlags StatusFlags.CF (adcR64M64Effect 0x117590 1 (.sib 4 none 0 (.d32 0xc0)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[367, 4, 427]
    (.letOp (n := 430) (.exec 0x117590 (LoadPre 0x117590 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x117590 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x117590 1 (.sib 4 none 0 (.d32 0xc0)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[367, 4, 427]
    (.letOp (n := 431) (.out 0x117598 (addR64R64Effect 0x117598 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[426, 423]
    (.letOp (n := 432) (.out 0x117598 (addR64R64Effect 0x117598 15 0) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 0] []) (.flag .CF)) #v[426, 423]
    (.letOp (n := 433) (.exec 0x117598 (fun s => s.RIP = 0x117598) (addR64R64Effect 0x117598 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[426, 423]
    (.letOp (n := 434) (.out 0x11759b (atFlags StatusFlags.CF (adcR64R64Effect 0x11759b 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[429, 424, 432]
    (.letOp (n := 435) (.exec 0x11759b (fun s => s.RIP = 0x11759b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11759b 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[429, 424, 432]
    (.letOp (n := 436) (.out 0x11759e (addR64R64Effect 0x11759e 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[431, 350]
    (.letOp (n := 437) (.out 0x11759e (addR64R64Effect 0x11759e 15 8) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 8] []) (.flag .CF)) #v[431, 350]
    (.letOp (n := 438) (.exec 0x11759e (fun s => s.RIP = 0x11759e) (addR64R64Effect 0x11759e 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[431, 350]
    (.letOp (n := 439) (.exec 0x1175a1 (StorePre 0x1175a1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1175a1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1175a1 15 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[436, 4]
    (b_l117297_9)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l117297_8 : List UInt8 :=
  [0x4C, 0x89, 0xE0, 0x4C, 0x8B, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE1, 0x49, 0x01,
    0xDE, 0x4C, 0x11, 0xDF, 0x4C, 0x01, 0xF0, 0x48, 0x11, 0xD7, 0x48, 0x01, 0xF0, 0x48, 0x83, 0xD7,
    0x00, 0x48, 0x0F, 0xA4, 0xC7, 0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x4D, 0x01, 0xEF, 0x48, 0x13, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC7, 0x48, 0x11,
    0xD1, 0x4D, 0x01, 0xC7, 0x4C, 0x89, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] ++ bytes_l117297_9

theorem code_l117297_8 : ∀ x ∈ codeRange 0x11754d bytes_l117297_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1754d 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117297_9

def b_l117297_7 : Block Op Label signature Reg.count 350 :=
  .letOp (n := 350) (.out 0x1174ff (shldR64R64Effect 0x1174ff 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[348, 344]
    (.letOp (n := 351) (.exec 0x1174ff (fun s => s.RIP = 0x1174ff) (shldR64R64Effect 0x1174ff 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[348, 344]
    (.letOp (n := 352) (.out 0x117504 (movR64R64Effect 0x117504 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[300]
    (.letOp (n := 353) (.exec 0x117504 (fun s => s.RIP = 0x117504) (movR64R64Effect 0x117504 0 5) (Reg.operands [.gpr 5] [])) #v[300]
    (.letOp (n := 354) (.out 0x117507 (mulR64Effect 0x117507 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[258, 352]
    (.letOp (n := 355) (.out 0x117507 (mulR64Effect 0x117507 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[258, 352]
    (.letOp (n := 356) (.exec 0x117507 (fun s => s.RIP = 0x117507) (mulR64Effect 0x117507 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[258, 352]
    (.letOp (n := 357) (.exec 0x11750a (StorePre 0x11750a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11750a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11750a 2 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[355, 4]
    (.letOp (n := 358) (.out 0x117512 (movR64R64Effect 0x117512 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[354]
    (.letOp (n := 359) (.exec 0x117512 (fun s => s.RIP = 0x117512) (movR64R64Effect 0x117512 13 0) (Reg.operands [.gpr 0] [])) #v[354]
    (.letOp (n := 360) (.out 0x117515 (movR64M64Effect 0x117515 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 361) (.exec 0x117515 (LoadPre 0x117515 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x117515 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117515 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 362) (.out 0x11751a (movR64M64Effect 0x11751a 10 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 363) (.exec 0x11751a (LoadPre 0x11751a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11751a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11751a 10 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 364) (.out 0x11751f (mulR64Effect 0x11751f 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[362, 360]
    (.letOp (n := 365) (.out 0x11751f (mulR64Effect 0x11751f 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[362, 360]
    (.letOp (n := 366) (.exec 0x11751f (fun s => s.RIP = 0x11751f) (mulR64Effect 0x11751f 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[362, 360]
    (.letOp (n := 367) (.out 0x117522 (movR64R64Effect 0x117522 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[365]
    (.letOp (n := 368) (.exec 0x117522 (fun s => s.RIP = 0x117522) (movR64R64Effect 0x117522 1 2) (Reg.operands [.gpr 2] [])) #v[365]
    (.letOp (n := 369) (.out 0x117525 (movR64R64Effect 0x117525 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[364]
    (.letOp (n := 370) (.exec 0x117525 (fun s => s.RIP = 0x117525) (movR64R64Effect 0x117525 15 0) (Reg.operands [.gpr 0] [])) #v[364]
    (.letOp (n := 371) (.out 0x117528 (movR64M64Effect 0x117528 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 372) (.exec 0x117528 (LoadPre 0x117528 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x117528 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117528 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 373) (.out 0x11752d (movR64R64Effect 0x11752d 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[371]
    (.letOp (n := 374) (.exec 0x11752d (fun s => s.RIP = 0x11752d) (movR64R64Effect 0x11752d 0 5) (Reg.operands [.gpr 5] [])) #v[371]
    (.letOp (n := 375) (.out 0x117530 (mulR64Effect 0x117530 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[280, 373]
    (.letOp (n := 376) (.out 0x117530 (mulR64Effect 0x117530 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[280, 373]
    (.letOp (n := 377) (.exec 0x117530 (fun s => s.RIP = 0x117530) (mulR64Effect 0x117530 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[280, 373]
    (.letOp (n := 378) (.out 0x117533 (movR64R64Effect 0x117533 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[376]
    (.letOp (n := 379) (.exec 0x117533 (fun s => s.RIP = 0x117533) (movR64R64Effect 0x117533 11 2) (Reg.operands [.gpr 2] [])) #v[376]
    (.letOp (n := 380) (.out 0x117536 (movR64R64Effect 0x117536 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[375]
    (.letOp (n := 381) (.exec 0x117536 (fun s => s.RIP = 0x117536) (movR64R64Effect 0x117536 3 0) (Reg.operands [.gpr 0] [])) #v[375]
    (.letOp (n := 382) (.out 0x117539 (movR64R64Effect 0x117539 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[276]
    (.letOp (n := 383) (.exec 0x117539 (fun s => s.RIP = 0x117539) (movR64R64Effect 0x117539 0 9) (Reg.operands [.gpr 9] [])) #v[276]
    (.letOp (n := 384) (.out 0x11753c (mulR64Effect 0x11753c 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[291, 382]
    (.letOp (n := 385) (.out 0x11753c (mulR64Effect 0x11753c 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[291, 382]
    (.letOp (n := 386) (.exec 0x11753c (fun s => s.RIP = 0x11753c) (mulR64Effect 0x11753c 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[291, 382]
    (.letOp (n := 387) (.out 0x11753f (movR64R64Effect 0x11753f 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[385]
    (.letOp (n := 388) (.exec 0x11753f (fun s => s.RIP = 0x11753f) (movR64R64Effect 0x11753f 7 2) (Reg.operands [.gpr 2] [])) #v[385]
    (.letOp (n := 389) (.out 0x117542 (movR64R64Effect 0x117542 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[384]
    (.letOp (n := 390) (.exec 0x117542 (fun s => s.RIP = 0x117542) (movR64R64Effect 0x117542 14 0) (Reg.operands [.gpr 0] [])) #v[384]
    (.letOp (n := 391) (.out 0x117545 (movR64M64Effect 0x117545 12 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 392) (.exec 0x117545 (LoadPre 0x117545 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x117545 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117545 12 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l117297_8)))))))))))))))))))))))))))))))))))))))))))

def bytes_l117297_7 : List UInt8 :=
  [0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0x94, 0x24, 0xC0,
    0x00, 0x00, 0x00, 0x49, 0x89, 0xC5, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x4C, 0x8B, 0x54, 0x24, 0x78,
    0x49, 0xF7, 0xE2, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x6C, 0x24, 0x50, 0x48, 0x89,
    0xE8, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC3, 0x4C, 0x89, 0xC8, 0x49, 0xF7, 0xE4,
    0x48, 0x89, 0xD7, 0x49, 0x89, 0xC6, 0x4C, 0x8B, 0xA4, 0x24, 0x08, 0x01, 0x00, 0x00] ++ bytes_l117297_8

theorem code_l117297_7 : ∀ x ∈ codeRange 0x1174ff bytes_l117297_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x174ff 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117297_8

def b_l117297_6 : Block Op Label signature Reg.count 304 :=
  .letOp (n := 304) (.out 0x11749d (mulM64Effect 0x11749d 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[302, 4]
    (.letOp (n := 305) (.out 0x11749d (mulM64Effect 0x11749d 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[302, 4]
    (.letOp (n := 306) (.exec 0x11749d (LoadPre 0x11749d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11749d + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11749d 8 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[302, 4]
    (.letOp (n := 307) (.out 0x1174a5 (addR64R64Effect 0x1174a5 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[287, 270]
    (.letOp (n := 308) (.out 0x1174a5 (addR64R64Effect 0x1174a5 11 8) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 8] []) (.flag .CF)) #v[287, 270]
    (.letOp (n := 309) (.exec 0x1174a5 (fun s => s.RIP = 0x1174a5) (addR64R64Effect 0x1174a5 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[287, 270]
    (.letOp (n := 310) (.out 0x1174a8 (atFlags StatusFlags.CF (adcR64R64Effect 0x1174a8 6 10)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[285, 272, 308]
    (.letOp (n := 311) (.exec 0x1174a8 (fun s => s.RIP = 0x1174a8) (atFlags StatusFlags.CF (adcR64R64Effect 0x1174a8 6 10)) (Reg.operands [.gpr 6, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[285, 272, 308]
    (.letOp (n := 312) (.out 0x1174ab (addR64R64Effect 0x1174ab 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[307, 298]
    (.letOp (n := 313) (.out 0x1174ab (addR64R64Effect 0x1174ab 11 14) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 14] []) (.flag .CF)) #v[307, 298]
    (.letOp (n := 314) (.exec 0x1174ab (fun s => s.RIP = 0x1174ab) (addR64R64Effect 0x1174ab 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[307, 298]
    (.letOp (n := 315) (.out 0x1174ae (atFlags StatusFlags.CF (adcR64R64Effect 0x1174ae 6 3)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[310, 296, 313]
    (.letOp (n := 316) (.exec 0x1174ae (fun s => s.RIP = 0x1174ae) (atFlags StatusFlags.CF (adcR64R64Effect 0x1174ae 6 3)) (Reg.operands [.gpr 6, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[310, 296, 313]
    (.letOp (n := 317) (.out 0x1174b1 (addR64R64Effect 0x1174b1 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[304, 312]
    (.letOp (n := 318) (.out 0x1174b1 (addR64R64Effect 0x1174b1 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[304, 312]
    (.letOp (n := 319) (.exec 0x1174b1 (fun s => s.RIP = 0x1174b1) (addR64R64Effect 0x1174b1 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[304, 312]
    (.letOp (n := 320) (.out 0x1174b4 (atFlags StatusFlags.CF (adcR64R64Effect 0x1174b4 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[315, 305, 318]
    (.letOp (n := 321) (.exec 0x1174b4 (fun s => s.RIP = 0x1174b4) (atFlags StatusFlags.CF (adcR64R64Effect 0x1174b4 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[315, 305, 318]
    (.letOp (n := 322) (.out 0x1174b7 (addR64R64Effect 0x1174b7 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[317, 250]
    (.letOp (n := 323) (.out 0x1174b7 (addR64R64Effect 0x1174b7 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[317, 250]
    (.letOp (n := 324) (.exec 0x1174b7 (fun s => s.RIP = 0x1174b7) (addR64R64Effect 0x1174b7 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[317, 250]
    (.letOp (n := 325) (.out 0x1174ba (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1174ba 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[320, 323]
    (.letOp (n := 326) (.exec 0x1174ba (fun s => s.RIP = 0x1174ba) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1174ba 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[320, 323]
    (.letOp (n := 327) (.out 0x1174be (shldR64R64Effect 0x1174be 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[325, 322]
    (.letOp (n := 328) (.exec 0x1174be (fun s => s.RIP = 0x1174be) (shldR64R64Effect 0x1174be 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[325, 322]
    (.letOp (n := 329) (.out 0x1174c3 (shlR64Effect 0x1174c3 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[322]
    (.letOp (n := 330) (.exec 0x1174c3 (fun s => s.RIP = 0x1174c3) (shlR64Effect 0x1174c3 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[322]
    (.letOp (n := 331) (.out 0x1174c7 (movR64Imm64Effect 0x1174c7 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 332) (.exec 0x1174c7 (fun s => s.RIP = 0x1174c7) (movR64Imm64Effect 0x1174c7 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 333) (.out 0x1174d1 (andR64R64Effect 0x1174d1 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[329, 331]
    (.letOp (n := 334) (.exec 0x1174d1 (fun s => s.RIP = 0x1174d1) (andR64R64Effect 0x1174d1 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[329, 331]
    (.letOp (n := 335) (.out 0x1174d4 (orR64R64Effect 0x1174d4 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[333, 274]
    (.letOp (n := 336) (.exec 0x1174d4 (fun s => s.RIP = 0x1174d4) (orR64R64Effect 0x1174d4 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[333, 274]
    (.letOp (n := 337) (.out 0x1174d7 (movR64Imm64Effect 0x1174d7 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 338) (.exec 0x1174d7 (fun s => s.RIP = 0x1174d7) (movR64Imm64Effect 0x1174d7 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 339) (.out 0x1174e1 (mulR64Effect 0x1174e1 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[337, 335]
    (.letOp (n := 340) (.out 0x1174e1 (mulR64Effect 0x1174e1 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[337, 335]
    (.letOp (n := 341) (.exec 0x1174e1 (fun s => s.RIP = 0x1174e1) (mulR64Effect 0x1174e1 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[337, 335]
    (.letOp (n := 342) (.out 0x1174e4 (movR64R64Effect 0x1174e4 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[340]
    (.letOp (n := 343) (.exec 0x1174e4 (fun s => s.RIP = 0x1174e4) (movR64R64Effect 0x1174e4 8 2) (Reg.operands [.gpr 2] [])) #v[340]
    (.letOp (n := 344) (.out 0x1174e7 (addR64M64Effect 0x1174e7 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[339, 4]
    (.letOp (n := 345) (.out 0x1174e7 (addR64M64Effect 0x1174e7 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[339, 4]
    (.letOp (n := 346) (.exec 0x1174e7 (LoadPre 0x1174e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1174e7 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x1174e7 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[339, 4]
    (.letOp (n := 347) (.exec 0x1174ef (StorePre 0x1174ef 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1174ef + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1174ef 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[344, 4]
    (.letOp (n := 348) (.out 0x1174f7 (atFlags StatusFlags.CF (adcR64M64Effect 0x1174f7 8 (.sib 4 none 0 (.d32 0xc0)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[342, 4, 345]
    (.letOp (n := 349) (.exec 0x1174f7 (LoadPre 0x1174f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1174f7 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1174f7 8 (.sib 4 none 0 (.d32 0xc0)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[342, 4, 345]
    (b_l117297_7))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l117297_6 : List UInt8 :=
  [0x48, 0xF7, 0xA4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xC3, 0x4C, 0x11, 0xD6, 0x4D, 0x01,
    0xF3, 0x48, 0x11, 0xDE, 0x4C, 0x01, 0xD8, 0x48, 0x11, 0xD6, 0x48, 0x01, 0xC8, 0x48, 0x83, 0xD6,
    0x00, 0x48, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C, 0x09, 0xF8, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD0, 0x48, 0x03, 0x84, 0x24, 0x88, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x84, 0x24, 0xC0, 0x00,
    0x00, 0x00] ++ bytes_l117297_7

theorem code_l117297_6 : ∀ x ∈ codeRange 0x11749d bytes_l117297_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1749d 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117297_7

def b_l117297_5 : Block Op Label signature Reg.count 263 :=
  .letOp (n := 263) (.exec 0x117439 (StorePre 0x117439 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x117439 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117439 2 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[261, 4]
    (.letOp (n := 264) (.exec 0x117441 (StorePre 0x117441 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x117441 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117441 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[260, 4]
    (.letOp (n := 265) (.out 0x117449 (movR64M64Effect 0x117449 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 266) (.exec 0x117449 (LoadPre 0x117449 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x117449 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117449 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 267) (.out 0x11744e (mulM64Effect 0x11744e 5 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[265, 4]
    (.letOp (n := 268) (.out 0x11744e (mulM64Effect 0x11744e 5 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[265, 4]
    (.letOp (n := 269) (.exec 0x11744e (LoadPre 0x11744e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11744e + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11744e 5 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[265, 4]
    (.letOp (n := 270) (.out 0x117453 (movR64R64Effect 0x117453 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[267]
    (.letOp (n := 271) (.exec 0x117453 (fun s => s.RIP = 0x117453) (movR64R64Effect 0x117453 8 0) (Reg.operands [.gpr 0] [])) #v[267]
    (.letOp (n := 272) (.out 0x117456 (movR64R64Effect 0x117456 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[268]
    (.letOp (n := 273) (.exec 0x117456 (fun s => s.RIP = 0x117456) (movR64R64Effect 0x117456 10 2) (Reg.operands [.gpr 2] [])) #v[268]
    (.letOp (n := 274) (.out 0x117459 (andR32Imm8Effect 0x117459 4 15 0xf) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[254]
    (.letOp (n := 275) (.exec 0x117459 (fun s => s.RIP = 0x117459) (andR32Imm8Effect 0x117459 4 15 0xf) (Reg.operands [.gpr 15] [])) #v[254]
    (.letOp (n := 276) (.out 0x11745d (movR64M64Effect 0x11745d 9 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 277) (.exec 0x11745d (LoadPre 0x11745d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11745d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11745d 9 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 278) (.out 0x117465 (movR64R64Effect 0x117465 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[276]
    (.letOp (n := 279) (.exec 0x117465 (fun s => s.RIP = 0x117465) (movR64R64Effect 0x117465 0 9) (Reg.operands [.gpr 9] [])) #v[276]
    (.letOp (n := 280) (.out 0x117468 (movR64M64Effect 0x117468 7 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 281) (.exec 0x117468 (LoadPre 0x117468 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x117468 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117468 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 282) (.out 0x117470 (mulR64Effect 0x117470 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[280, 278]
    (.letOp (n := 283) (.out 0x117470 (mulR64Effect 0x117470 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[280, 278]
    (.letOp (n := 284) (.exec 0x117470 (fun s => s.RIP = 0x117470) (mulR64Effect 0x117470 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[280, 278]
    (.letOp (n := 285) (.out 0x117473 (movR64R64Effect 0x117473 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[283]
    (.letOp (n := 286) (.exec 0x117473 (fun s => s.RIP = 0x117473) (movR64R64Effect 0x117473 6 2) (Reg.operands [.gpr 2] [])) #v[283]
    (.letOp (n := 287) (.out 0x117476 (movR64R64Effect 0x117476 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[282]
    (.letOp (n := 288) (.exec 0x117476 (fun s => s.RIP = 0x117476) (movR64R64Effect 0x117476 11 0) (Reg.operands [.gpr 0] [])) #v[282]
    (.letOp (n := 289) (.out 0x117479 (movR64M64Effect 0x117479 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 290) (.exec 0x117479 (LoadPre 0x117479 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x117479 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117479 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 291) (.out 0x117481 (movR64M64Effect 0x117481 12 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 292) (.exec 0x117481 (LoadPre 0x117481 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x117481 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117481 12 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 293) (.out 0x117489 (mulR64Effect 0x117489 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[291, 289]
    (.letOp (n := 294) (.out 0x117489 (mulR64Effect 0x117489 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[291, 289]
    (.letOp (n := 295) (.exec 0x117489 (fun s => s.RIP = 0x117489) (mulR64Effect 0x117489 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[291, 289]
    (.letOp (n := 296) (.out 0x11748c (movR64R64Effect 0x11748c 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[294]
    (.letOp (n := 297) (.exec 0x11748c (fun s => s.RIP = 0x11748c) (movR64R64Effect 0x11748c 3 2) (Reg.operands [.gpr 2] [])) #v[294]
    (.letOp (n := 298) (.out 0x11748f (movR64R64Effect 0x11748f 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[293]
    (.letOp (n := 299) (.exec 0x11748f (fun s => s.RIP = 0x11748f) (movR64R64Effect 0x11748f 14 0) (Reg.operands [.gpr 0] [])) #v[293]
    (.letOp (n := 300) (.out 0x117492 (movR64M64Effect 0x117492 5 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 301) (.exec 0x117492 (LoadPre 0x117492 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x117492 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117492 5 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 302) (.out 0x11749a (movR64R64Effect 0x11749a 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[300]
    (.letOp (n := 303) (.exec 0x11749a (fun s => s.RIP = 0x11749a) (movR64R64Effect 0x11749a 0 5) (Reg.operands [.gpr 5] [])) #v[300]
    (b_l117297_6)))))))))))))))))))))))))))))))))))))))))

def bytes_l117297_5 : List UInt8 :=
  [0x48, 0x89, 0x94, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0xF7, 0x64, 0x24, 0x78, 0x49, 0x89, 0xC0, 0x49, 0x89, 0xD2,
    0x41, 0x83, 0xE7, 0x0F, 0x4C, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xC8, 0x48,
    0x8B, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC3,
    0x48, 0x8B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0xA4, 0x24, 0xE8, 0x00, 0x00, 0x00,
    0x49, 0xF7, 0xE4, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0xAC, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xE8] ++ bytes_l117297_6

theorem code_l117297_5 : ∀ x ∈ codeRange 0x117439 bytes_l117297_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17439 100 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117297_6

def b_l117297_4 : Block Op Label signature Reg.count 217 :=
  .letOp (n := 217) (.out 0x1173e9 (addR64R64Effect 0x1173e9 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[210, 215]
    (.letOp (n := 218) (.exec 0x1173e9 (fun s => s.RIP = 0x1173e9) (addR64R64Effect 0x1173e9 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[210, 215]
    (.letOp (n := 219) (.out 0x1173ec (addR64M64Effect 0x1173ec 10 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[178, 4]
    (.letOp (n := 220) (.out 0x1173ec (addR64M64Effect 0x1173ec 10 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[178, 4]
    (.letOp (n := 221) (.exec 0x1173ec (LoadPre 0x1173ec (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1173ec + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x1173ec 10 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[178, 4]
    (.letOp (n := 222) (.out 0x1173f4 (atFlags StatusFlags.CF (adcR64M64Effect 0x1173f4 1 (.sib 4 none 0 (.d8 0x70)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[176, 4, 220]
    (.letOp (n := 223) (.exec 0x1173f4 (LoadPre 0x1173f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1173f4 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1173f4 1 (.sib 4 none 0 (.d8 0x70)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[176, 4, 220]
    (.letOp (n := 224) (.out 0x1173f9 (addR64R64Effect 0x1173f9 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[219, 186]
    (.letOp (n := 225) (.out 0x1173f9 (addR64R64Effect 0x1173f9 10 5) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 5] []) (.flag .CF)) #v[219, 186]
    (.letOp (n := 226) (.exec 0x1173f9 (fun s => s.RIP = 0x1173f9) (addR64R64Effect 0x1173f9 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[219, 186]
    (.letOp (n := 227) (.out 0x1173fc (atFlags StatusFlags.CF (adcR64M64Effect 0x1173fc 1 (.sib 4 none 0 (.d32 0xc0)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[222, 4, 225]
    (.letOp (n := 228) (.exec 0x1173fc (LoadPre 0x1173fc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1173fc + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1173fc 1 (.sib 4 none 0 (.d32 0xc0)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[222, 4, 225]
    (.letOp (n := 229) (.out 0x117404 (addR64R64Effect 0x117404 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[224, 195]
    (.letOp (n := 230) (.out 0x117404 (addR64R64Effect 0x117404 10 14) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 14] []) (.flag .CF)) #v[224, 195]
    (.letOp (n := 231) (.exec 0x117404 (fun s => s.RIP = 0x117404) (addR64R64Effect 0x117404 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[224, 195]
    (.letOp (n := 232) (.out 0x117407 (atFlags StatusFlags.CF (adcR64R64Effect 0x117407 1 13)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[227, 193, 230]
    (.letOp (n := 233) (.exec 0x117407 (fun s => s.RIP = 0x117407) (atFlags StatusFlags.CF (adcR64R64Effect 0x117407 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[227, 193, 230]
    (.letOp (n := 234) (.out 0x11740a (addR64R64Effect 0x11740a 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[229, 202]
    (.letOp (n := 235) (.out 0x11740a (addR64R64Effect 0x11740a 10 3) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 3] []) (.flag .CF)) #v[229, 202]
    (.letOp (n := 236) (.exec 0x11740a (fun s => s.RIP = 0x11740a) (addR64R64Effect 0x11740a 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[229, 202]
    (.letOp (n := 237) (.out 0x11740d (atFlags StatusFlags.CF (adcR64R64Effect 0x11740d 1 15)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[232, 204, 235]
    (.letOp (n := 238) (.exec 0x11740d (fun s => s.RIP = 0x11740d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11740d 1 15)) (Reg.operands [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[232, 204, 235]
    (.letOp (n := 239) (.out 0x117410 (addR64R64Effect 0x117410 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[234, 214]
    (.letOp (n := 240) (.out 0x117410 (addR64R64Effect 0x117410 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[234, 214]
    (.letOp (n := 241) (.exec 0x117410 (fun s => s.RIP = 0x117410) (addR64R64Effect 0x117410 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[234, 214]
    (.letOp (n := 242) (.out 0x117413 (atFlags StatusFlags.CF (adcR64R64Effect 0x117413 1 6)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[237, 217, 240]
    (.letOp (n := 243) (.exec 0x117413 (fun s => s.RIP = 0x117413) (atFlags StatusFlags.CF (adcR64R64Effect 0x117413 1 6)) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[237, 217, 240]
    (.letOp (n := 244) (.out 0x117416 (addR64R64Effect 0x117416 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[239, 162]
    (.letOp (n := 245) (.out 0x117416 (addR64R64Effect 0x117416 10 7) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 7] []) (.flag .CF)) #v[239, 162]
    (.letOp (n := 246) (.exec 0x117416 (fun s => s.RIP = 0x117416) (addR64R64Effect 0x117416 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[239, 162]
    (.letOp (n := 247) (.exec 0x117419 (StorePre 0x117419 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x117419 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117419 10 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[244, 4]
    (.letOp (n := 248) (.out 0x11741e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11741e 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[242, 245]
    (.letOp (n := 249) (.exec 0x11741e (fun s => s.RIP = 0x11741e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11741e 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[242, 245]
    (.letOp (n := 250) (.out 0x117422 (shldR64R64Effect 0x117422 5 1 10 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[248, 244]
    (.letOp (n := 251) (.exec 0x117422 (fun s => s.RIP = 0x117422) (shldR64R64Effect 0x117422 5 1 10 12) (Reg.operands [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[248, 244]
    (.letOp (n := 252) (.out 0x117427 (movR64R64Effect 0x117427 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 10] []) (.reg (.gpr 15))) #v[244]
    (.letOp (n := 253) (.exec 0x117427 (fun s => s.RIP = 0x117427) (movR64R64Effect 0x117427 15 10) (Reg.operands [.gpr 10] [])) #v[244]
    (.letOp (n := 254) (.out 0x11742a (shrR64Effect 0x11742a 4 15 48) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[252]
    (.letOp (n := 255) (.exec 0x11742a (fun s => s.RIP = 0x11742a) (shrR64Effect 0x11742a 4 15 48) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[252]
    (.letOp (n := 256) (.out 0x11742e (movR64R64Effect 0x11742e 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[112]
    (.letOp (n := 257) (.exec 0x11742e (fun s => s.RIP = 0x11742e) (movR64R64Effect 0x11742e 0 8) (Reg.operands [.gpr 8] [])) #v[112]
    (.letOp (n := 258) (.out 0x117431 (movR64M64Effect 0x117431 13 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 259) (.exec 0x117431 (LoadPre 0x117431 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x117431 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117431 13 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 260) (.out 0x117436 (mulR64Effect 0x117436 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[258, 256]
    (.letOp (n := 261) (.out 0x117436 (mulR64Effect 0x117436 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[258, 256]
    (.letOp (n := 262) (.exec 0x117436 (fun s => s.RIP = 0x117436) (mulR64Effect 0x117436 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[258, 256]
    (b_l117297_5))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l117297_4 : List UInt8 :=
  [0x48, 0x01, 0xD6, 0x4C, 0x03, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x13, 0x4C, 0x24, 0x70,
    0x49, 0x01, 0xEA, 0x48, 0x13, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xF2, 0x4C, 0x11,
    0xE9, 0x49, 0x01, 0xDA, 0x4C, 0x11, 0xF9, 0x49, 0x01, 0xC2, 0x48, 0x11, 0xF1, 0x49, 0x01, 0xFA,
    0x4C, 0x89, 0x54, 0x24, 0x70, 0x48, 0x83, 0xD1, 0x00, 0x4C, 0x0F, 0xA4, 0xD1, 0x0C, 0x4D, 0x89,
    0xD7, 0x49, 0xC1, 0xEF, 0x30, 0x4C, 0x89, 0xC0, 0x4C, 0x8B, 0x6C, 0x24, 0x60, 0x49, 0xF7, 0xE5] ++ bytes_l117297_5

theorem code_l117297_4 : ∀ x ∈ codeRange 0x1173e9 bytes_l117297_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x173e9 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117297_5

def b_l117297_3 : Block Op Label signature Reg.count 173 :=
  .letOp (n := 173) (.out 0x117398 (mulM64Effect 0x117398 5 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[171, 4]
    (.letOp (n := 174) (.out 0x117398 (mulM64Effect 0x117398 5 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[171, 4]
    (.letOp (n := 175) (.exec 0x117398 (LoadPre 0x117398 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x117398 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x117398 5 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[171, 4]
    (.letOp (n := 176) (.out 0x11739d (movR64R64Effect 0x11739d 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[174]
    (.letOp (n := 177) (.exec 0x11739d (fun s => s.RIP = 0x11739d) (movR64R64Effect 0x11739d 1 2) (Reg.operands [.gpr 2] [])) #v[174]
    (.letOp (n := 178) (.out 0x1173a0 (movR64R64Effect 0x1173a0 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[173]
    (.letOp (n := 179) (.exec 0x1173a0 (fun s => s.RIP = 0x1173a0) (movR64R64Effect 0x1173a0 10 0) (Reg.operands [.gpr 0] [])) #v[173]
    (.letOp (n := 180) (.out 0x1173a3 (movR64R64Effect 0x1173a3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[78]
    (.letOp (n := 181) (.exec 0x1173a3 (fun s => s.RIP = 0x1173a3) (movR64R64Effect 0x1173a3 0 14) (Reg.operands [.gpr 14] [])) #v[78]
    (.letOp (n := 182) (.out 0x1173a6 (mulM64Effect 0x1173a6 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[180, 4]
    (.letOp (n := 183) (.out 0x1173a6 (mulM64Effect 0x1173a6 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[180, 4]
    (.letOp (n := 184) (.exec 0x1173a6 (LoadPre 0x1173a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1173a6 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1173a6 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[180, 4]
    (.letOp (n := 185) (.exec 0x1173ae (StorePre 0x1173ae 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1173ae + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1173ae 2 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[183, 4]
    (.letOp (n := 186) (.out 0x1173b6 (movR64R64Effect 0x1173b6 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[182]
    (.letOp (n := 187) (.exec 0x1173b6 (fun s => s.RIP = 0x1173b6) (movR64R64Effect 0x1173b6 5 0) (Reg.operands [.gpr 0] [])) #v[182]
    (.letOp (n := 188) (.out 0x1173b9 (movR64R64Effect 0x1173b9 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[95]
    (.letOp (n := 189) (.exec 0x1173b9 (fun s => s.RIP = 0x1173b9) (movR64R64Effect 0x1173b9 0 3) (Reg.operands [.gpr 3] [])) #v[95]
    (.letOp (n := 190) (.out 0x1173bc (mulR64Effect 0x1173bc 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[119, 188]
    (.letOp (n := 191) (.out 0x1173bc (mulR64Effect 0x1173bc 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[119, 188]
    (.letOp (n := 192) (.exec 0x1173bc (fun s => s.RIP = 0x1173bc) (mulR64Effect 0x1173bc 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[119, 188]
    (.letOp (n := 193) (.out 0x1173bf (movR64R64Effect 0x1173bf 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[191]
    (.letOp (n := 194) (.exec 0x1173bf (fun s => s.RIP = 0x1173bf) (movR64R64Effect 0x1173bf 13 2) (Reg.operands [.gpr 2] [])) #v[191]
    (.letOp (n := 195) (.out 0x1173c2 (movR64R64Effect 0x1173c2 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[190]
    (.letOp (n := 196) (.exec 0x1173c2 (fun s => s.RIP = 0x1173c2) (movR64R64Effect 0x1173c2 14 0) (Reg.operands [.gpr 0] [])) #v[190]
    (.letOp (n := 197) (.out 0x1173c5 (movR64R64Effect 0x1173c5 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[112]
    (.letOp (n := 198) (.exec 0x1173c5 (fun s => s.RIP = 0x1173c5) (movR64R64Effect 0x1173c5 0 8) (Reg.operands [.gpr 8] [])) #v[112]
    (.letOp (n := 199) (.out 0x1173c8 (mulR64Effect 0x1173c8 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[53, 197]
    (.letOp (n := 200) (.out 0x1173c8 (mulR64Effect 0x1173c8 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[53, 197]
    (.letOp (n := 201) (.exec 0x1173c8 (fun s => s.RIP = 0x1173c8) (mulR64Effect 0x1173c8 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[53, 197]
    (.letOp (n := 202) (.out 0x1173cb (movR64R64Effect 0x1173cb 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[199]
    (.letOp (n := 203) (.exec 0x1173cb (fun s => s.RIP = 0x1173cb) (movR64R64Effect 0x1173cb 3 0) (Reg.operands [.gpr 0] [])) #v[199]
    (.letOp (n := 204) (.out 0x1173ce (movR64R64Effect 0x1173ce 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[200]
    (.letOp (n := 205) (.exec 0x1173ce (fun s => s.RIP = 0x1173ce) (movR64R64Effect 0x1173ce 15 2) (Reg.operands [.gpr 2] [])) #v[200]
    (.letOp (n := 206) (.out 0x1173d1 (shrR64Effect 0x1173d1 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[139]
    (.letOp (n := 207) (.exec 0x1173d1 (fun s => s.RIP = 0x1173d1) (shrR64Effect 0x1173d1 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[139]
    (.letOp (n := 208) (.out 0x1173d5 (movR64Imm64Effect 0x1173d5 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 209) (.exec 0x1173d5 (fun s => s.RIP = 0x1173d5) (movR64Imm64Effect 0x1173d5 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 210) (.out 0x1173df (imulR64R64Effect 0x1173df 4 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[206, 208]
    (.letOp (n := 211) (.exec 0x1173df (fun s => s.RIP = 0x1173df) (imulR64R64Effect 0x1173df 4 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[206, 208]
    (.letOp (n := 212) (.out 0x1173e3 (movR64R64Effect 0x1173e3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[143]
    (.letOp (n := 213) (.exec 0x1173e3 (fun s => s.RIP = 0x1173e3) (movR64R64Effect 0x1173e3 0 11) (Reg.operands [.gpr 11] [])) #v[143]
    (.letOp (n := 214) (.out 0x1173e6 (mulR64Effect 0x1173e6 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[208, 212]
    (.letOp (n := 215) (.out 0x1173e6 (mulR64Effect 0x1173e6 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[208, 212]
    (.letOp (n := 216) (.exec 0x1173e6 (fun s => s.RIP = 0x1173e6) (mulR64Effect 0x1173e6 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[208, 212]
    (b_l117297_4))))))))))))))))))))))))))))))))))))))))))))

def bytes_l117297_3 : List UInt8 :=
  [0x48, 0xF7, 0x64, 0x24, 0x78, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC2, 0x4C, 0x89, 0xF0, 0x48, 0xF7,
    0xA4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89,
    0xC5, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xD5, 0x49, 0x89, 0xC6, 0x4C, 0x89, 0xC0,
    0x49, 0xF7, 0xE4, 0x48, 0x89, 0xC3, 0x49, 0x89, 0xD7, 0x48, 0xC1, 0xEE, 0x34, 0x48, 0xBA, 0x10,
    0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xF2, 0x4C, 0x89, 0xD8, 0x48, 0xF7,
    0xE2] ++ bytes_l117297_4

theorem code_l117297_3 : ∀ x ∈ codeRange 0x117398 bytes_l117297_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17398 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117297_4

def b_l117297_2 : Block Op Label signature Reg.count 133 :=
  .letOp (n := 133) (.out 0x11733a (movR64R64Effect 0x11733a 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[131]
    (.letOp (n := 134) (.exec 0x11733a (fun s => s.RIP = 0x11733a) (movR64R64Effect 0x11733a 0 15) (Reg.operands [.gpr 15] [])) #v[131]
    (.letOp (n := 135) (.out 0x11733d (mulR64Effect 0x11733d 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[53, 133]
    (.letOp (n := 136) (.out 0x11733d (mulR64Effect 0x11733d 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[53, 133]
    (.letOp (n := 137) (.exec 0x11733d (fun s => s.RIP = 0x11733d) (mulR64Effect 0x11733d 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[53, 133]
    (.letOp (n := 138) (.exec 0x117340 (StorePre 0x117340 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x117340 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117340 12 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 139) (.out 0x117348 (movR64R64Effect 0x117348 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[136]
    (.letOp (n := 140) (.exec 0x117348 (fun s => s.RIP = 0x117348) (movR64R64Effect 0x117348 6 2) (Reg.operands [.gpr 2] [])) #v[136]
    (.letOp (n := 141) (.out 0x11734b (movR64R64Effect 0x11734b 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[136]
    (.letOp (n := 142) (.exec 0x11734b (fun s => s.RIP = 0x11734b) (movR64R64Effect 0x11734b 11 2) (Reg.operands [.gpr 2] [])) #v[136]
    (.letOp (n := 143) (.out 0x11734e (shldR64R64Effect 0x11734e 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[141, 135]
    (.letOp (n := 144) (.exec 0x11734e (fun s => s.RIP = 0x11734e) (shldR64R64Effect 0x11734e 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[141, 135]
    (.letOp (n := 145) (.out 0x117353 (movR64Imm64Effect 0x117353 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 146) (.exec 0x117353 (fun s => s.RIP = 0x117353) (movR64Imm64Effect 0x117353 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 147) (.out 0x11735d (andR64R64Effect 0x11735d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[135, 145]
    (.letOp (n := 148) (.exec 0x11735d (fun s => s.RIP = 0x11735d) (andR64R64Effect 0x11735d 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[135, 145]
    (.letOp (n := 149) (.out 0x117360 (movR64Imm64Effect 0x117360 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 150) (.exec 0x117360 (fun s => s.RIP = 0x117360) (movR64Imm64Effect 0x117360 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 151) (.out 0x11736a (mulR64Effect 0x11736a 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[149, 147]
    (.letOp (n := 152) (.out 0x11736a (mulR64Effect 0x11736a 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[149, 147]
    (.letOp (n := 153) (.exec 0x11736a (fun s => s.RIP = 0x11736a) (mulR64Effect 0x11736a 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[149, 147]
    (.letOp (n := 154) (.out 0x11736d (movR64R64Effect 0x11736d 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[152]
    (.letOp (n := 155) (.exec 0x11736d (fun s => s.RIP = 0x11736d) (movR64R64Effect 0x11736d 7 2) (Reg.operands [.gpr 2] [])) #v[152]
    (.letOp (n := 156) (.out 0x117370 (addR64R64Effect 0x117370 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[151, 126]
    (.letOp (n := 157) (.out 0x117370 (addR64R64Effect 0x117370 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[151, 126]
    (.letOp (n := 158) (.exec 0x117370 (fun s => s.RIP = 0x117370) (addR64R64Effect 0x117370 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[151, 126]
    (.letOp (n := 159) (.exec 0x117373 (StorePre 0x117373 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x117373 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117373 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[156, 4]
    (.letOp (n := 160) (.out 0x117378 (atFlags StatusFlags.CF (adcR64R64Effect 0x117378 7 9)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[154, 129, 157]
    (.letOp (n := 161) (.exec 0x117378 (fun s => s.RIP = 0x117378) (atFlags StatusFlags.CF (adcR64R64Effect 0x117378 7 9)) (Reg.operands [.gpr 7, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[154, 129, 157]
    (.letOp (n := 162) (.out 0x11737b (shldR64R64Effect 0x11737b 5 7 0 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[160, 156]
    (.letOp (n := 163) (.exec 0x11737b (fun s => s.RIP = 0x11737b) (shldR64R64Effect 0x11737b 5 7 0 12) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[160, 156]
    (.letOp (n := 164) (.out 0x117380 (movR64R64Effect 0x117380 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[131]
    (.letOp (n := 165) (.exec 0x117380 (fun s => s.RIP = 0x117380) (movR64R64Effect 0x117380 0 15) (Reg.operands [.gpr 15] [])) #v[131]
    (.letOp (n := 166) (.out 0x117383 (mulM64Effect 0x117383 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[164, 4]
    (.letOp (n := 167) (.out 0x117383 (mulM64Effect 0x117383 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[164, 4]
    (.letOp (n := 168) (.exec 0x117383 (LoadPre 0x117383 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x117383 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x117383 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[164, 4]
    (.letOp (n := 169) (.exec 0x117388 (StorePre 0x117388 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x117388 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117388 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[167, 4]
    (.letOp (n := 170) (.exec 0x11738d (StorePre 0x11738d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11738d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11738d 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[166, 4]
    (.letOp (n := 171) (.out 0x117395 (movR64R64Effect 0x117395 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 172) (.exec 0x117395 (fun s => s.RIP = 0x117395) (movR64R64Effect 0x117395 0 5) (Reg.operands [.gpr 5] [])) #v[66]
    (b_l117297_3))))))))))))))))))))))))))))))))))))))))

def bytes_l117297_2 : List UInt8 :=
  [0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE4, 0x4C, 0x89, 0xA4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89,
    0xD6, 0x49, 0x89, 0xD3, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD7, 0x4C, 0x01, 0xD0, 0x48, 0x89, 0x44, 0x24, 0x68, 0x4C, 0x11,
    0xCF, 0x48, 0x0F, 0xA4, 0xC7, 0x0C, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x60, 0x48, 0x89,
    0x54, 0x24, 0x70, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE8] ++ bytes_l117297_3

theorem code_l117297_2 : ∀ x ∈ codeRange 0x11733a bytes_l117297_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1733a 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117297_3

def b_l117297_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.out 0x1172f0 (addR64R64Effect 0x1172f0 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[88, 76]
    (.letOp (n := 91) (.out 0x1172f0 (addR64R64Effect 0x1172f0 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[88, 76]
    (.letOp (n := 92) (.exec 0x1172f0 (fun s => s.RIP = 0x1172f0) (addR64R64Effect 0x1172f0 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[88, 76]
    (.letOp (n := 93) (.out 0x1172f3 (atFlags StatusFlags.CF (adcR64R64Effect 0x1172f3 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[86, 74, 91]
    (.letOp (n := 94) (.exec 0x1172f3 (fun s => s.RIP = 0x1172f3) (atFlags StatusFlags.CF (adcR64R64Effect 0x1172f3 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[86, 74, 91]
    (.letOp (n := 95) (.out 0x1172f6 (movR64R64Effect 0x1172f6 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[15]
    (.letOp (n := 96) (.exec 0x1172f6 (fun s => s.RIP = 0x1172f6) (movR64R64Effect 0x1172f6 3 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 97) (.exec 0x1172f9 (StorePre 0x1172f9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1172f9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1172f9 15 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 98) (.out 0x117301 (movR64R64Effect 0x117301 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 99) (.exec 0x117301 (fun s => s.RIP = 0x117301) (movR64R64Effect 0x117301 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 100) (.out 0x117304 (mulR64Effect 0x117304 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[57, 98]
    (.letOp (n := 101) (.out 0x117304 (mulR64Effect 0x117304 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[57, 98]
    (.letOp (n := 102) (.exec 0x117304 (fun s => s.RIP = 0x117304) (mulR64Effect 0x117304 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[57, 98]
    (.letOp (n := 103) (.out 0x117307 (movR64R64Effect 0x117307 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[101]
    (.letOp (n := 104) (.exec 0x117307 (fun s => s.RIP = 0x117307) (movR64R64Effect 0x117307 1 2) (Reg.operands [.gpr 2] [])) #v[101]
    (.letOp (n := 105) (.out 0x11730a (movR64R64Effect 0x11730a 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[100]
    (.letOp (n := 106) (.exec 0x11730a (fun s => s.RIP = 0x11730a) (movR64R64Effect 0x11730a 6 0) (Reg.operands [.gpr 0] [])) #v[100]
    (.letOp (n := 107) (.out 0x11730d (addR64R64Effect 0x11730d 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[105, 90]
    (.letOp (n := 108) (.out 0x11730d (addR64R64Effect 0x11730d 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[105, 90]
    (.letOp (n := 109) (.exec 0x11730d (fun s => s.RIP = 0x11730d) (addR64R64Effect 0x11730d 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[105, 90]
    (.letOp (n := 110) (.out 0x117310 (atFlags StatusFlags.CF (adcR64R64Effect 0x117310 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[103, 93, 108]
    (.letOp (n := 111) (.exec 0x117310 (fun s => s.RIP = 0x117310) (atFlags StatusFlags.CF (adcR64R64Effect 0x117310 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[103, 93, 108]
    (.letOp (n := 112) (.out 0x117313 (movR64M64Effect 0x117313 8 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 113) (.exec 0x117313 (LoadPre 0x117313 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x117313 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117313 8 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 114) (.out 0x117318 (movR64R64Effect 0x117318 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[112]
    (.letOp (n := 115) (.exec 0x117318 (fun s => s.RIP = 0x117318) (movR64R64Effect 0x117318 0 8) (Reg.operands [.gpr 8] [])) #v[112]
    (.letOp (n := 116) (.out 0x11731b (mulR64Effect 0x11731b 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[55, 114]
    (.letOp (n := 117) (.out 0x11731b (mulR64Effect 0x11731b 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[55, 114]
    (.letOp (n := 118) (.exec 0x11731b (fun s => s.RIP = 0x11731b) (mulR64Effect 0x11731b 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[55, 114]
    (.letOp (n := 119) (.out 0x11731e (movR64R64Effect 0x11731e 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[55]
    (.letOp (n := 120) (.exec 0x11731e (fun s => s.RIP = 0x11731e) (movR64R64Effect 0x11731e 13 9) (Reg.operands [.gpr 9] [])) #v[55]
    (.letOp (n := 121) (.exec 0x117321 (StorePre 0x117321 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x117321 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117321 9 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 122) (.out 0x117329 (movR64R64Effect 0x117329 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[117]
    (.letOp (n := 123) (.exec 0x117329 (fun s => s.RIP = 0x117329) (movR64R64Effect 0x117329 9 2) (Reg.operands [.gpr 2] [])) #v[117]
    (.letOp (n := 124) (.out 0x11732c (movR64R64Effect 0x11732c 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[116]
    (.letOp (n := 125) (.exec 0x11732c (fun s => s.RIP = 0x11732c) (movR64R64Effect 0x11732c 10 0) (Reg.operands [.gpr 0] [])) #v[116]
    (.letOp (n := 126) (.out 0x11732f (addR64R64Effect 0x11732f 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[124, 107]
    (.letOp (n := 127) (.out 0x11732f (addR64R64Effect 0x11732f 10 6) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 6] []) (.flag .CF)) #v[124, 107]
    (.letOp (n := 128) (.exec 0x11732f (fun s => s.RIP = 0x11732f) (addR64R64Effect 0x11732f 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[124, 107]
    (.letOp (n := 129) (.out 0x117332 (atFlags StatusFlags.CF (adcR64R64Effect 0x117332 9 1)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[122, 110, 127]
    (.letOp (n := 130) (.exec 0x117332 (fun s => s.RIP = 0x117332) (atFlags StatusFlags.CF (adcR64R64Effect 0x117332 9 1)) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[122, 110, 127]
    (.letOp (n := 131) (.out 0x117335 (movR64M64Effect 0x117335 15 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 132) (.exec 0x117335 (LoadPre 0x117335 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x117335 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117335 15 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l117297_2)))))))))))))))))))))))))))))))))))))))))))

def bytes_l117297_1 : List UInt8 :=
  [0x49, 0x01, 0xF0, 0x48, 0x11, 0xCF, 0x4C, 0x89, 0xFB, 0x4C, 0x89, 0xBC, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x01, 0xC6,
    0x48, 0x11, 0xF9, 0x4C, 0x8B, 0x44, 0x24, 0x58, 0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE1, 0x4D, 0x89,
    0xCD, 0x4C, 0x89, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC2, 0x49,
    0x01, 0xF2, 0x49, 0x11, 0xC9, 0x4C, 0x8B, 0x7C, 0x24, 0x50] ++ bytes_l117297_2

theorem code_l117297_1 : ∀ x ∈ codeRange 0x1172f0 bytes_l117297_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x172f0 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117297_2

def b_l117297 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117297 (movR64M64Effect 0x117297 12 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 54) (.exec 0x117297 (LoadPre 0x117297 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117297 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117297 12 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11729c (movR64M64Effect 0x11729c 9 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 56) (.exec 0x11729c (LoadPre 0x11729c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11729c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11729c 9 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1172a1 (movR64M64Effect 0x1172a1 10 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 58) (.exec 0x1172a1 (LoadPre 0x1172a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1172a1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1172a1 10 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x1172a6 (StorePre 0x1172a6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1172a6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1172a6 10 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x1172ae (movR64M64Effect 0x1172ae 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 61) (.exec 0x1172ae (LoadPre 0x1172ae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1172ae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1172ae 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x1172b3 (StorePre 0x1172b3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1172b3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1172b3 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x1172b8 (movR64M64Effect 0x1172b8 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x1172b8 (LoadPre 0x1172b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1172b8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1172b8 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x1172bd (StorePre 0x1172bd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1172bd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1172bd 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x1172c2 (movR64R64Effect 0x1172c2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[3]
    (.letOp (n := 67) (.exec 0x1172c2 (fun s => s.RIP = 0x1172c2) (movR64R64Effect 0x1172c2 5 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 68) (.exec 0x1172c5 (StorePre 0x1172c5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1172c5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1172c5 3 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 69) (.out 0x1172cd (movR64R64Effect 0x1172cd 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 70) (.exec 0x1172cd (fun s => s.RIP = 0x1172cd) (movR64R64Effect 0x1172cd 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 71) (.out 0x1172d0 (mulR64Effect 0x1172d0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[60, 69]
    (.letOp (n := 72) (.out 0x1172d0 (mulR64Effect 0x1172d0 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[60, 69]
    (.letOp (n := 73) (.exec 0x1172d0 (fun s => s.RIP = 0x1172d0) (mulR64Effect 0x1172d0 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[60, 69]
    (.letOp (n := 74) (.out 0x1172d3 (movR64R64Effect 0x1172d3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[72]
    (.letOp (n := 75) (.exec 0x1172d3 (fun s => s.RIP = 0x1172d3) (movR64R64Effect 0x1172d3 1 2) (Reg.operands [.gpr 2] [])) #v[72]
    (.letOp (n := 76) (.out 0x1172d6 (movR64R64Effect 0x1172d6 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 77) (.exec 0x1172d6 (fun s => s.RIP = 0x1172d6) (movR64R64Effect 0x1172d6 6 0) (Reg.operands [.gpr 0] [])) #v[71]
    (.letOp (n := 78) (.out 0x1172d9 (movR64R64Effect 0x1172d9 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 13] []) (.reg (.gpr 14))) #v[13]
    (.letOp (n := 79) (.exec 0x1172d9 (fun s => s.RIP = 0x1172d9) (movR64R64Effect 0x1172d9 14 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 80) (.exec 0x1172dc (StorePre 0x1172dc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1172dc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1172dc 13 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 81) (.out 0x1172e4 (movR64R64Effect 0x1172e4 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 82) (.exec 0x1172e4 (fun s => s.RIP = 0x1172e4) (movR64R64Effect 0x1172e4 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 83) (.out 0x1172e7 (mulR64Effect 0x1172e7 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[63, 81]
    (.letOp (n := 84) (.out 0x1172e7 (mulR64Effect 0x1172e7 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[63, 81]
    (.letOp (n := 85) (.exec 0x1172e7 (fun s => s.RIP = 0x1172e7) (mulR64Effect 0x1172e7 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[63, 81]
    (.letOp (n := 86) (.out 0x1172ea (movR64R64Effect 0x1172ea 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[84]
    (.letOp (n := 87) (.exec 0x1172ea (fun s => s.RIP = 0x1172ea) (movR64R64Effect 0x1172ea 7 2) (Reg.operands [.gpr 2] [])) #v[84]
    (.letOp (n := 88) (.out 0x1172ed (movR64R64Effect 0x1172ed 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[83]
    (.letOp (n := 89) (.exec 0x1172ed (fun s => s.RIP = 0x1172ed) (movR64R64Effect 0x1172ed 8 0) (Reg.operands [.gpr 0] [])) #v[83]
    (b_l117297_1)))))))))))))))))))))))))))))))))))))

def bytes_l117297 : List UInt8 :=
  [0x4C, 0x8B, 0x64, 0x24, 0x48, 0x4C, 0x8B, 0x4C, 0x24, 0x40, 0x4C, 0x8B, 0x54, 0x24, 0x38, 0x4C,
    0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x48, 0x89, 0x4C, 0x24,
    0x60, 0x48, 0x8B, 0x7C, 0x24, 0x30, 0x48, 0x89, 0x7C, 0x24, 0x78, 0x48, 0x89, 0xDD, 0x48, 0x89,
    0x9C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD1, 0x48,
    0x89, 0xC6, 0x4D, 0x89, 0xEE, 0x4C, 0x89, 0xAC, 0x24, 0x08, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE8,
    0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0] ++ bytes_l117297_1

theorem code_l117297 : ∀ x ∈ codeRange 0x117297 bytes_l117297, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17297 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117297_1

@[cfg_block] def b_l1176f2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1176f2 (movR64M64Effect 0x1176f2 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1176f2 (LoadPre 0x1176f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1176f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1176f2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1176f7 (StorePre 0x1176f7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1176f7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1176f7 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1176fc (movR64M64Effect 0x1176fc 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1176fc (LoadPre 0x1176fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1176fc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1176fc 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117701 (StorePre 0x117701 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117701 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117701 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117706 (movR64M64Effect 0x117706 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117706 (LoadPre 0x117706 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117706 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117706 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11770b (StorePre 0x11770b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11770b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11770b 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117710 (movR64M64Effect 0x117710 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117710 (LoadPre 0x117710 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117710 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117710 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117715 (movR64M64Effect 0x117715 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117715 (LoadPre 0x117715 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117715 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117715 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11771a (StorePre 0x11771a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11771a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11771a 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11771f (StorePre 0x11771f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11771f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11771f 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117723 (movR64R64Effect 0x117723 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117723 (fun s => s.RIP = 0x117723) (movR64R64Effect 0x117723 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117726 (movR64R64Effect 0x117726 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117726 (fun s => s.RIP = 0x117726) (movR64R64Effect 0x117726 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117729 (callEffect (fun _ => 0x1145f0) 0x11772e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117729 (PushPre 0x117729 5) (callEffect (fun _ => 0x1145f0) 0x11772e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11772e⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11772e, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1176f2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xC2, 0xCE, 0xFF, 0xFF]

theorem code_l1176f2 : ∀ x ∈ codeRange 0x1176f2 bytes_l1176f2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x176f2 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11772e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11772e (movR64M64Effect 0x11772e 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11772e (LoadPre 0x11772e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11772e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11772e 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117733 (StorePre 0x117733 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117733 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117733 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117738 (movR64M64Effect 0x117738 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117738 (LoadPre 0x117738 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117738 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117738 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11773d (StorePre 0x11773d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11773d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11773d 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117742 (movR64M64Effect 0x117742 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117742 (LoadPre 0x117742 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117742 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117742 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117747 (StorePre 0x117747 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117747 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117747 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11774c (movR64M64Effect 0x11774c 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11774c (LoadPre 0x11774c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11774c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11774c 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117751 (movR64M64Effect 0x117751 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117751 (LoadPre 0x117751 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117751 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117751 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117756 (StorePre 0x117756 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117756 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117756 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11775b (StorePre 0x11775b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11775b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11775b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11775f (movR64R64Effect 0x11775f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11775f (fun s => s.RIP = 0x11775f) (movR64R64Effect 0x11775f 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117762 (movR64R64Effect 0x117762 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117762 (fun s => s.RIP = 0x117762) (movR64R64Effect 0x117762 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117765 (callEffect (fun _ => 0x1145f0) 0x11776a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117765 (PushPre 0x117765 5) (callEffect (fun _ => 0x1145f0) 0x11776a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11776a⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11776a, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11772e : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x86, 0xCE, 0xFF, 0xFF]

theorem code_l11772e : ∀ x ∈ codeRange 0x11772e bytes_l11772e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1772e 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Signing.LIR
