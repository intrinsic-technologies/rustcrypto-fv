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

@[cfg_block] def b_l11776a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11776a (movR64M64Effect 0x11776a 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11776a (LoadPre 0x11776a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11776a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11776a 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11776f (StorePre 0x11776f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11776f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11776f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117774 (movR64M64Effect 0x117774 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117774 (LoadPre 0x117774 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117774 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117774 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117779 (StorePre 0x117779 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117779 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117779 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11777e (movR64M64Effect 0x11777e 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11777e (LoadPre 0x11777e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11777e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11777e 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117783 (StorePre 0x117783 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117783 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117783 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117788 (movR64M64Effect 0x117788 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117788 (LoadPre 0x117788 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117788 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117788 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11778d (movR64M64Effect 0x11778d 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11778d (LoadPre 0x11778d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11778d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11778d 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117792 (StorePre 0x117792 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117792 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117792 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117797 (StorePre 0x117797 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117797 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117797 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11779b (movR64R64Effect 0x11779b 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11779b (fun s => s.RIP = 0x11779b) (movR64R64Effect 0x11779b 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11779e (movR64R64Effect 0x11779e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11779e (fun s => s.RIP = 0x11779e) (movR64R64Effect 0x11779e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1177a1 (callEffect (fun _ => 0x1145f0) 0x1177a6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1177a1 (PushPre 0x1177a1 5) (callEffect (fun _ => 0x1145f0) 0x1177a6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1177a6⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1177a6, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11776a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x4A, 0xCE, 0xFF, 0xFF]

theorem code_l11776a : ∀ x ∈ codeRange 0x11776a bytes_l11776a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1776a 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1177a6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1177a6 (movR64M64Effect 0x1177a6 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1177a6 (LoadPre 0x1177a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1177a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177a6 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1177ab (StorePre 0x1177ab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1177ab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177ab 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1177b0 (movR64M64Effect 0x1177b0 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1177b0 (LoadPre 0x1177b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1177b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177b0 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1177b5 (StorePre 0x1177b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1177b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177b5 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1177ba (movR64M64Effect 0x1177ba 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1177ba (LoadPre 0x1177ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1177ba + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177ba 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1177bf (StorePre 0x1177bf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1177bf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177bf 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1177c4 (movR64M64Effect 0x1177c4 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1177c4 (LoadPre 0x1177c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1177c4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177c4 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1177c9 (movR64M64Effect 0x1177c9 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1177c9 (LoadPre 0x1177c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1177c9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177c9 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1177ce (StorePre 0x1177ce 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1177ce + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177ce 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1177d3 (StorePre 0x1177d3 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1177d3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1177d3 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1177d7 (movR64R64Effect 0x1177d7 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1177d7 (fun s => s.RIP = 0x1177d7) (movR64R64Effect 0x1177d7 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1177da (movR64R64Effect 0x1177da 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1177da (fun s => s.RIP = 0x1177da) (movR64R64Effect 0x1177da 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1177dd (callEffect (fun _ => 0x1145f0) 0x1177e2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1177dd (PushPre 0x1177dd 5) (callEffect (fun _ => 0x1145f0) 0x1177e2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1177e2⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1177e2, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1177a6 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x0E, 0xCE, 0xFF, 0xFF]

theorem code_l1177a6 : ∀ x ∈ codeRange 0x1177a6 bytes_l1177a6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x177a6 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1177e2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1177e2 (movR64M64Effect 0x1177e2 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1177e2 (LoadPre 0x1177e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1177e2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177e2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1177e7 (StorePre 0x1177e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1177e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177e7 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1177ec (movR64M64Effect 0x1177ec 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1177ec (LoadPre 0x1177ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1177ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177ec 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1177f1 (StorePre 0x1177f1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1177f1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177f1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1177f6 (movR64M64Effect 0x1177f6 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1177f6 (LoadPre 0x1177f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1177f6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177f6 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1177fb (StorePre 0x1177fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1177fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177fb 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117800 (movR64M64Effect 0x117800 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117800 (LoadPre 0x117800 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117800 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117800 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117805 (movR64M64Effect 0x117805 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117805 (LoadPre 0x117805 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117805 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117805 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11780a (StorePre 0x11780a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11780a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11780a 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11780f (StorePre 0x11780f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11780f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11780f 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117813 (movR64R64Effect 0x117813 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117813 (fun s => s.RIP = 0x117813) (movR64R64Effect 0x117813 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117816 (movR64R64Effect 0x117816 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117816 (fun s => s.RIP = 0x117816) (movR64R64Effect 0x117816 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117819 (callEffect (fun _ => 0x1145f0) 0x11781e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117819 (PushPre 0x117819 5) (callEffect (fun _ => 0x1145f0) 0x11781e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11781e⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11781e, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1177e2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xD2, 0xCD, 0xFF, 0xFF]

theorem code_l1177e2 : ∀ x ∈ codeRange 0x1177e2 bytes_l1177e2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x177e2 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11781e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11781e (movR64M64Effect 0x11781e 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11781e (LoadPre 0x11781e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11781e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11781e 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117823 (StorePre 0x117823 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117823 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117823 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117828 (movR64M64Effect 0x117828 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117828 (LoadPre 0x117828 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117828 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117828 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11782d (StorePre 0x11782d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11782d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11782d 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117832 (movR64M64Effect 0x117832 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117832 (LoadPre 0x117832 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117832 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117832 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117837 (StorePre 0x117837 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117837 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117837 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11783c (movR64M64Effect 0x11783c 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11783c (LoadPre 0x11783c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11783c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11783c 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117841 (movR64M64Effect 0x117841 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117841 (LoadPre 0x117841 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117841 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117841 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117846 (StorePre 0x117846 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117846 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117846 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11784b (StorePre 0x11784b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11784b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11784b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11784f (movR64R64Effect 0x11784f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11784f (fun s => s.RIP = 0x11784f) (movR64R64Effect 0x11784f 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117852 (movR64R64Effect 0x117852 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117852 (fun s => s.RIP = 0x117852) (movR64R64Effect 0x117852 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117855 (callEffect (fun _ => 0x1145f0) 0x11785a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117855 (PushPre 0x117855 5) (callEffect (fun _ => 0x1145f0) 0x11785a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11785a⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11785a, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11781e : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x96, 0xCD, 0xFF, 0xFF]

theorem code_l11781e : ∀ x ∈ codeRange 0x11781e bytes_l11781e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1781e 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11785a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11785a (movR64M64Effect 0x11785a 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11785a (LoadPre 0x11785a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11785a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11785a 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11785f (StorePre 0x11785f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11785f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11785f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117864 (movR64M64Effect 0x117864 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117864 (LoadPre 0x117864 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117864 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117864 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117869 (StorePre 0x117869 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117869 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117869 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11786e (movR64M64Effect 0x11786e 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11786e (LoadPre 0x11786e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11786e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11786e 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117873 (StorePre 0x117873 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117873 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117873 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117878 (movR64M64Effect 0x117878 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117878 (LoadPre 0x117878 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117878 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117878 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11787d (movR64M64Effect 0x11787d 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11787d (LoadPre 0x11787d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11787d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11787d 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117882 (StorePre 0x117882 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117882 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117882 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117887 (StorePre 0x117887 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117887 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117887 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11788b (movR64R64Effect 0x11788b 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11788b (fun s => s.RIP = 0x11788b) (movR64R64Effect 0x11788b 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11788e (movR64R64Effect 0x11788e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11788e (fun s => s.RIP = 0x11788e) (movR64R64Effect 0x11788e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117891 (callEffect (fun _ => 0x1145f0) 0x117896) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117891 (PushPre 0x117891 5) (callEffect (fun _ => 0x1145f0) 0x117896) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117896⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117896, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11785a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x5A, 0xCD, 0xFF, 0xFF]

theorem code_l11785a : ∀ x ∈ codeRange 0x11785a bytes_l11785a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1785a 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117896 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117896 (movR64M64Effect 0x117896 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117896 (LoadPre 0x117896 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117896 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117896 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11789b (StorePre 0x11789b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11789b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11789b 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1178a0 (movR64M64Effect 0x1178a0 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1178a0 (LoadPre 0x1178a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1178a0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178a0 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1178a5 (StorePre 0x1178a5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1178a5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178a5 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1178aa (movR64M64Effect 0x1178aa 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1178aa (LoadPre 0x1178aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1178aa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178aa 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1178af (StorePre 0x1178af 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1178af + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178af 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1178b4 (movR64M64Effect 0x1178b4 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1178b4 (LoadPre 0x1178b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1178b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178b4 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1178b9 (movR64M64Effect 0x1178b9 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1178b9 (LoadPre 0x1178b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1178b9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178b9 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1178be (StorePre 0x1178be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1178be + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178be 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1178c3 (StorePre 0x1178c3 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1178c3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1178c3 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1178c7 (movR64R64Effect 0x1178c7 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1178c7 (fun s => s.RIP = 0x1178c7) (movR64R64Effect 0x1178c7 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1178ca (movR64R64Effect 0x1178ca 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1178ca (fun s => s.RIP = 0x1178ca) (movR64R64Effect 0x1178ca 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1178cd (callEffect (fun _ => 0x1145f0) 0x1178d2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1178cd (PushPre 0x1178cd 5) (callEffect (fun _ => 0x1145f0) 0x1178d2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1178d2⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1178d2, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117896 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x1E, 0xCD, 0xFF, 0xFF]

theorem code_l117896 : ∀ x ∈ codeRange 0x117896 bytes_l117896, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17896 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1178d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1178d2 (movR64M64Effect 0x1178d2 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1178d2 (LoadPre 0x1178d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1178d2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178d2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1178d7 (StorePre 0x1178d7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1178d7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178d7 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1178dc (movR64M64Effect 0x1178dc 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1178dc (LoadPre 0x1178dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1178dc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178dc 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1178e1 (StorePre 0x1178e1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1178e1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178e1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1178e6 (movR64M64Effect 0x1178e6 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1178e6 (LoadPre 0x1178e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1178e6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178e6 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1178eb (StorePre 0x1178eb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1178eb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178eb 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1178f0 (movR64M64Effect 0x1178f0 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1178f0 (LoadPre 0x1178f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1178f0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178f0 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1178f5 (movR64M64Effect 0x1178f5 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1178f5 (LoadPre 0x1178f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1178f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178f5 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1178fa (StorePre 0x1178fa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1178fa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178fa 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1178ff (StorePre 0x1178ff 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1178ff + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1178ff 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117903 (movR64R64Effect 0x117903 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117903 (fun s => s.RIP = 0x117903) (movR64R64Effect 0x117903 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117906 (movR64R64Effect 0x117906 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117906 (fun s => s.RIP = 0x117906) (movR64R64Effect 0x117906 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117909 (callEffect (fun _ => 0x1145f0) 0x11790e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117909 (PushPre 0x117909 5) (callEffect (fun _ => 0x1145f0) 0x11790e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11790e⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11790e, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1178d2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xE2, 0xCC, 0xFF, 0xFF]

theorem code_l1178d2 : ∀ x ∈ codeRange 0x1178d2 bytes_l1178d2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x178d2 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11790e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11790e (movR64M64Effect 0x11790e 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11790e (LoadPre 0x11790e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11790e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11790e 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117913 (StorePre 0x117913 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117913 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117913 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117918 (movR64M64Effect 0x117918 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117918 (LoadPre 0x117918 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117918 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117918 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11791d (StorePre 0x11791d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11791d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11791d 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117922 (movR64M64Effect 0x117922 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117922 (LoadPre 0x117922 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117922 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117922 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117927 (StorePre 0x117927 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117927 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117927 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11792c (movR64M64Effect 0x11792c 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11792c (LoadPre 0x11792c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11792c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11792c 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117931 (movR64M64Effect 0x117931 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117931 (LoadPre 0x117931 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117931 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117931 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117936 (StorePre 0x117936 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117936 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117936 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11793b (StorePre 0x11793b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11793b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11793b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11793f (movR64R64Effect 0x11793f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11793f (fun s => s.RIP = 0x11793f) (movR64R64Effect 0x11793f 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117942 (movR64R64Effect 0x117942 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117942 (fun s => s.RIP = 0x117942) (movR64R64Effect 0x117942 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117945 (callEffect (fun _ => 0x1145f0) 0x11794a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117945 (PushPre 0x117945 5) (callEffect (fun _ => 0x1145f0) 0x11794a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11794a⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11794a, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11790e : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xA6, 0xCC, 0xFF, 0xFF]

theorem code_l11790e : ∀ x ∈ codeRange 0x11790e bytes_l11790e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1790e 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11794a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11794a (movR64M64Effect 0x11794a 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11794a (LoadPre 0x11794a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11794a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11794a 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11794f (StorePre 0x11794f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11794f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11794f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117954 (movR64M64Effect 0x117954 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117954 (LoadPre 0x117954 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117954 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117954 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117959 (StorePre 0x117959 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117959 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117959 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11795e (movR64M64Effect 0x11795e 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11795e (LoadPre 0x11795e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11795e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11795e 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117963 (StorePre 0x117963 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117963 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117963 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117968 (movR64M64Effect 0x117968 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117968 (LoadPre 0x117968 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117968 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117968 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11796d (movR64M64Effect 0x11796d 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11796d (LoadPre 0x11796d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11796d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11796d 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117972 (StorePre 0x117972 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117972 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117972 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117977 (StorePre 0x117977 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117977 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117977 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11797b (movR64R64Effect 0x11797b 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11797b (fun s => s.RIP = 0x11797b) (movR64R64Effect 0x11797b 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11797e (movR64R64Effect 0x11797e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11797e (fun s => s.RIP = 0x11797e) (movR64R64Effect 0x11797e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117981 (callEffect (fun _ => 0x1145f0) 0x117986) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117981 (PushPre 0x117981 5) (callEffect (fun _ => 0x1145f0) 0x117986) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117986⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117986, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11794a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x6A, 0xCC, 0xFF, 0xFF]

theorem code_l11794a : ∀ x ∈ codeRange 0x11794a bytes_l11794a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1794a 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117986 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117986 (movR64M64Effect 0x117986 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117986 (LoadPre 0x117986 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117986 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117986 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11798b (StorePre 0x11798b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11798b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11798b 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117990 (movR64M64Effect 0x117990 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117990 (LoadPre 0x117990 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117990 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117990 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117995 (StorePre 0x117995 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117995 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117995 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11799a (movR64M64Effect 0x11799a 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11799a (LoadPre 0x11799a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11799a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11799a 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11799f (StorePre 0x11799f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11799f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11799f 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1179a4 (movR64M64Effect 0x1179a4 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1179a4 (LoadPre 0x1179a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1179a4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179a4 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1179a9 (movR64M64Effect 0x1179a9 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1179a9 (LoadPre 0x1179a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1179a9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179a9 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1179ae (StorePre 0x1179ae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1179ae + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1179ae 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1179b3 (StorePre 0x1179b3 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1179b3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1179b3 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1179b7 (movR64R64Effect 0x1179b7 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1179b7 (fun s => s.RIP = 0x1179b7) (movR64R64Effect 0x1179b7 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1179ba (movR64R64Effect 0x1179ba 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1179ba (fun s => s.RIP = 0x1179ba) (movR64R64Effect 0x1179ba 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1179bd (callEffect (fun _ => 0x1145f0) 0x1179c2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1179bd (PushPre 0x1179bd 5) (callEffect (fun _ => 0x1145f0) 0x1179c2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1179c2⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1179c2, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117986 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x2E, 0xCC, 0xFF, 0xFF]

theorem code_l117986 : ∀ x ∈ codeRange 0x117986 bytes_l117986, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17986 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1179c2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1179c2 (movR64M64Effect 0x1179c2 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1179c2 (LoadPre 0x1179c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1179c2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179c2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1179c7 (StorePre 0x1179c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1179c7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1179c7 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1179cc (movR64M64Effect 0x1179cc 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1179cc (LoadPre 0x1179cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1179cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179cc 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1179d1 (StorePre 0x1179d1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1179d1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1179d1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1179d6 (movR64M64Effect 0x1179d6 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1179d6 (LoadPre 0x1179d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1179d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179d6 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1179db (StorePre 0x1179db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1179db + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1179db 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1179e0 (movR64M64Effect 0x1179e0 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1179e0 (LoadPre 0x1179e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1179e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179e0 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1179e5 (movR64M64Effect 0x1179e5 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1179e5 (LoadPre 0x1179e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1179e5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179e5 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1179ea (StorePre 0x1179ea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1179ea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1179ea 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1179ef (StorePre 0x1179ef 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1179ef + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1179ef 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1179f3 (movR64R64Effect 0x1179f3 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1179f3 (fun s => s.RIP = 0x1179f3) (movR64R64Effect 0x1179f3 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1179f6 (movR64R64Effect 0x1179f6 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1179f6 (fun s => s.RIP = 0x1179f6) (movR64R64Effect 0x1179f6 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1179f9 (callEffect (fun _ => 0x1145f0) 0x1179fe) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1179f9 (PushPre 0x1179f9 5) (callEffect (fun _ => 0x1145f0) 0x1179fe) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1179fe⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1179fe, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1179c2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xF2, 0xCB, 0xFF, 0xFF]

theorem code_l1179c2 : ∀ x ∈ codeRange 0x1179c2 bytes_l1179c2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x179c2 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1179fe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1179fe (movR64M64Effect 0x1179fe 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1179fe (LoadPre 0x1179fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1179fe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179fe 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117a03 (StorePre 0x117a03 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117a03 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a03 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117a08 (movR64M64Effect 0x117a08 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117a08 (LoadPre 0x117a08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117a08 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a08 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117a0d (StorePre 0x117a0d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117a0d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a0d 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117a12 (movR64M64Effect 0x117a12 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117a12 (LoadPre 0x117a12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117a12 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a12 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117a17 (StorePre 0x117a17 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117a17 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a17 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117a1c (movR64M64Effect 0x117a1c 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117a1c (LoadPre 0x117a1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117a1c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a1c 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117a21 (movR64M64Effect 0x117a21 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117a21 (LoadPre 0x117a21 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117a21 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a21 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117a26 (StorePre 0x117a26 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117a26 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a26 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117a2b (StorePre 0x117a2b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117a2b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117a2b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117a2f (movR64R64Effect 0x117a2f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117a2f (fun s => s.RIP = 0x117a2f) (movR64R64Effect 0x117a2f 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117a32 (movR64R64Effect 0x117a32 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117a32 (fun s => s.RIP = 0x117a32) (movR64R64Effect 0x117a32 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117a35 (callEffect (fun _ => 0x1145f0) 0x117a3a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117a35 (PushPre 0x117a35 5) (callEffect (fun _ => 0x1145f0) 0x117a3a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117a3a⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117a3a, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1179fe : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xB6, 0xCB, 0xFF, 0xFF]

theorem code_l1179fe : ∀ x ∈ codeRange 0x1179fe bytes_l1179fe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x179fe 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117a3a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117a3a (movR64M64Effect 0x117a3a 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117a3a (LoadPre 0x117a3a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117a3a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a3a 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117a3f (StorePre 0x117a3f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117a3f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a3f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117a44 (movR64M64Effect 0x117a44 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117a44 (LoadPre 0x117a44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117a44 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a44 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117a49 (StorePre 0x117a49 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117a49 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a49 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117a4e (movR64M64Effect 0x117a4e 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117a4e (LoadPre 0x117a4e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117a4e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a4e 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117a53 (StorePre 0x117a53 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117a53 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a53 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117a58 (movR64M64Effect 0x117a58 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117a58 (LoadPre 0x117a58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117a58 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a58 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117a5d (movR64M64Effect 0x117a5d 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117a5d (LoadPre 0x117a5d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117a5d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a5d 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117a62 (StorePre 0x117a62 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117a62 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a62 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117a67 (StorePre 0x117a67 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117a67 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117a67 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117a6b (movR64R64Effect 0x117a6b 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117a6b (fun s => s.RIP = 0x117a6b) (movR64R64Effect 0x117a6b 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117a6e (movR64R64Effect 0x117a6e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117a6e (fun s => s.RIP = 0x117a6e) (movR64R64Effect 0x117a6e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117a71 (callEffect (fun _ => 0x1145f0) 0x117a76) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117a71 (PushPre 0x117a71 5) (callEffect (fun _ => 0x1145f0) 0x117a76) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117a76⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117a76, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117a3a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x7A, 0xCB, 0xFF, 0xFF]

theorem code_l117a3a : ∀ x ∈ codeRange 0x117a3a bytes_l117a3a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17a3a 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117a76 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117a76 (movR64M64Effect 0x117a76 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117a76 (LoadPre 0x117a76 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117a76 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a76 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117a7b (StorePre 0x117a7b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117a7b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a7b 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117a80 (movR64M64Effect 0x117a80 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117a80 (LoadPre 0x117a80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117a80 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a80 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117a85 (StorePre 0x117a85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117a85 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a85 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117a8a (movR64M64Effect 0x117a8a 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117a8a (LoadPre 0x117a8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117a8a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a8a 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117a8f (StorePre 0x117a8f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117a8f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a8f 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117a94 (movR64M64Effect 0x117a94 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117a94 (LoadPre 0x117a94 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117a94 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a94 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117a99 (movR64M64Effect 0x117a99 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117a99 (LoadPre 0x117a99 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117a99 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a99 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117a9e (StorePre 0x117a9e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117a9e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a9e 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117aa3 (StorePre 0x117aa3 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117aa3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117aa3 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117aa7 (movR64R64Effect 0x117aa7 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117aa7 (fun s => s.RIP = 0x117aa7) (movR64R64Effect 0x117aa7 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117aaa (movR64R64Effect 0x117aaa 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117aaa (fun s => s.RIP = 0x117aaa) (movR64R64Effect 0x117aaa 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117aad (callEffect (fun _ => 0x1145f0) 0x117ab2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117aad (PushPre 0x117aad 5) (callEffect (fun _ => 0x1145f0) 0x117ab2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117ab2⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117ab2, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117a76 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x3E, 0xCB, 0xFF, 0xFF]

theorem code_l117a76 : ∀ x ∈ codeRange 0x117a76 bytes_l117a76, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17a76 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117ab2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117ab2 (movR64M64Effect 0x117ab2 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117ab2 (LoadPre 0x117ab2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117ab2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117ab2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117ab7 (StorePre 0x117ab7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117ab7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117ab7 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117abc (movR64M64Effect 0x117abc 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117abc (LoadPre 0x117abc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117abc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117abc 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117ac1 (StorePre 0x117ac1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117ac1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117ac1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117ac6 (movR64M64Effect 0x117ac6 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117ac6 (LoadPre 0x117ac6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117ac6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117ac6 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117acb (StorePre 0x117acb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117acb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117acb 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117ad0 (movR64M64Effect 0x117ad0 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117ad0 (LoadPre 0x117ad0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117ad0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117ad0 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117ad5 (movR64M64Effect 0x117ad5 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117ad5 (LoadPre 0x117ad5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117ad5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117ad5 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117ada (StorePre 0x117ada 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117ada + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117ada 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117adf (StorePre 0x117adf 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117adf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117adf 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117ae3 (movR64R64Effect 0x117ae3 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117ae3 (fun s => s.RIP = 0x117ae3) (movR64R64Effect 0x117ae3 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117ae6 (movR64R64Effect 0x117ae6 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117ae6 (fun s => s.RIP = 0x117ae6) (movR64R64Effect 0x117ae6 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117ae9 (callEffect (fun _ => 0x1145f0) 0x117aee) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117ae9 (PushPre 0x117ae9 5) (callEffect (fun _ => 0x1145f0) 0x117aee) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117aee⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117aee, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117ab2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x02, 0xCB, 0xFF, 0xFF]

theorem code_l117ab2 : ∀ x ∈ codeRange 0x117ab2 bytes_l117ab2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17ab2 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117aee : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117aee (movR64M64Effect 0x117aee 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117aee (LoadPre 0x117aee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117aee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117aee 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117af3 (StorePre 0x117af3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117af3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117af3 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117af8 (movR64M64Effect 0x117af8 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117af8 (LoadPre 0x117af8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117af8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117af8 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117afd (StorePre 0x117afd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117afd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117afd 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117b02 (movR64M64Effect 0x117b02 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117b02 (LoadPre 0x117b02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117b02 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b02 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117b07 (StorePre 0x117b07 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117b07 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b07 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117b0c (movR64M64Effect 0x117b0c 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117b0c (LoadPre 0x117b0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117b0c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b0c 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117b11 (movR64M64Effect 0x117b11 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117b11 (LoadPre 0x117b11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117b11 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b11 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117b16 (StorePre 0x117b16 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117b16 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b16 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117b1b (StorePre 0x117b1b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117b1b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117b1b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117b1f (movR64R64Effect 0x117b1f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117b1f (fun s => s.RIP = 0x117b1f) (movR64R64Effect 0x117b1f 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117b22 (movR64R64Effect 0x117b22 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117b22 (fun s => s.RIP = 0x117b22) (movR64R64Effect 0x117b22 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117b25 (callEffect (fun _ => 0x1145f0) 0x117b2a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117b25 (PushPre 0x117b25 5) (callEffect (fun _ => 0x1145f0) 0x117b2a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117b2a⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117b2a, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117aee : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xC6, 0xCA, 0xFF, 0xFF]

theorem code_l117aee : ∀ x ∈ codeRange 0x117aee bytes_l117aee, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17aee 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117b2a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117b2a (movR64M64Effect 0x117b2a 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117b2a (LoadPre 0x117b2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117b2a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b2a 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117b2f (StorePre 0x117b2f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117b2f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b2f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117b34 (movR64M64Effect 0x117b34 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117b34 (LoadPre 0x117b34 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117b34 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b34 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117b39 (StorePre 0x117b39 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117b39 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b39 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117b3e (movR64M64Effect 0x117b3e 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117b3e (LoadPre 0x117b3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117b3e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b3e 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117b43 (StorePre 0x117b43 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117b43 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b43 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117b48 (movR64M64Effect 0x117b48 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117b48 (LoadPre 0x117b48 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117b48 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b48 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117b4d (movR64M64Effect 0x117b4d 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117b4d (LoadPre 0x117b4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117b4d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b4d 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117b52 (StorePre 0x117b52 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117b52 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b52 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117b57 (StorePre 0x117b57 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117b57 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117b57 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117b5b (movR64R64Effect 0x117b5b 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117b5b (fun s => s.RIP = 0x117b5b) (movR64R64Effect 0x117b5b 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117b5e (movR64R64Effect 0x117b5e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117b5e (fun s => s.RIP = 0x117b5e) (movR64R64Effect 0x117b5e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117b61 (callEffect (fun _ => 0x1145f0) 0x117b66) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117b61 (PushPre 0x117b61 5) (callEffect (fun _ => 0x1145f0) 0x117b66) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117b66⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117b66, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117b2a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x8A, 0xCA, 0xFF, 0xFF]

theorem code_l117b2a : ∀ x ∈ codeRange 0x117b2a bytes_l117b2a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17b2a 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117b66 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117b66 (movR64M64Effect 0x117b66 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117b66 (LoadPre 0x117b66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117b66 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b66 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117b6b (StorePre 0x117b6b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117b6b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b6b 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117b70 (movR64M64Effect 0x117b70 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117b70 (LoadPre 0x117b70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117b70 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b70 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117b75 (StorePre 0x117b75 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117b75 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b75 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117b7a (movR64M64Effect 0x117b7a 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117b7a (LoadPre 0x117b7a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117b7a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b7a 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117b7f (StorePre 0x117b7f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117b7f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b7f 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117b84 (movR64M64Effect 0x117b84 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117b84 (LoadPre 0x117b84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117b84 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b84 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117b89 (movR64M64Effect 0x117b89 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117b89 (LoadPre 0x117b89 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117b89 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b89 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117b8e (StorePre 0x117b8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117b8e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b8e 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117b93 (StorePre 0x117b93 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117b93 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117b93 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117b97 (movR64R64Effect 0x117b97 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117b97 (fun s => s.RIP = 0x117b97) (movR64R64Effect 0x117b97 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117b9a (movR64R64Effect 0x117b9a 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117b9a (fun s => s.RIP = 0x117b9a) (movR64R64Effect 0x117b9a 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117b9d (callEffect (fun _ => 0x1145f0) 0x117ba2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117b9d (PushPre 0x117b9d 5) (callEffect (fun _ => 0x1145f0) 0x117ba2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117ba2⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117ba2, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117b66 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x4E, 0xCA, 0xFF, 0xFF]

theorem code_l117b66 : ∀ x ∈ codeRange 0x117b66 bytes_l117b66, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17b66 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117ba2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117ba2 (movR64M64Effect 0x117ba2 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117ba2 (LoadPre 0x117ba2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117ba2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117ba2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117ba7 (StorePre 0x117ba7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117ba7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117ba7 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117bac (movR64M64Effect 0x117bac 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117bac (LoadPre 0x117bac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117bac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117bac 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117bb1 (StorePre 0x117bb1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117bb1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117bb1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117bb6 (movR64M64Effect 0x117bb6 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117bb6 (LoadPre 0x117bb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117bb6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117bb6 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117bbb (StorePre 0x117bbb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117bbb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117bbb 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117bc0 (movR64M64Effect 0x117bc0 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117bc0 (LoadPre 0x117bc0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117bc0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117bc0 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117bc5 (movR64M64Effect 0x117bc5 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117bc5 (LoadPre 0x117bc5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117bc5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117bc5 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117bca (StorePre 0x117bca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117bca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117bca 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117bcf (StorePre 0x117bcf 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117bcf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117bcf 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117bd3 (movR64R64Effect 0x117bd3 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117bd3 (fun s => s.RIP = 0x117bd3) (movR64R64Effect 0x117bd3 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117bd6 (movR64R64Effect 0x117bd6 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117bd6 (fun s => s.RIP = 0x117bd6) (movR64R64Effect 0x117bd6 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117bd9 (callEffect (fun _ => 0x1145f0) 0x117bde) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117bd9 (PushPre 0x117bd9 5) (callEffect (fun _ => 0x1145f0) 0x117bde) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117bde⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117bde, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117ba2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x12, 0xCA, 0xFF, 0xFF]

theorem code_l117ba2 : ∀ x ∈ codeRange 0x117ba2 bytes_l117ba2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17ba2 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Ecdh.LIR
