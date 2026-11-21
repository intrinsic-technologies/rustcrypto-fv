import K256.Proofs.Sec1.LIR.Labels
import K256.Proofs.Common.CFG.EvalAttr
import K256.Proofs.Common.Lift.Generated.Footprints.Part1
import K256.Proofs.Common.Lift.Generated.Footprints.Part2
import K256.Proofs.Common.Lift.Generated.Footprints.Part3
import K256.Proofs.Common.Lift.Generated.Footprints.Part4
import K256.Proofs.Common.Lift.Generated.Footprints.Part5
import K256.Proofs.Sec1.LIR.Generated.Footprints

namespace K256.Proofs.Sec1.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

def b_l118e1a_12 : Block Op Label signature Reg.count 571 :=
  .letOp (n := 571) (.out 0x119250 (movR64R64Effect 0x119250 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[567]
    (.letOp (n := 572) (.exec 0x119250 (fun s => s.RIP = 0x119250) (movR64R64Effect 0x119250 6 14) (Reg.operands [.gpr 14] [])) #v[567]
    (.letOp (n := 573) (.out 0x119253 (callEffect (fun _ => 0x1145f0) 0x119258) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 574) (.exec 0x119253 (PushPre 0x119253 5) (callEffect (fun _ => 0x1145f0) 0x119258) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 575) (.const ⟨64, 0x119258⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 552), (1, 561), (2, 550), (3, 565), (4, 573), (5, 487), (6, 571), (7, 569), (8, 460), (9, 434), (10, 534), (11, 498), (12, 494), (13, 457), (14, 567), (15, 375), (22, 22), (39, 39), (50, 50), (51, 51)] 576⟩ { target := .l119258, kept := #v[], arity := rfl, guard := some (Fin.last 575) }))))))

def bytes_l118e1a_12 : List UInt8 :=
  [0x4C, 0x89, 0xF6, 0xE8, 0x98, 0xB3, 0xFF, 0xFF]

theorem code_l118e1a_12 : ∀ x ∈ codeRange 0x119250 bytes_l118e1a_12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19250 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l118e1a_11 : Block Op Label signature Reg.count 534 :=
  .letOp (n := 534) (.out 0x1191f9 (andR64R64Effect 0x1191f9 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[519, 494]
    (.letOp (n := 535) (.exec 0x1191f9 (fun s => s.RIP = 0x1191f9) (andR64R64Effect 0x1191f9 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[519, 494]
    (.letOp (n := 536) (.out 0x1191fc (movR64M64Effect 0x1191fc 1 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 537) (.exec 0x1191fc (LoadPre 0x1191fc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1191fc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1191fc 1 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 538) (.out 0x119204 (andR64R64Effect 0x119204 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[536, 494]
    (.letOp (n := 539) (.exec 0x119204 (fun s => s.RIP = 0x119204) (andR64R64Effect 0x119204 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[536, 494]
    (.letOp (n := 540) (.out 0x119207 (addR64R64Effect 0x119207 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[538, 531]
    (.letOp (n := 541) (.out 0x119207 (addR64R64Effect 0x119207 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[538, 531]
    (.letOp (n := 542) (.exec 0x119207 (fun s => s.RIP = 0x119207) (addR64R64Effect 0x119207 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[538, 531]
    (.letOp (n := 543) (.out 0x11920a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11920a 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[532, 541]
    (.letOp (n := 544) (.exec 0x11920a (fun s => s.RIP = 0x11920a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11920a 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[532, 541]
    (.letOp (n := 545) (.out 0x11920e (addR64R64Effect 0x11920e 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[540, 526]
    (.letOp (n := 546) (.out 0x11920e (addR64R64Effect 0x11920e 1 3) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 3] []) (.flag .CF)) #v[540, 526]
    (.letOp (n := 547) (.exec 0x11920e (fun s => s.RIP = 0x11920e) (addR64R64Effect 0x11920e 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[540, 526]
    (.letOp (n := 548) (.out 0x119211 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119211 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[543, 546]
    (.letOp (n := 549) (.exec 0x119211 (fun s => s.RIP = 0x119211) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119211 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[543, 546]
    (.letOp (n := 550) (.out 0x119215 (shldR64R64Effect 0x119215 5 2 1 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[548, 545]
    (.letOp (n := 551) (.exec 0x119215 (fun s => s.RIP = 0x119215) (shldR64R64Effect 0x119215 5 2 1 12) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[548, 545]
    (.letOp (n := 552) (.out 0x11921a (movR64Imm64Effect 0x11921a 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 553) (.exec 0x11921a (fun s => s.RIP = 0x11921a) (movR64Imm64Effect 0x11921a 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 554) (.out 0x119224 (andR64R64Effect 0x119224 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[240, 552]
    (.letOp (n := 555) (.exec 0x119224 (fun s => s.RIP = 0x119224) (andR64R64Effect 0x119224 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[240, 552]
    (.letOp (n := 556) (.out 0x119227 (addR64R64Effect 0x119227 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[554, 550]
    (.letOp (n := 557) (.exec 0x119227 (fun s => s.RIP = 0x119227) (addR64R64Effect 0x119227 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[554, 550]
    (.letOp (n := 558) (.exec 0x11922a (StorePre 0x11922a 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11922a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11922a 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 15, .gpr 4] [])) #v[375, 4]
    (.letOp (n := 559) (.exec 0x11922e (StorePre 0x11922e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11922e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11922e 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[460, 4]
    (.letOp (n := 560) (.exec 0x119233 (StorePre 0x119233 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119233 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119233 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[534, 4]
    (.letOp (n := 561) (.out 0x119238 (andR64R64Effect 0x119238 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[545, 494]
    (.letOp (n := 562) (.exec 0x119238 (fun s => s.RIP = 0x119238) (andR64R64Effect 0x119238 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[545, 494]
    (.letOp (n := 563) (.exec 0x11923b (StorePre 0x11923b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11923b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11923b 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[561, 4]
    (.letOp (n := 564) (.exec 0x119240 (StorePre 0x119240 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119240 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119240 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[556, 4]
    (.letOp (n := 565) (.out 0x119245 (leaR64Effect 0x119245 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 566) (.exec 0x119245 (fun s => s.RIP = 0x119245) (leaR64Effect 0x119245 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 567) (.out 0x11924a (movR64R64Effect 0x11924a 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 568) (.exec 0x11924a (fun s => s.RIP = 0x11924a) (movR64R64Effect 0x11924a 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 569) (.out 0x11924d (movR64R64Effect 0x11924d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[565]
    (.letOp (n := 570) (.exec 0x11924d (fun s => s.RIP = 0x11924d) (movR64R64Effect 0x11924d 7 3) (Reg.operands [.gpr 3] [])) #v[565]
    (b_l118e1a_12)))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_11 : List UInt8 :=
  [0x4D, 0x21, 0xE2, 0x48, 0x8B, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x4C, 0x21, 0xE1, 0x48, 0x01,
    0xC1, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x01, 0xD9, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x0F, 0xA4, 0xCA,
    0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x21, 0xC6, 0x48, 0x01,
    0xD6, 0x4C, 0x89, 0x3C, 0x24, 0x4C, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x89, 0x54, 0x24, 0x10, 0x4C,
    0x21, 0xE1, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x74, 0x24, 0x20, 0x48, 0x8D, 0x5C, 0x24,
    0x28, 0x49, 0x89, 0xE6, 0x48, 0x89, 0xDF] ++ bytes_l118e1a_12

theorem code_l118e1a_11 : ∀ x ∈ codeRange 0x1191f9 bytes_l118e1a_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x191f9 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_12

def b_l118e1a_10 : Block Op Label signature Reg.count 490 :=
  .letOp (n := 490) (.out 0x119199 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119199 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[485, 488]
    (.letOp (n := 491) (.exec 0x119199 (fun s => s.RIP = 0x119199) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119199 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[485, 488]
    (.letOp (n := 492) (.out 0x11919d (movR64R64Effect 0x11919d 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[487]
    (.letOp (n := 493) (.exec 0x11919d (fun s => s.RIP = 0x11919d) (movR64R64Effect 0x11919d 0 5) (Reg.operands [.gpr 5] [])) #v[487]
    (.letOp (n := 494) (.out 0x1191a0 (movR64Imm64Effect 0x1191a0 12 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 495) (.exec 0x1191a0 (fun s => s.RIP = 0x1191a0) (movR64Imm64Effect 0x1191a0 12 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 496) (.out 0x1191aa (andR64R64Effect 0x1191aa 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[492, 494]
    (.letOp (n := 497) (.exec 0x1191aa (fun s => s.RIP = 0x1191aa) (andR64R64Effect 0x1191aa 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[492, 494]
    (.letOp (n := 498) (.out 0x1191ad (movR64Imm64Effect 0x1191ad 11 0x1000003d10) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 499) (.exec 0x1191ad (fun s => s.RIP = 0x1191ad) (movR64Imm64Effect 0x1191ad 11 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 500) (.out 0x1191b7 (mulR64Effect 0x1191b7 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[498, 496]
    (.letOp (n := 501) (.out 0x1191b7 (mulR64Effect 0x1191b7 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[498, 496]
    (.letOp (n := 502) (.exec 0x1191b7 (fun s => s.RIP = 0x1191b7) (mulR64Effect 0x1191b7 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[498, 496]
    (.letOp (n := 503) (.out 0x1191ba (addR64M64Effect 0x1191ba 10 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[450, 4]
    (.letOp (n := 504) (.out 0x1191ba (addR64M64Effect 0x1191ba 10 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[450, 4]
    (.letOp (n := 505) (.exec 0x1191ba (LoadPre 0x1191ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1191ba + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1191ba 10 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[450, 4]
    (.letOp (n := 506) (.out 0x1191bf (atFlags StatusFlags.CF (adcR64M64Effect 0x1191bf 3 (.sib 4 none 0 (.d32 0xd0)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[448, 4, 504]
    (.letOp (n := 507) (.exec 0x1191bf (LoadPre 0x1191bf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1191bf + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1191bf 3 (.sib 4 none 0 (.d32 0xd0)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[448, 4, 504]
    (.letOp (n := 508) (.out 0x1191c7 (addR64R64Effect 0x1191c7 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[503, 457]
    (.letOp (n := 509) (.out 0x1191c7 (addR64R64Effect 0x1191c7 10 13) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 13] []) (.flag .CF)) #v[503, 457]
    (.letOp (n := 510) (.exec 0x1191c7 (fun s => s.RIP = 0x1191c7) (addR64R64Effect 0x1191c7 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[503, 457]
    (.letOp (n := 511) (.out 0x1191ca (atFlags StatusFlags.CF (adcR64M64Effect 0x1191ca 3 (.sib 4 none 0 (.d32 0xa0)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[506, 4, 509]
    (.letOp (n := 512) (.exec 0x1191ca (LoadPre 0x1191ca (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1191ca + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1191ca 3 (.sib 4 none 0 (.d32 0xa0)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[506, 4, 509]
    (.letOp (n := 513) (.out 0x1191d2 (addR64R64Effect 0x1191d2 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[508, 500]
    (.letOp (n := 514) (.out 0x1191d2 (addR64R64Effect 0x1191d2 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[508, 500]
    (.letOp (n := 515) (.exec 0x1191d2 (fun s => s.RIP = 0x1191d2) (addR64R64Effect 0x1191d2 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[508, 500]
    (.letOp (n := 516) (.out 0x1191d5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1191d5 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[511, 501, 514]
    (.letOp (n := 517) (.exec 0x1191d5 (fun s => s.RIP = 0x1191d5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1191d5 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[511, 501, 514]
    (.letOp (n := 518) (.exec 0x1191d8 (StorePre 0x1191d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1191d8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1191d8 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[475, 4]
    (.letOp (n := 519) (.out 0x1191dd (addR64R64Effect 0x1191dd 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[513, 434]
    (.letOp (n := 520) (.out 0x1191dd (addR64R64Effect 0x1191dd 10 9) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 9] []) (.flag .CF)) #v[513, 434]
    (.letOp (n := 521) (.exec 0x1191dd (fun s => s.RIP = 0x1191dd) (addR64R64Effect 0x1191dd 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[513, 434]
    (.letOp (n := 522) (.out 0x1191e0 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1191e0 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[516, 520]
    (.letOp (n := 523) (.exec 0x1191e0 (fun s => s.RIP = 0x1191e0) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1191e0 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[516, 520]
    (.letOp (n := 524) (.out 0x1191e4 (shldR64R64Effect 0x1191e4 5 14 5 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[490, 487]
    (.letOp (n := 525) (.exec 0x1191e4 (fun s => s.RIP = 0x1191e4) (shldR64R64Effect 0x1191e4 5 14 5 12) (Reg.operands [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[490, 487]
    (.letOp (n := 526) (.out 0x1191e9 (shldR64R64Effect 0x1191e9 5 3 10 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[522, 519]
    (.letOp (n := 527) (.exec 0x1191e9 (fun s => s.RIP = 0x1191e9) (shldR64R64Effect 0x1191e9 5 3 10 12) (Reg.operands [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[522, 519]
    (.letOp (n := 528) (.exec 0x1191ee (StorePre 0x1191ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1191ee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1191ee 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[464, 4]
    (.letOp (n := 529) (.out 0x1191f3 (movR64R64Effect 0x1191f3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[524]
    (.letOp (n := 530) (.exec 0x1191f3 (fun s => s.RIP = 0x1191f3) (movR64R64Effect 0x1191f3 0 14) (Reg.operands [.gpr 14] [])) #v[524]
    (.letOp (n := 531) (.out 0x1191f6 (mulR64Effect 0x1191f6 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[498, 529]
    (.letOp (n := 532) (.out 0x1191f6 (mulR64Effect 0x1191f6 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[498, 529]
    (.letOp (n := 533) (.exec 0x1191f6 (fun s => s.RIP = 0x1191f6) (mulR64Effect 0x1191f6 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[498, 529]
    (b_l118e1a_11))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_10 : List UInt8 :=
  [0x49, 0x83, 0xD6, 0x00, 0x48, 0x89, 0xE8, 0x49, 0xBC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F,
    0x00, 0x4C, 0x21, 0xE0, 0x49, 0xBB, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x49, 0xF7,
    0xE3, 0x4C, 0x03, 0x54, 0x24, 0x60, 0x48, 0x13, 0x9C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4D, 0x01,
    0xEA, 0x48, 0x13, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC2, 0x48, 0x11, 0xD3, 0x48,
    0x89, 0x4C, 0x24, 0x20, 0x4D, 0x01, 0xCA, 0x48, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xEE, 0x0C,
    0x4C, 0x0F, 0xA4, 0xD3, 0x0C, 0x48, 0x89, 0x7C, 0x24, 0x18, 0x4C, 0x89, 0xF0, 0x49, 0xF7, 0xE3] ++ bytes_l118e1a_11

theorem code_l118e1a_10 : ∀ x ∈ codeRange 0x119199 bytes_l118e1a_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19199 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_11

def b_l118e1a_9 : Block Op Label signature Reg.count 445 :=
  .letOp (n := 445) (.out 0x119140 (mulM64Effect 0x119140 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[443, 4]
    (.letOp (n := 446) (.out 0x119140 (mulM64Effect 0x119140 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[443, 4]
    (.letOp (n := 447) (.exec 0x119140 (LoadPre 0x119140 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x119140 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x119140 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[443, 4]
    (.letOp (n := 448) (.out 0x119148 (movR64R64Effect 0x119148 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[446]
    (.letOp (n := 449) (.exec 0x119148 (fun s => s.RIP = 0x119148) (movR64R64Effect 0x119148 3 2) (Reg.operands [.gpr 2] [])) #v[446]
    (.letOp (n := 450) (.out 0x11914b (movR64R64Effect 0x11914b 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[445]
    (.letOp (n := 451) (.exec 0x11914b (fun s => s.RIP = 0x11914b) (movR64R64Effect 0x11914b 10 0) (Reg.operands [.gpr 0] [])) #v[445]
    (.letOp (n := 452) (.out 0x11914e (movR64M64Effect 0x11914e 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 453) (.exec 0x11914e (LoadPre 0x11914e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11914e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11914e 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 454) (.out 0x119156 (mulR64Effect 0x119156 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[364, 452]
    (.letOp (n := 455) (.out 0x119156 (mulR64Effect 0x119156 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[364, 452]
    (.letOp (n := 456) (.exec 0x119156 (fun s => s.RIP = 0x119156) (mulR64Effect 0x119156 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[364, 452]
    (.letOp (n := 457) (.out 0x119159 (movR64R64Effect 0x119159 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[454]
    (.letOp (n := 458) (.exec 0x119159 (fun s => s.RIP = 0x119159) (movR64R64Effect 0x119159 13 0) (Reg.operands [.gpr 0] [])) #v[454]
    (.letOp (n := 459) (.exec 0x11915c (StorePre 0x11915c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11915c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11915c 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[455, 4]
    (.letOp (n := 460) (.out 0x119164 (andR64R64Effect 0x119164 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[429, 412]
    (.letOp (n := 461) (.exec 0x119164 (fun s => s.RIP = 0x119164) (andR64R64Effect 0x119164 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[429, 412]
    (.letOp (n := 462) (.out 0x119167 (movR64M64Effect 0x119167 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 463) (.exec 0x119167 (LoadPre 0x119167 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x119167 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119167 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 464) (.out 0x11916f (movR64M64Effect 0x11916f 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 465) (.exec 0x11916f (LoadPre 0x11916f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11916f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11916f 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 466) (.out 0x119174 (mulR64Effect 0x119174 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[464, 462]
    (.letOp (n := 467) (.out 0x119174 (mulR64Effect 0x119174 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[464, 462]
    (.letOp (n := 468) (.exec 0x119174 (fun s => s.RIP = 0x119174) (mulR64Effect 0x119174 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[464, 462]
    (.letOp (n := 469) (.out 0x119177 (movR64R64Effect 0x119177 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[467]
    (.letOp (n := 470) (.exec 0x119177 (fun s => s.RIP = 0x119177) (movR64R64Effect 0x119177 14 2) (Reg.operands [.gpr 2] [])) #v[467]
    (.letOp (n := 471) (.out 0x11917a (movR64R64Effect 0x11917a 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[466]
    (.letOp (n := 472) (.exec 0x11917a (fun s => s.RIP = 0x11917a) (movR64R64Effect 0x11917a 12 0) (Reg.operands [.gpr 0] [])) #v[466]
    (.letOp (n := 473) (.out 0x11917d (movR64M64Effect 0x11917d 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 474) (.exec 0x11917d (LoadPre 0x11917d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11917d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11917d 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 475) (.out 0x119185 (movR64M64Effect 0x119185 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 476) (.exec 0x119185 (LoadPre 0x119185 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x119185 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119185 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 477) (.out 0x11918a (mulR64Effect 0x11918a 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[475, 473]
    (.letOp (n := 478) (.out 0x11918a (mulR64Effect 0x11918a 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[475, 473]
    (.letOp (n := 479) (.exec 0x11918a (fun s => s.RIP = 0x11918a) (mulR64Effect 0x11918a 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[475, 473]
    (.letOp (n := 480) (.out 0x11918d (movR64R64Effect 0x11918d 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[477]
    (.letOp (n := 481) (.exec 0x11918d (fun s => s.RIP = 0x11918d) (movR64R64Effect 0x11918d 5 0) (Reg.operands [.gpr 0] [])) #v[477]
    (.letOp (n := 482) (.out 0x119190 (addR64R64Effect 0x119190 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[480, 471]
    (.letOp (n := 483) (.out 0x119190 (addR64R64Effect 0x119190 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[480, 471]
    (.letOp (n := 484) (.exec 0x119190 (fun s => s.RIP = 0x119190) (addR64R64Effect 0x119190 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[480, 471]
    (.letOp (n := 485) (.out 0x119193 (atFlags StatusFlags.CF (adcR64R64Effect 0x119193 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[469, 478, 483]
    (.letOp (n := 486) (.exec 0x119193 (fun s => s.RIP = 0x119193) (atFlags StatusFlags.CF (adcR64R64Effect 0x119193 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[469, 478, 483]
    (.letOp (n := 487) (.out 0x119196 (addR64R64Effect 0x119196 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[482, 408]
    (.letOp (n := 488) (.out 0x119196 (addR64R64Effect 0x119196 5 11) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 11] []) (.flag .CF)) #v[482, 408]
    (.letOp (n := 489) (.exec 0x119196 (fun s => s.RIP = 0x119196) (addR64R64Effect 0x119196 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[482, 408]
    (b_l118e1a_10)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_9 : List UInt8 :=
  [0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC2, 0x48, 0x8B,
    0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xC5, 0x48, 0x89, 0x94, 0x24,
    0xA0, 0x00, 0x00, 0x00, 0x4D, 0x21, 0xE0, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x7C, 0x24, 0x78, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x84,
    0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x50, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC5,
    0x4C, 0x01, 0xE5, 0x49, 0x11, 0xD6, 0x4C, 0x01, 0xDD] ++ bytes_l118e1a_10

theorem code_l118e1a_9 : ∀ x ∈ codeRange 0x119140 bytes_l118e1a_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19140 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_10

def b_l118e1a_8 : Block Op Label signature Reg.count 401 :=
  .letOp (n := 401) (.out 0x1190df (atFlags StatusFlags.CF (adcR64R64Effect 0x1190df 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[396, 391, 399]
    (.letOp (n := 402) (.exec 0x1190df (fun s => s.RIP = 0x1190df) (atFlags StatusFlags.CF (adcR64R64Effect 0x1190df 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[396, 391, 399]
    (.letOp (n := 403) (.out 0x1190e2 (addR64R64Effect 0x1190e2 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[398, 320]
    (.letOp (n := 404) (.out 0x1190e2 (addR64R64Effect 0x1190e2 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[398, 320]
    (.letOp (n := 405) (.exec 0x1190e2 (fun s => s.RIP = 0x1190e2) (addR64R64Effect 0x1190e2 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[398, 320]
    (.letOp (n := 406) (.out 0x1190e5 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1190e5 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[401, 404]
    (.letOp (n := 407) (.exec 0x1190e5 (fun s => s.RIP = 0x1190e5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1190e5 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[401, 404]
    (.letOp (n := 408) (.out 0x1190e9 (shldR64R64Effect 0x1190e9 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[406, 403]
    (.letOp (n := 409) (.exec 0x1190e9 (fun s => s.RIP = 0x1190e9) (shldR64R64Effect 0x1190e9 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[406, 403]
    (.letOp (n := 410) (.out 0x1190ee (andR64R64Effect 0x1190ee 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[403, 373]
    (.letOp (n := 411) (.exec 0x1190ee (fun s => s.RIP = 0x1190ee) (andR64R64Effect 0x1190ee 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[403, 373]
    (.letOp (n := 412) (.out 0x1190f1 (movR64R64Effect 0x1190f1 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[373]
    (.letOp (n := 413) (.exec 0x1190f1 (fun s => s.RIP = 0x1190f1) (movR64R64Effect 0x1190f1 12 1) (Reg.operands [.gpr 1] [])) #v[373]
    (.letOp (n := 414) (.out 0x1190f4 (movR64Imm64Effect 0x1190f4 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 415) (.exec 0x1190f4 (fun s => s.RIP = 0x1190f4) (movR64Imm64Effect 0x1190f4 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 416) (.out 0x1190fe (mulR64Effect 0x1190fe 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[414, 410]
    (.letOp (n := 417) (.out 0x1190fe (mulR64Effect 0x1190fe 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[414, 410]
    (.letOp (n := 418) (.exec 0x1190fe (fun s => s.RIP = 0x1190fe) (mulR64Effect 0x1190fe 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[414, 410]
    (.letOp (n := 419) (.out 0x119101 (addR64M64Effect 0x119101 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[360, 4]
    (.letOp (n := 420) (.out 0x119101 (addR64M64Effect 0x119101 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[360, 4]
    (.letOp (n := 421) (.exec 0x119101 (LoadPre 0x119101 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x119101 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x119101 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[360, 4]
    (.letOp (n := 422) (.out 0x119109 (atFlags StatusFlags.CF (adcR64M64Effect 0x119109 9 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[358, 4, 420]
    (.letOp (n := 423) (.exec 0x119109 (LoadPre 0x119109 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x119109 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x119109 9 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[358, 4, 420]
    (.letOp (n := 424) (.out 0x119111 (addR64R64Effect 0x119111 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[419, 416]
    (.letOp (n := 425) (.out 0x119111 (addR64R64Effect 0x119111 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[419, 416]
    (.letOp (n := 426) (.exec 0x119111 (fun s => s.RIP = 0x119111) (addR64R64Effect 0x119111 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[419, 416]
    (.letOp (n := 427) (.out 0x119114 (atFlags StatusFlags.CF (adcR64R64Effect 0x119114 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[422, 417, 425]
    (.letOp (n := 428) (.exec 0x119114 (fun s => s.RIP = 0x119114) (atFlags StatusFlags.CF (adcR64R64Effect 0x119114 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[422, 417, 425]
    (.letOp (n := 429) (.out 0x119117 (addR64R64Effect 0x119117 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[424, 344]
    (.letOp (n := 430) (.out 0x119117 (addR64R64Effect 0x119117 8 3) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 3] []) (.flag .CF)) #v[424, 344]
    (.letOp (n := 431) (.exec 0x119117 (fun s => s.RIP = 0x119117) (addR64R64Effect 0x119117 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[424, 344]
    (.letOp (n := 432) (.out 0x11911a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11911a 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[427, 430]
    (.letOp (n := 433) (.exec 0x11911a (fun s => s.RIP = 0x11911a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11911a 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[427, 430]
    (.letOp (n := 434) (.out 0x11911e (shldR64R64Effect 0x11911e 5 9 8 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[432, 429]
    (.letOp (n := 435) (.exec 0x11911e (fun s => s.RIP = 0x11911e) (shldR64R64Effect 0x11911e 5 9 8 12) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[432, 429]
    (.letOp (n := 436) (.out 0x119123 (movR64R64Effect 0x119123 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[386]
    (.letOp (n := 437) (.exec 0x119123 (fun s => s.RIP = 0x119123) (movR64R64Effect 0x119123 0 7) (Reg.operands [.gpr 7] [])) #v[386]
    (.letOp (n := 438) (.out 0x119126 (mulM64Effect 0x119126 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[436, 4]
    (.letOp (n := 439) (.out 0x119126 (mulM64Effect 0x119126 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[436, 4]
    (.letOp (n := 440) (.exec 0x119126 (LoadPre 0x119126 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x119126 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x119126 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[436, 4]
    (.letOp (n := 441) (.exec 0x11912b (StorePre 0x11912b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11912b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11912b 2 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[439, 4]
    (.letOp (n := 442) (.exec 0x119133 (StorePre 0x119133 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x119133 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119133 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[438, 4]
    (.letOp (n := 443) (.out 0x119138 (movR64M64Effect 0x119138 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 444) (.exec 0x119138 (LoadPre 0x119138 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x119138 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119138 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l118e1a_9))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_8 : List UInt8 :=
  [0x49, 0x11, 0xD3, 0x4C, 0x01, 0xD0, 0x49, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x48,
    0x21, 0xC8, 0x49, 0x89, 0xCC, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE1, 0x4C, 0x03, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x8C, 0x24, 0x98, 0x00,
    0x00, 0x00, 0x49, 0x01, 0xC0, 0x49, 0x11, 0xD1, 0x49, 0x01, 0xD8, 0x49, 0x83, 0xD1, 0x00, 0x4D,
    0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x60, 0x48, 0x89, 0x94, 0x24,
    0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00,
    0x00] ++ bytes_l118e1a_9

theorem code_l118e1a_8 : ∀ x ∈ codeRange 0x1190df bytes_l118e1a_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x190df 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_9

def b_l118e1a_7 : Block Op Label signature Reg.count 355 :=
  .letOp (n := 355) (.out 0x119089 (mulR64Effect 0x119089 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[262, 353]
    (.letOp (n := 356) (.out 0x119089 (mulR64Effect 0x119089 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[262, 353]
    (.letOp (n := 357) (.exec 0x119089 (fun s => s.RIP = 0x119089) (mulR64Effect 0x119089 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[262, 353]
    (.letOp (n := 358) (.out 0x11908c (movR64R64Effect 0x11908c 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[356]
    (.letOp (n := 359) (.exec 0x11908c (fun s => s.RIP = 0x11908c) (movR64R64Effect 0x11908c 9 2) (Reg.operands [.gpr 2] [])) #v[356]
    (.letOp (n := 360) (.out 0x11908f (movR64R64Effect 0x11908f 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[355]
    (.letOp (n := 361) (.exec 0x11908f (fun s => s.RIP = 0x11908f) (movR64R64Effect 0x11908f 8 0) (Reg.operands [.gpr 0] [])) #v[355]
    (.letOp (n := 362) (.out 0x119092 (movR64M64Effect 0x119092 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 363) (.exec 0x119092 (LoadPre 0x119092 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x119092 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119092 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 364) (.out 0x11909a (movR64M64Effect 0x11909a 14 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 365) (.exec 0x11909a (LoadPre 0x11909a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11909a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11909a 14 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 366) (.out 0x11909f (mulR64Effect 0x11909f 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[364, 362]
    (.letOp (n := 367) (.out 0x11909f (mulR64Effect 0x11909f 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[364, 362]
    (.letOp (n := 368) (.exec 0x11909f (fun s => s.RIP = 0x11909f) (mulR64Effect 0x11909f 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[364, 362]
    (.letOp (n := 369) (.out 0x1190a2 (movR64R64Effect 0x1190a2 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[366]
    (.letOp (n := 370) (.exec 0x1190a2 (fun s => s.RIP = 0x1190a2) (movR64R64Effect 0x1190a2 12 0) (Reg.operands [.gpr 0] [])) #v[366]
    (.letOp (n := 371) (.out 0x1190a5 (movR64R64Effect 0x1190a5 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[367]
    (.letOp (n := 372) (.exec 0x1190a5 (fun s => s.RIP = 0x1190a5) (movR64R64Effect 0x1190a5 13 2) (Reg.operands [.gpr 2] [])) #v[367]
    (.letOp (n := 373) (.out 0x1190a8 (movR64Imm64Effect 0x1190a8 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 374) (.exec 0x1190a8 (fun s => s.RIP = 0x1190a8) (movR64Imm64Effect 0x1190a8 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 375) (.out 0x1190b2 (andR64R64Effect 0x1190b2 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[339, 373]
    (.letOp (n := 376) (.exec 0x1190b2 (fun s => s.RIP = 0x1190b2) (andR64R64Effect 0x1190b2 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[339, 373]
    (.letOp (n := 377) (.out 0x1190b5 (movR64M64Effect 0x1190b5 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 378) (.exec 0x1190b5 (LoadPre 0x1190b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1190b5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1190b5 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 379) (.out 0x1190bd (mulR64Effect 0x1190bd 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[284, 377]
    (.letOp (n := 380) (.out 0x1190bd (mulR64Effect 0x1190bd 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[284, 377]
    (.letOp (n := 381) (.exec 0x1190bd (fun s => s.RIP = 0x1190bd) (mulR64Effect 0x1190bd 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[284, 377]
    (.letOp (n := 382) (.out 0x1190c0 (movR64R64Effect 0x1190c0 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[380]
    (.letOp (n := 383) (.exec 0x1190c0 (fun s => s.RIP = 0x1190c0) (movR64R64Effect 0x1190c0 11 2) (Reg.operands [.gpr 2] [])) #v[380]
    (.letOp (n := 384) (.out 0x1190c3 (movR64R64Effect 0x1190c3 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[379]
    (.letOp (n := 385) (.exec 0x1190c3 (fun s => s.RIP = 0x1190c3) (movR64R64Effect 0x1190c3 5 0) (Reg.operands [.gpr 0] [])) #v[379]
    (.letOp (n := 386) (.out 0x1190c6 (movR64M64Effect 0x1190c6 7 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 387) (.exec 0x1190c6 (LoadPre 0x1190c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1190c6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1190c6 7 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 388) (.out 0x1190ce (movR64R64Effect 0x1190ce 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[386]
    (.letOp (n := 389) (.exec 0x1190ce (fun s => s.RIP = 0x1190ce) (movR64R64Effect 0x1190ce 0 7) (Reg.operands [.gpr 7] [])) #v[386]
    (.letOp (n := 390) (.out 0x1190d1 (mulM64Effect 0x1190d1 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[388, 4]
    (.letOp (n := 391) (.out 0x1190d1 (mulM64Effect 0x1190d1 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[388, 4]
    (.letOp (n := 392) (.exec 0x1190d1 (LoadPre 0x1190d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1190d1 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1190d1 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[388, 4]
    (.letOp (n := 393) (.out 0x1190d6 (addR64R64Effect 0x1190d6 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[384, 369]
    (.letOp (n := 394) (.out 0x1190d6 (addR64R64Effect 0x1190d6 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[384, 369]
    (.letOp (n := 395) (.exec 0x1190d6 (fun s => s.RIP = 0x1190d6) (addR64R64Effect 0x1190d6 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[384, 369]
    (.letOp (n := 396) (.out 0x1190d9 (atFlags StatusFlags.CF (adcR64R64Effect 0x1190d9 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[382, 371, 394]
    (.letOp (n := 397) (.exec 0x1190d9 (fun s => s.RIP = 0x1190d9) (atFlags StatusFlags.CF (adcR64R64Effect 0x1190d9 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[382, 371, 394]
    (.letOp (n := 398) (.out 0x1190dc (addR64R64Effect 0x1190dc 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[390, 393]
    (.letOp (n := 399) (.out 0x1190dc (addR64R64Effect 0x1190dc 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[390, 393]
    (.letOp (n := 400) (.exec 0x1190dc (fun s => s.RIP = 0x1190dc) (addR64R64Effect 0x1190dc 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[390, 393]
    (b_l118e1a_8))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_7 : List UInt8 :=
  [0x49, 0xF7, 0xE1, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC0, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00,
    0x00, 0x4C, 0x8B, 0x74, 0x24, 0x58, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD5, 0x48,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xCF, 0x48, 0x8B, 0x84, 0x24,
    0xA8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0xBC,
    0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x50, 0x4C, 0x01, 0xE5,
    0x4D, 0x11, 0xEB, 0x48, 0x01, 0xE8] ++ bytes_l118e1a_8

theorem code_l118e1a_7 : ∀ x ∈ codeRange 0x119089 bytes_l118e1a_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19089 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_8

def b_l118e1a_6 : Block Op Label signature Reg.count 313 :=
  .letOp (n := 313) (.out 0x119020 (atFlags StatusFlags.CF (adcR64R64Effect 0x119020 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[308, 298, 311]
    (.letOp (n := 314) (.exec 0x119020 (fun s => s.RIP = 0x119020) (atFlags StatusFlags.CF (adcR64R64Effect 0x119020 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[308, 298, 311]
    (.letOp (n := 315) (.out 0x119023 (addR64R64Effect 0x119023 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[310, 245]
    (.letOp (n := 316) (.out 0x119023 (addR64R64Effect 0x119023 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[310, 245]
    (.letOp (n := 317) (.exec 0x119023 (fun s => s.RIP = 0x119023) (addR64R64Effect 0x119023 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[310, 245]
    (.letOp (n := 318) (.out 0x119026 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119026 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[313, 316]
    (.letOp (n := 319) (.exec 0x119026 (fun s => s.RIP = 0x119026) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119026 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[313, 316]
    (.letOp (n := 320) (.out 0x11902a (shldR64R64Effect 0x11902a 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[318, 315]
    (.letOp (n := 321) (.exec 0x11902a (fun s => s.RIP = 0x11902a) (shldR64R64Effect 0x11902a 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[318, 315]
    (.letOp (n := 322) (.out 0x11902f (shlR64Effect 0x11902f 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[315]
    (.letOp (n := 323) (.exec 0x11902f (fun s => s.RIP = 0x11902f) (shlR64Effect 0x11902f 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[315]
    (.letOp (n := 324) (.out 0x119033 (movR64Imm64Effect 0x119033 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 325) (.exec 0x119033 (fun s => s.RIP = 0x119033) (movR64Imm64Effect 0x119033 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 326) (.out 0x11903d (andR64R64Effect 0x11903d 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[322, 324]
    (.letOp (n := 327) (.exec 0x11903d (fun s => s.RIP = 0x11903d) (andR64R64Effect 0x11903d 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[322, 324]
    (.letOp (n := 328) (.out 0x119040 (orR64R64Effect 0x119040 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[326, 271]
    (.letOp (n := 329) (.exec 0x119040 (fun s => s.RIP = 0x119040) (orR64R64Effect 0x119040 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[326, 271]
    (.letOp (n := 330) (.out 0x119043 (movR64Imm64Effect 0x119043 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 331) (.exec 0x119043 (fun s => s.RIP = 0x119043) (movR64Imm64Effect 0x119043 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 332) (.out 0x11904d (mulR64Effect 0x11904d 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[330, 328]
    (.letOp (n := 333) (.out 0x11904d (mulR64Effect 0x11904d 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[330, 328]
    (.letOp (n := 334) (.exec 0x11904d (fun s => s.RIP = 0x11904d) (mulR64Effect 0x11904d 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[330, 328]
    (.letOp (n := 335) (.out 0x119050 (movR64R64Effect 0x119050 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[333]
    (.letOp (n := 336) (.exec 0x119050 (fun s => s.RIP = 0x119050) (movR64R64Effect 0x119050 3 2) (Reg.operands [.gpr 2] [])) #v[333]
    (.letOp (n := 337) (.out 0x119053 (movR64R64Effect 0x119053 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[332]
    (.letOp (n := 338) (.exec 0x119053 (fun s => s.RIP = 0x119053) (movR64R64Effect 0x119053 15 0) (Reg.operands [.gpr 0] [])) #v[332]
    (.letOp (n := 339) (.out 0x119056 (addR64M64Effect 0x119056 15 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[337, 4]
    (.letOp (n := 340) (.out 0x119056 (addR64M64Effect 0x119056 15 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[337, 4]
    (.letOp (n := 341) (.exec 0x119056 (LoadPre 0x119056 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x119056 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x119056 15 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[337, 4]
    (.letOp (n := 342) (.out 0x11905e (atFlags StatusFlags.CF (adcR64M64Effect 0x11905e 3 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[335, 4, 340]
    (.letOp (n := 343) (.exec 0x11905e (LoadPre 0x11905e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11905e + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11905e 3 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[335, 4, 340]
    (.letOp (n := 344) (.out 0x119066 (shldR64R64Effect 0x119066 5 3 15 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[342, 339]
    (.letOp (n := 345) (.exec 0x119066 (fun s => s.RIP = 0x119066) (shldR64R64Effect 0x119066 5 3 15 12) (Reg.operands [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[342, 339]
    (.letOp (n := 346) (.out 0x11906b (movR64R64Effect 0x11906b 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[293]
    (.letOp (n := 347) (.exec 0x11906b (fun s => s.RIP = 0x11906b) (movR64R64Effect 0x11906b 0 1) (Reg.operands [.gpr 1] [])) #v[293]
    (.letOp (n := 348) (.out 0x11906e (mulR64Effect 0x11906e 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[253, 346]
    (.letOp (n := 349) (.out 0x11906e (mulR64Effect 0x11906e 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[253, 346]
    (.letOp (n := 350) (.exec 0x11906e (fun s => s.RIP = 0x11906e) (mulR64Effect 0x11906e 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[253, 346]
    (.letOp (n := 351) (.exec 0x119071 (StorePre 0x119071 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x119071 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119071 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[349, 4]
    (.letOp (n := 352) (.exec 0x119079 (StorePre 0x119079 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x119079 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119079 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[348, 4]
    (.letOp (n := 353) (.out 0x119081 (movR64M64Effect 0x119081 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 354) (.exec 0x119081 (LoadPre 0x119081 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x119081 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119081 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l118e1a_7))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_6 : List UInt8 :=
  [0x49, 0x11, 0xD2, 0x48, 0x01, 0xF8, 0x49, 0x83, 0xD2, 0x00, 0x49, 0x0F, 0xA4, 0xC2, 0x0C, 0x48,
    0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0,
    0x4C, 0x09, 0xE8, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x48, 0x89, 0xD3, 0x49, 0x89, 0xC7, 0x4C, 0x03, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x13,
    0x9C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xA4, 0xFB, 0x0C, 0x48, 0x89, 0xC8, 0x49, 0xF7,
    0xE0, 0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] ++ bytes_l118e1a_7

theorem code_l118e1a_6 : ∀ x ∈ codeRange 0x119020 bytes_l118e1a_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19020 105 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_7

def b_l118e1a_5 : Block Op Label signature Reg.count 267 :=
  .letOp (n := 267) (.out 0x118fce (movR64R64Effect 0x118fce 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[264]
    (.letOp (n := 268) (.exec 0x118fce (fun s => s.RIP = 0x118fce) (movR64R64Effect 0x118fce 11 0) (Reg.operands [.gpr 0] [])) #v[264]
    (.letOp (n := 269) (.out 0x118fd1 (movR64R64Effect 0x118fd1 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[265]
    (.letOp (n := 270) (.exec 0x118fd1 (fun s => s.RIP = 0x118fd1) (movR64R64Effect 0x118fd1 3 2) (Reg.operands [.gpr 2] [])) #v[265]
    (.letOp (n := 271) (.out 0x118fd4 (andR32Imm8Effect 0x118fd4 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[249]
    (.letOp (n := 272) (.exec 0x118fd4 (fun s => s.RIP = 0x118fd4) (andR32Imm8Effect 0x118fd4 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[249]
    (.letOp (n := 273) (.out 0x118fd8 (movR64M64Effect 0x118fd8 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 274) (.exec 0x118fd8 (LoadPre 0x118fd8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x118fd8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118fd8 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 275) (.out 0x118fe0 (mulM64Effect 0x118fe0 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[273, 4]
    (.letOp (n := 276) (.out 0x118fe0 (mulM64Effect 0x118fe0 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[273, 4]
    (.letOp (n := 277) (.exec 0x118fe0 (LoadPre 0x118fe0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x118fe0 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x118fe0 5 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[273, 4]
    (.letOp (n := 278) (.out 0x118fe5 (movR64R64Effect 0x118fe5 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[276]
    (.letOp (n := 279) (.exec 0x118fe5 (fun s => s.RIP = 0x118fe5) (movR64R64Effect 0x118fe5 10 2) (Reg.operands [.gpr 2] [])) #v[276]
    (.letOp (n := 280) (.out 0x118fe8 (movR64R64Effect 0x118fe8 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[275]
    (.letOp (n := 281) (.exec 0x118fe8 (fun s => s.RIP = 0x118fe8) (movR64R64Effect 0x118fe8 14 0) (Reg.operands [.gpr 0] [])) #v[275]
    (.letOp (n := 282) (.out 0x118feb (movR64M64Effect 0x118feb 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 283) (.exec 0x118feb (LoadPre 0x118feb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x118feb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118feb 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 284) (.out 0x118ff3 (movR64M64Effect 0x118ff3 5 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 285) (.exec 0x118ff3 (LoadPre 0x118ff3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x118ff3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118ff3 5 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 286) (.out 0x118ff8 (mulR64Effect 0x118ff8 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[284, 282]
    (.letOp (n := 287) (.out 0x118ff8 (mulR64Effect 0x118ff8 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[284, 282]
    (.letOp (n := 288) (.exec 0x118ff8 (fun s => s.RIP = 0x118ff8) (mulR64Effect 0x118ff8 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[284, 282]
    (.letOp (n := 289) (.out 0x118ffb (movR64R64Effect 0x118ffb 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[287]
    (.letOp (n := 290) (.exec 0x118ffb (fun s => s.RIP = 0x118ffb) (movR64R64Effect 0x118ffb 15 2) (Reg.operands [.gpr 2] [])) #v[287]
    (.letOp (n := 291) (.out 0x118ffe (movR64R64Effect 0x118ffe 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[286]
    (.letOp (n := 292) (.exec 0x118ffe (fun s => s.RIP = 0x118ffe) (movR64R64Effect 0x118ffe 12 0) (Reg.operands [.gpr 0] [])) #v[286]
    (.letOp (n := 293) (.out 0x119001 (movR64M64Effect 0x119001 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 294) (.exec 0x119001 (LoadPre 0x119001 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x119001 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119001 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 295) (.out 0x119009 (movR64R64Effect 0x119009 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[293]
    (.letOp (n := 296) (.exec 0x119009 (fun s => s.RIP = 0x119009) (movR64R64Effect 0x119009 0 1) (Reg.operands [.gpr 1] [])) #v[293]
    (.letOp (n := 297) (.out 0x11900c (mulM64Effect 0x11900c 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[295, 4]
    (.letOp (n := 298) (.out 0x11900c (mulM64Effect 0x11900c 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[295, 4]
    (.letOp (n := 299) (.exec 0x11900c (LoadPre 0x11900c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11900c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11900c 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[295, 4]
    (.letOp (n := 300) (.out 0x119011 (addR64R64Effect 0x119011 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[280, 267]
    (.letOp (n := 301) (.out 0x119011 (addR64R64Effect 0x119011 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[280, 267]
    (.letOp (n := 302) (.exec 0x119011 (fun s => s.RIP = 0x119011) (addR64R64Effect 0x119011 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[280, 267]
    (.letOp (n := 303) (.out 0x119014 (atFlags StatusFlags.CF (adcR64R64Effect 0x119014 10 3)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[278, 269, 301]
    (.letOp (n := 304) (.exec 0x119014 (fun s => s.RIP = 0x119014) (atFlags StatusFlags.CF (adcR64R64Effect 0x119014 10 3)) (Reg.operands [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[278, 269, 301]
    (.letOp (n := 305) (.out 0x119017 (addR64R64Effect 0x119017 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[300, 291]
    (.letOp (n := 306) (.out 0x119017 (addR64R64Effect 0x119017 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[300, 291]
    (.letOp (n := 307) (.exec 0x119017 (fun s => s.RIP = 0x119017) (addR64R64Effect 0x119017 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[300, 291]
    (.letOp (n := 308) (.out 0x11901a (atFlags StatusFlags.CF (adcR64R64Effect 0x11901a 10 15)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[303, 289, 306]
    (.letOp (n := 309) (.exec 0x11901a (fun s => s.RIP = 0x11901a) (atFlags StatusFlags.CF (adcR64R64Effect 0x11901a 10 15)) (Reg.operands [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[303, 289, 306]
    (.letOp (n := 310) (.out 0x11901d (addR64R64Effect 0x11901d 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[297, 305]
    (.letOp (n := 311) (.out 0x11901d (addR64R64Effect 0x11901d 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[297, 305]
    (.letOp (n := 312) (.exec 0x11901d (fun s => s.RIP = 0x11901d) (addR64R64Effect 0x11901d 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[297, 305]
    (b_l118e1a_6))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_5 : List UInt8 :=
  [0x49, 0x89, 0xC3, 0x48, 0x89, 0xD3, 0x41, 0x83, 0xE5, 0x0F, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x58, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x84,
    0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x6C, 0x24, 0x78, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD7,
    0x49, 0x89, 0xC4, 0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x48, 0xF7,
    0x64, 0x24, 0x50, 0x4D, 0x01, 0xDE, 0x49, 0x11, 0xDA, 0x4D, 0x01, 0xE6, 0x4D, 0x11, 0xFA, 0x4C,
    0x01, 0xF0] ++ bytes_l118e1a_6

theorem code_l118e1a_5 : ∀ x ∈ codeRange 0x118fce bytes_l118e1a_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18fce 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_6

def b_l118e1a_4 : Block Op Label signature Reg.count 223 :=
  .letOp (n := 223) (.out 0x118f78 (atFlags StatusFlags.CF (adcR64R64Effect 0x118f78 7 14)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[218, 178, 221]
    (.letOp (n := 224) (.exec 0x118f78 (fun s => s.RIP = 0x118f78) (atFlags StatusFlags.CF (adcR64R64Effect 0x118f78 7 14)) (Reg.operands [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[218, 178, 221]
    (.letOp (n := 225) (.out 0x118f7b (addR64R64Effect 0x118f7b 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[220, 189]
    (.letOp (n := 226) (.out 0x118f7b (addR64R64Effect 0x118f7b 6 13) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 13] []) (.flag .CF)) #v[220, 189]
    (.letOp (n := 227) (.exec 0x118f7b (fun s => s.RIP = 0x118f7b) (addR64R64Effect 0x118f7b 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[220, 189]
    (.letOp (n := 228) (.out 0x118f7e (atFlags StatusFlags.CF (adcR64R64Effect 0x118f7e 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[223, 187, 226]
    (.letOp (n := 229) (.exec 0x118f7e (fun s => s.RIP = 0x118f7e) (atFlags StatusFlags.CF (adcR64R64Effect 0x118f7e 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[223, 187, 226]
    (.letOp (n := 230) (.out 0x118f81 (addR64R64Effect 0x118f81 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[225, 198]
    (.letOp (n := 231) (.out 0x118f81 (addR64R64Effect 0x118f81 6 11) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 11] []) (.flag .CF)) #v[225, 198]
    (.letOp (n := 232) (.exec 0x118f81 (fun s => s.RIP = 0x118f81) (addR64R64Effect 0x118f81 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[225, 198]
    (.letOp (n := 233) (.out 0x118f84 (atFlags StatusFlags.CF (adcR64R64Effect 0x118f84 7 5)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[228, 200, 231]
    (.letOp (n := 234) (.exec 0x118f84 (fun s => s.RIP = 0x118f84) (atFlags StatusFlags.CF (adcR64R64Effect 0x118f84 7 5)) (Reg.operands [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[228, 200, 231]
    (.letOp (n := 235) (.out 0x118f87 (addR64R64Effect 0x118f87 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[230, 210]
    (.letOp (n := 236) (.out 0x118f87 (addR64R64Effect 0x118f87 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[230, 210]
    (.letOp (n := 237) (.exec 0x118f87 (fun s => s.RIP = 0x118f87) (addR64R64Effect 0x118f87 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[230, 210]
    (.letOp (n := 238) (.out 0x118f8a (atFlags StatusFlags.CF (adcR64R64Effect 0x118f8a 7 8)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[233, 213, 236]
    (.letOp (n := 239) (.exec 0x118f8a (fun s => s.RIP = 0x118f8a) (atFlags StatusFlags.CF (adcR64R64Effect 0x118f8a 7 8)) (Reg.operands [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[233, 213, 236]
    (.letOp (n := 240) (.out 0x118f8d (addR64R64Effect 0x118f8d 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[235, 155]
    (.letOp (n := 241) (.out 0x118f8d (addR64R64Effect 0x118f8d 6 9) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 9] []) (.flag .CF)) #v[235, 155]
    (.letOp (n := 242) (.exec 0x118f8d (fun s => s.RIP = 0x118f8d) (addR64R64Effect 0x118f8d 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[235, 155]
    (.letOp (n := 243) (.out 0x118f90 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118f90 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[238, 241]
    (.letOp (n := 244) (.exec 0x118f90 (fun s => s.RIP = 0x118f90) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118f90 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[238, 241]
    (.letOp (n := 245) (.out 0x118f94 (shldR64R64Effect 0x118f94 5 7 6 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[243, 240]
    (.letOp (n := 246) (.exec 0x118f94 (fun s => s.RIP = 0x118f94) (shldR64R64Effect 0x118f94 5 7 6 12) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[243, 240]
    (.letOp (n := 247) (.out 0x118f99 (movR64R64Effect 0x118f99 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[240]
    (.letOp (n := 248) (.exec 0x118f99 (fun s => s.RIP = 0x118f99) (movR64R64Effect 0x118f99 13 6) (Reg.operands [.gpr 6] [])) #v[240]
    (.letOp (n := 249) (.out 0x118f9c (shrR64Effect 0x118f9c 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[247]
    (.letOp (n := 250) (.exec 0x118f9c (fun s => s.RIP = 0x118f9c) (shrR64Effect 0x118f9c 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[247]
    (.letOp (n := 251) (.out 0x118fa0 (movR64R64Effect 0x118fa0 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[191]
    (.letOp (n := 252) (.exec 0x118fa0 (fun s => s.RIP = 0x118fa0) (movR64R64Effect 0x118fa0 0 10) (Reg.operands [.gpr 10] [])) #v[191]
    (.letOp (n := 253) (.out 0x118fa3 (movR64M64Effect 0x118fa3 8 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 254) (.exec 0x118fa3 (LoadPre 0x118fa3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x118fa3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118fa3 8 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 255) (.out 0x118fa8 (mulR64Effect 0x118fa8 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[253, 251]
    (.letOp (n := 256) (.out 0x118fa8 (mulR64Effect 0x118fa8 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[253, 251]
    (.letOp (n := 257) (.exec 0x118fa8 (fun s => s.RIP = 0x118fa8) (mulR64Effect 0x118fa8 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[253, 251]
    (.letOp (n := 258) (.exec 0x118fab (StorePre 0x118fab 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x118fab + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118fab 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[256, 4]
    (.letOp (n := 259) (.exec 0x118fb3 (StorePre 0x118fb3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x118fb3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118fb3 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[255, 4]
    (.letOp (n := 260) (.out 0x118fbb (movR64M64Effect 0x118fbb 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 261) (.exec 0x118fbb (LoadPre 0x118fbb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x118fbb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118fbb 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 262) (.out 0x118fc3 (movR64M64Effect 0x118fc3 9 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 263) (.exec 0x118fc3 (LoadPre 0x118fc3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x118fc3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118fc3 9 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 264) (.out 0x118fcb (mulR64Effect 0x118fcb 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[262, 260]
    (.letOp (n := 265) (.out 0x118fcb (mulR64Effect 0x118fcb 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[262, 260]
    (.letOp (n := 266) (.exec 0x118fcb (fun s => s.RIP = 0x118fcb) (mulR64Effect 0x118fcb 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[262, 260]
    (b_l118e1a_5))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_4 : List UInt8 :=
  [0x4C, 0x11, 0xF7, 0x4C, 0x01, 0xEE, 0x4C, 0x11, 0xFF, 0x4C, 0x01, 0xDE, 0x48, 0x11, 0xEF, 0x48,
    0x01, 0xC6, 0x4C, 0x11, 0xC7, 0x4C, 0x01, 0xCE, 0x48, 0x83, 0xD7, 0x00, 0x48, 0x0F, 0xA4, 0xF7,
    0x0C, 0x49, 0x89, 0xF5, 0x49, 0xC1, 0xED, 0x30, 0x4C, 0x89, 0xD0, 0x4C, 0x8B, 0x44, 0x24, 0x60,
    0x49, 0xF7, 0xE0, 0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB8,
    0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x8C, 0x24, 0x80,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE1] ++ bytes_l118e1a_5

theorem code_l118e1a_4 : ∀ x ∈ codeRange 0x118f78 bytes_l118e1a_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18f78 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_5

def b_l118e1a_3 : Block Op Label signature Reg.count 178 :=
  .letOp (n := 178) (.out 0x118f24 (movR64R64Effect 0x118f24 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[176]
    (.letOp (n := 179) (.exec 0x118f24 (fun s => s.RIP = 0x118f24) (movR64R64Effect 0x118f24 14 2) (Reg.operands [.gpr 2] [])) #v[176]
    (.letOp (n := 180) (.out 0x118f27 (movR64R64Effect 0x118f27 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[175]
    (.letOp (n := 181) (.exec 0x118f27 (fun s => s.RIP = 0x118f27) (movR64R64Effect 0x118f27 12 0) (Reg.operands [.gpr 0] [])) #v[175]
    (.letOp (n := 182) (.out 0x118f2a (movR64R64Effect 0x118f2a 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[90]
    (.letOp (n := 183) (.exec 0x118f2a (fun s => s.RIP = 0x118f2a) (movR64R64Effect 0x118f2a 0 5) (Reg.operands [.gpr 5] [])) #v[90]
    (.letOp (n := 184) (.out 0x118f2d (mulR64Effect 0x118f2d 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[55, 182]
    (.letOp (n := 185) (.out 0x118f2d (mulR64Effect 0x118f2d 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[55, 182]
    (.letOp (n := 186) (.exec 0x118f2d (fun s => s.RIP = 0x118f2d) (mulR64Effect 0x118f2d 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[55, 182]
    (.letOp (n := 187) (.out 0x118f30 (movR64R64Effect 0x118f30 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[185]
    (.letOp (n := 188) (.exec 0x118f30 (fun s => s.RIP = 0x118f30) (movR64R64Effect 0x118f30 15 2) (Reg.operands [.gpr 2] [])) #v[185]
    (.letOp (n := 189) (.out 0x118f33 (movR64R64Effect 0x118f33 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[184]
    (.letOp (n := 190) (.exec 0x118f33 (fun s => s.RIP = 0x118f33) (movR64R64Effect 0x118f33 13 0) (Reg.operands [.gpr 0] [])) #v[184]
    (.letOp (n := 191) (.out 0x118f36 (movR64M64Effect 0x118f36 10 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 192) (.exec 0x118f36 (LoadPre 0x118f36 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x118f36 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118f36 10 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 193) (.out 0x118f3e (movR64R64Effect 0x118f3e 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[191]
    (.letOp (n := 194) (.exec 0x118f3e (fun s => s.RIP = 0x118f3e) (movR64R64Effect 0x118f3e 0 10) (Reg.operands [.gpr 10] [])) #v[191]
    (.letOp (n := 195) (.out 0x118f41 (mulR64Effect 0x118f41 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[126, 193]
    (.letOp (n := 196) (.out 0x118f41 (mulR64Effect 0x118f41 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[126, 193]
    (.letOp (n := 197) (.exec 0x118f41 (fun s => s.RIP = 0x118f41) (mulR64Effect 0x118f41 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[126, 193]
    (.letOp (n := 198) (.out 0x118f44 (movR64R64Effect 0x118f44 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[195]
    (.letOp (n := 199) (.exec 0x118f44 (fun s => s.RIP = 0x118f44) (movR64R64Effect 0x118f44 11 0) (Reg.operands [.gpr 0] [])) #v[195]
    (.letOp (n := 200) (.out 0x118f47 (movR64R64Effect 0x118f47 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[196]
    (.letOp (n := 201) (.exec 0x118f47 (fun s => s.RIP = 0x118f47) (movR64R64Effect 0x118f47 5 2) (Reg.operands [.gpr 2] [])) #v[196]
    (.letOp (n := 202) (.out 0x118f4a (shrR64Effect 0x118f4a 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[132]
    (.letOp (n := 203) (.exec 0x118f4a (fun s => s.RIP = 0x118f4a) (shrR64Effect 0x118f4a 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[132]
    (.letOp (n := 204) (.out 0x118f4e (movR64Imm64Effect 0x118f4e 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 205) (.exec 0x118f4e (fun s => s.RIP = 0x118f4e) (movR64Imm64Effect 0x118f4e 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 206) (.out 0x118f58 (imulR64R64Effect 0x118f58 4 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[202, 204]
    (.letOp (n := 207) (.exec 0x118f58 (fun s => s.RIP = 0x118f58) (imulR64R64Effect 0x118f58 4 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[202, 204]
    (.letOp (n := 208) (.out 0x118f5c (movR64R64Effect 0x118f5c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[136]
    (.letOp (n := 209) (.exec 0x118f5c (fun s => s.RIP = 0x118f5c) (movR64R64Effect 0x118f5c 0 3) (Reg.operands [.gpr 3] [])) #v[136]
    (.letOp (n := 210) (.out 0x118f5f (mulR64Effect 0x118f5f 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[204, 208]
    (.letOp (n := 211) (.out 0x118f5f (mulR64Effect 0x118f5f 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[204, 208]
    (.letOp (n := 212) (.exec 0x118f5f (fun s => s.RIP = 0x118f5f) (mulR64Effect 0x118f5f 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[204, 208]
    (.letOp (n := 213) (.out 0x118f62 (addR64R64Effect 0x118f62 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[206, 211]
    (.letOp (n := 214) (.exec 0x118f62 (fun s => s.RIP = 0x118f62) (addR64R64Effect 0x118f62 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[206, 211]
    (.letOp (n := 215) (.out 0x118f65 (addR64M64Effect 0x118f65 6 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[171, 4]
    (.letOp (n := 216) (.out 0x118f65 (addR64M64Effect 0x118f65 6 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[171, 4]
    (.letOp (n := 217) (.exec 0x118f65 (LoadPre 0x118f65 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x118f65 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x118f65 6 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[171, 4]
    (.letOp (n := 218) (.out 0x118f6d (atFlags StatusFlags.CF (adcR64M64Effect 0x118f6d 7 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[169, 4, 216]
    (.letOp (n := 219) (.exec 0x118f6d (LoadPre 0x118f6d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x118f6d + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x118f6d 7 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[169, 4, 216]
    (.letOp (n := 220) (.out 0x118f75 (addR64R64Effect 0x118f75 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[215, 180]
    (.letOp (n := 221) (.out 0x118f75 (addR64R64Effect 0x118f75 6 12) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 12] []) (.flag .CF)) #v[215, 180]
    (.letOp (n := 222) (.exec 0x118f75 (fun s => s.RIP = 0x118f75) (addR64R64Effect 0x118f75 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[215, 180]
    (b_l118e1a_4)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_3 : List UInt8 :=
  [0x49, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD7, 0x49,
    0x89, 0xC5, 0x4C, 0x8B, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0xE1,
    0x49, 0x89, 0xC3, 0x48, 0x89, 0xD5, 0x49, 0xC1, 0xE8, 0x34, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xC1, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0xE1, 0x49, 0x01,
    0xD0, 0x48, 0x03, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x13, 0xBC, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x4C, 0x01, 0xE6] ++ bytes_l118e1a_4

theorem code_l118e1a_3 : ∀ x ∈ codeRange 0x118f24 bytes_l118e1a_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18f24 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_4

def b_l118e1a_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x118ec2 (shldR64R64Effect 0x118ec2 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[134, 129]
    (.letOp (n := 137) (.exec 0x118ec2 (fun s => s.RIP = 0x118ec2) (shldR64R64Effect 0x118ec2 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[134, 129]
    (.letOp (n := 138) (.out 0x118ec7 (movR64Imm64Effect 0x118ec7 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 139) (.exec 0x118ec7 (fun s => s.RIP = 0x118ec7) (movR64Imm64Effect 0x118ec7 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 140) (.out 0x118ed1 (andR64R64Effect 0x118ed1 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[129, 138]
    (.letOp (n := 141) (.exec 0x118ed1 (fun s => s.RIP = 0x118ed1) (andR64R64Effect 0x118ed1 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[129, 138]
    (.letOp (n := 142) (.out 0x118ed4 (movR64Imm64Effect 0x118ed4 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 143) (.exec 0x118ed4 (fun s => s.RIP = 0x118ed4) (movR64Imm64Effect 0x118ed4 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 144) (.out 0x118ede (mulR64Effect 0x118ede 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[142, 140]
    (.letOp (n := 145) (.out 0x118ede (mulR64Effect 0x118ede 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[142, 140]
    (.letOp (n := 146) (.exec 0x118ede (fun s => s.RIP = 0x118ede) (mulR64Effect 0x118ede 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[142, 140]
    (.letOp (n := 147) (.out 0x118ee1 (movR64R64Effect 0x118ee1 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[145]
    (.letOp (n := 148) (.exec 0x118ee1 (fun s => s.RIP = 0x118ee1) (movR64R64Effect 0x118ee1 9 2) (Reg.operands [.gpr 2] [])) #v[145]
    (.letOp (n := 149) (.out 0x118ee4 (addR64R64Effect 0x118ee4 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[144, 117]
    (.letOp (n := 150) (.out 0x118ee4 (addR64R64Effect 0x118ee4 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[144, 117]
    (.letOp (n := 151) (.exec 0x118ee4 (fun s => s.RIP = 0x118ee4) (addR64R64Effect 0x118ee4 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[144, 117]
    (.letOp (n := 152) (.exec 0x118ee7 (StorePre 0x118ee7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x118ee7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118ee7 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[149, 4]
    (.letOp (n := 153) (.out 0x118eef (atFlags StatusFlags.CF (adcR64R64Effect 0x118eef 9 7)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[147, 120, 150]
    (.letOp (n := 154) (.exec 0x118eef (fun s => s.RIP = 0x118eef) (atFlags StatusFlags.CF (adcR64R64Effect 0x118eef 9 7)) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[147, 120, 150]
    (.letOp (n := 155) (.out 0x118ef2 (shldR64R64Effect 0x118ef2 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[153, 149]
    (.letOp (n := 156) (.exec 0x118ef2 (fun s => s.RIP = 0x118ef2) (shldR64R64Effect 0x118ef2 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[153, 149]
    (.letOp (n := 157) (.out 0x118ef7 (movR64R64Effect 0x118ef7 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[122]
    (.letOp (n := 158) (.exec 0x118ef7 (fun s => s.RIP = 0x118ef7) (movR64R64Effect 0x118ef7 0 6) (Reg.operands [.gpr 6] [])) #v[122]
    (.letOp (n := 159) (.out 0x118efa (mulR64Effect 0x118efa 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[59, 157]
    (.letOp (n := 160) (.out 0x118efa (mulR64Effect 0x118efa 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[59, 157]
    (.letOp (n := 161) (.exec 0x118efa (fun s => s.RIP = 0x118efa) (mulR64Effect 0x118efa 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[59, 157]
    (.letOp (n := 162) (.exec 0x118efd (StorePre 0x118efd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x118efd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118efd 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[160, 4]
    (.letOp (n := 163) (.exec 0x118f05 (StorePre 0x118f05 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x118f05 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118f05 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[159, 4]
    (.letOp (n := 164) (.out 0x118f0d (movR64M64Effect 0x118f0d 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 165) (.exec 0x118f0d (LoadPre 0x118f0d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x118f0d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118f0d 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 166) (.out 0x118f15 (mulR64Effect 0x118f15 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[61, 164]
    (.letOp (n := 167) (.out 0x118f15 (mulR64Effect 0x118f15 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[61, 164]
    (.letOp (n := 168) (.exec 0x118f15 (fun s => s.RIP = 0x118f15) (mulR64Effect 0x118f15 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[61, 164]
    (.letOp (n := 169) (.out 0x118f18 (movR64R64Effect 0x118f18 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[167]
    (.letOp (n := 170) (.exec 0x118f18 (fun s => s.RIP = 0x118f18) (movR64R64Effect 0x118f18 7 2) (Reg.operands [.gpr 2] [])) #v[167]
    (.letOp (n := 171) (.out 0x118f1b (movR64R64Effect 0x118f1b 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[166]
    (.letOp (n := 172) (.exec 0x118f1b (fun s => s.RIP = 0x118f1b) (movR64R64Effect 0x118f1b 6 0) (Reg.operands [.gpr 0] [])) #v[166]
    (.letOp (n := 173) (.out 0x118f1e (movR64R64Effect 0x118f1e 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 174) (.exec 0x118f1e (fun s => s.RIP = 0x118f1e) (movR64R64Effect 0x118f1e 0 12) (Reg.operands [.gpr 12] [])) #v[73]
    (.letOp (n := 175) (.out 0x118f21 (mulR64Effect 0x118f21 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[57, 173]
    (.letOp (n := 176) (.out 0x118f21 (mulR64Effect 0x118f21 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[57, 173]
    (.letOp (n := 177) (.exec 0x118f21 (fun s => s.RIP = 0x118f21) (mulR64Effect 0x118f21 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[57, 173]
    (b_l118e1a_3))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_2 : List UInt8 :=
  [0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48,
    0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49,
    0x89, 0xD1, 0x4C, 0x01, 0xD8, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x49, 0x11, 0xF9,
    0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0x94, 0x24, 0x98,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xA8,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0xD7, 0x48, 0x89, 0xC6, 0x4C, 0x89, 0xE0, 0x49,
    0xF7, 0xE7] ++ bytes_l118e1a_3

theorem code_l118e1a_2 : ∀ x ∈ codeRange 0x118ec2 bytes_l118e1a_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18ec2 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_3

def b_l118e1a_1 : Block Op Label signature Reg.count 94 :=
  .letOp (n := 94) (.out 0x118e76 (mulR64Effect 0x118e76 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[57, 92]
    (.letOp (n := 95) (.out 0x118e76 (mulR64Effect 0x118e76 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[57, 92]
    (.letOp (n := 96) (.exec 0x118e76 (fun s => s.RIP = 0x118e76) (mulR64Effect 0x118e76 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[57, 92]
    (.letOp (n := 97) (.exec 0x118e79 (StorePre 0x118e79 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x118e79 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118e79 15 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 98) (.out 0x118e7e (movR64R64Effect 0x118e7e 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 99) (.exec 0x118e7e (fun s => s.RIP = 0x118e7e) (movR64R64Effect 0x118e7e 1 2) (Reg.operands [.gpr 2] [])) #v[95]
    (.letOp (n := 100) (.out 0x118e81 (movR64R64Effect 0x118e81 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[94]
    (.letOp (n := 101) (.exec 0x118e81 (fun s => s.RIP = 0x118e81) (movR64R64Effect 0x118e81 6 0) (Reg.operands [.gpr 0] [])) #v[94]
    (.letOp (n := 102) (.out 0x118e84 (addR64R64Effect 0x118e84 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[100, 85]
    (.letOp (n := 103) (.out 0x118e84 (addR64R64Effect 0x118e84 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[100, 85]
    (.letOp (n := 104) (.exec 0x118e84 (fun s => s.RIP = 0x118e84) (addR64R64Effect 0x118e84 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[100, 85]
    (.letOp (n := 105) (.out 0x118e87 (atFlags StatusFlags.CF (adcR64R64Effect 0x118e87 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[98, 88, 103]
    (.letOp (n := 106) (.exec 0x118e87 (fun s => s.RIP = 0x118e87) (atFlags StatusFlags.CF (adcR64R64Effect 0x118e87 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[98, 88, 103]
    (.letOp (n := 107) (.out 0x118e8a (movR64M64Effect 0x118e8a 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 108) (.exec 0x118e8a (LoadPre 0x118e8a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x118e8a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118e8a 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 109) (.out 0x118e92 (mulR64Effect 0x118e92 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[55, 107]
    (.letOp (n := 110) (.out 0x118e92 (mulR64Effect 0x118e92 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[55, 107]
    (.letOp (n := 111) (.exec 0x118e92 (fun s => s.RIP = 0x118e92) (mulR64Effect 0x118e92 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[55, 107]
    (.letOp (n := 112) (.exec 0x118e95 (StorePre 0x118e95 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x118e95 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118e95 10 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 113) (.out 0x118e9a (movR64R64Effect 0x118e9a 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[110]
    (.letOp (n := 114) (.exec 0x118e9a (fun s => s.RIP = 0x118e9a) (movR64R64Effect 0x118e9a 7 2) (Reg.operands [.gpr 2] [])) #v[110]
    (.letOp (n := 115) (.out 0x118e9d (movR64R64Effect 0x118e9d 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[109]
    (.letOp (n := 116) (.exec 0x118e9d (fun s => s.RIP = 0x118e9d) (movR64R64Effect 0x118e9d 11 0) (Reg.operands [.gpr 0] [])) #v[109]
    (.letOp (n := 117) (.out 0x118ea0 (addR64R64Effect 0x118ea0 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[115, 102]
    (.letOp (n := 118) (.out 0x118ea0 (addR64R64Effect 0x118ea0 11 6) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 6] []) (.flag .CF)) #v[115, 102]
    (.letOp (n := 119) (.exec 0x118ea0 (fun s => s.RIP = 0x118ea0) (addR64R64Effect 0x118ea0 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[115, 102]
    (.letOp (n := 120) (.out 0x118ea3 (atFlags StatusFlags.CF (adcR64R64Effect 0x118ea3 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[113, 105, 118]
    (.letOp (n := 121) (.exec 0x118ea3 (fun s => s.RIP = 0x118ea3) (atFlags StatusFlags.CF (adcR64R64Effect 0x118ea3 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[113, 105, 118]
    (.letOp (n := 122) (.out 0x118ea6 (movR64M64Effect 0x118ea6 6 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 123) (.exec 0x118ea6 (LoadPre 0x118ea6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x118ea6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118ea6 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 124) (.out 0x118eae (movR64R64Effect 0x118eae 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[122]
    (.letOp (n := 125) (.exec 0x118eae (fun s => s.RIP = 0x118eae) (movR64R64Effect 0x118eae 0 6) (Reg.operands [.gpr 6] [])) #v[122]
    (.letOp (n := 126) (.out 0x118eb1 (movR64R64Effect 0x118eb1 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 127) (.exec 0x118eb1 (fun s => s.RIP = 0x118eb1) (movR64R64Effect 0x118eb1 1 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 128) (.exec 0x118eb4 (StorePre 0x118eb4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x118eb4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118eb4 3 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 129) (.out 0x118eb9 (mulR64Effect 0x118eb9 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[53, 124]
    (.letOp (n := 130) (.out 0x118eb9 (mulR64Effect 0x118eb9 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[53, 124]
    (.letOp (n := 131) (.exec 0x118eb9 (fun s => s.RIP = 0x118eb9) (mulR64Effect 0x118eb9 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[53, 124]
    (.letOp (n := 132) (.out 0x118ebc (movR64R64Effect 0x118ebc 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[130]
    (.letOp (n := 133) (.exec 0x118ebc (fun s => s.RIP = 0x118ebc) (movR64R64Effect 0x118ebc 8 2) (Reg.operands [.gpr 2] [])) #v[130]
    (.letOp (n := 134) (.out 0x118ebf (movR64R64Effect 0x118ebf 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[130]
    (.letOp (n := 135) (.exec 0x118ebf (fun s => s.RIP = 0x118ebf) (movR64R64Effect 0x118ebf 3 2) (Reg.operands [.gpr 2] [])) #v[130]
    (b_l118e1a_2))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_1 : List UInt8 :=
  [0x49, 0xF7, 0xE7, 0x4C, 0x89, 0x7C, 0x24, 0x58, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x01,
    0xC6, 0x48, 0x11, 0xF9, 0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x4C,
    0x89, 0x54, 0x24, 0x78, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC3, 0x49, 0x01, 0xF3, 0x48, 0x11, 0xCF,
    0x48, 0x8B, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF0, 0x48, 0x89, 0xD9, 0x48, 0x89,
    0x5C, 0x24, 0x50, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD0, 0x48, 0x89, 0xD3] ++ bytes_l118e1a_2

theorem code_l118e1a_1 : ∀ x ∈ codeRange 0x118e76 bytes_l118e1a_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18e76 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_2

def b_l118e1a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x118e1a (movR64M64Effect 0x118e1a 3 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x118e1a (LoadPre 0x118e1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x118e1a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118e1a 3 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x118e1f (movR64M64Effect 0x118e1f 10 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 56) (.exec 0x118e1f (LoadPre 0x118e1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x118e1f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118e1f 10 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x118e24 (movR64M64Effect 0x118e24 15 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 58) (.exec 0x118e24 (LoadPre 0x118e24 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x118e24 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118e24 15 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x118e29 (movR64M64Effect 0x118e29 13 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 60) (.exec 0x118e29 (LoadPre 0x118e29 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x118e29 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118e29 13 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x118e2e (movR64M64Effect 0x118e2e 14 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 62) (.exec 0x118e2e (LoadPre 0x118e2e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x118e2e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118e2e 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x118e33 (movR64M64Effect 0x118e33 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x118e33 (LoadPre 0x118e33 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x118e33 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118e33 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x118e3b (mulR64Effect 0x118e3b 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[59, 63]
    (.letOp (n := 66) (.out 0x118e3b (mulR64Effect 0x118e3b 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[59, 63]
    (.letOp (n := 67) (.exec 0x118e3b (fun s => s.RIP = 0x118e3b) (mulR64Effect 0x118e3b 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[59, 63]
    (.letOp (n := 68) (.exec 0x118e3e (StorePre 0x118e3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x118e3e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118e3e 13 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 69) (.out 0x118e43 (movR64R64Effect 0x118e43 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[66]
    (.letOp (n := 70) (.exec 0x118e43 (fun s => s.RIP = 0x118e43) (movR64R64Effect 0x118e43 1 2) (Reg.operands [.gpr 2] [])) #v[66]
    (.letOp (n := 71) (.out 0x118e46 (movR64R64Effect 0x118e46 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 72) (.exec 0x118e46 (fun s => s.RIP = 0x118e46) (movR64R64Effect 0x118e46 6 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 73) (.out 0x118e49 (movR64M64Effect 0x118e49 12 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 74) (.exec 0x118e49 (LoadPre 0x118e49 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x118e49 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118e49 12 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x118e51 (movR64R64Effect 0x118e51 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 76) (.exec 0x118e51 (fun s => s.RIP = 0x118e51) (movR64R64Effect 0x118e51 0 12) (Reg.operands [.gpr 12] [])) #v[73]
    (.letOp (n := 77) (.out 0x118e54 (mulR64Effect 0x118e54 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[61, 75]
    (.letOp (n := 78) (.out 0x118e54 (mulR64Effect 0x118e54 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[61, 75]
    (.letOp (n := 79) (.exec 0x118e54 (fun s => s.RIP = 0x118e54) (mulR64Effect 0x118e54 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[61, 75]
    (.letOp (n := 80) (.exec 0x118e57 (StorePre 0x118e57 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x118e57 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118e57 14 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 81) (.out 0x118e5f (movR64R64Effect 0x118e5f 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[78]
    (.letOp (n := 82) (.exec 0x118e5f (fun s => s.RIP = 0x118e5f) (movR64R64Effect 0x118e5f 7 2) (Reg.operands [.gpr 2] [])) #v[78]
    (.letOp (n := 83) (.out 0x118e62 (movR64R64Effect 0x118e62 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[77]
    (.letOp (n := 84) (.exec 0x118e62 (fun s => s.RIP = 0x118e62) (movR64R64Effect 0x118e62 8 0) (Reg.operands [.gpr 0] [])) #v[77]
    (.letOp (n := 85) (.out 0x118e65 (addR64R64Effect 0x118e65 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[83, 71]
    (.letOp (n := 86) (.out 0x118e65 (addR64R64Effect 0x118e65 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[83, 71]
    (.letOp (n := 87) (.exec 0x118e65 (fun s => s.RIP = 0x118e65) (addR64R64Effect 0x118e65 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[83, 71]
    (.letOp (n := 88) (.out 0x118e68 (atFlags StatusFlags.CF (adcR64R64Effect 0x118e68 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[81, 69, 86]
    (.letOp (n := 89) (.exec 0x118e68 (fun s => s.RIP = 0x118e68) (atFlags StatusFlags.CF (adcR64R64Effect 0x118e68 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[81, 69, 86]
    (.letOp (n := 90) (.out 0x118e6b (movR64M64Effect 0x118e6b 5 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 91) (.exec 0x118e6b (LoadPre 0x118e6b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x118e6b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118e6b 5 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.out 0x118e73 (movR64R64Effect 0x118e73 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[90]
    (.letOp (n := 93) (.exec 0x118e73 (fun s => s.RIP = 0x118e73) (movR64R64Effect 0x118e73 0 5) (Reg.operands [.gpr 5] [])) #v[90]
    (b_l118e1a_1)))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a : List UInt8 :=
  [0x48, 0x8B, 0x5C, 0x24, 0x48, 0x4C, 0x8B, 0x54, 0x24, 0x40, 0x4C, 0x8B, 0x7C, 0x24, 0x38, 0x4C,
    0x8B, 0x6C, 0x24, 0x28, 0x4C, 0x8B, 0x74, 0x24, 0x30, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00,
    0x00, 0x49, 0xF7, 0xE5, 0x4C, 0x89, 0x6C, 0x24, 0x60, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C,
    0x8B, 0xA4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE6, 0x4C, 0x89, 0xB4,
    0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0, 0x49, 0x01, 0xF0, 0x48, 0x11,
    0xCF, 0x48, 0x8B, 0xAC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE8] ++ bytes_l118e1a_1

theorem code_l118e1a : ∀ x ∈ codeRange 0x118e1a bytes_l118e1a, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18e1a 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_1

@[cfg_block] def b_l119258 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119258 (movR64M64Effect 0x119258 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119258 (LoadPre 0x119258 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119258 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119258 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11925d (StorePre 0x11925d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11925d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11925d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119262 (movR64M64Effect 0x119262 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119262 (LoadPre 0x119262 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119262 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119262 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119267 (StorePre 0x119267 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119267 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119267 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11926c (movR64M64Effect 0x11926c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11926c (LoadPre 0x11926c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11926c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11926c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119271 (StorePre 0x119271 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119271 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119271 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119276 (movR64M64Effect 0x119276 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119276 (LoadPre 0x119276 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119276 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119276 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11927b (movR64M64Effect 0x11927b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11927b (LoadPre 0x11927b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11927b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11927b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119280 (StorePre 0x119280 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119280 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119280 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119285 (StorePre 0x119285 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119285 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119285 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119289 (movR64R64Effect 0x119289 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119289 (fun s => s.RIP = 0x119289) (movR64R64Effect 0x119289 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11928c (movR64R64Effect 0x11928c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11928c (fun s => s.RIP = 0x11928c) (movR64R64Effect 0x11928c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11928f (callEffect (fun _ => 0x1145f0) 0x119294) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11928f (PushPre 0x11928f 5) (callEffect (fun _ => 0x1145f0) 0x119294) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119294⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119294, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119258 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x5C, 0xB3, 0xFF, 0xFF]

theorem code_l119258 : ∀ x ∈ codeRange 0x119258 bytes_l119258, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19258 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119294 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119294 (movR64M64Effect 0x119294 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119294 (LoadPre 0x119294 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119294 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119294 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119299 (StorePre 0x119299 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119299 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119299 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11929e (movR64M64Effect 0x11929e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11929e (LoadPre 0x11929e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11929e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11929e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1192a3 (StorePre 0x1192a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1192a3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192a3 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1192a8 (movR64M64Effect 0x1192a8 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1192a8 (LoadPre 0x1192a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1192a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192a8 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1192ad (StorePre 0x1192ad 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1192ad + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192ad 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1192b2 (movR64M64Effect 0x1192b2 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1192b2 (LoadPre 0x1192b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1192b2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192b2 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1192b7 (movR64M64Effect 0x1192b7 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1192b7 (LoadPre 0x1192b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1192b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192b7 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1192bc (StorePre 0x1192bc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1192bc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192bc 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1192c1 (StorePre 0x1192c1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1192c1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1192c1 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1192c5 (movR64R64Effect 0x1192c5 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1192c5 (fun s => s.RIP = 0x1192c5) (movR64R64Effect 0x1192c5 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1192c8 (movR64R64Effect 0x1192c8 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1192c8 (fun s => s.RIP = 0x1192c8) (movR64R64Effect 0x1192c8 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1192cb (callEffect (fun _ => 0x1145f0) 0x1192d0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1192cb (PushPre 0x1192cb 5) (callEffect (fun _ => 0x1145f0) 0x1192d0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1192d0⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1192d0, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119294 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x20, 0xB3, 0xFF, 0xFF]

theorem code_l119294 : ∀ x ∈ codeRange 0x119294 bytes_l119294, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19294 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1192d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1192d0 (movR64M64Effect 0x1192d0 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1192d0 (LoadPre 0x1192d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1192d0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192d0 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1192d5 (StorePre 0x1192d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1192d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192d5 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1192da (movR64M64Effect 0x1192da 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1192da (LoadPre 0x1192da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1192da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192da 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1192df (StorePre 0x1192df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1192df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192df 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1192e4 (movR64M64Effect 0x1192e4 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1192e4 (LoadPre 0x1192e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1192e4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192e4 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1192e9 (StorePre 0x1192e9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1192e9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192e9 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1192ee (movR64M64Effect 0x1192ee 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1192ee (LoadPre 0x1192ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1192ee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192ee 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1192f3 (movR64M64Effect 0x1192f3 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1192f3 (LoadPre 0x1192f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1192f3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192f3 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1192f8 (StorePre 0x1192f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1192f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192f8 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1192fd (StorePre 0x1192fd 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1192fd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1192fd 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119301 (movR64R64Effect 0x119301 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119301 (fun s => s.RIP = 0x119301) (movR64R64Effect 0x119301 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119304 (movR64R64Effect 0x119304 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119304 (fun s => s.RIP = 0x119304) (movR64R64Effect 0x119304 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119307 (callEffect (fun _ => 0x1145f0) 0x11930c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119307 (PushPre 0x119307 5) (callEffect (fun _ => 0x1145f0) 0x11930c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11930c⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11930c, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1192d0 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xE4, 0xB2, 0xFF, 0xFF]

theorem code_l1192d0 : ∀ x ∈ codeRange 0x1192d0 bytes_l1192d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x192d0 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11930c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11930c (movR64M64Effect 0x11930c 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11930c (LoadPre 0x11930c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11930c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11930c 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119311 (StorePre 0x119311 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119311 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119311 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119316 (movR64M64Effect 0x119316 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119316 (LoadPre 0x119316 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119316 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119316 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11931b (StorePre 0x11931b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11931b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11931b 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119320 (movR64M64Effect 0x119320 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119320 (LoadPre 0x119320 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119320 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119320 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119325 (StorePre 0x119325 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119325 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119325 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11932a (movR64M64Effect 0x11932a 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11932a (LoadPre 0x11932a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11932a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11932a 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11932f (movR64M64Effect 0x11932f 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11932f (LoadPre 0x11932f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11932f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11932f 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119334 (StorePre 0x119334 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119334 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119334 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119339 (StorePre 0x119339 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119339 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119339 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11933d (movR64R64Effect 0x11933d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11933d (fun s => s.RIP = 0x11933d) (movR64R64Effect 0x11933d 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119340 (movR64R64Effect 0x119340 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119340 (fun s => s.RIP = 0x119340) (movR64R64Effect 0x119340 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119343 (callEffect (fun _ => 0x1145f0) 0x119348) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119343 (PushPre 0x119343 5) (callEffect (fun _ => 0x1145f0) 0x119348) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119348⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119348, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11930c : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xA8, 0xB2, 0xFF, 0xFF]

theorem code_l11930c : ∀ x ∈ codeRange 0x11930c bytes_l11930c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1930c 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119348 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119348 (movR64M64Effect 0x119348 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119348 (LoadPre 0x119348 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119348 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119348 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11934d (StorePre 0x11934d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11934d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11934d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119352 (movR64M64Effect 0x119352 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119352 (LoadPre 0x119352 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119352 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119352 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119357 (StorePre 0x119357 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119357 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119357 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11935c (movR64M64Effect 0x11935c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11935c (LoadPre 0x11935c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11935c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11935c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119361 (StorePre 0x119361 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119361 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119361 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119366 (movR64M64Effect 0x119366 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119366 (LoadPre 0x119366 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119366 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119366 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11936b (movR64M64Effect 0x11936b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11936b (LoadPre 0x11936b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11936b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11936b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119370 (StorePre 0x119370 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119370 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119370 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119375 (StorePre 0x119375 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119375 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119375 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119379 (movR64R64Effect 0x119379 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119379 (fun s => s.RIP = 0x119379) (movR64R64Effect 0x119379 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11937c (movR64R64Effect 0x11937c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11937c (fun s => s.RIP = 0x11937c) (movR64R64Effect 0x11937c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11937f (callEffect (fun _ => 0x1145f0) 0x119384) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11937f (PushPre 0x11937f 5) (callEffect (fun _ => 0x1145f0) 0x119384) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119384⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119384, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119348 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x6C, 0xB2, 0xFF, 0xFF]

theorem code_l119348 : ∀ x ∈ codeRange 0x119348 bytes_l119348, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19348 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119384 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119384 (movR64M64Effect 0x119384 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119384 (LoadPre 0x119384 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119384 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119384 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119389 (StorePre 0x119389 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119389 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119389 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11938e (movR64M64Effect 0x11938e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11938e (LoadPre 0x11938e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11938e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11938e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119393 (StorePre 0x119393 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119393 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119393 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119398 (movR64M64Effect 0x119398 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119398 (LoadPre 0x119398 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119398 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119398 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11939d (StorePre 0x11939d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11939d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11939d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1193a2 (movR64M64Effect 0x1193a2 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1193a2 (LoadPre 0x1193a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1193a2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193a2 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1193a7 (movR64M64Effect 0x1193a7 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1193a7 (LoadPre 0x1193a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1193a7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193a7 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1193ac (StorePre 0x1193ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1193ac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1193ac 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1193b1 (StorePre 0x1193b1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1193b1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1193b1 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1193b5 (movR64R64Effect 0x1193b5 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1193b5 (fun s => s.RIP = 0x1193b5) (movR64R64Effect 0x1193b5 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1193b8 (movR64R64Effect 0x1193b8 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1193b8 (fun s => s.RIP = 0x1193b8) (movR64R64Effect 0x1193b8 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1193bb (callEffect (fun _ => 0x1145f0) 0x1193c0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1193bb (PushPre 0x1193bb 5) (callEffect (fun _ => 0x1145f0) 0x1193c0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1193c0⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1193c0, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119384 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x30, 0xB2, 0xFF, 0xFF]

theorem code_l119384 : ∀ x ∈ codeRange 0x119384 bytes_l119384, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19384 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1193c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1193c0 (movR64M64Effect 0x1193c0 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1193c0 (LoadPre 0x1193c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1193c0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193c0 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1193c5 (StorePre 0x1193c5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1193c5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1193c5 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1193ca (movR64M64Effect 0x1193ca 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1193ca (LoadPre 0x1193ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1193ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193ca 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1193cf (StorePre 0x1193cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1193cf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1193cf 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1193d4 (movR64M64Effect 0x1193d4 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1193d4 (LoadPre 0x1193d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1193d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193d4 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1193d9 (StorePre 0x1193d9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1193d9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1193d9 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1193de (movR64M64Effect 0x1193de 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1193de (LoadPre 0x1193de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1193de + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193de 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1193e3 (movR64M64Effect 0x1193e3 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1193e3 (LoadPre 0x1193e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1193e3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193e3 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1193e8 (StorePre 0x1193e8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1193e8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1193e8 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1193ed (StorePre 0x1193ed 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1193ed + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1193ed 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1193f1 (movR64R64Effect 0x1193f1 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1193f1 (fun s => s.RIP = 0x1193f1) (movR64R64Effect 0x1193f1 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1193f4 (movR64R64Effect 0x1193f4 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1193f4 (fun s => s.RIP = 0x1193f4) (movR64R64Effect 0x1193f4 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1193f7 (callEffect (fun _ => 0x1145f0) 0x1193fc) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1193f7 (PushPre 0x1193f7 5) (callEffect (fun _ => 0x1145f0) 0x1193fc) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1193fc⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1193fc, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1193c0 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xF4, 0xB1, 0xFF, 0xFF]

theorem code_l1193c0 : ∀ x ∈ codeRange 0x1193c0 bytes_l1193c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x193c0 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1193fc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1193fc (movR64M64Effect 0x1193fc 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1193fc (LoadPre 0x1193fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1193fc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193fc 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119401 (StorePre 0x119401 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119401 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119401 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119406 (movR64M64Effect 0x119406 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119406 (LoadPre 0x119406 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119406 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119406 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11940b (StorePre 0x11940b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11940b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11940b 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119410 (movR64M64Effect 0x119410 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119410 (LoadPre 0x119410 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119410 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119410 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119415 (StorePre 0x119415 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119415 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119415 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11941a (movR64M64Effect 0x11941a 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11941a (LoadPre 0x11941a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11941a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11941a 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11941f (movR64M64Effect 0x11941f 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11941f (LoadPre 0x11941f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11941f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11941f 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119424 (StorePre 0x119424 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119424 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119424 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119429 (StorePre 0x119429 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119429 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119429 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11942d (movR64R64Effect 0x11942d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11942d (fun s => s.RIP = 0x11942d) (movR64R64Effect 0x11942d 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119430 (movR64R64Effect 0x119430 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119430 (fun s => s.RIP = 0x119430) (movR64R64Effect 0x119430 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119433 (callEffect (fun _ => 0x1145f0) 0x119438) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119433 (PushPre 0x119433 5) (callEffect (fun _ => 0x1145f0) 0x119438) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119438⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119438, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1193fc : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xB8, 0xB1, 0xFF, 0xFF]

theorem code_l1193fc : ∀ x ∈ codeRange 0x1193fc bytes_l1193fc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x193fc 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119438 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119438 (movR64M64Effect 0x119438 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119438 (LoadPre 0x119438 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119438 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119438 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11943d (StorePre 0x11943d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11943d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11943d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119442 (movR64M64Effect 0x119442 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119442 (LoadPre 0x119442 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119442 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119442 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119447 (StorePre 0x119447 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119447 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119447 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11944c (movR64M64Effect 0x11944c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11944c (LoadPre 0x11944c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11944c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11944c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119451 (StorePre 0x119451 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119451 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119451 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119456 (movR64M64Effect 0x119456 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119456 (LoadPre 0x119456 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119456 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119456 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11945b (movR64M64Effect 0x11945b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11945b (LoadPre 0x11945b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11945b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11945b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119460 (StorePre 0x119460 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119460 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119460 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119465 (StorePre 0x119465 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119465 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119465 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119469 (movR64R64Effect 0x119469 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119469 (fun s => s.RIP = 0x119469) (movR64R64Effect 0x119469 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11946c (movR64R64Effect 0x11946c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11946c (fun s => s.RIP = 0x11946c) (movR64R64Effect 0x11946c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11946f (callEffect (fun _ => 0x1145f0) 0x119474) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11946f (PushPre 0x11946f 5) (callEffect (fun _ => 0x1145f0) 0x119474) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119474⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119474, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119438 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x7C, 0xB1, 0xFF, 0xFF]

theorem code_l119438 : ∀ x ∈ codeRange 0x119438 bytes_l119438, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19438 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119474 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119474 (movR64M64Effect 0x119474 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119474 (LoadPre 0x119474 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119474 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119474 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119479 (StorePre 0x119479 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119479 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119479 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11947e (movR64M64Effect 0x11947e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11947e (LoadPre 0x11947e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11947e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11947e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119483 (StorePre 0x119483 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119483 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119483 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119488 (movR64M64Effect 0x119488 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119488 (LoadPre 0x119488 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119488 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119488 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11948d (StorePre 0x11948d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11948d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11948d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119492 (movR64M64Effect 0x119492 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119492 (LoadPre 0x119492 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119492 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119492 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x119497 (movR64M64Effect 0x119497 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x119497 (LoadPre 0x119497 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119497 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119497 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11949c (StorePre 0x11949c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11949c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11949c 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1194a1 (StorePre 0x1194a1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1194a1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1194a1 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1194a5 (movR64R64Effect 0x1194a5 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1194a5 (fun s => s.RIP = 0x1194a5) (movR64R64Effect 0x1194a5 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1194a8 (movR64R64Effect 0x1194a8 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1194a8 (fun s => s.RIP = 0x1194a8) (movR64R64Effect 0x1194a8 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1194ab (callEffect (fun _ => 0x1145f0) 0x1194b0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1194ab (PushPre 0x1194ab 5) (callEffect (fun _ => 0x1145f0) 0x1194b0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1194b0⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1194b0, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119474 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x40, 0xB1, 0xFF, 0xFF]

theorem code_l119474 : ∀ x ∈ codeRange 0x119474 bytes_l119474, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19474 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1194b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1194b0 (movR64M64Effect 0x1194b0 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1194b0 (LoadPre 0x1194b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1194b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194b0 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1194b5 (StorePre 0x1194b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1194b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1194b5 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1194ba (movR64M64Effect 0x1194ba 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1194ba (LoadPre 0x1194ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1194ba + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194ba 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1194bf (StorePre 0x1194bf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1194bf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1194bf 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1194c4 (movR64M64Effect 0x1194c4 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1194c4 (LoadPre 0x1194c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1194c4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194c4 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1194c9 (StorePre 0x1194c9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1194c9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1194c9 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1194ce (movR64M64Effect 0x1194ce 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1194ce (LoadPre 0x1194ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1194ce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194ce 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1194d3 (movR64M64Effect 0x1194d3 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1194d3 (LoadPre 0x1194d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1194d3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194d3 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1194d8 (StorePre 0x1194d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1194d8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1194d8 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1194dd (StorePre 0x1194dd 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1194dd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1194dd 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1194e1 (movR64R64Effect 0x1194e1 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1194e1 (fun s => s.RIP = 0x1194e1) (movR64R64Effect 0x1194e1 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1194e4 (movR64R64Effect 0x1194e4 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1194e4 (fun s => s.RIP = 0x1194e4) (movR64R64Effect 0x1194e4 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1194e7 (callEffect (fun _ => 0x1145f0) 0x1194ec) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1194e7 (PushPre 0x1194e7 5) (callEffect (fun _ => 0x1145f0) 0x1194ec) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1194ec⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1194ec, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1194b0 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x04, 0xB1, 0xFF, 0xFF]

theorem code_l1194b0 : ∀ x ∈ codeRange 0x1194b0 bytes_l1194b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x194b0 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1194ec : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1194ec (movR64M64Effect 0x1194ec 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1194ec (LoadPre 0x1194ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1194ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194ec 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1194f1 (StorePre 0x1194f1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1194f1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1194f1 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1194f6 (movR64M64Effect 0x1194f6 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1194f6 (LoadPre 0x1194f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1194f6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194f6 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1194fb (StorePre 0x1194fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1194fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1194fb 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119500 (movR64M64Effect 0x119500 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119500 (LoadPre 0x119500 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119500 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119500 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119505 (StorePre 0x119505 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119505 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119505 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11950a (movR64M64Effect 0x11950a 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11950a (LoadPre 0x11950a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11950a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11950a 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11950f (movR64M64Effect 0x11950f 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11950f (LoadPre 0x11950f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11950f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11950f 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119514 (StorePre 0x119514 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119514 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119514 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119519 (StorePre 0x119519 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119519 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119519 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11951d (movR64R64Effect 0x11951d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11951d (fun s => s.RIP = 0x11951d) (movR64R64Effect 0x11951d 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119520 (movR64R64Effect 0x119520 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119520 (fun s => s.RIP = 0x119520) (movR64R64Effect 0x119520 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119523 (callEffect (fun _ => 0x1145f0) 0x119528) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119523 (PushPre 0x119523 5) (callEffect (fun _ => 0x1145f0) 0x119528) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119528⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119528, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1194ec : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xC8, 0xB0, 0xFF, 0xFF]

theorem code_l1194ec : ∀ x ∈ codeRange 0x1194ec bytes_l1194ec, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x194ec 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119528 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119528 (movR64M64Effect 0x119528 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119528 (LoadPre 0x119528 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119528 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119528 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11952d (StorePre 0x11952d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11952d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11952d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119532 (movR64M64Effect 0x119532 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119532 (LoadPre 0x119532 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119532 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119532 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119537 (StorePre 0x119537 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119537 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119537 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11953c (movR64M64Effect 0x11953c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11953c (LoadPre 0x11953c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11953c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11953c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119541 (StorePre 0x119541 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119541 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119541 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119546 (movR64M64Effect 0x119546 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119546 (LoadPre 0x119546 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119546 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119546 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11954b (movR64M64Effect 0x11954b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11954b (LoadPre 0x11954b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11954b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11954b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119550 (StorePre 0x119550 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119550 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119550 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119555 (StorePre 0x119555 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119555 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119555 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119559 (movR64R64Effect 0x119559 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119559 (fun s => s.RIP = 0x119559) (movR64R64Effect 0x119559 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11955c (movR64R64Effect 0x11955c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11955c (fun s => s.RIP = 0x11955c) (movR64R64Effect 0x11955c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11955f (callEffect (fun _ => 0x1145f0) 0x119564) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11955f (PushPre 0x11955f 5) (callEffect (fun _ => 0x1145f0) 0x119564) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119564⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119564, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119528 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x8C, 0xB0, 0xFF, 0xFF]

theorem code_l119528 : ∀ x ∈ codeRange 0x119528 bytes_l119528, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19528 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119564 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119564 (movR64M64Effect 0x119564 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119564 (LoadPre 0x119564 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119564 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119564 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119569 (StorePre 0x119569 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119569 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119569 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11956e (movR64M64Effect 0x11956e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11956e (LoadPre 0x11956e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11956e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11956e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119573 (StorePre 0x119573 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119573 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119573 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119578 (movR64M64Effect 0x119578 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119578 (LoadPre 0x119578 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119578 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119578 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11957d (StorePre 0x11957d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11957d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11957d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119582 (movR64M64Effect 0x119582 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119582 (LoadPre 0x119582 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119582 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119582 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x119587 (movR64M64Effect 0x119587 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x119587 (LoadPre 0x119587 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119587 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119587 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11958c (StorePre 0x11958c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11958c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11958c 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119591 (StorePre 0x119591 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119591 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119591 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119595 (movR64R64Effect 0x119595 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119595 (fun s => s.RIP = 0x119595) (movR64R64Effect 0x119595 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119598 (movR64R64Effect 0x119598 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119598 (fun s => s.RIP = 0x119598) (movR64R64Effect 0x119598 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11959b (callEffect (fun _ => 0x1145f0) 0x1195a0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11959b (PushPre 0x11959b 5) (callEffect (fun _ => 0x1145f0) 0x1195a0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1195a0⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1195a0, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119564 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x50, 0xB0, 0xFF, 0xFF]

theorem code_l119564 : ∀ x ∈ codeRange 0x119564 bytes_l119564, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19564 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1195a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1195a0 (movR64M64Effect 0x1195a0 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1195a0 (LoadPre 0x1195a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1195a0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195a0 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1195a5 (StorePre 0x1195a5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1195a5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195a5 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1195aa (movR64M64Effect 0x1195aa 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1195aa (LoadPre 0x1195aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1195aa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195aa 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1195af (StorePre 0x1195af 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1195af + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195af 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1195b4 (movR64M64Effect 0x1195b4 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1195b4 (LoadPre 0x1195b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1195b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195b4 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1195b9 (StorePre 0x1195b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1195b9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195b9 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1195be (movR64M64Effect 0x1195be 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1195be (LoadPre 0x1195be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1195be + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195be 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1195c3 (movR64M64Effect 0x1195c3 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1195c3 (LoadPre 0x1195c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1195c3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195c3 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1195c8 (StorePre 0x1195c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1195c8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195c8 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1195cd (StorePre 0x1195cd 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1195cd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1195cd 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1195d1 (movR64R64Effect 0x1195d1 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1195d1 (fun s => s.RIP = 0x1195d1) (movR64R64Effect 0x1195d1 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1195d4 (movR64R64Effect 0x1195d4 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1195d4 (fun s => s.RIP = 0x1195d4) (movR64R64Effect 0x1195d4 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1195d7 (callEffect (fun _ => 0x1145f0) 0x1195dc) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1195d7 (PushPre 0x1195d7 5) (callEffect (fun _ => 0x1145f0) 0x1195dc) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1195dc⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1195dc, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1195a0 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x14, 0xB0, 0xFF, 0xFF]

theorem code_l1195a0 : ∀ x ∈ codeRange 0x1195a0 bytes_l1195a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x195a0 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1195dc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1195dc (movR64M64Effect 0x1195dc 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1195dc (LoadPre 0x1195dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1195dc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195dc 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1195e1 (StorePre 0x1195e1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1195e1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195e1 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1195e6 (movR64M64Effect 0x1195e6 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1195e6 (LoadPre 0x1195e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1195e6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195e6 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1195eb (StorePre 0x1195eb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1195eb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195eb 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1195f0 (movR64M64Effect 0x1195f0 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1195f0 (LoadPre 0x1195f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1195f0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195f0 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1195f5 (StorePre 0x1195f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1195f5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195f5 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1195fa (movR64M64Effect 0x1195fa 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1195fa (LoadPre 0x1195fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1195fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195fa 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1195ff (movR64M64Effect 0x1195ff 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1195ff (LoadPre 0x1195ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1195ff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195ff 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119604 (StorePre 0x119604 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119604 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119604 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119609 (StorePre 0x119609 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119609 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119609 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11960d (movR64R64Effect 0x11960d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11960d (fun s => s.RIP = 0x11960d) (movR64R64Effect 0x11960d 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119610 (movR64R64Effect 0x119610 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119610 (fun s => s.RIP = 0x119610) (movR64R64Effect 0x119610 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119613 (callEffect (fun _ => 0x1145f0) 0x119618) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119613 (PushPre 0x119613 5) (callEffect (fun _ => 0x1145f0) 0x119618) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119618⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119618, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1195dc : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xD8, 0xAF, 0xFF, 0xFF]

theorem code_l1195dc : ∀ x ∈ codeRange 0x1195dc bytes_l1195dc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x195dc 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119618 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119618 (movR64M64Effect 0x119618 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119618 (LoadPre 0x119618 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119618 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119618 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11961d (StorePre 0x11961d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11961d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11961d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119622 (movR64M64Effect 0x119622 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119622 (LoadPre 0x119622 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119622 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119622 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119627 (StorePre 0x119627 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119627 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119627 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11962c (movR64M64Effect 0x11962c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11962c (LoadPre 0x11962c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11962c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11962c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119631 (StorePre 0x119631 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119631 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119631 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119636 (movR64M64Effect 0x119636 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119636 (LoadPre 0x119636 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119636 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119636 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11963b (movR64M64Effect 0x11963b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11963b (LoadPre 0x11963b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11963b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11963b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119640 (StorePre 0x119640 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119640 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119640 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119645 (StorePre 0x119645 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119645 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119645 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119649 (movR64R64Effect 0x119649 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119649 (fun s => s.RIP = 0x119649) (movR64R64Effect 0x119649 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11964c (movR64R64Effect 0x11964c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11964c (fun s => s.RIP = 0x11964c) (movR64R64Effect 0x11964c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11964f (callEffect (fun _ => 0x1145f0) 0x119654) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11964f (PushPre 0x11964f 5) (callEffect (fun _ => 0x1145f0) 0x119654) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119654⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119654, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119618 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x9C, 0xAF, 0xFF, 0xFF]

theorem code_l119618 : ∀ x ∈ codeRange 0x119618 bytes_l119618, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19618 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119654 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119654 (movR64M64Effect 0x119654 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119654 (LoadPre 0x119654 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119654 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119654 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119659 (StorePre 0x119659 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119659 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119659 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11965e (movR64M64Effect 0x11965e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11965e (LoadPre 0x11965e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11965e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11965e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119663 (StorePre 0x119663 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119663 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119663 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119668 (movR64M64Effect 0x119668 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119668 (LoadPre 0x119668 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119668 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119668 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11966d (StorePre 0x11966d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11966d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11966d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119672 (movR64M64Effect 0x119672 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119672 (LoadPre 0x119672 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119672 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119672 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x119677 (movR64M64Effect 0x119677 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x119677 (LoadPre 0x119677 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119677 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119677 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11967c (StorePre 0x11967c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11967c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11967c 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119681 (StorePre 0x119681 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119681 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119681 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119685 (movR64R64Effect 0x119685 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119685 (fun s => s.RIP = 0x119685) (movR64R64Effect 0x119685 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119688 (movR64R64Effect 0x119688 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119688 (fun s => s.RIP = 0x119688) (movR64R64Effect 0x119688 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11968b (callEffect (fun _ => 0x1145f0) 0x119690) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11968b (PushPre 0x11968b 5) (callEffect (fun _ => 0x1145f0) 0x119690) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119690⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119690, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119654 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x60, 0xAF, 0xFF, 0xFF]

theorem code_l119654 : ∀ x ∈ codeRange 0x119654 bytes_l119654, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19654 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119690 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119690 (movR64M64Effect 0x119690 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119690 (LoadPre 0x119690 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119690 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119690 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119695 (StorePre 0x119695 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119695 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119695 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11969a (movR64M64Effect 0x11969a 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11969a (LoadPre 0x11969a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11969a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11969a 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11969f (StorePre 0x11969f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11969f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11969f 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1196a4 (movR64M64Effect 0x1196a4 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1196a4 (LoadPre 0x1196a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1196a4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196a4 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1196a9 (StorePre 0x1196a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1196a9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1196a9 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1196ae (movR64M64Effect 0x1196ae 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1196ae (LoadPre 0x1196ae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1196ae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196ae 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1196b3 (movR64M64Effect 0x1196b3 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1196b3 (LoadPre 0x1196b3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1196b3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196b3 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1196b8 (StorePre 0x1196b8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1196b8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1196b8 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1196bd (StorePre 0x1196bd 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1196bd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1196bd 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1196c1 (movR64R64Effect 0x1196c1 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1196c1 (fun s => s.RIP = 0x1196c1) (movR64R64Effect 0x1196c1 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1196c4 (movR64R64Effect 0x1196c4 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1196c4 (fun s => s.RIP = 0x1196c4) (movR64R64Effect 0x1196c4 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1196c7 (callEffect (fun _ => 0x1145f0) 0x1196cc) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1196c7 (PushPre 0x1196c7 5) (callEffect (fun _ => 0x1145f0) 0x1196cc) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1196cc⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1196cc, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119690 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x24, 0xAF, 0xFF, 0xFF]

theorem code_l119690 : ∀ x ∈ codeRange 0x119690 bytes_l119690, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19690 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1196cc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1196cc (movR64M64Effect 0x1196cc 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1196cc (LoadPre 0x1196cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1196cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196cc 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1196d1 (StorePre 0x1196d1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1196d1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1196d1 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1196d6 (movR64M64Effect 0x1196d6 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1196d6 (LoadPre 0x1196d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1196d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196d6 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1196db (StorePre 0x1196db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1196db + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1196db 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1196e0 (movR64M64Effect 0x1196e0 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1196e0 (LoadPre 0x1196e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1196e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196e0 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1196e5 (StorePre 0x1196e5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1196e5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1196e5 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1196ea (movR64M64Effect 0x1196ea 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1196ea (LoadPre 0x1196ea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1196ea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196ea 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1196ef (movR64M64Effect 0x1196ef 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1196ef (LoadPre 0x1196ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1196ef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196ef 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1196f4 (StorePre 0x1196f4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1196f4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1196f4 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1196f9 (StorePre 0x1196f9 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1196f9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1196f9 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1196fd (movR64R64Effect 0x1196fd 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1196fd (fun s => s.RIP = 0x1196fd) (movR64R64Effect 0x1196fd 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119700 (movR64R64Effect 0x119700 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119700 (fun s => s.RIP = 0x119700) (movR64R64Effect 0x119700 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119703 (callEffect (fun _ => 0x1145f0) 0x119708) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119703 (PushPre 0x119703 5) (callEffect (fun _ => 0x1145f0) 0x119708) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119708⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119708, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1196cc : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xE8, 0xAE, 0xFF, 0xFF]

theorem code_l1196cc : ∀ x ∈ codeRange 0x1196cc bytes_l1196cc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x196cc 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119708 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119708 (movR64M64Effect 0x119708 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119708 (LoadPre 0x119708 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119708 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119708 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11970d (StorePre 0x11970d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11970d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11970d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119712 (movR64M64Effect 0x119712 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119712 (LoadPre 0x119712 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119712 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119712 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119717 (StorePre 0x119717 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119717 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119717 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11971c (movR64M64Effect 0x11971c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11971c (LoadPre 0x11971c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11971c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11971c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119721 (StorePre 0x119721 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119721 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119721 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119726 (movR64M64Effect 0x119726 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119726 (LoadPre 0x119726 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119726 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119726 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11972b (movR64M64Effect 0x11972b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11972b (LoadPre 0x11972b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11972b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11972b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119730 (StorePre 0x119730 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119730 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119730 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119735 (StorePre 0x119735 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119735 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119735 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119739 (movR64R64Effect 0x119739 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119739 (fun s => s.RIP = 0x119739) (movR64R64Effect 0x119739 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11973c (movR64R64Effect 0x11973c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11973c (fun s => s.RIP = 0x11973c) (movR64R64Effect 0x11973c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11973f (callEffect (fun _ => 0x1145f0) 0x119744) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11973f (PushPre 0x11973f 5) (callEffect (fun _ => 0x1145f0) 0x119744) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119744⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119744, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119708 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xAC, 0xAE, 0xFF, 0xFF]

theorem code_l119708 : ∀ x ∈ codeRange 0x119708 bytes_l119708, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19708 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119744 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119744 (movR64M64Effect 0x119744 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119744 (LoadPre 0x119744 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119744 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119744 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119749 (StorePre 0x119749 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119749 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119749 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11974e (movR64M64Effect 0x11974e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11974e (LoadPre 0x11974e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11974e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11974e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119753 (StorePre 0x119753 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119753 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119753 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119758 (movR64M64Effect 0x119758 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119758 (LoadPre 0x119758 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119758 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119758 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11975d (StorePre 0x11975d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11975d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11975d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119762 (movR64M64Effect 0x119762 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119762 (LoadPre 0x119762 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119762 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119762 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x119767 (movR64M64Effect 0x119767 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x119767 (LoadPre 0x119767 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119767 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119767 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11976c (StorePre 0x11976c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11976c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11976c 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119771 (StorePre 0x119771 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119771 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119771 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119775 (movR64R64Effect 0x119775 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119775 (fun s => s.RIP = 0x119775) (movR64R64Effect 0x119775 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119778 (movR64R64Effect 0x119778 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119778 (fun s => s.RIP = 0x119778) (movR64R64Effect 0x119778 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11977b (callEffect (fun _ => 0x1145f0) 0x119780) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11977b (PushPre 0x11977b 5) (callEffect (fun _ => 0x1145f0) 0x119780) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119780⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119780, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119744 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x70, 0xAE, 0xFF, 0xFF]

theorem code_l119744 : ∀ x ∈ codeRange 0x119744 bytes_l119744, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19744 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l119780_11 : Block Op Label signature Reg.count 535 :=
  .letOp (n := 535) (.out 0x119b46 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119b46 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[524, 533]
    (.letOp (n := 536) (.exec 0x119b46 (fun s => s.RIP = 0x119b46) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119b46 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[524, 533]
    (.letOp (n := 537) (.out 0x119b4a (addR64R64Effect 0x119b4a 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[532, 518]
    (.letOp (n := 538) (.out 0x119b4a (addR64R64Effect 0x119b4a 1 3) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 3] []) (.flag .CF)) #v[532, 518]
    (.letOp (n := 539) (.exec 0x119b4a (fun s => s.RIP = 0x119b4a) (addR64R64Effect 0x119b4a 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[532, 518]
    (.letOp (n := 540) (.out 0x119b4d (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119b4d 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[535, 538]
    (.letOp (n := 541) (.exec 0x119b4d (fun s => s.RIP = 0x119b4d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119b4d 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[535, 538]
    (.letOp (n := 542) (.out 0x119b51 (shldR64R64Effect 0x119b51 5 2 1 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[540, 537]
    (.letOp (n := 543) (.exec 0x119b51 (fun s => s.RIP = 0x119b51) (shldR64R64Effect 0x119b51 5 2 1 12) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[540, 537]
    (.letOp (n := 544) (.out 0x119b56 (movR64Imm64Effect 0x119b56 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 545) (.exec 0x119b56 (fun s => s.RIP = 0x119b56) (movR64Imm64Effect 0x119b56 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 546) (.out 0x119b60 (andR64R64Effect 0x119b60 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[232, 544]
    (.letOp (n := 547) (.exec 0x119b60 (fun s => s.RIP = 0x119b60) (andR64R64Effect 0x119b60 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[232, 544]
    (.letOp (n := 548) (.out 0x119b63 (addR64R64Effect 0x119b63 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[546, 542]
    (.letOp (n := 549) (.exec 0x119b63 (fun s => s.RIP = 0x119b63) (addR64R64Effect 0x119b63 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[546, 542]
    (.letOp (n := 550) (.exec 0x119b66 (StorePre 0x119b66 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119b66 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119b66 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 15, .gpr 4] [])) #v[367, 4]
    (.letOp (n := 551) (.exec 0x119b6a (StorePre 0x119b6a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119b6a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119b6a 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[452, 4]
    (.letOp (n := 552) (.exec 0x119b6f (StorePre 0x119b6f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119b6f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119b6f 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[526, 4]
    (.letOp (n := 553) (.out 0x119b74 (andR64R64Effect 0x119b74 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[537, 486]
    (.letOp (n := 554) (.exec 0x119b74 (fun s => s.RIP = 0x119b74) (andR64R64Effect 0x119b74 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[537, 486]
    (.letOp (n := 555) (.exec 0x119b77 (StorePre 0x119b77 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119b77 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119b77 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[553, 4]
    (.letOp (n := 556) (.exec 0x119b7c (StorePre 0x119b7c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119b7c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119b7c 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[548, 4]
    (.letOp (n := 557) (.out 0x119b81 (leaR64Effect 0x119b81 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 558) (.exec 0x119b81 (fun s => s.RIP = 0x119b81) (leaR64Effect 0x119b81 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 559) (.out 0x119b86 (movR64R64Effect 0x119b86 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 560) (.exec 0x119b86 (fun s => s.RIP = 0x119b86) (movR64R64Effect 0x119b86 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 561) (.out 0x119b89 (movR64R64Effect 0x119b89 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[557]
    (.letOp (n := 562) (.exec 0x119b89 (fun s => s.RIP = 0x119b89) (movR64R64Effect 0x119b89 7 3) (Reg.operands [.gpr 3] [])) #v[557]
    (.letOp (n := 563) (.out 0x119b8c (movR64R64Effect 0x119b8c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[559]
    (.letOp (n := 564) (.exec 0x119b8c (fun s => s.RIP = 0x119b8c) (movR64R64Effect 0x119b8c 6 14) (Reg.operands [.gpr 14] [])) #v[559]
    (.letOp (n := 565) (.out 0x119b8f (callEffect (fun _ => 0x1145f0) 0x119b94) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 566) (.exec 0x119b8f (PushPre 0x119b8f 5) (callEffect (fun _ => 0x1145f0) 0x119b94) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 567) (.const ⟨64, 0x119b94⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 544), (1, 553), (2, 542), (3, 557), (4, 565), (5, 479), (6, 563), (7, 561), (8, 452), (9, 426), (10, 526), (11, 490), (12, 486), (13, 449), (14, 559), (15, 367), (22, 22), (39, 39), (50, 50), (51, 51)] 568⟩ { target := .l119b94, kept := #v[], arity := rfl, guard := some (Fin.last 567) }))))))))))))))))))))))))))))))))))

def bytes_l119780_11 : List UInt8 :=
  [0x48, 0x83, 0xD2, 0x00, 0x48, 0x01, 0xD9, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x0F, 0xA4, 0xCA, 0x0C,
    0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x21, 0xC6, 0x48, 0x01, 0xD6,
    0x4C, 0x89, 0x3C, 0x24, 0x4C, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x89, 0x54, 0x24, 0x10, 0x4C, 0x21,
    0xE1, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x74, 0x24, 0x20, 0x48, 0x8D, 0x5C, 0x24, 0x28,
    0x49, 0x89, 0xE6, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x5C, 0xAA, 0xFF, 0xFF]

theorem code_l119780_11 : ∀ x ∈ codeRange 0x119b46 bytes_l119780_11, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19b46 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l119780_10 : Block Op Label signature Reg.count 490 :=
  .letOp (n := 490) (.out 0x119ae9 (movR64Imm64Effect 0x119ae9 11 0x1000003d10) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 491) (.exec 0x119ae9 (fun s => s.RIP = 0x119ae9) (movR64Imm64Effect 0x119ae9 11 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 492) (.out 0x119af3 (mulR64Effect 0x119af3 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[490, 488]
    (.letOp (n := 493) (.out 0x119af3 (mulR64Effect 0x119af3 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[490, 488]
    (.letOp (n := 494) (.exec 0x119af3 (fun s => s.RIP = 0x119af3) (mulR64Effect 0x119af3 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[490, 488]
    (.letOp (n := 495) (.out 0x119af6 (addR64M64Effect 0x119af6 10 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[442, 4]
    (.letOp (n := 496) (.out 0x119af6 (addR64M64Effect 0x119af6 10 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[442, 4]
    (.letOp (n := 497) (.exec 0x119af6 (LoadPre 0x119af6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x119af6 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x119af6 10 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[442, 4]
    (.letOp (n := 498) (.out 0x119afb (atFlags StatusFlags.CF (adcR64M64Effect 0x119afb 3 (.sib 4 none 0 (.d32 0xb0)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[440, 4, 496]
    (.letOp (n := 499) (.exec 0x119afb (LoadPre 0x119afb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x119afb + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x119afb 3 (.sib 4 none 0 (.d32 0xb0)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[440, 4, 496]
    (.letOp (n := 500) (.out 0x119b03 (addR64R64Effect 0x119b03 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[495, 449]
    (.letOp (n := 501) (.out 0x119b03 (addR64R64Effect 0x119b03 10 13) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 13] []) (.flag .CF)) #v[495, 449]
    (.letOp (n := 502) (.exec 0x119b03 (fun s => s.RIP = 0x119b03) (addR64R64Effect 0x119b03 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[495, 449]
    (.letOp (n := 503) (.out 0x119b06 (atFlags StatusFlags.CF (adcR64M64Effect 0x119b06 3 (.sib 4 none 0 (.d32 0x90)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[498, 4, 501]
    (.letOp (n := 504) (.exec 0x119b06 (LoadPre 0x119b06 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x119b06 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x119b06 3 (.sib 4 none 0 (.d32 0x90)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[498, 4, 501]
    (.letOp (n := 505) (.out 0x119b0e (addR64R64Effect 0x119b0e 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[500, 492]
    (.letOp (n := 506) (.out 0x119b0e (addR64R64Effect 0x119b0e 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[500, 492]
    (.letOp (n := 507) (.exec 0x119b0e (fun s => s.RIP = 0x119b0e) (addR64R64Effect 0x119b0e 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[500, 492]
    (.letOp (n := 508) (.out 0x119b11 (atFlags StatusFlags.CF (adcR64R64Effect 0x119b11 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[503, 493, 506]
    (.letOp (n := 509) (.exec 0x119b11 (fun s => s.RIP = 0x119b11) (atFlags StatusFlags.CF (adcR64R64Effect 0x119b11 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[503, 493, 506]
    (.letOp (n := 510) (.exec 0x119b14 (StorePre 0x119b14 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119b14 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119b14 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[467, 4]
    (.letOp (n := 511) (.out 0x119b19 (addR64R64Effect 0x119b19 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[505, 426]
    (.letOp (n := 512) (.out 0x119b19 (addR64R64Effect 0x119b19 10 9) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 9] []) (.flag .CF)) #v[505, 426]
    (.letOp (n := 513) (.exec 0x119b19 (fun s => s.RIP = 0x119b19) (addR64R64Effect 0x119b19 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[505, 426]
    (.letOp (n := 514) (.out 0x119b1c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119b1c 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[508, 512]
    (.letOp (n := 515) (.exec 0x119b1c (fun s => s.RIP = 0x119b1c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119b1c 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[508, 512]
    (.letOp (n := 516) (.out 0x119b20 (shldR64R64Effect 0x119b20 5 14 5 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[482, 479]
    (.letOp (n := 517) (.exec 0x119b20 (fun s => s.RIP = 0x119b20) (shldR64R64Effect 0x119b20 5 14 5 12) (Reg.operands [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[482, 479]
    (.letOp (n := 518) (.out 0x119b25 (shldR64R64Effect 0x119b25 5 3 10 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[514, 511]
    (.letOp (n := 519) (.exec 0x119b25 (fun s => s.RIP = 0x119b25) (shldR64R64Effect 0x119b25 5 3 10 12) (Reg.operands [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[514, 511]
    (.letOp (n := 520) (.exec 0x119b2a (StorePre 0x119b2a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119b2a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119b2a 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[456, 4]
    (.letOp (n := 521) (.out 0x119b2f (movR64R64Effect 0x119b2f 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[516]
    (.letOp (n := 522) (.exec 0x119b2f (fun s => s.RIP = 0x119b2f) (movR64R64Effect 0x119b2f 0 14) (Reg.operands [.gpr 14] [])) #v[516]
    (.letOp (n := 523) (.out 0x119b32 (mulR64Effect 0x119b32 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[490, 521]
    (.letOp (n := 524) (.out 0x119b32 (mulR64Effect 0x119b32 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[490, 521]
    (.letOp (n := 525) (.exec 0x119b32 (fun s => s.RIP = 0x119b32) (mulR64Effect 0x119b32 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[490, 521]
    (.letOp (n := 526) (.out 0x119b35 (andR64R64Effect 0x119b35 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[511, 486]
    (.letOp (n := 527) (.exec 0x119b35 (fun s => s.RIP = 0x119b35) (andR64R64Effect 0x119b35 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[511, 486]
    (.letOp (n := 528) (.out 0x119b38 (movR64M64Effect 0x119b38 1 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 529) (.exec 0x119b38 (LoadPre 0x119b38 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x119b38 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119b38 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 530) (.out 0x119b40 (andR64R64Effect 0x119b40 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[528, 486]
    (.letOp (n := 531) (.exec 0x119b40 (fun s => s.RIP = 0x119b40) (andR64R64Effect 0x119b40 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[528, 486]
    (.letOp (n := 532) (.out 0x119b43 (addR64R64Effect 0x119b43 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[530, 523]
    (.letOp (n := 533) (.out 0x119b43 (addR64R64Effect 0x119b43 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[530, 523]
    (.letOp (n := 534) (.exec 0x119b43 (fun s => s.RIP = 0x119b43) (addR64R64Effect 0x119b43 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[530, 523]
    (b_l119780_11)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l119780_10 : List UInt8 :=
  [0x49, 0xBB, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE3, 0x4C, 0x03, 0x54,
    0x24, 0x58, 0x48, 0x13, 0x9C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xEA, 0x48, 0x13, 0x9C,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC2, 0x48, 0x11, 0xD3, 0x48, 0x89, 0x4C, 0x24, 0x20,
    0x4D, 0x01, 0xCA, 0x48, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xEE, 0x0C, 0x4C, 0x0F, 0xA4, 0xD3,
    0x0C, 0x48, 0x89, 0x7C, 0x24, 0x18, 0x4C, 0x89, 0xF0, 0x49, 0xF7, 0xE3, 0x4D, 0x21, 0xE2, 0x48,
    0x8B, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4C, 0x21, 0xE1, 0x48, 0x01, 0xC1] ++ bytes_l119780_11

theorem code_l119780_10 : ∀ x ∈ codeRange 0x119ae9 bytes_l119780_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19ae9 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119780_11

def b_l119780_9 : Block Op Label signature Reg.count 446 :=
  .letOp (n := 446) (.out 0x119a92 (mulR64Effect 0x119a92 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[356, 444]
    (.letOp (n := 447) (.out 0x119a92 (mulR64Effect 0x119a92 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[356, 444]
    (.letOp (n := 448) (.exec 0x119a92 (fun s => s.RIP = 0x119a92) (mulR64Effect 0x119a92 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[356, 444]
    (.letOp (n := 449) (.out 0x119a95 (movR64R64Effect 0x119a95 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[446]
    (.letOp (n := 450) (.exec 0x119a95 (fun s => s.RIP = 0x119a95) (movR64R64Effect 0x119a95 13 0) (Reg.operands [.gpr 0] [])) #v[446]
    (.letOp (n := 451) (.exec 0x119a98 (StorePre 0x119a98 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x119a98 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119a98 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[447, 4]
    (.letOp (n := 452) (.out 0x119aa0 (andR64R64Effect 0x119aa0 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[421, 404]
    (.letOp (n := 453) (.exec 0x119aa0 (fun s => s.RIP = 0x119aa0) (andR64R64Effect 0x119aa0 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[421, 404]
    (.letOp (n := 454) (.out 0x119aa3 (movR64M64Effect 0x119aa3 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 455) (.exec 0x119aa3 (LoadPre 0x119aa3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x119aa3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119aa3 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 456) (.out 0x119aa8 (movR64M64Effect 0x119aa8 7 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 457) (.exec 0x119aa8 (LoadPre 0x119aa8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x119aa8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119aa8 7 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 458) (.out 0x119ab0 (mulR64Effect 0x119ab0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[456, 454]
    (.letOp (n := 459) (.out 0x119ab0 (mulR64Effect 0x119ab0 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[456, 454]
    (.letOp (n := 460) (.exec 0x119ab0 (fun s => s.RIP = 0x119ab0) (mulR64Effect 0x119ab0 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[456, 454]
    (.letOp (n := 461) (.out 0x119ab3 (movR64R64Effect 0x119ab3 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[459]
    (.letOp (n := 462) (.exec 0x119ab3 (fun s => s.RIP = 0x119ab3) (movR64R64Effect 0x119ab3 14 2) (Reg.operands [.gpr 2] [])) #v[459]
    (.letOp (n := 463) (.out 0x119ab6 (movR64R64Effect 0x119ab6 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[458]
    (.letOp (n := 464) (.exec 0x119ab6 (fun s => s.RIP = 0x119ab6) (movR64R64Effect 0x119ab6 12 0) (Reg.operands [.gpr 0] [])) #v[458]
    (.letOp (n := 465) (.out 0x119ab9 (movR64M64Effect 0x119ab9 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 466) (.exec 0x119ab9 (LoadPre 0x119ab9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x119ab9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119ab9 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 467) (.out 0x119abe (movR64M64Effect 0x119abe 1 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 468) (.exec 0x119abe (LoadPre 0x119abe (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x119abe + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119abe 1 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 469) (.out 0x119ac6 (mulR64Effect 0x119ac6 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[467, 465]
    (.letOp (n := 470) (.out 0x119ac6 (mulR64Effect 0x119ac6 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[467, 465]
    (.letOp (n := 471) (.exec 0x119ac6 (fun s => s.RIP = 0x119ac6) (mulR64Effect 0x119ac6 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[467, 465]
    (.letOp (n := 472) (.out 0x119ac9 (movR64R64Effect 0x119ac9 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[469]
    (.letOp (n := 473) (.exec 0x119ac9 (fun s => s.RIP = 0x119ac9) (movR64R64Effect 0x119ac9 5 0) (Reg.operands [.gpr 0] [])) #v[469]
    (.letOp (n := 474) (.out 0x119acc (addR64R64Effect 0x119acc 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[472, 463]
    (.letOp (n := 475) (.out 0x119acc (addR64R64Effect 0x119acc 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[472, 463]
    (.letOp (n := 476) (.exec 0x119acc (fun s => s.RIP = 0x119acc) (addR64R64Effect 0x119acc 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[472, 463]
    (.letOp (n := 477) (.out 0x119acf (atFlags StatusFlags.CF (adcR64R64Effect 0x119acf 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[461, 470, 475]
    (.letOp (n := 478) (.exec 0x119acf (fun s => s.RIP = 0x119acf) (atFlags StatusFlags.CF (adcR64R64Effect 0x119acf 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[461, 470, 475]
    (.letOp (n := 479) (.out 0x119ad2 (addR64R64Effect 0x119ad2 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[474, 400]
    (.letOp (n := 480) (.out 0x119ad2 (addR64R64Effect 0x119ad2 5 11) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 11] []) (.flag .CF)) #v[474, 400]
    (.letOp (n := 481) (.exec 0x119ad2 (fun s => s.RIP = 0x119ad2) (addR64R64Effect 0x119ad2 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[474, 400]
    (.letOp (n := 482) (.out 0x119ad5 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119ad5 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[477, 480]
    (.letOp (n := 483) (.exec 0x119ad5 (fun s => s.RIP = 0x119ad5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119ad5 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[477, 480]
    (.letOp (n := 484) (.out 0x119ad9 (movR64R64Effect 0x119ad9 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[479]
    (.letOp (n := 485) (.exec 0x119ad9 (fun s => s.RIP = 0x119ad9) (movR64R64Effect 0x119ad9 0 5) (Reg.operands [.gpr 5] [])) #v[479]
    (.letOp (n := 486) (.out 0x119adc (movR64Imm64Effect 0x119adc 12 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 487) (.exec 0x119adc (fun s => s.RIP = 0x119adc) (movR64Imm64Effect 0x119adc 12 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 488) (.out 0x119ae6 (andR64R64Effect 0x119ae6 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[484, 486]
    (.letOp (n := 489) (.exec 0x119ae6 (fun s => s.RIP = 0x119ae6) (andR64R64Effect 0x119ae6 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[484, 486]
    (b_l119780_10))))))))))))))))))))))))))))))))))))))))))))

def bytes_l119780_9 : List UInt8 :=
  [0x49, 0xF7, 0xE6, 0x49, 0x89, 0xC5, 0x48, 0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4D, 0x21,
    0xE0, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x48, 0x8B, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xE7, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0x8B, 0x8C, 0x24,
    0xA8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC5, 0x4C, 0x01, 0xE5, 0x49, 0x11, 0xD6,
    0x4C, 0x01, 0xDD, 0x49, 0x83, 0xD6, 0x00, 0x48, 0x89, 0xE8, 0x49, 0xBC, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xE0] ++ bytes_l119780_10

theorem code_l119780_9 : ∀ x ∈ codeRange 0x119a92 bytes_l119780_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19a92 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119780_10

def b_l119780_8 : Block Op Label signature Reg.count 402 :=
  .letOp (n := 402) (.out 0x119a30 (andR64R64Effect 0x119a30 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[395, 365]
    (.letOp (n := 403) (.exec 0x119a30 (fun s => s.RIP = 0x119a30) (andR64R64Effect 0x119a30 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[395, 365]
    (.letOp (n := 404) (.out 0x119a33 (movR64R64Effect 0x119a33 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[365]
    (.letOp (n := 405) (.exec 0x119a33 (fun s => s.RIP = 0x119a33) (movR64R64Effect 0x119a33 12 1) (Reg.operands [.gpr 1] [])) #v[365]
    (.letOp (n := 406) (.out 0x119a36 (movR64Imm64Effect 0x119a36 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 407) (.exec 0x119a36 (fun s => s.RIP = 0x119a36) (movR64Imm64Effect 0x119a36 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 408) (.out 0x119a40 (mulR64Effect 0x119a40 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[406, 402]
    (.letOp (n := 409) (.out 0x119a40 (mulR64Effect 0x119a40 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[406, 402]
    (.letOp (n := 410) (.exec 0x119a40 (fun s => s.RIP = 0x119a40) (mulR64Effect 0x119a40 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[406, 402]
    (.letOp (n := 411) (.out 0x119a43 (addR64M64Effect 0x119a43 8 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[352, 4]
    (.letOp (n := 412) (.out 0x119a43 (addR64M64Effect 0x119a43 8 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[352, 4]
    (.letOp (n := 413) (.exec 0x119a43 (LoadPre 0x119a43 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x119a43 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x119a43 8 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[352, 4]
    (.letOp (n := 414) (.out 0x119a48 (atFlags StatusFlags.CF (adcR64M64Effect 0x119a48 9 (.sib 4 none 0 (.d8 0x58)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[350, 4, 412]
    (.letOp (n := 415) (.exec 0x119a48 (LoadPre 0x119a48 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x119a48 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x119a48 9 (.sib 4 none 0 (.d8 0x58)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[350, 4, 412]
    (.letOp (n := 416) (.out 0x119a4d (addR64R64Effect 0x119a4d 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[411, 408]
    (.letOp (n := 417) (.out 0x119a4d (addR64R64Effect 0x119a4d 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[411, 408]
    (.letOp (n := 418) (.exec 0x119a4d (fun s => s.RIP = 0x119a4d) (addR64R64Effect 0x119a4d 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[411, 408]
    (.letOp (n := 419) (.out 0x119a50 (atFlags StatusFlags.CF (adcR64R64Effect 0x119a50 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[414, 409, 417]
    (.letOp (n := 420) (.exec 0x119a50 (fun s => s.RIP = 0x119a50) (atFlags StatusFlags.CF (adcR64R64Effect 0x119a50 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[414, 409, 417]
    (.letOp (n := 421) (.out 0x119a53 (addR64R64Effect 0x119a53 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[416, 336]
    (.letOp (n := 422) (.out 0x119a53 (addR64R64Effect 0x119a53 8 3) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 3] []) (.flag .CF)) #v[416, 336]
    (.letOp (n := 423) (.exec 0x119a53 (fun s => s.RIP = 0x119a53) (addR64R64Effect 0x119a53 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[416, 336]
    (.letOp (n := 424) (.out 0x119a56 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119a56 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[419, 422]
    (.letOp (n := 425) (.exec 0x119a56 (fun s => s.RIP = 0x119a56) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119a56 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[419, 422]
    (.letOp (n := 426) (.out 0x119a5a (shldR64R64Effect 0x119a5a 5 9 8 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[424, 421]
    (.letOp (n := 427) (.exec 0x119a5a (fun s => s.RIP = 0x119a5a) (shldR64R64Effect 0x119a5a 5 9 8 12) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[424, 421]
    (.letOp (n := 428) (.out 0x119a5f (movR64R64Effect 0x119a5f 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[378]
    (.letOp (n := 429) (.exec 0x119a5f (fun s => s.RIP = 0x119a5f) (movR64R64Effect 0x119a5f 0 7) (Reg.operands [.gpr 7] [])) #v[378]
    (.letOp (n := 430) (.out 0x119a62 (mulM64Effect 0x119a62 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[428, 4]
    (.letOp (n := 431) (.out 0x119a62 (mulM64Effect 0x119a62 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[428, 4]
    (.letOp (n := 432) (.exec 0x119a62 (LoadPre 0x119a62 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x119a62 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x119a62 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[428, 4]
    (.letOp (n := 433) (.exec 0x119a6a (StorePre 0x119a6a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x119a6a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119a6a 2 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[431, 4]
    (.letOp (n := 434) (.exec 0x119a72 (StorePre 0x119a72 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x119a72 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119a72 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[430, 4]
    (.letOp (n := 435) (.out 0x119a77 (movR64M64Effect 0x119a77 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 436) (.exec 0x119a77 (LoadPre 0x119a77 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x119a77 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119a77 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 437) (.out 0x119a7f (mulM64Effect 0x119a7f 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[435, 4]
    (.letOp (n := 438) (.out 0x119a7f (mulM64Effect 0x119a7f 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[435, 4]
    (.letOp (n := 439) (.exec 0x119a7f (LoadPre 0x119a7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x119a7f + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x119a7f 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[435, 4]
    (.letOp (n := 440) (.out 0x119a84 (movR64R64Effect 0x119a84 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[438]
    (.letOp (n := 441) (.exec 0x119a84 (fun s => s.RIP = 0x119a84) (movR64R64Effect 0x119a84 3 2) (Reg.operands [.gpr 2] [])) #v[438]
    (.letOp (n := 442) (.out 0x119a87 (movR64R64Effect 0x119a87 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[437]
    (.letOp (n := 443) (.exec 0x119a87 (fun s => s.RIP = 0x119a87) (movR64R64Effect 0x119a87 10 0) (Reg.operands [.gpr 0] [])) #v[437]
    (.letOp (n := 444) (.out 0x119a8a (movR64M64Effect 0x119a8a 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 445) (.exec 0x119a8a (LoadPre 0x119a8a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x119a8a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119a8a 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l119780_9))))))))))))))))))))))))))))))))))))))))))))

def bytes_l119780_8 : List UInt8 :=
  [0x48, 0x21, 0xC8, 0x49, 0x89, 0xCC, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE1, 0x4C, 0x03, 0x44, 0x24, 0x78, 0x4C, 0x13, 0x4C, 0x24, 0x58, 0x49, 0x01, 0xC0,
    0x49, 0x11, 0xD1, 0x49, 0x01, 0xD8, 0x49, 0x83, 0xD1, 0x00, 0x4D, 0x0F, 0xA4, 0xC1, 0x0C, 0x48,
    0x89, 0xF8, 0x48, 0xF7, 0xA4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xB0, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x58, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0x64, 0x24, 0x50, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC2, 0x48, 0x8B, 0x84, 0x24, 0x88, 0x00,
    0x00, 0x00] ++ bytes_l119780_9

theorem code_l119780_8 : ∀ x ∈ codeRange 0x119a30 bytes_l119780_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19a30 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119780_9

def b_l119780_7 : Block Op Label signature Reg.count 356 :=
  .letOp (n := 356) (.out 0x1199d9 (movR64M64Effect 0x1199d9 14 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 357) (.exec 0x1199d9 (LoadPre 0x1199d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1199d9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1199d9 14 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 358) (.out 0x1199e1 (mulR64Effect 0x1199e1 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[356, 354]
    (.letOp (n := 359) (.out 0x1199e1 (mulR64Effect 0x1199e1 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[356, 354]
    (.letOp (n := 360) (.exec 0x1199e1 (fun s => s.RIP = 0x1199e1) (mulR64Effect 0x1199e1 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[356, 354]
    (.letOp (n := 361) (.out 0x1199e4 (movR64R64Effect 0x1199e4 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[358]
    (.letOp (n := 362) (.exec 0x1199e4 (fun s => s.RIP = 0x1199e4) (movR64R64Effect 0x1199e4 12 0) (Reg.operands [.gpr 0] [])) #v[358]
    (.letOp (n := 363) (.out 0x1199e7 (movR64R64Effect 0x1199e7 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[359]
    (.letOp (n := 364) (.exec 0x1199e7 (fun s => s.RIP = 0x1199e7) (movR64R64Effect 0x1199e7 13 2) (Reg.operands [.gpr 2] [])) #v[359]
    (.letOp (n := 365) (.out 0x1199ea (movR64Imm64Effect 0x1199ea 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 366) (.exec 0x1199ea (fun s => s.RIP = 0x1199ea) (movR64Imm64Effect 0x1199ea 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 367) (.out 0x1199f4 (andR64R64Effect 0x1199f4 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[331, 365]
    (.letOp (n := 368) (.exec 0x1199f4 (fun s => s.RIP = 0x1199f4) (andR64R64Effect 0x1199f4 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[331, 365]
    (.letOp (n := 369) (.out 0x1199f7 (movR64M64Effect 0x1199f7 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 370) (.exec 0x1199f7 (LoadPre 0x1199f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1199f7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1199f7 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 371) (.out 0x1199fc (mulR64Effect 0x1199fc 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[276, 369]
    (.letOp (n := 372) (.out 0x1199fc (mulR64Effect 0x1199fc 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[276, 369]
    (.letOp (n := 373) (.exec 0x1199fc (fun s => s.RIP = 0x1199fc) (mulR64Effect 0x1199fc 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[276, 369]
    (.letOp (n := 374) (.out 0x1199ff (movR64R64Effect 0x1199ff 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[372]
    (.letOp (n := 375) (.exec 0x1199ff (fun s => s.RIP = 0x1199ff) (movR64R64Effect 0x1199ff 11 2) (Reg.operands [.gpr 2] [])) #v[372]
    (.letOp (n := 376) (.out 0x119a02 (movR64R64Effect 0x119a02 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[371]
    (.letOp (n := 377) (.exec 0x119a02 (fun s => s.RIP = 0x119a02) (movR64R64Effect 0x119a02 5 0) (Reg.operands [.gpr 0] [])) #v[371]
    (.letOp (n := 378) (.out 0x119a05 (movR64M64Effect 0x119a05 7 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 379) (.exec 0x119a05 (LoadPre 0x119a05 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x119a05 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119a05 7 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 380) (.out 0x119a0d (movR64R64Effect 0x119a0d 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[378]
    (.letOp (n := 381) (.exec 0x119a0d (fun s => s.RIP = 0x119a0d) (movR64R64Effect 0x119a0d 0 7) (Reg.operands [.gpr 7] [])) #v[378]
    (.letOp (n := 382) (.out 0x119a10 (mulM64Effect 0x119a10 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[380, 4]
    (.letOp (n := 383) (.out 0x119a10 (mulM64Effect 0x119a10 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[380, 4]
    (.letOp (n := 384) (.exec 0x119a10 (LoadPre 0x119a10 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x119a10 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x119a10 8 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[380, 4]
    (.letOp (n := 385) (.out 0x119a18 (addR64R64Effect 0x119a18 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[376, 361]
    (.letOp (n := 386) (.out 0x119a18 (addR64R64Effect 0x119a18 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[376, 361]
    (.letOp (n := 387) (.exec 0x119a18 (fun s => s.RIP = 0x119a18) (addR64R64Effect 0x119a18 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[376, 361]
    (.letOp (n := 388) (.out 0x119a1b (atFlags StatusFlags.CF (adcR64R64Effect 0x119a1b 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[374, 363, 386]
    (.letOp (n := 389) (.exec 0x119a1b (fun s => s.RIP = 0x119a1b) (atFlags StatusFlags.CF (adcR64R64Effect 0x119a1b 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[374, 363, 386]
    (.letOp (n := 390) (.out 0x119a1e (addR64R64Effect 0x119a1e 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[382, 385]
    (.letOp (n := 391) (.out 0x119a1e (addR64R64Effect 0x119a1e 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[382, 385]
    (.letOp (n := 392) (.exec 0x119a1e (fun s => s.RIP = 0x119a1e) (addR64R64Effect 0x119a1e 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[382, 385]
    (.letOp (n := 393) (.out 0x119a21 (atFlags StatusFlags.CF (adcR64R64Effect 0x119a21 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[388, 383, 391]
    (.letOp (n := 394) (.exec 0x119a21 (fun s => s.RIP = 0x119a21) (atFlags StatusFlags.CF (adcR64R64Effect 0x119a21 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[388, 383, 391]
    (.letOp (n := 395) (.out 0x119a24 (addR64R64Effect 0x119a24 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[390, 312]
    (.letOp (n := 396) (.out 0x119a24 (addR64R64Effect 0x119a24 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[390, 312]
    (.letOp (n := 397) (.exec 0x119a24 (fun s => s.RIP = 0x119a24) (addR64R64Effect 0x119a24 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[390, 312]
    (.letOp (n := 398) (.out 0x119a27 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119a27 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[393, 396]
    (.letOp (n := 399) (.exec 0x119a27 (fun s => s.RIP = 0x119a27) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119a27 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[393, 396]
    (.letOp (n := 400) (.out 0x119a2b (shldR64R64Effect 0x119a2b 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[398, 395]
    (.letOp (n := 401) (.exec 0x119a2b (fun s => s.RIP = 0x119a2b) (shldR64R64Effect 0x119a2b 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[398, 395]
    (b_l119780_8))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l119780_7 : List UInt8 :=
  [0x4C, 0x8B, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xC4, 0x49, 0x89,
    0xD5, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xCF, 0x48, 0x8B,
    0x44, 0x24, 0x68, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0xBC, 0x24,
    0x08, 0x01, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C,
    0x01, 0xE5, 0x4D, 0x11, 0xEB, 0x48, 0x01, 0xE8, 0x49, 0x11, 0xD3, 0x4C, 0x01, 0xD0, 0x49, 0x83,
    0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xC3, 0x0C] ++ bytes_l119780_8

theorem code_l119780_7 : ∀ x ∈ codeRange 0x1199d9 bytes_l119780_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x199d9 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119780_8

def b_l119780_6 : Block Op Label signature Reg.count 314 :=
  .letOp (n := 314) (.out 0x11997d (shlR64Effect 0x11997d 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[307]
    (.letOp (n := 315) (.exec 0x11997d (fun s => s.RIP = 0x11997d) (shlR64Effect 0x11997d 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[307]
    (.letOp (n := 316) (.out 0x119981 (movR64Imm64Effect 0x119981 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 317) (.exec 0x119981 (fun s => s.RIP = 0x119981) (movR64Imm64Effect 0x119981 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 318) (.out 0x11998b (andR64R64Effect 0x11998b 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[314, 316]
    (.letOp (n := 319) (.exec 0x11998b (fun s => s.RIP = 0x11998b) (andR64R64Effect 0x11998b 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[314, 316]
    (.letOp (n := 320) (.out 0x11998e (orR64R64Effect 0x11998e 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[318, 263]
    (.letOp (n := 321) (.exec 0x11998e (fun s => s.RIP = 0x11998e) (orR64R64Effect 0x11998e 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[318, 263]
    (.letOp (n := 322) (.out 0x119991 (movR64Imm64Effect 0x119991 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 323) (.exec 0x119991 (fun s => s.RIP = 0x119991) (movR64Imm64Effect 0x119991 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 324) (.out 0x11999b (mulR64Effect 0x11999b 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[322, 320]
    (.letOp (n := 325) (.out 0x11999b (mulR64Effect 0x11999b 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[322, 320]
    (.letOp (n := 326) (.exec 0x11999b (fun s => s.RIP = 0x11999b) (mulR64Effect 0x11999b 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[322, 320]
    (.letOp (n := 327) (.out 0x11999e (movR64R64Effect 0x11999e 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[325]
    (.letOp (n := 328) (.exec 0x11999e (fun s => s.RIP = 0x11999e) (movR64R64Effect 0x11999e 3 2) (Reg.operands [.gpr 2] [])) #v[325]
    (.letOp (n := 329) (.out 0x1199a1 (movR64R64Effect 0x1199a1 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[324]
    (.letOp (n := 330) (.exec 0x1199a1 (fun s => s.RIP = 0x1199a1) (movR64R64Effect 0x1199a1 15 0) (Reg.operands [.gpr 0] [])) #v[324]
    (.letOp (n := 331) (.out 0x1199a4 (addR64M64Effect 0x1199a4 15 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[329, 4]
    (.letOp (n := 332) (.out 0x1199a4 (addR64M64Effect 0x1199a4 15 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[329, 4]
    (.letOp (n := 333) (.exec 0x1199a4 (LoadPre 0x1199a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1199a4 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1199a4 15 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[329, 4]
    (.letOp (n := 334) (.out 0x1199a9 (atFlags StatusFlags.CF (adcR64M64Effect 0x1199a9 3 (.sib 4 none 0 (.d8 0x58)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[327, 4, 332]
    (.letOp (n := 335) (.exec 0x1199a9 (LoadPre 0x1199a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1199a9 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1199a9 3 (.sib 4 none 0 (.d8 0x58)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[327, 4, 332]
    (.letOp (n := 336) (.out 0x1199ae (shldR64R64Effect 0x1199ae 5 3 15 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[334, 331]
    (.letOp (n := 337) (.exec 0x1199ae (fun s => s.RIP = 0x1199ae) (shldR64R64Effect 0x1199ae 5 3 15 12) (Reg.operands [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[334, 331]
    (.letOp (n := 338) (.out 0x1199b3 (movR64R64Effect 0x1199b3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[285]
    (.letOp (n := 339) (.exec 0x1199b3 (fun s => s.RIP = 0x1199b3) (movR64R64Effect 0x1199b3 0 1) (Reg.operands [.gpr 1] [])) #v[285]
    (.letOp (n := 340) (.out 0x1199b6 (mulR64Effect 0x1199b6 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[245, 338]
    (.letOp (n := 341) (.out 0x1199b6 (mulR64Effect 0x1199b6 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[245, 338]
    (.letOp (n := 342) (.exec 0x1199b6 (fun s => s.RIP = 0x1199b6) (mulR64Effect 0x1199b6 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[245, 338]
    (.letOp (n := 343) (.exec 0x1199b9 (StorePre 0x1199b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1199b9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1199b9 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[341, 4]
    (.letOp (n := 344) (.exec 0x1199be (StorePre 0x1199be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1199be + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1199be 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[340, 4]
    (.letOp (n := 345) (.out 0x1199c3 (movR64M64Effect 0x1199c3 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 346) (.exec 0x1199c3 (LoadPre 0x1199c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1199c3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1199c3 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 347) (.out 0x1199cb (mulR64Effect 0x1199cb 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[254, 345]
    (.letOp (n := 348) (.out 0x1199cb (mulR64Effect 0x1199cb 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[254, 345]
    (.letOp (n := 349) (.exec 0x1199cb (fun s => s.RIP = 0x1199cb) (mulR64Effect 0x1199cb 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[254, 345]
    (.letOp (n := 350) (.out 0x1199ce (movR64R64Effect 0x1199ce 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[348]
    (.letOp (n := 351) (.exec 0x1199ce (fun s => s.RIP = 0x1199ce) (movR64R64Effect 0x1199ce 9 2) (Reg.operands [.gpr 2] [])) #v[348]
    (.letOp (n := 352) (.out 0x1199d1 (movR64R64Effect 0x1199d1 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[347]
    (.letOp (n := 353) (.exec 0x1199d1 (fun s => s.RIP = 0x1199d1) (movR64R64Effect 0x1199d1 8 0) (Reg.operands [.gpr 0] [])) #v[347]
    (.letOp (n := 354) (.out 0x1199d4 (movR64M64Effect 0x1199d4 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 355) (.exec 0x1199d4 (LoadPre 0x1199d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1199d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1199d4 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l119780_7))))))))))))))))))))))))))))))))))))))))))

def bytes_l119780_6 : List UInt8 :=
  [0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21,
    0xD0, 0x4C, 0x09, 0xE8, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xE2, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC7, 0x4C, 0x03, 0x7C, 0x24, 0x78, 0x48, 0x13, 0x5C, 0x24,
    0x58, 0x4C, 0x0F, 0xA4, 0xFB, 0x0C, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0x54, 0x24,
    0x58, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0xF7,
    0xE1, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC0, 0x48, 0x8B, 0x44, 0x24, 0x70] ++ bytes_l119780_7

theorem code_l119780_6 : ∀ x ∈ codeRange 0x11997d bytes_l119780_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1997d 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119780_7

def b_l119780_5 : Block Op Label signature Reg.count 267 :=
  .letOp (n := 267) (.out 0x119925 (mulM64Effect 0x119925 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[265, 4]
    (.letOp (n := 268) (.out 0x119925 (mulM64Effect 0x119925 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[265, 4]
    (.letOp (n := 269) (.exec 0x119925 (LoadPre 0x119925 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x119925 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x119925 8 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[265, 4]
    (.letOp (n := 270) (.out 0x11992d (movR64R64Effect 0x11992d 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[268]
    (.letOp (n := 271) (.exec 0x11992d (fun s => s.RIP = 0x11992d) (movR64R64Effect 0x11992d 10 2) (Reg.operands [.gpr 2] [])) #v[268]
    (.letOp (n := 272) (.out 0x119930 (movR64R64Effect 0x119930 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[267]
    (.letOp (n := 273) (.exec 0x119930 (fun s => s.RIP = 0x119930) (movR64R64Effect 0x119930 14 0) (Reg.operands [.gpr 0] [])) #v[267]
    (.letOp (n := 274) (.out 0x119933 (movR64M64Effect 0x119933 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 275) (.exec 0x119933 (LoadPre 0x119933 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x119933 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119933 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 276) (.out 0x11993b (movR64M64Effect 0x11993b 5 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 277) (.exec 0x11993b (LoadPre 0x11993b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11993b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11993b 5 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 278) (.out 0x119943 (mulR64Effect 0x119943 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[276, 274]
    (.letOp (n := 279) (.out 0x119943 (mulR64Effect 0x119943 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[276, 274]
    (.letOp (n := 280) (.exec 0x119943 (fun s => s.RIP = 0x119943) (mulR64Effect 0x119943 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[276, 274]
    (.letOp (n := 281) (.out 0x119946 (movR64R64Effect 0x119946 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[279]
    (.letOp (n := 282) (.exec 0x119946 (fun s => s.RIP = 0x119946) (movR64R64Effect 0x119946 15 2) (Reg.operands [.gpr 2] [])) #v[279]
    (.letOp (n := 283) (.out 0x119949 (movR64R64Effect 0x119949 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[278]
    (.letOp (n := 284) (.exec 0x119949 (fun s => s.RIP = 0x119949) (movR64R64Effect 0x119949 12 0) (Reg.operands [.gpr 0] [])) #v[278]
    (.letOp (n := 285) (.out 0x11994c (movR64M64Effect 0x11994c 1 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 286) (.exec 0x11994c (LoadPre 0x11994c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11994c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11994c 1 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 287) (.out 0x119954 (movR64R64Effect 0x119954 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[285]
    (.letOp (n := 288) (.exec 0x119954 (fun s => s.RIP = 0x119954) (movR64R64Effect 0x119954 0 1) (Reg.operands [.gpr 1] [])) #v[285]
    (.letOp (n := 289) (.out 0x119957 (mulM64Effect 0x119957 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[287, 4]
    (.letOp (n := 290) (.out 0x119957 (mulM64Effect 0x119957 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[287, 4]
    (.letOp (n := 291) (.exec 0x119957 (LoadPre 0x119957 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x119957 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x119957 8 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[287, 4]
    (.letOp (n := 292) (.out 0x11995f (addR64R64Effect 0x11995f 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[272, 259]
    (.letOp (n := 293) (.out 0x11995f (addR64R64Effect 0x11995f 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[272, 259]
    (.letOp (n := 294) (.exec 0x11995f (fun s => s.RIP = 0x11995f) (addR64R64Effect 0x11995f 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[272, 259]
    (.letOp (n := 295) (.out 0x119962 (atFlags StatusFlags.CF (adcR64R64Effect 0x119962 10 3)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[270, 261, 293]
    (.letOp (n := 296) (.exec 0x119962 (fun s => s.RIP = 0x119962) (atFlags StatusFlags.CF (adcR64R64Effect 0x119962 10 3)) (Reg.operands [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[270, 261, 293]
    (.letOp (n := 297) (.out 0x119965 (addR64R64Effect 0x119965 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[292, 283]
    (.letOp (n := 298) (.out 0x119965 (addR64R64Effect 0x119965 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[292, 283]
    (.letOp (n := 299) (.exec 0x119965 (fun s => s.RIP = 0x119965) (addR64R64Effect 0x119965 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[292, 283]
    (.letOp (n := 300) (.out 0x119968 (atFlags StatusFlags.CF (adcR64R64Effect 0x119968 10 15)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[295, 281, 298]
    (.letOp (n := 301) (.exec 0x119968 (fun s => s.RIP = 0x119968) (atFlags StatusFlags.CF (adcR64R64Effect 0x119968 10 15)) (Reg.operands [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[295, 281, 298]
    (.letOp (n := 302) (.out 0x11996b (addR64R64Effect 0x11996b 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[289, 297]
    (.letOp (n := 303) (.out 0x11996b (addR64R64Effect 0x11996b 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[289, 297]
    (.letOp (n := 304) (.exec 0x11996b (fun s => s.RIP = 0x11996b) (addR64R64Effect 0x11996b 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[289, 297]
    (.letOp (n := 305) (.out 0x11996e (atFlags StatusFlags.CF (adcR64R64Effect 0x11996e 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[300, 290, 303]
    (.letOp (n := 306) (.exec 0x11996e (fun s => s.RIP = 0x11996e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11996e 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[300, 290, 303]
    (.letOp (n := 307) (.out 0x119971 (addR64R64Effect 0x119971 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[302, 237]
    (.letOp (n := 308) (.out 0x119971 (addR64R64Effect 0x119971 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[302, 237]
    (.letOp (n := 309) (.exec 0x119971 (fun s => s.RIP = 0x119971) (addR64R64Effect 0x119971 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[302, 237]
    (.letOp (n := 310) (.out 0x119974 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119974 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[305, 308]
    (.letOp (n := 311) (.exec 0x119974 (fun s => s.RIP = 0x119974) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119974 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[305, 308]
    (.letOp (n := 312) (.out 0x119978 (shldR64R64Effect 0x119978 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[310, 307]
    (.letOp (n := 313) (.exec 0x119978 (fun s => s.RIP = 0x119978) (shldR64R64Effect 0x119978 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[310, 307]
    (b_l119780_6)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l119780_5 : List UInt8 :=
  [0x48, 0xF7, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC6, 0x48, 0x8B,
    0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0x8B, 0xAC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xE5, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48,
    0x89, 0xC8, 0x48, 0xF7, 0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xDE, 0x49, 0x11, 0xDA,
    0x4D, 0x01, 0xE6, 0x4D, 0x11, 0xFA, 0x4C, 0x01, 0xF0, 0x49, 0x11, 0xD2, 0x48, 0x01, 0xF8, 0x49,
    0x83, 0xD2, 0x00, 0x49, 0x0F, 0xA4, 0xC2, 0x0C] ++ bytes_l119780_6

theorem code_l119780_5 : ∀ x ∈ codeRange 0x119925 bytes_l119780_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19925 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119780_6

def b_l119780_4 : Block Op Label signature Reg.count 225 :=
  .letOp (n := 225) (.out 0x1198d5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1198d5 7 5)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[220, 194, 223]
    (.letOp (n := 226) (.exec 0x1198d5 (fun s => s.RIP = 0x1198d5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1198d5 7 5)) (Reg.operands [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[220, 194, 223]
    (.letOp (n := 227) (.out 0x1198d8 (addR64R64Effect 0x1198d8 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[222, 202]
    (.letOp (n := 228) (.out 0x1198d8 (addR64R64Effect 0x1198d8 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[222, 202]
    (.letOp (n := 229) (.exec 0x1198d8 (fun s => s.RIP = 0x1198d8) (addR64R64Effect 0x1198d8 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[222, 202]
    (.letOp (n := 230) (.out 0x1198db (atFlags StatusFlags.CF (adcR64R64Effect 0x1198db 7 8)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[225, 205, 228]
    (.letOp (n := 231) (.exec 0x1198db (fun s => s.RIP = 0x1198db) (atFlags StatusFlags.CF (adcR64R64Effect 0x1198db 7 8)) (Reg.operands [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[225, 205, 228]
    (.letOp (n := 232) (.out 0x1198de (addR64R64Effect 0x1198de 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[227, 149]
    (.letOp (n := 233) (.out 0x1198de (addR64R64Effect 0x1198de 6 9) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 9] []) (.flag .CF)) #v[227, 149]
    (.letOp (n := 234) (.exec 0x1198de (fun s => s.RIP = 0x1198de) (addR64R64Effect 0x1198de 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[227, 149]
    (.letOp (n := 235) (.out 0x1198e1 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1198e1 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[230, 233]
    (.letOp (n := 236) (.exec 0x1198e1 (fun s => s.RIP = 0x1198e1) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1198e1 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[230, 233]
    (.letOp (n := 237) (.out 0x1198e5 (shldR64R64Effect 0x1198e5 5 7 6 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[235, 232]
    (.letOp (n := 238) (.exec 0x1198e5 (fun s => s.RIP = 0x1198e5) (shldR64R64Effect 0x1198e5 5 7 6 12) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[235, 232]
    (.letOp (n := 239) (.out 0x1198ea (movR64R64Effect 0x1198ea 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[232]
    (.letOp (n := 240) (.exec 0x1198ea (fun s => s.RIP = 0x1198ea) (movR64R64Effect 0x1198ea 13 6) (Reg.operands [.gpr 6] [])) #v[232]
    (.letOp (n := 241) (.out 0x1198ed (shrR64Effect 0x1198ed 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[239]
    (.letOp (n := 242) (.exec 0x1198ed (fun s => s.RIP = 0x1198ed) (shrR64Effect 0x1198ed 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[239]
    (.letOp (n := 243) (.out 0x1198f1 (movR64R64Effect 0x1198f1 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[185]
    (.letOp (n := 244) (.exec 0x1198f1 (fun s => s.RIP = 0x1198f1) (movR64R64Effect 0x1198f1 0 10) (Reg.operands [.gpr 10] [])) #v[185]
    (.letOp (n := 245) (.out 0x1198f4 (movR64M64Effect 0x1198f4 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 246) (.exec 0x1198f4 (LoadPre 0x1198f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1198f4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1198f4 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 247) (.out 0x1198fc (mulR64Effect 0x1198fc 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[245, 243]
    (.letOp (n := 248) (.out 0x1198fc (mulR64Effect 0x1198fc 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[245, 243]
    (.letOp (n := 249) (.exec 0x1198fc (fun s => s.RIP = 0x1198fc) (mulR64Effect 0x1198fc 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[245, 243]
    (.letOp (n := 250) (.exec 0x1198ff (StorePre 0x1198ff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1198ff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1198ff 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[248, 4]
    (.letOp (n := 251) (.exec 0x119904 (StorePre 0x119904 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x119904 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119904 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[247, 4]
    (.letOp (n := 252) (.out 0x119909 (movR64M64Effect 0x119909 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 253) (.exec 0x119909 (LoadPre 0x119909 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x119909 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119909 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 254) (.out 0x11990e (movR64M64Effect 0x11990e 9 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 255) (.exec 0x11990e (LoadPre 0x11990e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11990e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11990e 9 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 256) (.out 0x119913 (mulR64Effect 0x119913 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[254, 252]
    (.letOp (n := 257) (.out 0x119913 (mulR64Effect 0x119913 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[254, 252]
    (.letOp (n := 258) (.exec 0x119913 (fun s => s.RIP = 0x119913) (mulR64Effect 0x119913 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[254, 252]
    (.letOp (n := 259) (.out 0x119916 (movR64R64Effect 0x119916 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[256]
    (.letOp (n := 260) (.exec 0x119916 (fun s => s.RIP = 0x119916) (movR64R64Effect 0x119916 11 0) (Reg.operands [.gpr 0] [])) #v[256]
    (.letOp (n := 261) (.out 0x119919 (movR64R64Effect 0x119919 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[257]
    (.letOp (n := 262) (.exec 0x119919 (fun s => s.RIP = 0x119919) (movR64R64Effect 0x119919 3 2) (Reg.operands [.gpr 2] [])) #v[257]
    (.letOp (n := 263) (.out 0x11991c (andR32Imm8Effect 0x11991c 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[241]
    (.letOp (n := 264) (.exec 0x11991c (fun s => s.RIP = 0x11991c) (andR32Imm8Effect 0x11991c 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[241]
    (.letOp (n := 265) (.out 0x119920 (movR64M64Effect 0x119920 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 266) (.exec 0x119920 (LoadPre 0x119920 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x119920 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119920 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l119780_5))))))))))))))))))))))))))))))))))))))))))

def bytes_l119780_4 : List UInt8 :=
  [0x48, 0x11, 0xEF, 0x48, 0x01, 0xC6, 0x4C, 0x11, 0xC7, 0x4C, 0x01, 0xCE, 0x48, 0x83, 0xD7, 0x00,
    0x48, 0x0F, 0xA4, 0xF7, 0x0C, 0x49, 0x89, 0xF5, 0x49, 0xC1, 0xED, 0x30, 0x4C, 0x89, 0xD0, 0x4C,
    0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0x54, 0x24, 0x58, 0x48,
    0x89, 0x44, 0x24, 0x78, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x4C, 0x8B, 0x4C, 0x24, 0x50, 0x49, 0xF7,
    0xE1, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xD3, 0x41, 0x83, 0xE5, 0x0F, 0x48, 0x8B, 0x44, 0x24, 0x68] ++ bytes_l119780_5

theorem code_l119780_4 : ∀ x ∈ codeRange 0x1198d5 bytes_l119780_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x198d5 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119780_5

def b_l119780_3 : Block Op Label signature Reg.count 178 :=
  .letOp (n := 178) (.out 0x11988e (mulR64Effect 0x11988e 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[55, 176]
    (.letOp (n := 179) (.out 0x11988e (mulR64Effect 0x11988e 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[55, 176]
    (.letOp (n := 180) (.exec 0x11988e (fun s => s.RIP = 0x11988e) (mulR64Effect 0x11988e 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[55, 176]
    (.letOp (n := 181) (.out 0x119891 (movR64R64Effect 0x119891 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[179]
    (.letOp (n := 182) (.exec 0x119891 (fun s => s.RIP = 0x119891) (movR64R64Effect 0x119891 15 2) (Reg.operands [.gpr 2] [])) #v[179]
    (.letOp (n := 183) (.out 0x119894 (movR64R64Effect 0x119894 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[178]
    (.letOp (n := 184) (.exec 0x119894 (fun s => s.RIP = 0x119894) (movR64R64Effect 0x119894 13 0) (Reg.operands [.gpr 0] [])) #v[178]
    (.letOp (n := 185) (.out 0x119897 (movR64M64Effect 0x119897 10 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 186) (.exec 0x119897 (LoadPre 0x119897 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x119897 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119897 10 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 187) (.out 0x11989f (movR64R64Effect 0x11989f 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[185]
    (.letOp (n := 188) (.exec 0x11989f (fun s => s.RIP = 0x11989f) (movR64R64Effect 0x11989f 0 10) (Reg.operands [.gpr 10] [])) #v[185]
    (.letOp (n := 189) (.out 0x1198a2 (mulR64Effect 0x1198a2 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[53, 187]
    (.letOp (n := 190) (.out 0x1198a2 (mulR64Effect 0x1198a2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[53, 187]
    (.letOp (n := 191) (.exec 0x1198a2 (fun s => s.RIP = 0x1198a2) (mulR64Effect 0x1198a2 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[53, 187]
    (.letOp (n := 192) (.out 0x1198a5 (movR64R64Effect 0x1198a5 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[189]
    (.letOp (n := 193) (.exec 0x1198a5 (fun s => s.RIP = 0x1198a5) (movR64R64Effect 0x1198a5 11 0) (Reg.operands [.gpr 0] [])) #v[189]
    (.letOp (n := 194) (.out 0x1198a8 (movR64R64Effect 0x1198a8 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[190]
    (.letOp (n := 195) (.exec 0x1198a8 (fun s => s.RIP = 0x1198a8) (movR64R64Effect 0x1198a8 5 2) (Reg.operands [.gpr 2] [])) #v[190]
    (.letOp (n := 196) (.out 0x1198ab (shrR64Effect 0x1198ab 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[126]
    (.letOp (n := 197) (.exec 0x1198ab (fun s => s.RIP = 0x1198ab) (shrR64Effect 0x1198ab 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[126]
    (.letOp (n := 198) (.out 0x1198af (imulR64R64Effect 0x1198af 4 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[196, 136]
    (.letOp (n := 199) (.exec 0x1198af (fun s => s.RIP = 0x1198af) (imulR64R64Effect 0x1198af 4 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[196, 136]
    (.letOp (n := 200) (.out 0x1198b3 (movR64R64Effect 0x1198b3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[130]
    (.letOp (n := 201) (.exec 0x1198b3 (fun s => s.RIP = 0x1198b3) (movR64R64Effect 0x1198b3 0 3) (Reg.operands [.gpr 3] [])) #v[130]
    (.letOp (n := 202) (.out 0x1198b6 (mulR64Effect 0x1198b6 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[136, 200]
    (.letOp (n := 203) (.out 0x1198b6 (mulR64Effect 0x1198b6 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[136, 200]
    (.letOp (n := 204) (.exec 0x1198b6 (fun s => s.RIP = 0x1198b6) (mulR64Effect 0x1198b6 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[136, 200]
    (.letOp (n := 205) (.out 0x1198b9 (addR64R64Effect 0x1198b9 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[198, 203]
    (.letOp (n := 206) (.exec 0x1198b9 (fun s => s.RIP = 0x1198b9) (addR64R64Effect 0x1198b9 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[198, 203]
    (.letOp (n := 207) (.out 0x1198bc (addR64M64Effect 0x1198bc 6 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[165, 4]
    (.letOp (n := 208) (.out 0x1198bc (addR64M64Effect 0x1198bc 6 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[165, 4]
    (.letOp (n := 209) (.exec 0x1198bc (LoadPre 0x1198bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1198bc + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1198bc 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[165, 4]
    (.letOp (n := 210) (.out 0x1198c1 (atFlags StatusFlags.CF (adcR64M64Effect 0x1198c1 7 (.sib 4 none 0 (.d8 0x58)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[163, 4, 208]
    (.letOp (n := 211) (.exec 0x1198c1 (LoadPre 0x1198c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1198c1 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1198c1 7 (.sib 4 none 0 (.d8 0x58)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[163, 4, 208]
    (.letOp (n := 212) (.out 0x1198c6 (addR64R64Effect 0x1198c6 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[207, 174]
    (.letOp (n := 213) (.out 0x1198c6 (addR64R64Effect 0x1198c6 6 12) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 12] []) (.flag .CF)) #v[207, 174]
    (.letOp (n := 214) (.exec 0x1198c6 (fun s => s.RIP = 0x1198c6) (addR64R64Effect 0x1198c6 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[207, 174]
    (.letOp (n := 215) (.out 0x1198c9 (atFlags StatusFlags.CF (adcR64R64Effect 0x1198c9 7 14)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[210, 172, 213]
    (.letOp (n := 216) (.exec 0x1198c9 (fun s => s.RIP = 0x1198c9) (atFlags StatusFlags.CF (adcR64R64Effect 0x1198c9 7 14)) (Reg.operands [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[210, 172, 213]
    (.letOp (n := 217) (.out 0x1198cc (addR64R64Effect 0x1198cc 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[212, 183]
    (.letOp (n := 218) (.out 0x1198cc (addR64R64Effect 0x1198cc 6 13) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 13] []) (.flag .CF)) #v[212, 183]
    (.letOp (n := 219) (.exec 0x1198cc (fun s => s.RIP = 0x1198cc) (addR64R64Effect 0x1198cc 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[212, 183]
    (.letOp (n := 220) (.out 0x1198cf (atFlags StatusFlags.CF (adcR64R64Effect 0x1198cf 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[215, 181, 218]
    (.letOp (n := 221) (.exec 0x1198cf (fun s => s.RIP = 0x1198cf) (atFlags StatusFlags.CF (adcR64R64Effect 0x1198cf 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[215, 181, 218]
    (.letOp (n := 222) (.out 0x1198d2 (addR64R64Effect 0x1198d2 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[217, 192]
    (.letOp (n := 223) (.out 0x1198d2 (addR64R64Effect 0x1198d2 6 11) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 11] []) (.flag .CF)) #v[217, 192]
    (.letOp (n := 224) (.exec 0x1198d2 (fun s => s.RIP = 0x1198d2) (addR64R64Effect 0x1198d2 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[217, 192]
    (b_l119780_4)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l119780_3 : List UInt8 :=
  [0x49, 0xF7, 0xE7, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC5, 0x4C, 0x8B, 0x94, 0x24, 0x88, 0x00, 0x00,
    0x00, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xD5, 0x49, 0xC1, 0xE8,
    0x34, 0x4C, 0x0F, 0xAF, 0xC1, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0xE1, 0x49, 0x01, 0xD0, 0x48, 0x03,
    0x74, 0x24, 0x78, 0x48, 0x13, 0x7C, 0x24, 0x58, 0x4C, 0x01, 0xE6, 0x4C, 0x11, 0xF7, 0x4C, 0x01,
    0xEE, 0x4C, 0x11, 0xFF, 0x4C, 0x01, 0xDE] ++ bytes_l119780_4

theorem code_l119780_3 : ∀ x ∈ codeRange 0x11988e bytes_l119780_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1988e 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119780_4

def b_l119780_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x119834 (movR64Imm64Effect 0x119834 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 137) (.exec 0x119834 (fun s => s.RIP = 0x119834) (movR64Imm64Effect 0x119834 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 138) (.out 0x11983e (mulR64Effect 0x11983e 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[136, 134]
    (.letOp (n := 139) (.out 0x11983e (mulR64Effect 0x11983e 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[136, 134]
    (.letOp (n := 140) (.exec 0x11983e (fun s => s.RIP = 0x11983e) (mulR64Effect 0x11983e 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[136, 134]
    (.letOp (n := 141) (.out 0x119841 (movR64R64Effect 0x119841 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[139]
    (.letOp (n := 142) (.exec 0x119841 (fun s => s.RIP = 0x119841) (movR64R64Effect 0x119841 9 2) (Reg.operands [.gpr 2] [])) #v[139]
    (.letOp (n := 143) (.out 0x119844 (addR64R64Effect 0x119844 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[138, 113]
    (.letOp (n := 144) (.out 0x119844 (addR64R64Effect 0x119844 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[138, 113]
    (.letOp (n := 145) (.exec 0x119844 (fun s => s.RIP = 0x119844) (addR64R64Effect 0x119844 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[138, 113]
    (.letOp (n := 146) (.exec 0x119847 (StorePre 0x119847 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x119847 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119847 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[143, 4]
    (.letOp (n := 147) (.out 0x11984f (atFlags StatusFlags.CF (adcR64R64Effect 0x11984f 9 7)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[141, 116, 144]
    (.letOp (n := 148) (.exec 0x11984f (fun s => s.RIP = 0x11984f) (atFlags StatusFlags.CF (adcR64R64Effect 0x11984f 9 7)) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[141, 116, 144]
    (.letOp (n := 149) (.out 0x119852 (shldR64R64Effect 0x119852 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[147, 143]
    (.letOp (n := 150) (.exec 0x119852 (fun s => s.RIP = 0x119852) (shldR64R64Effect 0x119852 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[147, 143]
    (.letOp (n := 151) (.out 0x119857 (movR64R64Effect 0x119857 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[118]
    (.letOp (n := 152) (.exec 0x119857 (fun s => s.RIP = 0x119857) (movR64R64Effect 0x119857 0 6) (Reg.operands [.gpr 6] [])) #v[118]
    (.letOp (n := 153) (.out 0x11985a (mulR64Effect 0x11985a 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[59, 151]
    (.letOp (n := 154) (.out 0x11985a (mulR64Effect 0x11985a 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[59, 151]
    (.letOp (n := 155) (.exec 0x11985a (fun s => s.RIP = 0x11985a) (mulR64Effect 0x11985a 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[59, 151]
    (.letOp (n := 156) (.exec 0x11985d (StorePre 0x11985d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11985d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11985d 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[154, 4]
    (.letOp (n := 157) (.exec 0x119862 (StorePre 0x119862 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x119862 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119862 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[153, 4]
    (.letOp (n := 158) (.out 0x119867 (movR64M64Effect 0x119867 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 159) (.exec 0x119867 (LoadPre 0x119867 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x119867 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119867 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 160) (.out 0x11986c (mulR64Effect 0x11986c 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[61, 158]
    (.letOp (n := 161) (.out 0x11986c (mulR64Effect 0x11986c 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[61, 158]
    (.letOp (n := 162) (.exec 0x11986c (fun s => s.RIP = 0x11986c) (mulR64Effect 0x11986c 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[61, 158]
    (.letOp (n := 163) (.out 0x11986f (movR64R64Effect 0x11986f 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[161]
    (.letOp (n := 164) (.exec 0x11986f (fun s => s.RIP = 0x11986f) (movR64R64Effect 0x11986f 7 2) (Reg.operands [.gpr 2] [])) #v[161]
    (.letOp (n := 165) (.out 0x119872 (movR64R64Effect 0x119872 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[160]
    (.letOp (n := 166) (.exec 0x119872 (fun s => s.RIP = 0x119872) (movR64R64Effect 0x119872 6 0) (Reg.operands [.gpr 0] [])) #v[160]
    (.letOp (n := 167) (.out 0x119875 (movR64M64Effect 0x119875 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 168) (.exec 0x119875 (LoadPre 0x119875 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x119875 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119875 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 169) (.out 0x11987d (mulR64Effect 0x11987d 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[57, 167]
    (.letOp (n := 170) (.out 0x11987d (mulR64Effect 0x11987d 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[57, 167]
    (.letOp (n := 171) (.exec 0x11987d (fun s => s.RIP = 0x11987d) (mulR64Effect 0x11987d 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[57, 167]
    (.letOp (n := 172) (.out 0x119880 (movR64R64Effect 0x119880 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[170]
    (.letOp (n := 173) (.exec 0x119880 (fun s => s.RIP = 0x119880) (movR64R64Effect 0x119880 14 2) (Reg.operands [.gpr 2] [])) #v[170]
    (.letOp (n := 174) (.out 0x119883 (movR64R64Effect 0x119883 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[169]
    (.letOp (n := 175) (.exec 0x119883 (fun s => s.RIP = 0x119883) (movR64R64Effect 0x119883 12 0) (Reg.operands [.gpr 0] [])) #v[169]
    (.letOp (n := 176) (.out 0x119886 (movR64M64Effect 0x119886 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 177) (.exec 0x119886 (LoadPre 0x119886 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x119886 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119886 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l119780_3))))))))))))))))))))))))))))))))))))))))))

def bytes_l119780_2 : List UInt8 :=
  [0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD1,
    0x4C, 0x01, 0xD8, 0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x49, 0x11, 0xF9, 0x49, 0x0F,
    0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE4, 0x48, 0x89, 0x54, 0x24, 0x58, 0x48, 0x89,
    0x44, 0x24, 0x78, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0xD7, 0x48, 0x89,
    0xC6, 0x48, 0x8B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xD6, 0x49,
    0x89, 0xC4, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] ++ bytes_l119780_3

theorem code_l119780_2 : ∀ x ∈ codeRange 0x119834 bytes_l119780_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19834 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119780_3

def b_l119780_1 : Block Op Label signature Reg.count 94 :=
  .letOp (n := 94) (.out 0x1197de (movR64R64Effect 0x1197de 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 95) (.exec 0x1197de (fun s => s.RIP = 0x1197de) (movR64R64Effect 0x1197de 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 96) (.out 0x1197e1 (movR64R64Effect 0x1197e1 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[90]
    (.letOp (n := 97) (.exec 0x1197e1 (fun s => s.RIP = 0x1197e1) (movR64R64Effect 0x1197e1 6 0) (Reg.operands [.gpr 0] [])) #v[90]
    (.letOp (n := 98) (.out 0x1197e4 (addR64R64Effect 0x1197e4 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[96, 83]
    (.letOp (n := 99) (.out 0x1197e4 (addR64R64Effect 0x1197e4 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[96, 83]
    (.letOp (n := 100) (.exec 0x1197e4 (fun s => s.RIP = 0x1197e4) (addR64R64Effect 0x1197e4 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[96, 83]
    (.letOp (n := 101) (.out 0x1197e7 (atFlags StatusFlags.CF (adcR64R64Effect 0x1197e7 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[94, 86, 99]
    (.letOp (n := 102) (.exec 0x1197e7 (fun s => s.RIP = 0x1197e7) (atFlags StatusFlags.CF (adcR64R64Effect 0x1197e7 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[94, 86, 99]
    (.letOp (n := 103) (.out 0x1197ea (movR64M64Effect 0x1197ea 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 104) (.exec 0x1197ea (LoadPre 0x1197ea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1197ea + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1197ea 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.out 0x1197f2 (mulR64Effect 0x1197f2 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[55, 103]
    (.letOp (n := 106) (.out 0x1197f2 (mulR64Effect 0x1197f2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[55, 103]
    (.letOp (n := 107) (.exec 0x1197f2 (fun s => s.RIP = 0x1197f2) (mulR64Effect 0x1197f2 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[55, 103]
    (.letOp (n := 108) (.exec 0x1197f5 (StorePre 0x1197f5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1197f5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1197f5 15 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 109) (.out 0x1197fd (movR64R64Effect 0x1197fd 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[106]
    (.letOp (n := 110) (.exec 0x1197fd (fun s => s.RIP = 0x1197fd) (movR64R64Effect 0x1197fd 7 2) (Reg.operands [.gpr 2] [])) #v[106]
    (.letOp (n := 111) (.out 0x119800 (movR64R64Effect 0x119800 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[105]
    (.letOp (n := 112) (.exec 0x119800 (fun s => s.RIP = 0x119800) (movR64R64Effect 0x119800 11 0) (Reg.operands [.gpr 0] [])) #v[105]
    (.letOp (n := 113) (.out 0x119803 (addR64R64Effect 0x119803 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[111, 98]
    (.letOp (n := 114) (.out 0x119803 (addR64R64Effect 0x119803 11 6) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 6] []) (.flag .CF)) #v[111, 98]
    (.letOp (n := 115) (.exec 0x119803 (fun s => s.RIP = 0x119803) (addR64R64Effect 0x119803 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[111, 98]
    (.letOp (n := 116) (.out 0x119806 (atFlags StatusFlags.CF (adcR64R64Effect 0x119806 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[109, 101, 114]
    (.letOp (n := 117) (.exec 0x119806 (fun s => s.RIP = 0x119806) (atFlags StatusFlags.CF (adcR64R64Effect 0x119806 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[109, 101, 114]
    (.letOp (n := 118) (.out 0x119809 (movR64M64Effect 0x119809 6 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 119) (.exec 0x119809 (LoadPre 0x119809 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x119809 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119809 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 120) (.out 0x11980e (movR64R64Effect 0x11980e 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[118]
    (.letOp (n := 121) (.exec 0x11980e (fun s => s.RIP = 0x11980e) (movR64R64Effect 0x11980e 0 6) (Reg.operands [.gpr 6] [])) #v[118]
    (.letOp (n := 122) (.out 0x119811 (mulR64Effect 0x119811 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[53, 120]
    (.letOp (n := 123) (.out 0x119811 (mulR64Effect 0x119811 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[53, 120]
    (.letOp (n := 124) (.exec 0x119811 (fun s => s.RIP = 0x119811) (mulR64Effect 0x119811 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[53, 120]
    (.letOp (n := 125) (.exec 0x119814 (StorePre 0x119814 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x119814 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119814 5 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 126) (.out 0x11981c (movR64R64Effect 0x11981c 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[123]
    (.letOp (n := 127) (.exec 0x11981c (fun s => s.RIP = 0x11981c) (movR64R64Effect 0x11981c 8 2) (Reg.operands [.gpr 2] [])) #v[123]
    (.letOp (n := 128) (.out 0x11981f (movR64R64Effect 0x11981f 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[123]
    (.letOp (n := 129) (.exec 0x11981f (fun s => s.RIP = 0x11981f) (movR64R64Effect 0x11981f 3 2) (Reg.operands [.gpr 2] [])) #v[123]
    (.letOp (n := 130) (.out 0x119822 (shldR64R64Effect 0x119822 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[128, 122]
    (.letOp (n := 131) (.exec 0x119822 (fun s => s.RIP = 0x119822) (shldR64R64Effect 0x119822 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[128, 122]
    (.letOp (n := 132) (.out 0x119827 (movR64Imm64Effect 0x119827 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 133) (.exec 0x119827 (fun s => s.RIP = 0x119827) (movR64Imm64Effect 0x119827 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 134) (.out 0x119831 (andR64R64Effect 0x119831 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[122, 132]
    (.letOp (n := 135) (.exec 0x119831 (fun s => s.RIP = 0x119831) (andR64R64Effect 0x119831 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[122, 132]
    (b_l119780_2))))))))))))))))))))))))))))))))))))))))))

def bytes_l119780_1 : List UInt8 :=
  [0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x01, 0xC6, 0x48, 0x11, 0xF9, 0x48, 0x8B, 0x84, 0x24,
    0x88, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE7, 0x4C, 0x89, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48,
    0x89, 0xD7, 0x49, 0x89, 0xC3, 0x49, 0x01, 0xF3, 0x48, 0x11, 0xCF, 0x48, 0x8B, 0x74, 0x24, 0x70,
    0x48, 0x89, 0xF0, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xAC, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x49, 0x89,
    0xD0, 0x48, 0x89, 0xD3, 0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8] ++ bytes_l119780_2

theorem code_l119780_1 : ∀ x ∈ codeRange 0x1197de bytes_l119780_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x197de 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119780_2

def b_l119780 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119780 (movR64M64Effect 0x119780 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x119780 (LoadPre 0x119780 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119780 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119780 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x119785 (movR64M64Effect 0x119785 15 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x119785 (LoadPre 0x119785 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119785 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119785 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11978a (movR64M64Effect 0x11978a 13 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 58) (.exec 0x11978a (LoadPre 0x11978a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11978a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11978a 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x11978f (movR64M64Effect 0x11978f 12 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 60) (.exec 0x11978f (LoadPre 0x11978f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11978f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11978f 12 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x119794 (movR64M64Effect 0x119794 14 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 62) (.exec 0x119794 (LoadPre 0x119794 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119794 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119794 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x119799 (movR64M64Effect 0x119799 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x119799 (LoadPre 0x119799 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x119799 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119799 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x11979e (mulR64Effect 0x11979e 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[59, 63]
    (.letOp (n := 66) (.out 0x11979e (mulR64Effect 0x11979e 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[59, 63]
    (.letOp (n := 67) (.exec 0x11979e (fun s => s.RIP = 0x11979e) (mulR64Effect 0x11979e 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[59, 63]
    (.letOp (n := 68) (.exec 0x1197a1 (StorePre 0x1197a1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1197a1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1197a1 12 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 69) (.out 0x1197a9 (movR64R64Effect 0x1197a9 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[66]
    (.letOp (n := 70) (.exec 0x1197a9 (fun s => s.RIP = 0x1197a9) (movR64R64Effect 0x1197a9 1 2) (Reg.operands [.gpr 2] [])) #v[66]
    (.letOp (n := 71) (.out 0x1197ac (movR64R64Effect 0x1197ac 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 72) (.exec 0x1197ac (fun s => s.RIP = 0x1197ac) (movR64R64Effect 0x1197ac 6 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 73) (.out 0x1197af (movR64M64Effect 0x1197af 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 74) (.exec 0x1197af (LoadPre 0x1197af (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1197af + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1197af 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x1197b7 (mulR64Effect 0x1197b7 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[61, 73]
    (.letOp (n := 76) (.out 0x1197b7 (mulR64Effect 0x1197b7 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[61, 73]
    (.letOp (n := 77) (.exec 0x1197b7 (fun s => s.RIP = 0x1197b7) (mulR64Effect 0x1197b7 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[61, 73]
    (.letOp (n := 78) (.exec 0x1197ba (StorePre 0x1197ba 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1197ba + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1197ba 14 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 79) (.out 0x1197bf (movR64R64Effect 0x1197bf 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[76]
    (.letOp (n := 80) (.exec 0x1197bf (fun s => s.RIP = 0x1197bf) (movR64R64Effect 0x1197bf 7 2) (Reg.operands [.gpr 2] [])) #v[76]
    (.letOp (n := 81) (.out 0x1197c2 (movR64R64Effect 0x1197c2 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[75]
    (.letOp (n := 82) (.exec 0x1197c2 (fun s => s.RIP = 0x1197c2) (movR64R64Effect 0x1197c2 8 0) (Reg.operands [.gpr 0] [])) #v[75]
    (.letOp (n := 83) (.out 0x1197c5 (addR64R64Effect 0x1197c5 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[81, 71]
    (.letOp (n := 84) (.out 0x1197c5 (addR64R64Effect 0x1197c5 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[81, 71]
    (.letOp (n := 85) (.exec 0x1197c5 (fun s => s.RIP = 0x1197c5) (addR64R64Effect 0x1197c5 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[81, 71]
    (.letOp (n := 86) (.out 0x1197c8 (atFlags StatusFlags.CF (adcR64R64Effect 0x1197c8 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[79, 69, 84]
    (.letOp (n := 87) (.exec 0x1197c8 (fun s => s.RIP = 0x1197c8) (atFlags StatusFlags.CF (adcR64R64Effect 0x1197c8 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[79, 69, 84]
    (.letOp (n := 88) (.out 0x1197cb (movR64M64Effect 0x1197cb 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 89) (.exec 0x1197cb (LoadPre 0x1197cb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1197cb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1197cb 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x1197d3 (mulR64Effect 0x1197d3 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[57, 88]
    (.letOp (n := 91) (.out 0x1197d3 (mulR64Effect 0x1197d3 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[57, 88]
    (.letOp (n := 92) (.exec 0x1197d3 (fun s => s.RIP = 0x1197d3) (mulR64Effect 0x1197d3 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[57, 88]
    (.letOp (n := 93) (.exec 0x1197d6 (StorePre 0x1197d6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1197d6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1197d6 13 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[57, 4]
    (b_l119780_1)))))))))))))))))))))))))))))))))))))))))

def bytes_l119780 : List UInt8 :=
  [0x48, 0x8B, 0x6C, 0x24, 0x48, 0x4C, 0x8B, 0x7C, 0x24, 0x40, 0x4C, 0x8B, 0x6C, 0x24, 0x38, 0x4C,
    0x8B, 0x64, 0x24, 0x28, 0x4C, 0x8B, 0x74, 0x24, 0x30, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x49, 0xF7,
    0xE4, 0x4C, 0x89, 0xA4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x48,
    0x8B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE6, 0x4C, 0x89, 0x74, 0x24, 0x50, 0x48,
    0x89, 0xD7, 0x49, 0x89, 0xC0, 0x49, 0x01, 0xF0, 0x48, 0x11, 0xCF, 0x48, 0x8B, 0x84, 0x24, 0xC0,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x4C, 0x89, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00] ++ bytes_l119780_1

theorem code_l119780 : ∀ x ∈ codeRange 0x119780 bytes_l119780, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19780 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119780_1

@[cfg_block] def b_l119b94 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119b94 (movR64M64Effect 0x119b94 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119b94 (LoadPre 0x119b94 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119b94 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119b94 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119b99 (StorePre 0x119b99 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119b99 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119b99 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119b9e (movR64M64Effect 0x119b9e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119b9e (LoadPre 0x119b9e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119b9e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119b9e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119ba3 (StorePre 0x119ba3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119ba3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119ba3 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119ba8 (movR64M64Effect 0x119ba8 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119ba8 (LoadPre 0x119ba8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119ba8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119ba8 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119bad (StorePre 0x119bad 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119bad + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119bad 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119bb2 (movR64M64Effect 0x119bb2 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119bb2 (LoadPre 0x119bb2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119bb2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119bb2 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x119bb7 (movR64M64Effect 0x119bb7 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x119bb7 (LoadPre 0x119bb7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119bb7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119bb7 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119bbc (StorePre 0x119bbc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119bbc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119bbc 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119bc1 (StorePre 0x119bc1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119bc1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119bc1 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119bc5 (movR64R64Effect 0x119bc5 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119bc5 (fun s => s.RIP = 0x119bc5) (movR64R64Effect 0x119bc5 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119bc8 (movR64R64Effect 0x119bc8 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119bc8 (fun s => s.RIP = 0x119bc8) (movR64R64Effect 0x119bc8 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119bcb (callEffect (fun _ => 0x1145f0) 0x119bd0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119bcb (PushPre 0x119bcb 5) (callEffect (fun _ => 0x1145f0) 0x119bd0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119bd0⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119bd0, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119b94 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x20, 0xAA, 0xFF, 0xFF]

theorem code_l119b94 : ∀ x ∈ codeRange 0x119b94 bytes_l119b94, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19b94 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119bd0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119bd0 (movR64M64Effect 0x119bd0 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119bd0 (LoadPre 0x119bd0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119bd0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119bd0 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119bd5 (StorePre 0x119bd5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119bd5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119bd5 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119bda (movR64M64Effect 0x119bda 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119bda (LoadPre 0x119bda (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119bda + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119bda 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119bdf (StorePre 0x119bdf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119bdf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119bdf 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119be4 (movR64M64Effect 0x119be4 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119be4 (LoadPre 0x119be4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119be4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119be4 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119be9 (StorePre 0x119be9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119be9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119be9 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119bee (movR64M64Effect 0x119bee 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119bee (LoadPre 0x119bee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119bee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119bee 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x119bf3 (movR64M64Effect 0x119bf3 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x119bf3 (LoadPre 0x119bf3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119bf3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119bf3 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119bf8 (StorePre 0x119bf8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119bf8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119bf8 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119bfd (StorePre 0x119bfd 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119bfd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119bfd 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119c01 (movR64R64Effect 0x119c01 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119c01 (fun s => s.RIP = 0x119c01) (movR64R64Effect 0x119c01 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119c04 (movR64R64Effect 0x119c04 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119c04 (fun s => s.RIP = 0x119c04) (movR64R64Effect 0x119c04 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119c07 (callEffect (fun _ => 0x1145f0) 0x119c0c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119c07 (PushPre 0x119c07 5) (callEffect (fun _ => 0x1145f0) 0x119c0c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119c0c⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119c0c, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119bd0 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xE4, 0xA9, 0xFF, 0xFF]

theorem code_l119bd0 : ∀ x ∈ codeRange 0x119bd0 bytes_l119bd0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19bd0 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119c0c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119c0c (movR64M64Effect 0x119c0c 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119c0c (LoadPre 0x119c0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119c0c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119c0c 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119c11 (StorePre 0x119c11 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119c11 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119c11 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119c16 (movR64M64Effect 0x119c16 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119c16 (LoadPre 0x119c16 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119c16 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119c16 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119c1b (StorePre 0x119c1b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119c1b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119c1b 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119c20 (movR64M64Effect 0x119c20 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119c20 (LoadPre 0x119c20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119c20 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119c20 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119c25 (StorePre 0x119c25 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119c25 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119c25 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119c2a (movR64M64Effect 0x119c2a 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119c2a (LoadPre 0x119c2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119c2a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119c2a 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x119c2f (movR64M64Effect 0x119c2f 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x119c2f (LoadPre 0x119c2f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119c2f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119c2f 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119c34 (StorePre 0x119c34 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119c34 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119c34 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119c39 (StorePre 0x119c39 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119c39 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119c39 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119c3d (movR64R64Effect 0x119c3d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119c3d (fun s => s.RIP = 0x119c3d) (movR64R64Effect 0x119c3d 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119c40 (movR64R64Effect 0x119c40 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119c40 (fun s => s.RIP = 0x119c40) (movR64R64Effect 0x119c40 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119c43 (callEffect (fun _ => 0x1145f0) 0x119c48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119c43 (PushPre 0x119c43 5) (callEffect (fun _ => 0x1145f0) 0x119c48) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119c48⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119c48, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119c0c : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xA8, 0xA9, 0xFF, 0xFF]

theorem code_l119c0c : ∀ x ∈ codeRange 0x119c0c bytes_l119c0c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19c0c 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119c48 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119c48 (movR64M64Effect 0x119c48 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119c48 (LoadPre 0x119c48 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119c48 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119c48 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119c4d (StorePre 0x119c4d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119c4d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119c4d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119c52 (movR64M64Effect 0x119c52 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119c52 (LoadPre 0x119c52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119c52 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119c52 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119c57 (StorePre 0x119c57 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119c57 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119c57 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119c5c (movR64M64Effect 0x119c5c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119c5c (LoadPre 0x119c5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119c5c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119c5c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119c61 (StorePre 0x119c61 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119c61 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119c61 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119c66 (movR64M64Effect 0x119c66 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119c66 (LoadPre 0x119c66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119c66 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119c66 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x119c6b (movR64M64Effect 0x119c6b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x119c6b (LoadPre 0x119c6b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119c6b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119c6b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119c70 (StorePre 0x119c70 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119c70 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119c70 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119c75 (StorePre 0x119c75 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119c75 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119c75 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119c79 (movR64R64Effect 0x119c79 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119c79 (fun s => s.RIP = 0x119c79) (movR64R64Effect 0x119c79 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119c7c (movR64R64Effect 0x119c7c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119c7c (fun s => s.RIP = 0x119c7c) (movR64R64Effect 0x119c7c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119c7f (callEffect (fun _ => 0x1145f0) 0x119c84) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119c7f (PushPre 0x119c7f 5) (callEffect (fun _ => 0x1145f0) 0x119c84) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119c84⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119c84, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119c48 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x6C, 0xA9, 0xFF, 0xFF]

theorem code_l119c48 : ∀ x ∈ codeRange 0x119c48 bytes_l119c48, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19c48 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119c84 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119c84 (movR64M64Effect 0x119c84 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119c84 (LoadPre 0x119c84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119c84 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119c84 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119c89 (StorePre 0x119c89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119c89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119c89 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119c8e (movR64M64Effect 0x119c8e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119c8e (LoadPre 0x119c8e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119c8e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119c8e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119c93 (StorePre 0x119c93 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119c93 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119c93 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119c98 (movR64M64Effect 0x119c98 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119c98 (LoadPre 0x119c98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119c98 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119c98 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119c9d (StorePre 0x119c9d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119c9d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119c9d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119ca2 (movR64M64Effect 0x119ca2 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119ca2 (LoadPre 0x119ca2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119ca2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119ca2 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x119ca7 (movR64M64Effect 0x119ca7 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x119ca7 (LoadPre 0x119ca7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119ca7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119ca7 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119cac (StorePre 0x119cac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119cac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119cac 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119cb1 (StorePre 0x119cb1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119cb1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119cb1 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119cb5 (movR64R64Effect 0x119cb5 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119cb5 (fun s => s.RIP = 0x119cb5) (movR64R64Effect 0x119cb5 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119cb8 (movR64R64Effect 0x119cb8 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119cb8 (fun s => s.RIP = 0x119cb8) (movR64R64Effect 0x119cb8 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119cbb (callEffect (fun _ => 0x1145f0) 0x119cc0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119cbb (PushPre 0x119cbb 5) (callEffect (fun _ => 0x1145f0) 0x119cc0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119cc0⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119cc0, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119c84 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x30, 0xA9, 0xFF, 0xFF]

theorem code_l119c84 : ∀ x ∈ codeRange 0x119c84 bytes_l119c84, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19c84 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l119cc0_12 : Block Op Label signature Reg.count 570 :=
  .letOp (n := 570) (.out 0x11a10b (callEffect (fun _ => 0x1145f0) 0x11a110) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 571) (.exec 0x11a10b (PushPre 0x11a10b 5) (callEffect (fun _ => 0x1145f0) 0x11a110) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 572) (.const ⟨64, 0x11a110⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 549), (1, 558), (2, 547), (3, 562), (4, 570), (5, 484), (6, 568), (7, 566), (8, 457), (9, 431), (10, 531), (11, 491), (12, 495), (13, 454), (14, 564), (15, 372), (22, 22), (39, 39), (50, 50), (51, 51)] 573⟩ { target := .l11a110, kept := #v[], arity := rfl, guard := some (Fin.last 572) }))))

def bytes_l119cc0_12 : List UInt8 :=
  [0xE8, 0xE0, 0xA4, 0xFF, 0xFF]

theorem code_l119cc0_12 : ∀ x ∈ codeRange 0x11a10b bytes_l119cc0_12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1a10b 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l119cc0_11 : Block Op Label signature Reg.count 533 :=
  .letOp (n := 533) (.out 0x11a0b7 (movR64M64Effect 0x11a0b7 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 534) (.exec 0x11a0b7 (LoadPre 0x11a0b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11a0b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11a0b7 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 535) (.out 0x11a0bc (andR64R64Effect 0x11a0bc 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[533, 491]
    (.letOp (n := 536) (.exec 0x11a0bc (fun s => s.RIP = 0x11a0bc) (andR64R64Effect 0x11a0bc 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[533, 491]
    (.letOp (n := 537) (.out 0x11a0bf (addR64R64Effect 0x11a0bf 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[535, 528]
    (.letOp (n := 538) (.out 0x11a0bf (addR64R64Effect 0x11a0bf 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[535, 528]
    (.letOp (n := 539) (.exec 0x11a0bf (fun s => s.RIP = 0x11a0bf) (addR64R64Effect 0x11a0bf 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[535, 528]
    (.letOp (n := 540) (.out 0x11a0c2 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a0c2 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[529, 538]
    (.letOp (n := 541) (.exec 0x11a0c2 (fun s => s.RIP = 0x11a0c2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a0c2 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[529, 538]
    (.letOp (n := 542) (.out 0x11a0c6 (addR64R64Effect 0x11a0c6 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[537, 523]
    (.letOp (n := 543) (.out 0x11a0c6 (addR64R64Effect 0x11a0c6 1 3) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 3] []) (.flag .CF)) #v[537, 523]
    (.letOp (n := 544) (.exec 0x11a0c6 (fun s => s.RIP = 0x11a0c6) (addR64R64Effect 0x11a0c6 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[537, 523]
    (.letOp (n := 545) (.out 0x11a0c9 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a0c9 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[540, 543]
    (.letOp (n := 546) (.exec 0x11a0c9 (fun s => s.RIP = 0x11a0c9) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a0c9 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[540, 543]
    (.letOp (n := 547) (.out 0x11a0cd (shldR64R64Effect 0x11a0cd 5 2 1 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[545, 542]
    (.letOp (n := 548) (.exec 0x11a0cd (fun s => s.RIP = 0x11a0cd) (shldR64R64Effect 0x11a0cd 5 2 1 12) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[545, 542]
    (.letOp (n := 549) (.out 0x11a0d2 (movR64Imm64Effect 0x11a0d2 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 550) (.exec 0x11a0d2 (fun s => s.RIP = 0x11a0d2) (movR64Imm64Effect 0x11a0d2 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 551) (.out 0x11a0dc (andR64R64Effect 0x11a0dc 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[239, 549]
    (.letOp (n := 552) (.exec 0x11a0dc (fun s => s.RIP = 0x11a0dc) (andR64R64Effect 0x11a0dc 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[239, 549]
    (.letOp (n := 553) (.out 0x11a0df (addR64R64Effect 0x11a0df 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[551, 547]
    (.letOp (n := 554) (.exec 0x11a0df (fun s => s.RIP = 0x11a0df) (addR64R64Effect 0x11a0df 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[551, 547]
    (.letOp (n := 555) (.exec 0x11a0e2 (StorePre 0x11a0e2 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11a0e2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11a0e2 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 15, .gpr 4] [])) #v[372, 4]
    (.letOp (n := 556) (.exec 0x11a0e6 (StorePre 0x11a0e6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11a0e6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a0e6 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[457, 4]
    (.letOp (n := 557) (.exec 0x11a0eb (StorePre 0x11a0eb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11a0eb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a0eb 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[531, 4]
    (.letOp (n := 558) (.out 0x11a0f0 (andR64R64Effect 0x11a0f0 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[542, 491]
    (.letOp (n := 559) (.exec 0x11a0f0 (fun s => s.RIP = 0x11a0f0) (andR64R64Effect 0x11a0f0 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[542, 491]
    (.letOp (n := 560) (.exec 0x11a0f3 (StorePre 0x11a0f3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11a0f3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a0f3 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[558, 4]
    (.letOp (n := 561) (.exec 0x11a0f8 (StorePre 0x11a0f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11a0f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a0f8 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[553, 4]
    (.letOp (n := 562) (.out 0x11a0fd (leaR64Effect 0x11a0fd 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 563) (.exec 0x11a0fd (fun s => s.RIP = 0x11a0fd) (leaR64Effect 0x11a0fd 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 564) (.out 0x11a102 (movR64R64Effect 0x11a102 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 565) (.exec 0x11a102 (fun s => s.RIP = 0x11a102) (movR64R64Effect 0x11a102 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 566) (.out 0x11a105 (movR64R64Effect 0x11a105 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[562]
    (.letOp (n := 567) (.exec 0x11a105 (fun s => s.RIP = 0x11a105) (movR64R64Effect 0x11a105 7 3) (Reg.operands [.gpr 3] [])) #v[562]
    (.letOp (n := 568) (.out 0x11a108 (movR64R64Effect 0x11a108 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[564]
    (.letOp (n := 569) (.exec 0x11a108 (fun s => s.RIP = 0x11a108) (movR64R64Effect 0x11a108 6 14) (Reg.operands [.gpr 14] [])) #v[564]
    (b_l119cc0_12)))))))))))))))))))))))))))))))))))))

def bytes_l119cc0_11 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x50, 0x4C, 0x21, 0xD9, 0x48, 0x01, 0xC1, 0x48, 0x83, 0xD2, 0x00, 0x48,
    0x01, 0xD9, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x0F, 0xA4, 0xCA, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x21, 0xC6, 0x48, 0x01, 0xD6, 0x4C, 0x89, 0x3C, 0x24, 0x4C,
    0x89, 0x44, 0x24, 0x08, 0x4C, 0x89, 0x54, 0x24, 0x10, 0x4C, 0x21, 0xD9, 0x48, 0x89, 0x4C, 0x24,
    0x18, 0x48, 0x89, 0x74, 0x24, 0x20, 0x48, 0x8D, 0x5C, 0x24, 0x28, 0x49, 0x89, 0xE6, 0x48, 0x89,
    0xDF, 0x4C, 0x89, 0xF6] ++ bytes_l119cc0_12

theorem code_l119cc0_11 : ∀ x ∈ codeRange 0x11a0b7 bytes_l119cc0_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a0b7 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119cc0_12

def b_l119cc0_10 : Block Op Label signature Reg.count 489 :=
  .letOp (n := 489) (.out 0x11a058 (movR64R64Effect 0x11a058 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[484]
    (.letOp (n := 490) (.exec 0x11a058 (fun s => s.RIP = 0x11a058) (movR64R64Effect 0x11a058 0 5) (Reg.operands [.gpr 5] [])) #v[484]
    (.letOp (n := 491) (.out 0x11a05b (movR64Imm64Effect 0x11a05b 11 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 492) (.exec 0x11a05b (fun s => s.RIP = 0x11a05b) (movR64Imm64Effect 0x11a05b 11 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 493) (.out 0x11a065 (andR64R64Effect 0x11a065 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[489, 491]
    (.letOp (n := 494) (.exec 0x11a065 (fun s => s.RIP = 0x11a065) (andR64R64Effect 0x11a065 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[489, 491]
    (.letOp (n := 495) (.out 0x11a068 (movR64Imm64Effect 0x11a068 12 0x1000003d10) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 496) (.exec 0x11a068 (fun s => s.RIP = 0x11a068) (movR64Imm64Effect 0x11a068 12 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 497) (.out 0x11a072 (mulR64Effect 0x11a072 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[495, 493]
    (.letOp (n := 498) (.out 0x11a072 (mulR64Effect 0x11a072 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[495, 493]
    (.letOp (n := 499) (.exec 0x11a072 (fun s => s.RIP = 0x11a072) (mulR64Effect 0x11a072 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[495, 493]
    (.letOp (n := 500) (.out 0x11a075 (addR64M64Effect 0x11a075 10 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[447, 4]
    (.letOp (n := 501) (.out 0x11a075 (addR64M64Effect 0x11a075 10 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[447, 4]
    (.letOp (n := 502) (.exec 0x11a075 (LoadPre 0x11a075 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11a075 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11a075 10 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[447, 4]
    (.letOp (n := 503) (.out 0x11a07a (atFlags StatusFlags.CF (adcR64M64Effect 0x11a07a 3 (.sib 4 none 0 (.d32 0xa0)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[445, 4, 501]
    (.letOp (n := 504) (.exec 0x11a07a (LoadPre 0x11a07a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11a07a + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11a07a 3 (.sib 4 none 0 (.d32 0xa0)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[445, 4, 501]
    (.letOp (n := 505) (.out 0x11a082 (addR64R64Effect 0x11a082 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[500, 454]
    (.letOp (n := 506) (.out 0x11a082 (addR64R64Effect 0x11a082 10 13) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 13] []) (.flag .CF)) #v[500, 454]
    (.letOp (n := 507) (.exec 0x11a082 (fun s => s.RIP = 0x11a082) (addR64R64Effect 0x11a082 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[500, 454]
    (.letOp (n := 508) (.out 0x11a085 (atFlags StatusFlags.CF (adcR64M64Effect 0x11a085 3 (.sib 4 none 0 (.d32 0x90)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[503, 4, 506]
    (.letOp (n := 509) (.exec 0x11a085 (LoadPre 0x11a085 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11a085 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11a085 3 (.sib 4 none 0 (.d32 0x90)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[503, 4, 506]
    (.letOp (n := 510) (.out 0x11a08d (addR64R64Effect 0x11a08d 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[505, 497]
    (.letOp (n := 511) (.out 0x11a08d (addR64R64Effect 0x11a08d 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[505, 497]
    (.letOp (n := 512) (.exec 0x11a08d (fun s => s.RIP = 0x11a08d) (addR64R64Effect 0x11a08d 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[505, 497]
    (.letOp (n := 513) (.out 0x11a090 (atFlags StatusFlags.CF (adcR64R64Effect 0x11a090 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[508, 498, 511]
    (.letOp (n := 514) (.exec 0x11a090 (fun s => s.RIP = 0x11a090) (atFlags StatusFlags.CF (adcR64R64Effect 0x11a090 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[508, 498, 511]
    (.letOp (n := 515) (.exec 0x11a093 (StorePre 0x11a093 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11a093 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a093 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[472, 4]
    (.letOp (n := 516) (.out 0x11a098 (addR64R64Effect 0x11a098 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[510, 431]
    (.letOp (n := 517) (.out 0x11a098 (addR64R64Effect 0x11a098 10 9) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 9] []) (.flag .CF)) #v[510, 431]
    (.letOp (n := 518) (.exec 0x11a098 (fun s => s.RIP = 0x11a098) (addR64R64Effect 0x11a098 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[510, 431]
    (.letOp (n := 519) (.out 0x11a09b (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a09b 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[513, 517]
    (.letOp (n := 520) (.exec 0x11a09b (fun s => s.RIP = 0x11a09b) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a09b 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[513, 517]
    (.letOp (n := 521) (.out 0x11a09f (shldR64R64Effect 0x11a09f 5 14 5 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[487, 484]
    (.letOp (n := 522) (.exec 0x11a09f (fun s => s.RIP = 0x11a09f) (shldR64R64Effect 0x11a09f 5 14 5 12) (Reg.operands [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[487, 484]
    (.letOp (n := 523) (.out 0x11a0a4 (shldR64R64Effect 0x11a0a4 5 3 10 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[519, 516]
    (.letOp (n := 524) (.exec 0x11a0a4 (fun s => s.RIP = 0x11a0a4) (shldR64R64Effect 0x11a0a4 5 3 10 12) (Reg.operands [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[519, 516]
    (.letOp (n := 525) (.exec 0x11a0a9 (StorePre 0x11a0a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11a0a9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a0a9 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[461, 4]
    (.letOp (n := 526) (.out 0x11a0ae (movR64R64Effect 0x11a0ae 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[521]
    (.letOp (n := 527) (.exec 0x11a0ae (fun s => s.RIP = 0x11a0ae) (movR64R64Effect 0x11a0ae 0 14) (Reg.operands [.gpr 14] [])) #v[521]
    (.letOp (n := 528) (.out 0x11a0b1 (mulR64Effect 0x11a0b1 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[495, 526]
    (.letOp (n := 529) (.out 0x11a0b1 (mulR64Effect 0x11a0b1 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[495, 526]
    (.letOp (n := 530) (.exec 0x11a0b1 (fun s => s.RIP = 0x11a0b1) (mulR64Effect 0x11a0b1 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[495, 526]
    (.letOp (n := 531) (.out 0x11a0b4 (andR64R64Effect 0x11a0b4 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[516, 491]
    (.letOp (n := 532) (.exec 0x11a0b4 (fun s => s.RIP = 0x11a0b4) (andR64R64Effect 0x11a0b4 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[516, 491]
    (b_l119cc0_11))))))))))))))))))))))))))))))))))))))))))))

def bytes_l119cc0_10 : List UInt8 :=
  [0x48, 0x89, 0xE8, 0x49, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xD8,
    0x49, 0xBC, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE4, 0x4C, 0x03, 0x54,
    0x24, 0x70, 0x48, 0x13, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xEA, 0x48, 0x13, 0x9C,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC2, 0x48, 0x11, 0xD3, 0x48, 0x89, 0x4C, 0x24, 0x20,
    0x4D, 0x01, 0xCA, 0x48, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xEE, 0x0C, 0x4C, 0x0F, 0xA4, 0xD3,
    0x0C, 0x48, 0x89, 0x7C, 0x24, 0x18, 0x4C, 0x89, 0xF0, 0x49, 0xF7, 0xE4, 0x4D, 0x21, 0xDA] ++ bytes_l119cc0_11

theorem code_l119cc0_10 : ∀ x ∈ codeRange 0x11a058 bytes_l119cc0_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a058 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119cc0_11

def b_l119cc0_9 : Block Op Label signature Reg.count 445 :=
  .letOp (n := 445) (.out 0x119ff8 (movR64R64Effect 0x119ff8 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[443]
    (.letOp (n := 446) (.exec 0x119ff8 (fun s => s.RIP = 0x119ff8) (movR64R64Effect 0x119ff8 3 2) (Reg.operands [.gpr 2] [])) #v[443]
    (.letOp (n := 447) (.out 0x119ffb (movR64R64Effect 0x119ffb 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[442]
    (.letOp (n := 448) (.exec 0x119ffb (fun s => s.RIP = 0x119ffb) (movR64R64Effect 0x119ffb 10 0) (Reg.operands [.gpr 0] [])) #v[442]
    (.letOp (n := 449) (.out 0x119ffe (movR64M64Effect 0x119ffe 0 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 450) (.exec 0x119ffe (LoadPre 0x119ffe (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x119ffe + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119ffe 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 451) (.out 0x11a006 (mulM64Effect 0x11a006 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[449, 4]
    (.letOp (n := 452) (.out 0x11a006 (mulM64Effect 0x11a006 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[449, 4]
    (.letOp (n := 453) (.exec 0x11a006 (LoadPre 0x11a006 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11a006 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11a006 8 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[449, 4]
    (.letOp (n := 454) (.out 0x11a00e (movR64R64Effect 0x11a00e 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[451]
    (.letOp (n := 455) (.exec 0x11a00e (fun s => s.RIP = 0x11a00e) (movR64R64Effect 0x11a00e 13 0) (Reg.operands [.gpr 0] [])) #v[451]
    (.letOp (n := 456) (.exec 0x11a011 (StorePre 0x11a011 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11a011 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11a011 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[452, 4]
    (.letOp (n := 457) (.out 0x11a019 (andR64R64Effect 0x11a019 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[426, 409]
    (.letOp (n := 458) (.exec 0x11a019 (fun s => s.RIP = 0x11a019) (andR64R64Effect 0x11a019 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[426, 409]
    (.letOp (n := 459) (.out 0x11a01c (movR64M64Effect 0x11a01c 0 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 460) (.exec 0x11a01c (LoadPre 0x11a01c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11a01c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a01c 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 461) (.out 0x11a024 (movR64M64Effect 0x11a024 7 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 462) (.exec 0x11a024 (LoadPre 0x11a024 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11a024 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a024 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 463) (.out 0x11a02c (mulR64Effect 0x11a02c 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[461, 459]
    (.letOp (n := 464) (.out 0x11a02c (mulR64Effect 0x11a02c 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[461, 459]
    (.letOp (n := 465) (.exec 0x11a02c (fun s => s.RIP = 0x11a02c) (mulR64Effect 0x11a02c 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[461, 459]
    (.letOp (n := 466) (.out 0x11a02f (movR64R64Effect 0x11a02f 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[464]
    (.letOp (n := 467) (.exec 0x11a02f (fun s => s.RIP = 0x11a02f) (movR64R64Effect 0x11a02f 14 2) (Reg.operands [.gpr 2] [])) #v[464]
    (.letOp (n := 468) (.out 0x11a032 (movR64R64Effect 0x11a032 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[463]
    (.letOp (n := 469) (.exec 0x11a032 (fun s => s.RIP = 0x11a032) (movR64R64Effect 0x11a032 12 0) (Reg.operands [.gpr 0] [])) #v[463]
    (.letOp (n := 470) (.out 0x11a035 (movR64M64Effect 0x11a035 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 471) (.exec 0x11a035 (LoadPre 0x11a035 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x11a035 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a035 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 472) (.out 0x11a03d (movR64M64Effect 0x11a03d 1 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 473) (.exec 0x11a03d (LoadPre 0x11a03d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11a03d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a03d 1 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 474) (.out 0x11a045 (mulR64Effect 0x11a045 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[472, 470]
    (.letOp (n := 475) (.out 0x11a045 (mulR64Effect 0x11a045 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[472, 470]
    (.letOp (n := 476) (.exec 0x11a045 (fun s => s.RIP = 0x11a045) (mulR64Effect 0x11a045 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[472, 470]
    (.letOp (n := 477) (.out 0x11a048 (movR64R64Effect 0x11a048 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[474]
    (.letOp (n := 478) (.exec 0x11a048 (fun s => s.RIP = 0x11a048) (movR64R64Effect 0x11a048 5 0) (Reg.operands [.gpr 0] [])) #v[474]
    (.letOp (n := 479) (.out 0x11a04b (addR64R64Effect 0x11a04b 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[477, 468]
    (.letOp (n := 480) (.out 0x11a04b (addR64R64Effect 0x11a04b 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[477, 468]
    (.letOp (n := 481) (.exec 0x11a04b (fun s => s.RIP = 0x11a04b) (addR64R64Effect 0x11a04b 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[477, 468]
    (.letOp (n := 482) (.out 0x11a04e (atFlags StatusFlags.CF (adcR64R64Effect 0x11a04e 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[466, 475, 480]
    (.letOp (n := 483) (.exec 0x11a04e (fun s => s.RIP = 0x11a04e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11a04e 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[466, 475, 480]
    (.letOp (n := 484) (.out 0x11a051 (addR64R64Effect 0x11a051 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[479, 405]
    (.letOp (n := 485) (.out 0x11a051 (addR64R64Effect 0x11a051 5 11) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 11] []) (.flag .CF)) #v[479, 405]
    (.letOp (n := 486) (.exec 0x11a051 (fun s => s.RIP = 0x11a051) (addR64R64Effect 0x11a051 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[479, 405]
    (.letOp (n := 487) (.out 0x11a054 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a054 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[482, 485]
    (.letOp (n := 488) (.exec 0x11a054 (fun s => s.RIP = 0x11a054) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a054 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[482, 485]
    (b_l119cc0_10))))))))))))))))))))))))))))))))))))))))))))

def bytes_l119cc0_9 : List UInt8 :=
  [0x48, 0x89, 0xD3, 0x49, 0x89, 0xC2, 0x48, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xA4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC5, 0x48, 0x89, 0x94, 0x24, 0x90, 0x00, 0x00,
    0x00, 0x4D, 0x21, 0xE0, 0x48, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xBC, 0x24,
    0xB0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x84,
    0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1,
    0x48, 0x89, 0xC5, 0x4C, 0x01, 0xE5, 0x49, 0x11, 0xD6, 0x4C, 0x01, 0xDD, 0x49, 0x83, 0xD6, 0x00] ++ bytes_l119cc0_10

theorem code_l119cc0_9 : ∀ x ∈ codeRange 0x119ff8 bytes_l119cc0_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19ff8 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119cc0_10

def b_l119cc0_8 : Block Op Label signature Reg.count 400 :=
  .letOp (n := 400) (.out 0x119f9a (addR64R64Effect 0x119f9a 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[395, 317]
    (.letOp (n := 401) (.out 0x119f9a (addR64R64Effect 0x119f9a 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[395, 317]
    (.letOp (n := 402) (.exec 0x119f9a (fun s => s.RIP = 0x119f9a) (addR64R64Effect 0x119f9a 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[395, 317]
    (.letOp (n := 403) (.out 0x119f9d (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119f9d 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[398, 401]
    (.letOp (n := 404) (.exec 0x119f9d (fun s => s.RIP = 0x119f9d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119f9d 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[398, 401]
    (.letOp (n := 405) (.out 0x119fa1 (shldR64R64Effect 0x119fa1 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[403, 400]
    (.letOp (n := 406) (.exec 0x119fa1 (fun s => s.RIP = 0x119fa1) (shldR64R64Effect 0x119fa1 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[403, 400]
    (.letOp (n := 407) (.out 0x119fa6 (andR64R64Effect 0x119fa6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[400, 370]
    (.letOp (n := 408) (.exec 0x119fa6 (fun s => s.RIP = 0x119fa6) (andR64R64Effect 0x119fa6 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[400, 370]
    (.letOp (n := 409) (.out 0x119fa9 (movR64R64Effect 0x119fa9 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[370]
    (.letOp (n := 410) (.exec 0x119fa9 (fun s => s.RIP = 0x119fa9) (movR64R64Effect 0x119fa9 12 1) (Reg.operands [.gpr 1] [])) #v[370]
    (.letOp (n := 411) (.out 0x119fac (movR64Imm64Effect 0x119fac 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 412) (.exec 0x119fac (fun s => s.RIP = 0x119fac) (movR64Imm64Effect 0x119fac 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 413) (.out 0x119fb6 (mulR64Effect 0x119fb6 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[411, 407]
    (.letOp (n := 414) (.out 0x119fb6 (mulR64Effect 0x119fb6 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[411, 407]
    (.letOp (n := 415) (.exec 0x119fb6 (fun s => s.RIP = 0x119fb6) (mulR64Effect 0x119fb6 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[411, 407]
    (.letOp (n := 416) (.out 0x119fb9 (addR64M64Effect 0x119fb9 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[359, 4]
    (.letOp (n := 417) (.out 0x119fb9 (addR64M64Effect 0x119fb9 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[359, 4]
    (.letOp (n := 418) (.exec 0x119fb9 (LoadPre 0x119fb9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x119fb9 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x119fb9 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[359, 4]
    (.letOp (n := 419) (.out 0x119fc1 (atFlags StatusFlags.CF (adcR64M64Effect 0x119fc1 9 (.sib 4 none 0 (.d8 0x70)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[357, 4, 417]
    (.letOp (n := 420) (.exec 0x119fc1 (LoadPre 0x119fc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x119fc1 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x119fc1 9 (.sib 4 none 0 (.d8 0x70)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[357, 4, 417]
    (.letOp (n := 421) (.out 0x119fc6 (addR64R64Effect 0x119fc6 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[416, 413]
    (.letOp (n := 422) (.out 0x119fc6 (addR64R64Effect 0x119fc6 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[416, 413]
    (.letOp (n := 423) (.exec 0x119fc6 (fun s => s.RIP = 0x119fc6) (addR64R64Effect 0x119fc6 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[416, 413]
    (.letOp (n := 424) (.out 0x119fc9 (atFlags StatusFlags.CF (adcR64R64Effect 0x119fc9 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[419, 414, 422]
    (.letOp (n := 425) (.exec 0x119fc9 (fun s => s.RIP = 0x119fc9) (atFlags StatusFlags.CF (adcR64R64Effect 0x119fc9 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[419, 414, 422]
    (.letOp (n := 426) (.out 0x119fcc (addR64R64Effect 0x119fcc 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[421, 341]
    (.letOp (n := 427) (.out 0x119fcc (addR64R64Effect 0x119fcc 8 3) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 3] []) (.flag .CF)) #v[421, 341]
    (.letOp (n := 428) (.exec 0x119fcc (fun s => s.RIP = 0x119fcc) (addR64R64Effect 0x119fcc 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[421, 341]
    (.letOp (n := 429) (.out 0x119fcf (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119fcf 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[424, 427]
    (.letOp (n := 430) (.exec 0x119fcf (fun s => s.RIP = 0x119fcf) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119fcf 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[424, 427]
    (.letOp (n := 431) (.out 0x119fd3 (shldR64R64Effect 0x119fd3 5 9 8 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[429, 426]
    (.letOp (n := 432) (.exec 0x119fd3 (fun s => s.RIP = 0x119fd3) (shldR64R64Effect 0x119fd3 5 9 8 12) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[429, 426]
    (.letOp (n := 433) (.out 0x119fd8 (movR64R64Effect 0x119fd8 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[383]
    (.letOp (n := 434) (.exec 0x119fd8 (fun s => s.RIP = 0x119fd8) (movR64R64Effect 0x119fd8 0 7) (Reg.operands [.gpr 7] [])) #v[383]
    (.letOp (n := 435) (.out 0x119fdb (mulR64Effect 0x119fdb 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[345, 433]
    (.letOp (n := 436) (.out 0x119fdb (mulR64Effect 0x119fdb 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[345, 433]
    (.letOp (n := 437) (.exec 0x119fdb (fun s => s.RIP = 0x119fdb) (mulR64Effect 0x119fdb 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[345, 433]
    (.letOp (n := 438) (.exec 0x119fde (StorePre 0x119fde 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x119fde + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119fde 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[436, 4]
    (.letOp (n := 439) (.exec 0x119fe6 (StorePre 0x119fe6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x119fe6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119fe6 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[435, 4]
    (.letOp (n := 440) (.out 0x119feb (movR64M64Effect 0x119feb 0 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 441) (.exec 0x119feb (LoadPre 0x119feb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x119feb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119feb 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 442) (.out 0x119ff3 (mulM64Effect 0x119ff3 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[440, 4]
    (.letOp (n := 443) (.out 0x119ff3 (mulM64Effect 0x119ff3 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[440, 4]
    (.letOp (n := 444) (.exec 0x119ff3 (LoadPre 0x119ff3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x119ff3 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x119ff3 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[440, 4]
    (b_l119cc0_9)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l119cc0_8 : List UInt8 :=
  [0x4C, 0x01, 0xD0, 0x49, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0x21, 0xC8, 0x49,
    0x89, 0xCC, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x4C,
    0x03, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x4C, 0x24, 0x70, 0x49, 0x01, 0xC0, 0x49,
    0x11, 0xD1, 0x49, 0x01, 0xD8, 0x49, 0x83, 0xD1, 0x00, 0x4D, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89,
    0xF8, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24,
    0x70, 0x48, 0x8B, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x68] ++ bytes_l119cc0_9

theorem code_l119cc0_8 : ∀ x ∈ codeRange 0x119f9a bytes_l119cc0_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19f9a 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119cc0_9

def b_l119cc0_7 : Block Op Label signature Reg.count 354 :=
  .letOp (n := 354) (.out 0x119f3e (mulR64Effect 0x119f3e 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[259, 352]
    (.letOp (n := 355) (.out 0x119f3e (mulR64Effect 0x119f3e 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[259, 352]
    (.letOp (n := 356) (.exec 0x119f3e (fun s => s.RIP = 0x119f3e) (mulR64Effect 0x119f3e 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[259, 352]
    (.letOp (n := 357) (.out 0x119f41 (movR64R64Effect 0x119f41 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[355]
    (.letOp (n := 358) (.exec 0x119f41 (fun s => s.RIP = 0x119f41) (movR64R64Effect 0x119f41 9 2) (Reg.operands [.gpr 2] [])) #v[355]
    (.letOp (n := 359) (.out 0x119f44 (movR64R64Effect 0x119f44 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[354]
    (.letOp (n := 360) (.exec 0x119f44 (fun s => s.RIP = 0x119f44) (movR64R64Effect 0x119f44 8 0) (Reg.operands [.gpr 0] [])) #v[354]
    (.letOp (n := 361) (.out 0x119f47 (movR64M64Effect 0x119f47 0 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 362) (.exec 0x119f47 (LoadPre 0x119f47 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x119f47 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119f47 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 363) (.out 0x119f4f (mulM64Effect 0x119f4f 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[361, 4]
    (.letOp (n := 364) (.out 0x119f4f (mulM64Effect 0x119f4f 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[361, 4]
    (.letOp (n := 365) (.exec 0x119f4f (LoadPre 0x119f4f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x119f4f + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x119f4f 8 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[361, 4]
    (.letOp (n := 366) (.out 0x119f57 (movR64R64Effect 0x119f57 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[363]
    (.letOp (n := 367) (.exec 0x119f57 (fun s => s.RIP = 0x119f57) (movR64R64Effect 0x119f57 12 0) (Reg.operands [.gpr 0] [])) #v[363]
    (.letOp (n := 368) (.out 0x119f5a (movR64R64Effect 0x119f5a 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[364]
    (.letOp (n := 369) (.exec 0x119f5a (fun s => s.RIP = 0x119f5a) (movR64R64Effect 0x119f5a 13 2) (Reg.operands [.gpr 2] [])) #v[364]
    (.letOp (n := 370) (.out 0x119f5d (movR64Imm64Effect 0x119f5d 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 371) (.exec 0x119f5d (fun s => s.RIP = 0x119f5d) (movR64Imm64Effect 0x119f5d 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 372) (.out 0x119f67 (andR64R64Effect 0x119f67 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[336, 370]
    (.letOp (n := 373) (.exec 0x119f67 (fun s => s.RIP = 0x119f67) (andR64R64Effect 0x119f67 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[336, 370]
    (.letOp (n := 374) (.out 0x119f6a (movR64M64Effect 0x119f6a 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 375) (.exec 0x119f6a (LoadPre 0x119f6a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x119f6a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119f6a 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 376) (.out 0x119f72 (mulR64Effect 0x119f72 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[281, 374]
    (.letOp (n := 377) (.out 0x119f72 (mulR64Effect 0x119f72 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[281, 374]
    (.letOp (n := 378) (.exec 0x119f72 (fun s => s.RIP = 0x119f72) (mulR64Effect 0x119f72 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[281, 374]
    (.letOp (n := 379) (.out 0x119f75 (movR64R64Effect 0x119f75 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[377]
    (.letOp (n := 380) (.exec 0x119f75 (fun s => s.RIP = 0x119f75) (movR64R64Effect 0x119f75 11 2) (Reg.operands [.gpr 2] [])) #v[377]
    (.letOp (n := 381) (.out 0x119f78 (movR64R64Effect 0x119f78 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[376]
    (.letOp (n := 382) (.exec 0x119f78 (fun s => s.RIP = 0x119f78) (movR64R64Effect 0x119f78 5 0) (Reg.operands [.gpr 0] [])) #v[376]
    (.letOp (n := 383) (.out 0x119f7b (movR64M64Effect 0x119f7b 7 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 384) (.exec 0x119f7b (LoadPre 0x119f7b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x119f7b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119f7b 7 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 385) (.out 0x119f83 (movR64R64Effect 0x119f83 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[383]
    (.letOp (n := 386) (.exec 0x119f83 (fun s => s.RIP = 0x119f83) (movR64R64Effect 0x119f83 0 7) (Reg.operands [.gpr 7] [])) #v[383]
    (.letOp (n := 387) (.out 0x119f86 (mulM64Effect 0x119f86 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[385, 4]
    (.letOp (n := 388) (.out 0x119f86 (mulM64Effect 0x119f86 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[385, 4]
    (.letOp (n := 389) (.exec 0x119f86 (LoadPre 0x119f86 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x119f86 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x119f86 8 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[385, 4]
    (.letOp (n := 390) (.out 0x119f8e (addR64R64Effect 0x119f8e 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[381, 366]
    (.letOp (n := 391) (.out 0x119f8e (addR64R64Effect 0x119f8e 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[381, 366]
    (.letOp (n := 392) (.exec 0x119f8e (fun s => s.RIP = 0x119f8e) (addR64R64Effect 0x119f8e 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[381, 366]
    (.letOp (n := 393) (.out 0x119f91 (atFlags StatusFlags.CF (adcR64R64Effect 0x119f91 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[379, 368, 391]
    (.letOp (n := 394) (.exec 0x119f91 (fun s => s.RIP = 0x119f91) (atFlags StatusFlags.CF (adcR64R64Effect 0x119f91 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[379, 368, 391]
    (.letOp (n := 395) (.out 0x119f94 (addR64R64Effect 0x119f94 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[387, 390]
    (.letOp (n := 396) (.out 0x119f94 (addR64R64Effect 0x119f94 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[387, 390]
    (.letOp (n := 397) (.exec 0x119f94 (fun s => s.RIP = 0x119f94) (addR64R64Effect 0x119f94 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[387, 390]
    (.letOp (n := 398) (.out 0x119f97 (atFlags StatusFlags.CF (adcR64R64Effect 0x119f97 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[393, 388, 396]
    (.letOp (n := 399) (.exec 0x119f97 (fun s => s.RIP = 0x119f97) (atFlags StatusFlags.CF (adcR64R64Effect 0x119f97 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[393, 388, 396]
    (b_l119cc0_8))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l119cc0_7 : List UInt8 :=
  [0x49, 0xF7, 0xE1, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC0, 0x48, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00,
    0x00, 0x48, 0xF7, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD5, 0x48,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xCF, 0x48, 0x8B, 0x84, 0x24,
    0x00, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0xBC,
    0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0x4C, 0x01, 0xE5, 0x4D, 0x11, 0xEB, 0x48, 0x01, 0xE8, 0x49, 0x11, 0xD3] ++ bytes_l119cc0_8

theorem code_l119cc0_7 : ∀ x ∈ codeRange 0x119f3e bytes_l119cc0_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19f3e 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119cc0_8

def b_l119cc0_6 : Block Op Label signature Reg.count 312 :=
  .letOp (n := 312) (.out 0x119ed6 (addR64R64Effect 0x119ed6 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[307, 244]
    (.letOp (n := 313) (.out 0x119ed6 (addR64R64Effect 0x119ed6 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[307, 244]
    (.letOp (n := 314) (.exec 0x119ed6 (fun s => s.RIP = 0x119ed6) (addR64R64Effect 0x119ed6 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[307, 244]
    (.letOp (n := 315) (.out 0x119ed9 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119ed9 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[310, 313]
    (.letOp (n := 316) (.exec 0x119ed9 (fun s => s.RIP = 0x119ed9) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119ed9 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[310, 313]
    (.letOp (n := 317) (.out 0x119edd (shldR64R64Effect 0x119edd 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[315, 312]
    (.letOp (n := 318) (.exec 0x119edd (fun s => s.RIP = 0x119edd) (shldR64R64Effect 0x119edd 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[315, 312]
    (.letOp (n := 319) (.out 0x119ee2 (shlR64Effect 0x119ee2 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[312]
    (.letOp (n := 320) (.exec 0x119ee2 (fun s => s.RIP = 0x119ee2) (shlR64Effect 0x119ee2 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[312]
    (.letOp (n := 321) (.out 0x119ee6 (movR64Imm64Effect 0x119ee6 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 322) (.exec 0x119ee6 (fun s => s.RIP = 0x119ee6) (movR64Imm64Effect 0x119ee6 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 323) (.out 0x119ef0 (andR64R64Effect 0x119ef0 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[319, 321]
    (.letOp (n := 324) (.exec 0x119ef0 (fun s => s.RIP = 0x119ef0) (andR64R64Effect 0x119ef0 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[319, 321]
    (.letOp (n := 325) (.out 0x119ef3 (orR64R64Effect 0x119ef3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[323, 268]
    (.letOp (n := 326) (.exec 0x119ef3 (fun s => s.RIP = 0x119ef3) (orR64R64Effect 0x119ef3 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[323, 268]
    (.letOp (n := 327) (.out 0x119ef6 (movR64Imm64Effect 0x119ef6 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 328) (.exec 0x119ef6 (fun s => s.RIP = 0x119ef6) (movR64Imm64Effect 0x119ef6 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 329) (.out 0x119f00 (mulR64Effect 0x119f00 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[327, 325]
    (.letOp (n := 330) (.out 0x119f00 (mulR64Effect 0x119f00 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[327, 325]
    (.letOp (n := 331) (.exec 0x119f00 (fun s => s.RIP = 0x119f00) (mulR64Effect 0x119f00 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[327, 325]
    (.letOp (n := 332) (.out 0x119f03 (movR64R64Effect 0x119f03 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[330]
    (.letOp (n := 333) (.exec 0x119f03 (fun s => s.RIP = 0x119f03) (movR64R64Effect 0x119f03 3 2) (Reg.operands [.gpr 2] [])) #v[330]
    (.letOp (n := 334) (.out 0x119f06 (movR64R64Effect 0x119f06 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[329]
    (.letOp (n := 335) (.exec 0x119f06 (fun s => s.RIP = 0x119f06) (movR64R64Effect 0x119f06 15 0) (Reg.operands [.gpr 0] [])) #v[329]
    (.letOp (n := 336) (.out 0x119f09 (addR64M64Effect 0x119f09 15 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[334, 4]
    (.letOp (n := 337) (.out 0x119f09 (addR64M64Effect 0x119f09 15 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[334, 4]
    (.letOp (n := 338) (.exec 0x119f09 (LoadPre 0x119f09 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x119f09 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x119f09 15 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[334, 4]
    (.letOp (n := 339) (.out 0x119f11 (atFlags StatusFlags.CF (adcR64M64Effect 0x119f11 3 (.sib 4 none 0 (.d8 0x70)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[332, 4, 337]
    (.letOp (n := 340) (.exec 0x119f11 (LoadPre 0x119f11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x119f11 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x119f11 3 (.sib 4 none 0 (.d8 0x70)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[332, 4, 337]
    (.letOp (n := 341) (.out 0x119f16 (shldR64R64Effect 0x119f16 5 3 15 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[339, 336]
    (.letOp (n := 342) (.exec 0x119f16 (fun s => s.RIP = 0x119f16) (shldR64R64Effect 0x119f16 5 3 15 12) (Reg.operands [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[339, 336]
    (.letOp (n := 343) (.out 0x119f1b (movR64R64Effect 0x119f1b 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[290]
    (.letOp (n := 344) (.exec 0x119f1b (fun s => s.RIP = 0x119f1b) (movR64R64Effect 0x119f1b 0 8) (Reg.operands [.gpr 8] [])) #v[290]
    (.letOp (n := 345) (.out 0x119f1e (movR64M64Effect 0x119f1e 14 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 346) (.exec 0x119f1e (LoadPre 0x119f1e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x119f1e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119f1e 14 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 347) (.out 0x119f26 (mulR64Effect 0x119f26 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[345, 343]
    (.letOp (n := 348) (.out 0x119f26 (mulR64Effect 0x119f26 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[345, 343]
    (.letOp (n := 349) (.exec 0x119f26 (fun s => s.RIP = 0x119f26) (mulR64Effect 0x119f26 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[345, 343]
    (.letOp (n := 350) (.exec 0x119f29 (StorePre 0x119f29 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x119f29 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119f29 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[348, 4]
    (.letOp (n := 351) (.exec 0x119f2e (StorePre 0x119f2e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x119f2e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119f2e 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[347, 4]
    (.letOp (n := 352) (.out 0x119f36 (movR64M64Effect 0x119f36 0 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 353) (.exec 0x119f36 (LoadPre 0x119f36 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x119f36 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119f36 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l119cc0_7))))))))))))))))))))))))))))))))))))))))))

def bytes_l119cc0_6 : List UInt8 :=
  [0x48, 0x01, 0xF8, 0x49, 0x83, 0xD2, 0x00, 0x49, 0x0F, 0xA4, 0xC2, 0x0C, 0x48, 0xC1, 0xE0, 0x04,
    0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C, 0x09, 0xE8,
    0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD3,
    0x49, 0x89, 0xC7, 0x4C, 0x03, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x13, 0x5C, 0x24, 0x70,
    0x4C, 0x0F, 0xA4, 0xFB, 0x0C, 0x4C, 0x89, 0xC0, 0x4C, 0x8B, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x49, 0xF7, 0xE6, 0x48, 0x89, 0x54, 0x24, 0x70, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] ++ bytes_l119cc0_7

theorem code_l119cc0_6 : ∀ x ∈ codeRange 0x119ed6 bytes_l119cc0_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19ed6 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119cc0_7

def b_l119cc0_5 : Block Op Label signature Reg.count 266 :=
  .letOp (n := 266) (.out 0x119e7b (movR64R64Effect 0x119e7b 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[262]
    (.letOp (n := 267) (.exec 0x119e7b (fun s => s.RIP = 0x119e7b) (movR64R64Effect 0x119e7b 3 2) (Reg.operands [.gpr 2] [])) #v[262]
    (.letOp (n := 268) (.out 0x119e7e (andR32Imm8Effect 0x119e7e 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[248]
    (.letOp (n := 269) (.exec 0x119e7e (fun s => s.RIP = 0x119e7e) (andR32Imm8Effect 0x119e7e 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[248]
    (.letOp (n := 270) (.out 0x119e82 (movR64M64Effect 0x119e82 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 271) (.exec 0x119e82 (LoadPre 0x119e82 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x119e82 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119e82 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 272) (.out 0x119e8a (mulM64Effect 0x119e8a 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[270, 4]
    (.letOp (n := 273) (.out 0x119e8a (mulM64Effect 0x119e8a 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[270, 4]
    (.letOp (n := 274) (.exec 0x119e8a (LoadPre 0x119e8a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x119e8a + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x119e8a 8 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[270, 4]
    (.letOp (n := 275) (.out 0x119e92 (movR64R64Effect 0x119e92 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[273]
    (.letOp (n := 276) (.exec 0x119e92 (fun s => s.RIP = 0x119e92) (movR64R64Effect 0x119e92 10 2) (Reg.operands [.gpr 2] [])) #v[273]
    (.letOp (n := 277) (.out 0x119e95 (movR64R64Effect 0x119e95 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[272]
    (.letOp (n := 278) (.exec 0x119e95 (fun s => s.RIP = 0x119e95) (movR64R64Effect 0x119e95 14 0) (Reg.operands [.gpr 0] [])) #v[272]
    (.letOp (n := 279) (.out 0x119e98 (movR64M64Effect 0x119e98 0 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 280) (.exec 0x119e98 (LoadPre 0x119e98 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x119e98 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119e98 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 281) (.out 0x119ea0 (movR64M64Effect 0x119ea0 5 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 282) (.exec 0x119ea0 (LoadPre 0x119ea0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x119ea0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119ea0 5 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 283) (.out 0x119ea8 (mulR64Effect 0x119ea8 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[281, 279]
    (.letOp (n := 284) (.out 0x119ea8 (mulR64Effect 0x119ea8 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[281, 279]
    (.letOp (n := 285) (.exec 0x119ea8 (fun s => s.RIP = 0x119ea8) (mulR64Effect 0x119ea8 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[281, 279]
    (.letOp (n := 286) (.out 0x119eab (movR64R64Effect 0x119eab 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[284]
    (.letOp (n := 287) (.exec 0x119eab (fun s => s.RIP = 0x119eab) (movR64R64Effect 0x119eab 15 2) (Reg.operands [.gpr 2] [])) #v[284]
    (.letOp (n := 288) (.out 0x119eae (movR64R64Effect 0x119eae 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[283]
    (.letOp (n := 289) (.exec 0x119eae (fun s => s.RIP = 0x119eae) (movR64R64Effect 0x119eae 12 0) (Reg.operands [.gpr 0] [])) #v[283]
    (.letOp (n := 290) (.out 0x119eb1 (movR64M64Effect 0x119eb1 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 291) (.exec 0x119eb1 (LoadPre 0x119eb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x119eb1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119eb1 8 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 292) (.out 0x119eb9 (movR64R64Effect 0x119eb9 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[290]
    (.letOp (n := 293) (.exec 0x119eb9 (fun s => s.RIP = 0x119eb9) (movR64R64Effect 0x119eb9 0 8) (Reg.operands [.gpr 8] [])) #v[290]
    (.letOp (n := 294) (.out 0x119ebc (mulM64Effect 0x119ebc 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[292, 4]
    (.letOp (n := 295) (.out 0x119ebc (mulM64Effect 0x119ebc 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[292, 4]
    (.letOp (n := 296) (.exec 0x119ebc (LoadPre 0x119ebc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x119ebc + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x119ebc 8 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[292, 4]
    (.letOp (n := 297) (.out 0x119ec4 (addR64R64Effect 0x119ec4 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[277, 264]
    (.letOp (n := 298) (.out 0x119ec4 (addR64R64Effect 0x119ec4 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[277, 264]
    (.letOp (n := 299) (.exec 0x119ec4 (fun s => s.RIP = 0x119ec4) (addR64R64Effect 0x119ec4 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[277, 264]
    (.letOp (n := 300) (.out 0x119ec7 (atFlags StatusFlags.CF (adcR64R64Effect 0x119ec7 10 3)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[275, 266, 298]
    (.letOp (n := 301) (.exec 0x119ec7 (fun s => s.RIP = 0x119ec7) (atFlags StatusFlags.CF (adcR64R64Effect 0x119ec7 10 3)) (Reg.operands [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[275, 266, 298]
    (.letOp (n := 302) (.out 0x119eca (addR64R64Effect 0x119eca 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[297, 288]
    (.letOp (n := 303) (.out 0x119eca (addR64R64Effect 0x119eca 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[297, 288]
    (.letOp (n := 304) (.exec 0x119eca (fun s => s.RIP = 0x119eca) (addR64R64Effect 0x119eca 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[297, 288]
    (.letOp (n := 305) (.out 0x119ecd (atFlags StatusFlags.CF (adcR64R64Effect 0x119ecd 10 15)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[300, 286, 303]
    (.letOp (n := 306) (.exec 0x119ecd (fun s => s.RIP = 0x119ecd) (atFlags StatusFlags.CF (adcR64R64Effect 0x119ecd 10 15)) (Reg.operands [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[300, 286, 303]
    (.letOp (n := 307) (.out 0x119ed0 (addR64R64Effect 0x119ed0 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[294, 302]
    (.letOp (n := 308) (.out 0x119ed0 (addR64R64Effect 0x119ed0 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[294, 302]
    (.letOp (n := 309) (.exec 0x119ed0 (fun s => s.RIP = 0x119ed0) (addR64R64Effect 0x119ed0 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[294, 302]
    (.letOp (n := 310) (.out 0x119ed3 (atFlags StatusFlags.CF (adcR64R64Effect 0x119ed3 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[305, 295, 308]
    (.letOp (n := 311) (.exec 0x119ed3 (fun s => s.RIP = 0x119ed3) (atFlags StatusFlags.CF (adcR64R64Effect 0x119ed3 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[305, 295, 308]
    (b_l119cc0_6))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l119cc0_5 : List UInt8 :=
  [0x48, 0x89, 0xD3, 0x41, 0x83, 0xE5, 0x0F, 0x48, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48,
    0xF7, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x84,
    0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x8B, 0xAC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE5,
    0x49, 0x89, 0xD7, 0x49, 0x89, 0xC4, 0x4C, 0x8B, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x4C, 0x89,
    0xC0, 0x48, 0xF7, 0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xDE, 0x49, 0x11, 0xDA, 0x4D,
    0x01, 0xE6, 0x4D, 0x11, 0xFA, 0x4C, 0x01, 0xF0, 0x49, 0x11, 0xD2] ++ bytes_l119cc0_6

theorem code_l119cc0_5 : ∀ x ∈ codeRange 0x119e7b bytes_l119cc0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19e7b 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119cc0_6

def b_l119cc0_4 : Block Op Label signature Reg.count 222 :=
  .letOp (n := 222) (.out 0x119e23 (atFlags StatusFlags.CF (adcR64M64Effect 0x119e23 7 (.sib 4 none 0 (.d32 0xd0)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[217, 4, 220]
    (.letOp (n := 223) (.exec 0x119e23 (LoadPre 0x119e23 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x119e23 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x119e23 7 (.sib 4 none 0 (.d32 0xd0)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[217, 4, 220]
    (.letOp (n := 224) (.out 0x119e2b (addR64R64Effect 0x119e2b 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[219, 188]
    (.letOp (n := 225) (.out 0x119e2b (addR64R64Effect 0x119e2b 6 13) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 13] []) (.flag .CF)) #v[219, 188]
    (.letOp (n := 226) (.exec 0x119e2b (fun s => s.RIP = 0x119e2b) (addR64R64Effect 0x119e2b 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[219, 188]
    (.letOp (n := 227) (.out 0x119e2e (atFlags StatusFlags.CF (adcR64R64Effect 0x119e2e 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[222, 186, 225]
    (.letOp (n := 228) (.exec 0x119e2e (fun s => s.RIP = 0x119e2e) (atFlags StatusFlags.CF (adcR64R64Effect 0x119e2e 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[222, 186, 225]
    (.letOp (n := 229) (.out 0x119e31 (addR64R64Effect 0x119e31 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[224, 197]
    (.letOp (n := 230) (.out 0x119e31 (addR64R64Effect 0x119e31 6 11) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 11] []) (.flag .CF)) #v[224, 197]
    (.letOp (n := 231) (.exec 0x119e31 (fun s => s.RIP = 0x119e31) (addR64R64Effect 0x119e31 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[224, 197]
    (.letOp (n := 232) (.out 0x119e34 (atFlags StatusFlags.CF (adcR64R64Effect 0x119e34 7 5)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[227, 199, 230]
    (.letOp (n := 233) (.exec 0x119e34 (fun s => s.RIP = 0x119e34) (atFlags StatusFlags.CF (adcR64R64Effect 0x119e34 7 5)) (Reg.operands [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[227, 199, 230]
    (.letOp (n := 234) (.out 0x119e37 (addR64R64Effect 0x119e37 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[229, 209]
    (.letOp (n := 235) (.out 0x119e37 (addR64R64Effect 0x119e37 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[229, 209]
    (.letOp (n := 236) (.exec 0x119e37 (fun s => s.RIP = 0x119e37) (addR64R64Effect 0x119e37 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[229, 209]
    (.letOp (n := 237) (.out 0x119e3a (atFlags StatusFlags.CF (adcR64R64Effect 0x119e3a 7 8)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[232, 212, 235]
    (.letOp (n := 238) (.exec 0x119e3a (fun s => s.RIP = 0x119e3a) (atFlags StatusFlags.CF (adcR64R64Effect 0x119e3a 7 8)) (Reg.operands [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[232, 212, 235]
    (.letOp (n := 239) (.out 0x119e3d (addR64R64Effect 0x119e3d 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[234, 155]
    (.letOp (n := 240) (.out 0x119e3d (addR64R64Effect 0x119e3d 6 9) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 9] []) (.flag .CF)) #v[234, 155]
    (.letOp (n := 241) (.exec 0x119e3d (fun s => s.RIP = 0x119e3d) (addR64R64Effect 0x119e3d 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[234, 155]
    (.letOp (n := 242) (.out 0x119e40 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119e40 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[237, 240]
    (.letOp (n := 243) (.exec 0x119e40 (fun s => s.RIP = 0x119e40) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119e40 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[237, 240]
    (.letOp (n := 244) (.out 0x119e44 (shldR64R64Effect 0x119e44 5 7 6 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[242, 239]
    (.letOp (n := 245) (.exec 0x119e44 (fun s => s.RIP = 0x119e44) (shldR64R64Effect 0x119e44 5 7 6 12) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[242, 239]
    (.letOp (n := 246) (.out 0x119e49 (movR64R64Effect 0x119e49 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[239]
    (.letOp (n := 247) (.exec 0x119e49 (fun s => s.RIP = 0x119e49) (movR64R64Effect 0x119e49 13 6) (Reg.operands [.gpr 6] [])) #v[239]
    (.letOp (n := 248) (.out 0x119e4c (shrR64Effect 0x119e4c 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[246]
    (.letOp (n := 249) (.exec 0x119e4c (fun s => s.RIP = 0x119e4c) (shrR64Effect 0x119e4c 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[246]
    (.letOp (n := 250) (.out 0x119e50 (movR64R64Effect 0x119e50 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[190]
    (.letOp (n := 251) (.exec 0x119e50 (fun s => s.RIP = 0x119e50) (movR64R64Effect 0x119e50 0 10) (Reg.operands [.gpr 10] [])) #v[190]
    (.letOp (n := 252) (.out 0x119e53 (mulM64Effect 0x119e53 8 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[250, 4]
    (.letOp (n := 253) (.out 0x119e53 (mulM64Effect 0x119e53 8 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[250, 4]
    (.letOp (n := 254) (.exec 0x119e53 (LoadPre 0x119e53 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x119e53 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x119e53 8 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[250, 4]
    (.letOp (n := 255) (.exec 0x119e5b (StorePre 0x119e5b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x119e5b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119e5b 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[253, 4]
    (.letOp (n := 256) (.exec 0x119e60 (StorePre 0x119e60 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x119e60 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119e60 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[252, 4]
    (.letOp (n := 257) (.out 0x119e68 (movR64M64Effect 0x119e68 0 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 258) (.exec 0x119e68 (LoadPre 0x119e68 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x119e68 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119e68 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 259) (.out 0x119e70 (movR64M64Effect 0x119e70 9 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 260) (.exec 0x119e70 (LoadPre 0x119e70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x119e70 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119e70 9 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 261) (.out 0x119e75 (mulR64Effect 0x119e75 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[259, 257]
    (.letOp (n := 262) (.out 0x119e75 (mulR64Effect 0x119e75 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[259, 257]
    (.letOp (n := 263) (.exec 0x119e75 (fun s => s.RIP = 0x119e75) (mulR64Effect 0x119e75 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[259, 257]
    (.letOp (n := 264) (.out 0x119e78 (movR64R64Effect 0x119e78 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[261]
    (.letOp (n := 265) (.exec 0x119e78 (fun s => s.RIP = 0x119e78) (movR64R64Effect 0x119e78 11 0) (Reg.operands [.gpr 0] [])) #v[261]
    (b_l119cc0_5))))))))))))))))))))))))))))))))))))))))))))

def bytes_l119cc0_4 : List UInt8 :=
  [0x48, 0x13, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xEE, 0x4C, 0x11, 0xFF, 0x4C, 0x01,
    0xDE, 0x48, 0x11, 0xEF, 0x48, 0x01, 0xC6, 0x4C, 0x11, 0xC7, 0x4C, 0x01, 0xCE, 0x48, 0x83, 0xD7,
    0x00, 0x48, 0x0F, 0xA4, 0xF7, 0x0C, 0x49, 0x89, 0xF5, 0x49, 0xC1, 0xED, 0x30, 0x4C, 0x89, 0xD0,
    0x48, 0xF7, 0xA4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x70, 0x48, 0x89, 0x84,
    0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x4C,
    0x24, 0x68, 0x49, 0xF7, 0xE1, 0x49, 0x89, 0xC3] ++ bytes_l119cc0_5

theorem code_l119cc0_4 : ∀ x ∈ codeRange 0x119e23 bytes_l119cc0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19e23 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119cc0_5

def b_l119cc0_3 : Block Op Label signature Reg.count 178 :=
  .letOp (n := 178) (.exec 0x119dcd (StorePre 0x119dcd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x119dcd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119dcd 2 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[176, 4]
    (.letOp (n := 179) (.out 0x119dd5 (movR64R64Effect 0x119dd5 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[175]
    (.letOp (n := 180) (.exec 0x119dd5 (fun s => s.RIP = 0x119dd5) (movR64R64Effect 0x119dd5 12 0) (Reg.operands [.gpr 0] [])) #v[175]
    (.letOp (n := 181) (.out 0x119dd8 (movR64R64Effect 0x119dd8 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[90]
    (.letOp (n := 182) (.exec 0x119dd8 (fun s => s.RIP = 0x119dd8) (movR64R64Effect 0x119dd8 0 14) (Reg.operands [.gpr 14] [])) #v[90]
    (.letOp (n := 183) (.out 0x119ddb (mulR64Effect 0x119ddb 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[55, 181]
    (.letOp (n := 184) (.out 0x119ddb (mulR64Effect 0x119ddb 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[55, 181]
    (.letOp (n := 185) (.exec 0x119ddb (fun s => s.RIP = 0x119ddb) (mulR64Effect 0x119ddb 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[55, 181]
    (.letOp (n := 186) (.out 0x119dde (movR64R64Effect 0x119dde 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[184]
    (.letOp (n := 187) (.exec 0x119dde (fun s => s.RIP = 0x119dde) (movR64R64Effect 0x119dde 15 2) (Reg.operands [.gpr 2] [])) #v[184]
    (.letOp (n := 188) (.out 0x119de1 (movR64R64Effect 0x119de1 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[183]
    (.letOp (n := 189) (.exec 0x119de1 (fun s => s.RIP = 0x119de1) (movR64R64Effect 0x119de1 13 0) (Reg.operands [.gpr 0] [])) #v[183]
    (.letOp (n := 190) (.out 0x119de4 (movR64M64Effect 0x119de4 10 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 191) (.exec 0x119de4 (LoadPre 0x119de4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x119de4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119de4 10 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 192) (.out 0x119dec (movR64R64Effect 0x119dec 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[190]
    (.letOp (n := 193) (.exec 0x119dec (fun s => s.RIP = 0x119dec) (movR64R64Effect 0x119dec 0 10) (Reg.operands [.gpr 10] [])) #v[190]
    (.letOp (n := 194) (.out 0x119def (mulR64Effect 0x119def 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[126, 192]
    (.letOp (n := 195) (.out 0x119def (mulR64Effect 0x119def 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[126, 192]
    (.letOp (n := 196) (.exec 0x119def (fun s => s.RIP = 0x119def) (mulR64Effect 0x119def 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[126, 192]
    (.letOp (n := 197) (.out 0x119df2 (movR64R64Effect 0x119df2 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[194]
    (.letOp (n := 198) (.exec 0x119df2 (fun s => s.RIP = 0x119df2) (movR64R64Effect 0x119df2 11 0) (Reg.operands [.gpr 0] [])) #v[194]
    (.letOp (n := 199) (.out 0x119df5 (movR64R64Effect 0x119df5 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[195]
    (.letOp (n := 200) (.exec 0x119df5 (fun s => s.RIP = 0x119df5) (movR64R64Effect 0x119df5 5 2) (Reg.operands [.gpr 2] [])) #v[195]
    (.letOp (n := 201) (.out 0x119df8 (shrR64Effect 0x119df8 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[132]
    (.letOp (n := 202) (.exec 0x119df8 (fun s => s.RIP = 0x119df8) (shrR64Effect 0x119df8 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[132]
    (.letOp (n := 203) (.out 0x119dfc (movR64Imm64Effect 0x119dfc 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 204) (.exec 0x119dfc (fun s => s.RIP = 0x119dfc) (movR64Imm64Effect 0x119dfc 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 205) (.out 0x119e06 (imulR64R64Effect 0x119e06 4 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[201, 203]
    (.letOp (n := 206) (.exec 0x119e06 (fun s => s.RIP = 0x119e06) (imulR64R64Effect 0x119e06 4 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[201, 203]
    (.letOp (n := 207) (.out 0x119e0a (movR64R64Effect 0x119e0a 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[136]
    (.letOp (n := 208) (.exec 0x119e0a (fun s => s.RIP = 0x119e0a) (movR64R64Effect 0x119e0a 0 3) (Reg.operands [.gpr 3] [])) #v[136]
    (.letOp (n := 209) (.out 0x119e0d (mulR64Effect 0x119e0d 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[203, 207]
    (.letOp (n := 210) (.out 0x119e0d (mulR64Effect 0x119e0d 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[203, 207]
    (.letOp (n := 211) (.exec 0x119e0d (fun s => s.RIP = 0x119e0d) (mulR64Effect 0x119e0d 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[203, 207]
    (.letOp (n := 212) (.out 0x119e10 (addR64R64Effect 0x119e10 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[205, 210]
    (.letOp (n := 213) (.exec 0x119e10 (fun s => s.RIP = 0x119e10) (addR64R64Effect 0x119e10 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[205, 210]
    (.letOp (n := 214) (.out 0x119e13 (addR64M64Effect 0x119e13 6 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[171, 4]
    (.letOp (n := 215) (.out 0x119e13 (addR64M64Effect 0x119e13 6 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[171, 4]
    (.letOp (n := 216) (.exec 0x119e13 (LoadPre 0x119e13 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x119e13 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x119e13 6 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[171, 4]
    (.letOp (n := 217) (.out 0x119e1b (atFlags StatusFlags.CF (adcR64M64Effect 0x119e1b 7 (.sib 4 none 0 (.d8 0x70)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[169, 4, 215]
    (.letOp (n := 218) (.exec 0x119e1b (LoadPre 0x119e1b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x119e1b + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x119e1b 7 (.sib 4 none 0 (.d8 0x70)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[169, 4, 215]
    (.letOp (n := 219) (.out 0x119e20 (addR64R64Effect 0x119e20 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[214, 179]
    (.letOp (n := 220) (.out 0x119e20 (addR64R64Effect 0x119e20 6 12) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 12] []) (.flag .CF)) #v[214, 179]
    (.letOp (n := 221) (.exec 0x119e20 (fun s => s.RIP = 0x119e20) (addR64R64Effect 0x119e20 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[214, 179]
    (b_l119cc0_4))))))))))))))))))))))))))))))))))))))))))))

def bytes_l119cc0_3 : List UInt8 :=
  [0x48, 0x89, 0x94, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC4, 0x4C, 0x89, 0xF0, 0x49, 0xF7,
    0xE2, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC5, 0x4C, 0x8B, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x4C,
    0x89, 0xD0, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xD5, 0x49, 0xC1, 0xE8, 0x34, 0x48,
    0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xC1, 0x48, 0x89, 0xD8,
    0x48, 0xF7, 0xE1, 0x49, 0x01, 0xD0, 0x48, 0x03, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x13,
    0x7C, 0x24, 0x70, 0x4C, 0x01, 0xE6] ++ bytes_l119cc0_4

theorem code_l119cc0_3 : ∀ x ∈ codeRange 0x119dcd bytes_l119cc0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19dcd 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119cc0_4

def b_l119cc0_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x119d71 (shldR64R64Effect 0x119d71 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[134, 129]
    (.letOp (n := 137) (.exec 0x119d71 (fun s => s.RIP = 0x119d71) (shldR64R64Effect 0x119d71 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[134, 129]
    (.letOp (n := 138) (.out 0x119d76 (movR64Imm64Effect 0x119d76 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 139) (.exec 0x119d76 (fun s => s.RIP = 0x119d76) (movR64Imm64Effect 0x119d76 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 140) (.out 0x119d80 (andR64R64Effect 0x119d80 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[129, 138]
    (.letOp (n := 141) (.exec 0x119d80 (fun s => s.RIP = 0x119d80) (andR64R64Effect 0x119d80 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[129, 138]
    (.letOp (n := 142) (.out 0x119d83 (movR64Imm64Effect 0x119d83 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 143) (.exec 0x119d83 (fun s => s.RIP = 0x119d83) (movR64Imm64Effect 0x119d83 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 144) (.out 0x119d8d (mulR64Effect 0x119d8d 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[142, 140]
    (.letOp (n := 145) (.out 0x119d8d (mulR64Effect 0x119d8d 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[142, 140]
    (.letOp (n := 146) (.exec 0x119d8d (fun s => s.RIP = 0x119d8d) (mulR64Effect 0x119d8d 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[142, 140]
    (.letOp (n := 147) (.out 0x119d90 (movR64R64Effect 0x119d90 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[145]
    (.letOp (n := 148) (.exec 0x119d90 (fun s => s.RIP = 0x119d90) (movR64R64Effect 0x119d90 9 2) (Reg.operands [.gpr 2] [])) #v[145]
    (.letOp (n := 149) (.out 0x119d93 (addR64R64Effect 0x119d93 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[144, 117]
    (.letOp (n := 150) (.out 0x119d93 (addR64R64Effect 0x119d93 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[144, 117]
    (.letOp (n := 151) (.exec 0x119d93 (fun s => s.RIP = 0x119d93) (addR64R64Effect 0x119d93 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[144, 117]
    (.letOp (n := 152) (.exec 0x119d96 (StorePre 0x119d96 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x119d96 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119d96 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[149, 4]
    (.letOp (n := 153) (.out 0x119d9b (atFlags StatusFlags.CF (adcR64R64Effect 0x119d9b 9 7)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[147, 120, 150]
    (.letOp (n := 154) (.exec 0x119d9b (fun s => s.RIP = 0x119d9b) (atFlags StatusFlags.CF (adcR64R64Effect 0x119d9b 9 7)) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[147, 120, 150]
    (.letOp (n := 155) (.out 0x119d9e (shldR64R64Effect 0x119d9e 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[153, 149]
    (.letOp (n := 156) (.exec 0x119d9e (fun s => s.RIP = 0x119d9e) (shldR64R64Effect 0x119d9e 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[153, 149]
    (.letOp (n := 157) (.out 0x119da3 (movR64R64Effect 0x119da3 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[122]
    (.letOp (n := 158) (.exec 0x119da3 (fun s => s.RIP = 0x119da3) (movR64R64Effect 0x119da3 0 6) (Reg.operands [.gpr 6] [])) #v[122]
    (.letOp (n := 159) (.out 0x119da6 (mulR64Effect 0x119da6 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[59, 157]
    (.letOp (n := 160) (.out 0x119da6 (mulR64Effect 0x119da6 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[59, 157]
    (.letOp (n := 161) (.exec 0x119da6 (fun s => s.RIP = 0x119da6) (mulR64Effect 0x119da6 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[59, 157]
    (.letOp (n := 162) (.exec 0x119da9 (StorePre 0x119da9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x119da9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119da9 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[160, 4]
    (.letOp (n := 163) (.exec 0x119dae (StorePre 0x119dae 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x119dae + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119dae 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[159, 4]
    (.letOp (n := 164) (.out 0x119db6 (movR64M64Effect 0x119db6 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 165) (.exec 0x119db6 (LoadPre 0x119db6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x119db6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119db6 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 166) (.out 0x119dbe (mulR64Effect 0x119dbe 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[61, 164]
    (.letOp (n := 167) (.out 0x119dbe (mulR64Effect 0x119dbe 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[61, 164]
    (.letOp (n := 168) (.exec 0x119dbe (fun s => s.RIP = 0x119dbe) (mulR64Effect 0x119dbe 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[61, 164]
    (.letOp (n := 169) (.out 0x119dc1 (movR64R64Effect 0x119dc1 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[167]
    (.letOp (n := 170) (.exec 0x119dc1 (fun s => s.RIP = 0x119dc1) (movR64R64Effect 0x119dc1 7 2) (Reg.operands [.gpr 2] [])) #v[167]
    (.letOp (n := 171) (.out 0x119dc4 (movR64R64Effect 0x119dc4 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[166]
    (.letOp (n := 172) (.exec 0x119dc4 (fun s => s.RIP = 0x119dc4) (movR64R64Effect 0x119dc4 6 0) (Reg.operands [.gpr 0] [])) #v[166]
    (.letOp (n := 173) (.out 0x119dc7 (movR64R64Effect 0x119dc7 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 174) (.exec 0x119dc7 (fun s => s.RIP = 0x119dc7) (movR64R64Effect 0x119dc7 0 5) (Reg.operands [.gpr 5] [])) #v[73]
    (.letOp (n := 175) (.out 0x119dca (mulR64Effect 0x119dca 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[57, 173]
    (.letOp (n := 176) (.out 0x119dca (mulR64Effect 0x119dca 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[57, 173]
    (.letOp (n := 177) (.exec 0x119dca (fun s => s.RIP = 0x119dca) (mulR64Effect 0x119dca 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[57, 173]
    (b_l119cc0_3))))))))))))))))))))))))))))))))))))))))))

def bytes_l119cc0_2 : List UInt8 :=
  [0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48,
    0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49,
    0x89, 0xD1, 0x4C, 0x01, 0xD8, 0x48, 0x89, 0x44, 0x24, 0x50, 0x49, 0x11, 0xF9, 0x49, 0x0F, 0xA4,
    0xC1, 0x0C, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0x54, 0x24, 0x70, 0x48, 0x89, 0x84,
    0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE4,
    0x48, 0x89, 0xD7, 0x48, 0x89, 0xC6, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE5] ++ bytes_l119cc0_3

theorem code_l119cc0_2 : ∀ x ∈ codeRange 0x119d71 bytes_l119cc0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19d71 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119cc0_3

def b_l119cc0_1 : Block Op Label signature Reg.count 94 :=
  .letOp (n := 94) (.out 0x119d1c (mulR64Effect 0x119d1c 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[57, 92]
    (.letOp (n := 95) (.out 0x119d1c (mulR64Effect 0x119d1c 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[57, 92]
    (.letOp (n := 96) (.exec 0x119d1c (fun s => s.RIP = 0x119d1c) (mulR64Effect 0x119d1c 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[57, 92]
    (.letOp (n := 97) (.exec 0x119d1f (StorePre 0x119d1f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x119d1f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119d1f 13 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 98) (.out 0x119d27 (movR64R64Effect 0x119d27 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 99) (.exec 0x119d27 (fun s => s.RIP = 0x119d27) (movR64R64Effect 0x119d27 1 2) (Reg.operands [.gpr 2] [])) #v[95]
    (.letOp (n := 100) (.out 0x119d2a (movR64R64Effect 0x119d2a 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[94]
    (.letOp (n := 101) (.exec 0x119d2a (fun s => s.RIP = 0x119d2a) (movR64R64Effect 0x119d2a 6 0) (Reg.operands [.gpr 0] [])) #v[94]
    (.letOp (n := 102) (.out 0x119d2d (addR64R64Effect 0x119d2d 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[100, 85]
    (.letOp (n := 103) (.out 0x119d2d (addR64R64Effect 0x119d2d 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[100, 85]
    (.letOp (n := 104) (.exec 0x119d2d (fun s => s.RIP = 0x119d2d) (addR64R64Effect 0x119d2d 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[100, 85]
    (.letOp (n := 105) (.out 0x119d30 (atFlags StatusFlags.CF (adcR64R64Effect 0x119d30 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[98, 88, 103]
    (.letOp (n := 106) (.exec 0x119d30 (fun s => s.RIP = 0x119d30) (atFlags StatusFlags.CF (adcR64R64Effect 0x119d30 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[98, 88, 103]
    (.letOp (n := 107) (.out 0x119d33 (movR64M64Effect 0x119d33 0 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 108) (.exec 0x119d33 (LoadPre 0x119d33 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x119d33 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119d33 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 109) (.out 0x119d3b (mulR64Effect 0x119d3b 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[55, 107]
    (.letOp (n := 110) (.out 0x119d3b (mulR64Effect 0x119d3b 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[55, 107]
    (.letOp (n := 111) (.exec 0x119d3b (fun s => s.RIP = 0x119d3b) (mulR64Effect 0x119d3b 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[55, 107]
    (.letOp (n := 112) (.exec 0x119d3e (StorePre 0x119d3e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x119d3e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119d3e 10 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 113) (.out 0x119d46 (movR64R64Effect 0x119d46 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[110]
    (.letOp (n := 114) (.exec 0x119d46 (fun s => s.RIP = 0x119d46) (movR64R64Effect 0x119d46 7 2) (Reg.operands [.gpr 2] [])) #v[110]
    (.letOp (n := 115) (.out 0x119d49 (movR64R64Effect 0x119d49 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[109]
    (.letOp (n := 116) (.exec 0x119d49 (fun s => s.RIP = 0x119d49) (movR64R64Effect 0x119d49 11 0) (Reg.operands [.gpr 0] [])) #v[109]
    (.letOp (n := 117) (.out 0x119d4c (addR64R64Effect 0x119d4c 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[115, 102]
    (.letOp (n := 118) (.out 0x119d4c (addR64R64Effect 0x119d4c 11 6) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 6] []) (.flag .CF)) #v[115, 102]
    (.letOp (n := 119) (.exec 0x119d4c (fun s => s.RIP = 0x119d4c) (addR64R64Effect 0x119d4c 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[115, 102]
    (.letOp (n := 120) (.out 0x119d4f (atFlags StatusFlags.CF (adcR64R64Effect 0x119d4f 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[113, 105, 118]
    (.letOp (n := 121) (.exec 0x119d4f (fun s => s.RIP = 0x119d4f) (atFlags StatusFlags.CF (adcR64R64Effect 0x119d4f 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[113, 105, 118]
    (.letOp (n := 122) (.out 0x119d52 (movR64M64Effect 0x119d52 6 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 123) (.exec 0x119d52 (LoadPre 0x119d52 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x119d52 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119d52 6 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 124) (.out 0x119d5a (movR64R64Effect 0x119d5a 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[122]
    (.letOp (n := 125) (.exec 0x119d5a (fun s => s.RIP = 0x119d5a) (movR64R64Effect 0x119d5a 0 6) (Reg.operands [.gpr 6] [])) #v[122]
    (.letOp (n := 126) (.out 0x119d5d (movR64R64Effect 0x119d5d 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 127) (.exec 0x119d5d (fun s => s.RIP = 0x119d5d) (movR64R64Effect 0x119d5d 1 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 128) (.exec 0x119d60 (StorePre 0x119d60 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x119d60 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119d60 3 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 129) (.out 0x119d68 (mulR64Effect 0x119d68 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[53, 124]
    (.letOp (n := 130) (.out 0x119d68 (mulR64Effect 0x119d68 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[53, 124]
    (.letOp (n := 131) (.exec 0x119d68 (fun s => s.RIP = 0x119d68) (mulR64Effect 0x119d68 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[53, 124]
    (.letOp (n := 132) (.out 0x119d6b (movR64R64Effect 0x119d6b 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[130]
    (.letOp (n := 133) (.exec 0x119d6b (fun s => s.RIP = 0x119d6b) (movR64R64Effect 0x119d6b 8 2) (Reg.operands [.gpr 2] [])) #v[130]
    (.letOp (n := 134) (.out 0x119d6e (movR64R64Effect 0x119d6e 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[130]
    (.letOp (n := 135) (.exec 0x119d6e (fun s => s.RIP = 0x119d6e) (movR64R64Effect 0x119d6e 3 2) (Reg.operands [.gpr 2] [])) #v[130]
    (b_l119cc0_2))))))))))))))))))))))))))))))))))))))))))

def bytes_l119cc0_1 : List UInt8 :=
  [0x49, 0xF7, 0xE5, 0x4C, 0x89, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD1, 0x48, 0x89,
    0xC6, 0x4C, 0x01, 0xC6, 0x48, 0x11, 0xF9, 0x48, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x49,
    0xF7, 0xE2, 0x4C, 0x89, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC3,
    0x49, 0x01, 0xF3, 0x48, 0x11, 0xCF, 0x48, 0x8B, 0xB4, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89,
    0xF0, 0x48, 0x89, 0xD9, 0x48, 0x89, 0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE3, 0x49,
    0x89, 0xD0, 0x48, 0x89, 0xD3] ++ bytes_l119cc0_2

theorem code_l119cc0_1 : ∀ x ∈ codeRange 0x119d1c bytes_l119cc0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19d1c 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119cc0_2

def b_l119cc0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119cc0 (movR64M64Effect 0x119cc0 3 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x119cc0 (LoadPre 0x119cc0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119cc0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119cc0 3 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x119cc5 (movR64M64Effect 0x119cc5 10 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 56) (.exec 0x119cc5 (LoadPre 0x119cc5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119cc5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119cc5 10 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x119cca (movR64M64Effect 0x119cca 13 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 58) (.exec 0x119cca (LoadPre 0x119cca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119cca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119cca 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x119ccf (movR64M64Effect 0x119ccf 15 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 60) (.exec 0x119ccf (LoadPre 0x119ccf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119ccf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119ccf 15 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x119cd4 (movR64M64Effect 0x119cd4 12 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 62) (.exec 0x119cd4 (LoadPre 0x119cd4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119cd4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119cd4 12 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x119cd9 (movR64M64Effect 0x119cd9 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x119cd9 (LoadPre 0x119cd9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x119cd9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119cd9 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x119ce1 (mulR64Effect 0x119ce1 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[59, 63]
    (.letOp (n := 66) (.out 0x119ce1 (mulR64Effect 0x119ce1 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[59, 63]
    (.letOp (n := 67) (.exec 0x119ce1 (fun s => s.RIP = 0x119ce1) (mulR64Effect 0x119ce1 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[59, 63]
    (.letOp (n := 68) (.exec 0x119ce4 (StorePre 0x119ce4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x119ce4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119ce4 15 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 69) (.out 0x119cec (movR64R64Effect 0x119cec 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[66]
    (.letOp (n := 70) (.exec 0x119cec (fun s => s.RIP = 0x119cec) (movR64R64Effect 0x119cec 1 2) (Reg.operands [.gpr 2] [])) #v[66]
    (.letOp (n := 71) (.out 0x119cef (movR64R64Effect 0x119cef 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 72) (.exec 0x119cef (fun s => s.RIP = 0x119cef) (movR64R64Effect 0x119cef 6 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 73) (.out 0x119cf2 (movR64M64Effect 0x119cf2 5 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 74) (.exec 0x119cf2 (LoadPre 0x119cf2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x119cf2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119cf2 5 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x119cfa (movR64R64Effect 0x119cfa 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 76) (.exec 0x119cfa (fun s => s.RIP = 0x119cfa) (movR64R64Effect 0x119cfa 0 5) (Reg.operands [.gpr 5] [])) #v[73]
    (.letOp (n := 77) (.out 0x119cfd (mulR64Effect 0x119cfd 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[61, 75]
    (.letOp (n := 78) (.out 0x119cfd (mulR64Effect 0x119cfd 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[61, 75]
    (.letOp (n := 79) (.exec 0x119cfd (fun s => s.RIP = 0x119cfd) (mulR64Effect 0x119cfd 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[61, 75]
    (.letOp (n := 80) (.exec 0x119d00 (StorePre 0x119d00 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x119d00 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119d00 12 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 81) (.out 0x119d05 (movR64R64Effect 0x119d05 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[78]
    (.letOp (n := 82) (.exec 0x119d05 (fun s => s.RIP = 0x119d05) (movR64R64Effect 0x119d05 7 2) (Reg.operands [.gpr 2] [])) #v[78]
    (.letOp (n := 83) (.out 0x119d08 (movR64R64Effect 0x119d08 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[77]
    (.letOp (n := 84) (.exec 0x119d08 (fun s => s.RIP = 0x119d08) (movR64R64Effect 0x119d08 8 0) (Reg.operands [.gpr 0] [])) #v[77]
    (.letOp (n := 85) (.out 0x119d0b (addR64R64Effect 0x119d0b 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[83, 71]
    (.letOp (n := 86) (.out 0x119d0b (addR64R64Effect 0x119d0b 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[83, 71]
    (.letOp (n := 87) (.exec 0x119d0b (fun s => s.RIP = 0x119d0b) (addR64R64Effect 0x119d0b 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[83, 71]
    (.letOp (n := 88) (.out 0x119d0e (atFlags StatusFlags.CF (adcR64R64Effect 0x119d0e 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[81, 69, 86]
    (.letOp (n := 89) (.exec 0x119d0e (fun s => s.RIP = 0x119d0e) (atFlags StatusFlags.CF (adcR64R64Effect 0x119d0e 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[81, 69, 86]
    (.letOp (n := 90) (.out 0x119d11 (movR64M64Effect 0x119d11 14 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 91) (.exec 0x119d11 (LoadPre 0x119d11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x119d11 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119d11 14 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.out 0x119d19 (movR64R64Effect 0x119d19 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[90]
    (.letOp (n := 93) (.exec 0x119d19 (fun s => s.RIP = 0x119d19) (movR64R64Effect 0x119d19 0 14) (Reg.operands [.gpr 14] [])) #v[90]
    (b_l119cc0_1)))))))))))))))))))))))))))))))))))))))))

def bytes_l119cc0 : List UInt8 :=
  [0x48, 0x8B, 0x5C, 0x24, 0x48, 0x4C, 0x8B, 0x54, 0x24, 0x40, 0x4C, 0x8B, 0x6C, 0x24, 0x38, 0x4C,
    0x8B, 0x7C, 0x24, 0x28, 0x4C, 0x8B, 0x64, 0x24, 0x30, 0x48, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00,
    0x00, 0x49, 0xF7, 0xE7, 0x4C, 0x89, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD1, 0x48,
    0x89, 0xC6, 0x48, 0x8B, 0xAC, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE4,
    0x4C, 0x89, 0x64, 0x24, 0x68, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0, 0x49, 0x01, 0xF0, 0x48, 0x11,
    0xCF, 0x4C, 0x8B, 0xB4, 0x24, 0x20, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF0] ++ bytes_l119cc0_1

theorem code_l119cc0 : ∀ x ∈ codeRange 0x119cc0 bytes_l119cc0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19cc0 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l119cc0_1

@[cfg_block] def b_l11a110 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11a110 (movR64M64Effect 0x11a110 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11a110 (LoadPre 0x11a110 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11a110 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11a110 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11a115 (StorePre 0x11a115 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11a115 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a115 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11a11a (movR64M64Effect 0x11a11a 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11a11a (LoadPre 0x11a11a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11a11a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11a11a 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11a11f (StorePre 0x11a11f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11a11f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a11f 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11a124 (movR64M64Effect 0x11a124 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11a124 (LoadPre 0x11a124 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11a124 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11a124 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11a129 (StorePre 0x11a129 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11a129 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a129 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11a12e (movR64M64Effect 0x11a12e 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11a12e (LoadPre 0x11a12e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11a12e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11a12e 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11a133 (movR64M64Effect 0x11a133 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11a133 (LoadPre 0x11a133 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11a133 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11a133 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11a138 (StorePre 0x11a138 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11a138 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a138 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11a13d (StorePre 0x11a13d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11a13d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11a13d 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11a141 (movR64R64Effect 0x11a141 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11a141 (fun s => s.RIP = 0x11a141) (movR64R64Effect 0x11a141 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11a144 (movR64R64Effect 0x11a144 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11a144 (fun s => s.RIP = 0x11a144) (movR64R64Effect 0x11a144 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11a147 (callEffect (fun _ => 0x1145f0) 0x11a14c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11a147 (PushPre 0x11a147 5) (callEffect (fun _ => 0x1145f0) 0x11a14c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11a14c⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11a14c, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11a110 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xA4, 0xA4, 0xFF, 0xFF]

theorem code_l11a110 : ∀ x ∈ codeRange 0x11a110 bytes_l11a110, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1a110 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l11a14c_11 : Block Op Label signature Reg.count 524 :=
  .letOp (n := 524) (.out 0x11a4cc (orR64R64Effect 0x11a4cc 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[516, 522]
    (.letOp (n := 525) (.exec 0x11a4cc (fun s => s.RIP = 0x11a4cc) (orR64R64Effect 0x11a4cc 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[516, 522]
    (.letOp (n := 526) (.out 0x11a4cf (andR64R64Effect 0x11a4cf 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[518, 522]
    (.letOp (n := 527) (.exec 0x11a4cf (fun s => s.RIP = 0x11a4cf) (andR64R64Effect 0x11a4cf 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[518, 522]
    (.letOp (n := 528) (.out 0x11a4d2 (shrR64Effect 0x11a4d2 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[522]
    (.letOp (n := 529) (.exec 0x11a4d2 (fun s => s.RIP = 0x11a4d2) (shrR64Effect 0x11a4d2 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[522]
    (.letOp (n := 530) (.out 0x11a4d6 (addR64R64Effect 0x11a4d6 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[528, 490]
    (.letOp (n := 531) (.exec 0x11a4d6 (fun s => s.RIP = 0x11a4d6) (addR64R64Effect 0x11a4d6 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[528, 490]
    (.letOp (n := 532) (.out 0x11a4d9 (movR64Imm64Effect 0x11a4d9 0 0xf000000000000) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 533) (.exec 0x11a4d9 (fun s => s.RIP = 0x11a4d9) (movR64Imm64Effect 0x11a4d9 0 0xf000000000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 534) (.out 0x11a4e3 (xorR64R64Effect 0x11a4e3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[532, 530]
    (.letOp (n := 535) (.exec 0x11a4e3 (fun s => s.RIP = 0x11a4e3) (xorR64R64Effect 0x11a4e3 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[532, 530]
    (.letOp (n := 536) (.out 0x11a4e6 (andR64R64Effect 0x11a4e6 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[526, 534]
    (.letOp (n := 537) (.exec 0x11a4e6 (fun s => s.RIP = 0x11a4e6) (andR64R64Effect 0x11a4e6 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[526, 534]
    (.letOp (n := 538) (.out 0x11a4e9 (andR64R64Effect 0x11a4e9 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[524, 372]
    (.letOp (n := 539) (.exec 0x11a4e9 (fun s => s.RIP = 0x11a4e9) (andR64R64Effect 0x11a4e9 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[524, 372]
    (.letOp (n := 540) (.out 0x11a4ec (orR64R64Effect 0x11a4ec 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[538, 530]
    (.letOp (n := 541) (.out 0x11a4ec (orR64R64Effect 0x11a4ec 6 7) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 7] []) (.flag .ZF)) #v[538, 530]
    (.letOp (n := 542) (.exec 0x11a4ec (fun s => s.RIP = 0x11a4ec) (orR64R64Effect 0x11a4ec 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[538, 530]
    (.letOp (n := 543) (.out 0x11a4ef (atFlags (condHolds 4) (setccR8Effect 0x11a4ef 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[534, 541]
    (.letOp (n := 544) (.exec 0x11a4ef (fun s => s.RIP = 0x11a4ef) (atFlags (condHolds 4) (setccR8Effect 0x11a4ef 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[534, 541]
    (.letOp (n := 545) (.out 0x11a4f2 (cmpR64R64Effect 0x11a4f2 1 13) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 13] []) (.flag .ZF)) #v[536, 372]
    (.letOp (n := 546) (.exec 0x11a4f2 (fun s => s.RIP = 0x11a4f2) (cmpR64R64Effect 0x11a4f2 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[536, 372]
    (.letOp (n := 547) (.out 0x11a4f5 (movR64M64Effect 0x11a4f5 3 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 548) (.exec 0x11a4f5 (LoadPre 0x11a4f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11a4f5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a4f5 3 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 549) (.exec 0x11a4fd (StorePre 0x11a4fd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11a4fd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a4fd 3 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[547, 4]
    (.letOp (n := 550) (.out 0x11a502 (movR64M64Effect 0x11a502 14 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 551) (.exec 0x11a502 (LoadPre 0x11a502 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11a502 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a502 14 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 552) (.exec 0x11a50a (StorePre 0x11a50a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11a50a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a50a 14 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[550, 4]
    (.letOp (n := 553) (.out 0x11a50f (atFlags (condHolds 4) (setccR8Effect 0x11a50f 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[536, 545]
    (.letOp (n := 554) (.exec 0x11a50f (fun s => s.RIP = 0x11a50f) (atFlags (condHolds 4) (setccR8Effect 0x11a50f 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[536, 545]
    (.letOp (n := 555) (.out 0x11a512 (orR8R8Effect 0x11a512 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[553, 543]
    (.letOp (n := 556) (.exec 0x11a512 (fun s => s.RIP = 0x11a512) (orR8R8Effect 0x11a512 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[553, 543]
    (.letOp (n := 557) (.out 0x11a514 (movzxR32R8Effect 0x11a514 3 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[555]
    (.letOp (n := 558) (.exec 0x11a514 (fun s => s.RIP = 0x11a514) (movzxR32R8Effect 0x11a514 3 7 1) (Reg.operands [.gpr 1] [])) #v[555]
    (.letOp (n := 559) (.out 0x11a517 (callEffect (fun _ => 0x127d50) 0x11a51c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 560) (.exec 0x11a517 (PushPre 0x11a517 5) (callEffect (fun _ => 0x127d50) 0x11a51c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 561) (.const ⟨64, 0x11a51c⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 543), (1, 555), (2, 462), (3, 547), (4, 559), (5, 419), (6, 540), (7, 557), (8, 488), (9, 421), (10, 480), (11, 474), (12, 385), (13, 372), (14, 550), (15, 381), (22, 22), (39, 39), (50, 50), (51, 51)] 562⟩ { target := .l11a51c, kept := #v[], arity := rfl, guard := some (Fin.last 561) })))))))))))))))))))))))))))))))))))))))

def bytes_l11a14c_11 : List UInt8 :=
  [0x48, 0x09, 0xFE, 0x48, 0x21, 0xF9, 0x48, 0xC1, 0xEF, 0x34, 0x48, 0x01, 0xC7, 0x48, 0xB8, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x0F, 0x00, 0x48, 0x31, 0xF8, 0x48, 0x21, 0xC1, 0x4C, 0x21, 0xEE,
    0x48, 0x09, 0xFE, 0x0F, 0x94, 0xC0, 0x4C, 0x39, 0xE9, 0x48, 0x8B, 0x9C, 0x24, 0xA0, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x5C, 0x24, 0x20, 0x4C, 0x8B, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0x74, 0x24, 0x18, 0x0F, 0x94, 0xC1, 0x08, 0xC1, 0x0F, 0xB6, 0xF9, 0xE8, 0x34, 0xD8, 0x00, 0x00]

theorem code_l11a14c_11 : ∀ x ∈ codeRange 0x11a4cc bytes_l11a14c_11, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1a4cc 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l11a14c_10 : Block Op Label signature Reg.count 484 :=
  .letOp (n := 484) (.out 0x11a486 (addR64R64Effect 0x11a486 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[482, 468]
    (.letOp (n := 485) (.exec 0x11a486 (fun s => s.RIP = 0x11a486) (addR64R64Effect 0x11a486 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[482, 468]
    (.letOp (n := 486) (.out 0x11a489 (andR64R64Effect 0x11a489 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[433, 372]
    (.letOp (n := 487) (.exec 0x11a489 (fun s => s.RIP = 0x11a489) (andR64R64Effect 0x11a489 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[433, 372]
    (.letOp (n := 488) (.out 0x11a48c (subR64R64Effect 0x11a48c 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[484, 486]
    (.letOp (n := 489) (.exec 0x11a48c (fun s => s.RIP = 0x11a48c) (subR64R64Effect 0x11a48c 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[484, 486]
    (.letOp (n := 490) (.out 0x11a48f (andR64R64Effect 0x11a48f 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[456, 440]
    (.letOp (n := 491) (.exec 0x11a48f (fun s => s.RIP = 0x11a48f) (andR64R64Effect 0x11a48f 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[456, 440]
    (.letOp (n := 492) (.out 0x11a492 (movR64Imm64Effect 0x11a492 1 0x3ffffbfffff0bc) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 493) (.exec 0x11a492 (fun s => s.RIP = 0x11a492) (movR64Imm64Effect 0x11a492 1 0x3ffffbfffff0bc) (Reg.operands [] [])) #v[]
    (.letOp (n := 494) (.out 0x11a49c (addR64R64Effect 0x11a49c 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[492, 448]
    (.letOp (n := 495) (.exec 0x11a49c (fun s => s.RIP = 0x11a49c) (addR64R64Effect 0x11a49c 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[492, 448]
    (.letOp (n := 496) (.out 0x11a49f (addR64R64Effect 0x11a49f 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[494, 466]
    (.letOp (n := 497) (.exec 0x11a49f (fun s => s.RIP = 0x11a49f) (addR64R64Effect 0x11a49f 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[494, 466]
    (.letOp (n := 498) (.out 0x11a4a2 (movR64R64Effect 0x11a4a2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[496]
    (.letOp (n := 499) (.exec 0x11a4a2 (fun s => s.RIP = 0x11a4a2) (movR64R64Effect 0x11a4a2 7 1) (Reg.operands [.gpr 1] [])) #v[496]
    (.letOp (n := 500) (.out 0x11a4a5 (shrR64Effect 0x11a4a5 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[498]
    (.letOp (n := 501) (.exec 0x11a4a5 (fun s => s.RIP = 0x11a4a5) (shrR64Effect 0x11a4a5 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[498]
    (.letOp (n := 502) (.out 0x11a4a9 (addR64R64Effect 0x11a4a9 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[500, 474]
    (.letOp (n := 503) (.exec 0x11a4a9 (fun s => s.RIP = 0x11a4a9) (addR64R64Effect 0x11a4a9 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[500, 474]
    (.letOp (n := 504) (.out 0x11a4ac (movR64R64Effect 0x11a4ac 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[502]
    (.letOp (n := 505) (.exec 0x11a4ac (fun s => s.RIP = 0x11a4ac) (movR64R64Effect 0x11a4ac 6 7) (Reg.operands [.gpr 7] [])) #v[502]
    (.letOp (n := 506) (.out 0x11a4af (orR64R64Effect 0x11a4af 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[504, 496]
    (.letOp (n := 507) (.exec 0x11a4af (fun s => s.RIP = 0x11a4af) (orR64R64Effect 0x11a4af 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[504, 496]
    (.letOp (n := 508) (.out 0x11a4b2 (xorR64R64Effect 0x11a4b2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[496, 462]
    (.letOp (n := 509) (.exec 0x11a4b2 (fun s => s.RIP = 0x11a4b2) (xorR64R64Effect 0x11a4b2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[496, 462]
    (.letOp (n := 510) (.out 0x11a4b5 (andR64R64Effect 0x11a4b5 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[508, 502]
    (.letOp (n := 511) (.exec 0x11a4b5 (fun s => s.RIP = 0x11a4b5) (andR64R64Effect 0x11a4b5 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[508, 502]
    (.letOp (n := 512) (.out 0x11a4b8 (shrR64Effect 0x11a4b8 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[502]
    (.letOp (n := 513) (.exec 0x11a4b8 (fun s => s.RIP = 0x11a4b8) (shrR64Effect 0x11a4b8 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[502]
    (.letOp (n := 514) (.out 0x11a4bc (addR64R64Effect 0x11a4bc 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[512, 480]
    (.letOp (n := 515) (.exec 0x11a4bc (fun s => s.RIP = 0x11a4bc) (addR64R64Effect 0x11a4bc 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[512, 480]
    (.letOp (n := 516) (.out 0x11a4bf (orR64R64Effect 0x11a4bf 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[506, 514]
    (.letOp (n := 517) (.exec 0x11a4bf (fun s => s.RIP = 0x11a4bf) (orR64R64Effect 0x11a4bf 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[506, 514]
    (.letOp (n := 518) (.out 0x11a4c2 (andR64R64Effect 0x11a4c2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[510, 514]
    (.letOp (n := 519) (.exec 0x11a4c2 (fun s => s.RIP = 0x11a4c2) (andR64R64Effect 0x11a4c2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[510, 514]
    (.letOp (n := 520) (.out 0x11a4c5 (shrR64Effect 0x11a4c5 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[514]
    (.letOp (n := 521) (.exec 0x11a4c5 (fun s => s.RIP = 0x11a4c5) (shrR64Effect 0x11a4c5 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[514]
    (.letOp (n := 522) (.out 0x11a4c9 (addR64R64Effect 0x11a4c9 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[520, 488]
    (.letOp (n := 523) (.exec 0x11a4c9 (fun s => s.RIP = 0x11a4c9) (addR64R64Effect 0x11a4c9 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[520, 488]
    (b_l11a14c_11))))))))))))))))))))))))))))))))))))))))

def bytes_l11a14c_10 : List UInt8 :=
  [0x49, 0x01, 0xF0, 0x4C, 0x21, 0xE9, 0x49, 0x29, 0xC8, 0x4C, 0x21, 0xF0, 0x48, 0xB9, 0xBC, 0xF0,
    0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00, 0x48, 0x01, 0xD9, 0x48, 0x01, 0xF9, 0x48, 0x89, 0xCF, 0x48,
    0xC1, 0xEF, 0x34, 0x4C, 0x01, 0xDF, 0x48, 0x89, 0xFE, 0x48, 0x09, 0xCE, 0x48, 0x31, 0xD1, 0x48,
    0x21, 0xF9, 0x48, 0xC1, 0xEF, 0x34, 0x4C, 0x01, 0xD7, 0x48, 0x09, 0xFE, 0x48, 0x21, 0xF9, 0x48,
    0xC1, 0xEF, 0x34, 0x4C, 0x01, 0xC7] ++ bytes_l11a14c_11

theorem code_l11a14c_10 : ∀ x ∈ codeRange 0x11a486 bytes_l11a14c_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a486 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11a14c_11

def b_l11a14c_9 : Block Op Label signature Reg.count 444 :=
  .letOp (n := 444) (.out 0x11a419 (addR64R64Effect 0x11a419 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[442, 438]
    (.letOp (n := 445) (.exec 0x11a419 (fun s => s.RIP = 0x11a419) (addR64R64Effect 0x11a419 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[442, 438]
    (.letOp (n := 446) (.out 0x11a41c (movR64M64Effect 0x11a41c 3 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 447) (.exec 0x11a41c (LoadPre 0x11a41c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x11a41c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a41c 3 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 448) (.out 0x11a424 (subR64R64Effect 0x11a424 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[446, 282]
    (.letOp (n := 449) (.exec 0x11a424 (fun s => s.RIP = 0x11a424) (subR64R64Effect 0x11a424 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[446, 282]
    (.letOp (n := 450) (.out 0x11a427 (movR64M64Effect 0x11a427 2 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 451) (.exec 0x11a427 (LoadPre 0x11a427 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x11a427 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a427 2 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 452) (.out 0x11a42f (subR64R64Effect 0x11a42f 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[450, 444]
    (.letOp (n := 453) (.exec 0x11a42f (fun s => s.RIP = 0x11a42f) (subR64R64Effect 0x11a42f 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[450, 444]
    (.letOp (n := 454) (.out 0x11a432 (movR64Imm64Effect 0x11a432 0 0x3fffffffffffc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 455) (.exec 0x11a432 (fun s => s.RIP = 0x11a432) (movR64Imm64Effect 0x11a432 0 0x3fffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 456) (.out 0x11a43c (addR64R64Effect 0x11a43c 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[454, 452]
    (.letOp (n := 457) (.exec 0x11a43c (fun s => s.RIP = 0x11a43c) (addR64R64Effect 0x11a43c 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[454, 452]
    (.letOp (n := 458) (.out 0x11a43f (movR64R64Effect 0x11a43f 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[456]
    (.letOp (n := 459) (.exec 0x11a43f (fun s => s.RIP = 0x11a43f) (movR64R64Effect 0x11a43f 6 0) (Reg.operands [.gpr 0] [])) #v[456]
    (.letOp (n := 460) (.out 0x11a442 (shrR64Effect 0x11a442 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[458]
    (.letOp (n := 461) (.exec 0x11a442 (fun s => s.RIP = 0x11a442) (shrR64Effect 0x11a442 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[458]
    (.letOp (n := 462) (.out 0x11a446 (movR64Imm64Effect 0x11a446 2 0x1000003d0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 463) (.exec 0x11a446 (fun s => s.RIP = 0x11a446) (movR64Imm64Effect 0x11a446 2 0x1000003d0) (Reg.operands [] [])) #v[]
    (.letOp (n := 464) (.out 0x11a450 (leaR64Effect 0x11a450 7 (.base 2 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[462]
    (.letOp (n := 465) (.exec 0x11a450 (fun s => s.RIP = 0x11a450) (leaR64Effect 0x11a450 7 (.base 2 (.d8 0x1))) (Reg.operands [.gpr 2] [])) #v[462]
    (.letOp (n := 466) (.out 0x11a454 (imulR64R64Effect 0x11a454 4 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[464, 460]
    (.letOp (n := 467) (.exec 0x11a454 (fun s => s.RIP = 0x11a454) (imulR64R64Effect 0x11a454 4 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[464, 460]
    (.letOp (n := 468) (.out 0x11a458 (movR64Imm64Effect 0x11a458 6 0x3ffffffffffffc) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 469) (.exec 0x11a458 (fun s => s.RIP = 0x11a458) (movR64Imm64Effect 0x11a458 6 0x3ffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 470) (.out 0x11a462 (movR64M64Effect 0x11a462 11 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 471) (.exec 0x11a462 (LoadPre 0x11a462 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x11a462 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a462 11 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 472) (.out 0x11a46a (addR64R64Effect 0x11a46a 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[470, 468]
    (.letOp (n := 473) (.exec 0x11a46a (fun s => s.RIP = 0x11a46a) (addR64R64Effect 0x11a46a 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[470, 468]
    (.letOp (n := 474) (.out 0x11a46d (subR64R64Effect 0x11a46d 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[472, 341]
    (.letOp (n := 475) (.exec 0x11a46d (fun s => s.RIP = 0x11a46d) (subR64R64Effect 0x11a46d 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[472, 341]
    (.letOp (n := 476) (.out 0x11a470 (movR64M64Effect 0x11a470 10 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 477) (.exec 0x11a470 (LoadPre 0x11a470 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x11a470 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a470 10 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 478) (.out 0x11a478 (addR64R64Effect 0x11a478 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[476, 468]
    (.letOp (n := 479) (.exec 0x11a478 (fun s => s.RIP = 0x11a478) (addR64R64Effect 0x11a478 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[476, 468]
    (.letOp (n := 480) (.out 0x11a47b (subR64R64Effect 0x11a47b 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[478, 421]
    (.letOp (n := 481) (.exec 0x11a47b (fun s => s.RIP = 0x11a47b) (subR64R64Effect 0x11a47b 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[478, 421]
    (.letOp (n := 482) (.out 0x11a47e (movR64M64Effect 0x11a47e 8 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 483) (.exec 0x11a47e (LoadPre 0x11a47e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x11a47e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a47e 8 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11a14c_10))))))))))))))))))))))))))))))))))))))))

def bytes_l11a14c_9 : List UInt8 :=
  [0x48, 0x01, 0xD6, 0x48, 0x8B, 0x9C, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x29, 0xFB, 0x48, 0x8B,
    0x94, 0x24, 0x40, 0x01, 0x00, 0x00, 0x48, 0x29, 0xF2, 0x48, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x03, 0x00, 0x48, 0x01, 0xD0, 0x48, 0x89, 0xC6, 0x48, 0xC1, 0xEE, 0x30, 0x48, 0xBA, 0xD0,
    0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7A, 0x01, 0x48, 0x0F, 0xAF, 0xFE, 0x48,
    0xBE, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00, 0x4C, 0x8B, 0x9C, 0x24, 0x48, 0x01, 0x00,
    0x00, 0x49, 0x01, 0xF3, 0x4D, 0x29, 0xC3, 0x4C, 0x8B, 0x94, 0x24, 0x30, 0x01, 0x00, 0x00, 0x49,
    0x01, 0xF2, 0x4D, 0x29, 0xCA, 0x4C, 0x8B, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00] ++ bytes_l11a14c_10

theorem code_l11a14c_9 : ∀ x ∈ codeRange 0x11a419 bytes_l11a14c_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a419 109 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11a14c_10

def b_l11a14c_8 : Block Op Label signature Reg.count 398 :=
  .letOp (n := 398) (.out 0x11a3ba (addR64M64Effect 0x11a3ba 9 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[392, 4]
    (.letOp (n := 399) (.out 0x11a3ba (addR64M64Effect 0x11a3ba 9 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 4] []) (.flag .CF)) #v[392, 4]
    (.letOp (n := 400) (.exec 0x11a3ba (LoadPre 0x11a3ba (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11a3ba + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11a3ba 9 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[392, 4]
    (.letOp (n := 401) (.out 0x11a3c2 (atFlags StatusFlags.CF (adcR64M64Effect 0x11a3c2 5 (.sib 4 none 0 (.d32 0xf8)))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 5))) #v[396, 4, 399]
    (.letOp (n := 402) (.exec 0x11a3c2 (LoadPre 0x11a3c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11a3c2 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11a3c2 5 (.sib 4 none 0 (.d32 0xf8)))) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[396, 4, 399]
    (.letOp (n := 403) (.out 0x11a3ca (addR64R64Effect 0x11a3ca 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[398, 379]
    (.letOp (n := 404) (.out 0x11a3ca (addR64R64Effect 0x11a3ca 9 1) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 1] []) (.flag .CF)) #v[398, 379]
    (.letOp (n := 405) (.exec 0x11a3ca (fun s => s.RIP = 0x11a3ca) (addR64R64Effect 0x11a3ca 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[398, 379]
    (.letOp (n := 406) (.out 0x11a3cd (atFlags StatusFlags.CF (adcR64R64Effect 0x11a3cd 5 15)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[401, 381, 404]
    (.letOp (n := 407) (.exec 0x11a3cd (fun s => s.RIP = 0x11a3cd) (atFlags StatusFlags.CF (adcR64R64Effect 0x11a3cd 5 15)) (Reg.operands [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[401, 381, 404]
    (.letOp (n := 408) (.out 0x11a3d0 (addR64R64Effect 0x11a3d0 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[403, 339]
    (.letOp (n := 409) (.out 0x11a3d0 (addR64R64Effect 0x11a3d0 9 11) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 11] []) (.flag .CF)) #v[403, 339]
    (.letOp (n := 410) (.exec 0x11a3d0 (fun s => s.RIP = 0x11a3d0) (addR64R64Effect 0x11a3d0 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[403, 339]
    (.letOp (n := 411) (.out 0x11a3d3 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a3d3 5 0x0)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[406, 409]
    (.letOp (n := 412) (.exec 0x11a3d3 (fun s => s.RIP = 0x11a3d3) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a3d3 5 0x0)) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[406, 409]
    (.letOp (n := 413) (.out 0x11a3d7 (shldR64R64Effect 0x11a3d7 5 10 14 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[366, 363]
    (.letOp (n := 414) (.exec 0x11a3d7 (fun s => s.RIP = 0x11a3d7) (shldR64R64Effect 0x11a3d7 5 10 14 12) (Reg.operands [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[366, 363]
    (.letOp (n := 415) (.out 0x11a3dc (movR64Imm64Effect 0x11a3dc 1 0xffffffffffffe) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 416) (.exec 0x11a3dc (fun s => s.RIP = 0x11a3dc) (movR64Imm64Effect 0x11a3dc 1 0xffffffffffffe) (Reg.operands [] [])) #v[]
    (.letOp (n := 417) (.out 0x11a3e6 (andR64M64Effect 0x11a3e6 1 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[415, 4]
    (.letOp (n := 418) (.exec 0x11a3e6 (LoadPre 0x11a3e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11a3e6 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x11a3e6 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[415, 4]
    (.letOp (n := 419) (.out 0x11a3eb (shldR64R64Effect 0x11a3eb 5 5 9 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[411, 408]
    (.letOp (n := 420) (.exec 0x11a3eb (fun s => s.RIP = 0x11a3eb) (shldR64R64Effect 0x11a3eb 5 5 9 12) (Reg.operands [.gpr 5, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[411, 408]
    (.letOp (n := 421) (.out 0x11a3f0 (andR64R64Effect 0x11a3f0 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[408, 372]
    (.letOp (n := 422) (.exec 0x11a3f0 (fun s => s.RIP = 0x11a3f0) (andR64R64Effect 0x11a3f0 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[408, 372]
    (.letOp (n := 423) (.out 0x11a3f3 (movR64R64Effect 0x11a3f3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[413]
    (.letOp (n := 424) (.exec 0x11a3f3 (fun s => s.RIP = 0x11a3f3) (movR64R64Effect 0x11a3f3 0 10) (Reg.operands [.gpr 10] [])) #v[413]
    (.letOp (n := 425) (.out 0x11a3f6 (mulR64Effect 0x11a3f6 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[377, 423]
    (.letOp (n := 426) (.out 0x11a3f6 (mulR64Effect 0x11a3f6 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[377, 423]
    (.letOp (n := 427) (.exec 0x11a3f6 (fun s => s.RIP = 0x11a3f6) (mulR64Effect 0x11a3f6 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[377, 423]
    (.letOp (n := 428) (.out 0x11a3f9 (addR64R64Effect 0x11a3f9 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[417, 425]
    (.letOp (n := 429) (.out 0x11a3f9 (addR64R64Effect 0x11a3f9 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[417, 425]
    (.letOp (n := 430) (.exec 0x11a3f9 (fun s => s.RIP = 0x11a3f9) (addR64R64Effect 0x11a3f9 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[417, 425]
    (.letOp (n := 431) (.out 0x11a3fc (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a3fc 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[426, 429]
    (.letOp (n := 432) (.exec 0x11a3fc (fun s => s.RIP = 0x11a3fc) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a3fc 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[426, 429]
    (.letOp (n := 433) (.out 0x11a400 (addR64R64Effect 0x11a400 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[428, 419]
    (.letOp (n := 434) (.out 0x11a400 (addR64R64Effect 0x11a400 1 5) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 5] []) (.flag .CF)) #v[428, 419]
    (.letOp (n := 435) (.exec 0x11a400 (fun s => s.RIP = 0x11a400) (addR64R64Effect 0x11a400 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[428, 419]
    (.letOp (n := 436) (.out 0x11a403 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a403 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[431, 434]
    (.letOp (n := 437) (.exec 0x11a403 (fun s => s.RIP = 0x11a403) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a403 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[431, 434]
    (.letOp (n := 438) (.out 0x11a407 (shldR64R64Effect 0x11a407 5 2 1 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[436, 433]
    (.letOp (n := 439) (.exec 0x11a407 (fun s => s.RIP = 0x11a407) (shldR64R64Effect 0x11a407 5 2 1 12) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[436, 433]
    (.letOp (n := 440) (.out 0x11a40c (movR64Imm64Effect 0x11a40c 14 0xffffffffffff) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 441) (.exec 0x11a40c (fun s => s.RIP = 0x11a40c) (movR64Imm64Effect 0x11a40c 14 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 442) (.out 0x11a416 (andR64R64Effect 0x11a416 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[177, 440]
    (.letOp (n := 443) (.exec 0x11a416 (fun s => s.RIP = 0x11a416) (andR64R64Effect 0x11a416 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[177, 440]
    (b_l11a14c_9))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11a14c_8 : List UInt8 :=
  [0x4C, 0x03, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x13, 0xAC, 0x24, 0xF8, 0x00, 0x00, 0x00,
    0x49, 0x01, 0xC9, 0x4C, 0x11, 0xFD, 0x4D, 0x01, 0xD9, 0x48, 0x83, 0xD5, 0x00, 0x4D, 0x0F, 0xA4,
    0xF2, 0x0C, 0x48, 0xB9, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x23, 0x4C, 0x24,
    0x68, 0x4C, 0x0F, 0xA4, 0xCD, 0x0C, 0x4D, 0x21, 0xE9, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0xE3, 0x48,
    0x01, 0xC1, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x01, 0xE9, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x0F, 0xA4,
    0xCA, 0x0C, 0x49, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x4C, 0x21, 0xF6] ++ bytes_l11a14c_9

theorem code_l11a14c_8 : ∀ x ∈ codeRange 0x11a3ba bytes_l11a14c_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a3ba 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11a14c_9

def b_l11a14c_7 : Block Op Label signature Reg.count 355 :=
  .letOp (n := 355) (.out 0x11a373 (movR64R64Effect 0x11a373 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[353]
    (.letOp (n := 356) (.exec 0x11a373 (fun s => s.RIP = 0x11a373) (movR64R64Effect 0x11a373 10 2) (Reg.operands [.gpr 2] [])) #v[353]
    (.letOp (n := 357) (.out 0x11a376 (movR64R64Effect 0x11a376 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[352]
    (.letOp (n := 358) (.exec 0x11a376 (fun s => s.RIP = 0x11a376) (movR64R64Effect 0x11a376 14 0) (Reg.operands [.gpr 0] [])) #v[352]
    (.letOp (n := 359) (.out 0x11a379 (shldR64R64Effect 0x11a379 5 10 0 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[355, 352]
    (.letOp (n := 360) (.exec 0x11a379 (fun s => s.RIP = 0x11a379) (shldR64R64Effect 0x11a379 5 10 0 1) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[355, 352]
    (.letOp (n := 361) (.out 0x11a37e (addR64R64Effect 0x11a37e 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[357, 352]
    (.letOp (n := 362) (.exec 0x11a37e (fun s => s.RIP = 0x11a37e) (addR64R64Effect 0x11a37e 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[357, 352]
    (.letOp (n := 363) (.out 0x11a381 (addR64R64Effect 0x11a381 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[361, 314]
    (.letOp (n := 364) (.out 0x11a381 (addR64R64Effect 0x11a381 14 5) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 5] []) (.flag .CF)) #v[361, 314]
    (.letOp (n := 365) (.exec 0x11a381 (fun s => s.RIP = 0x11a381) (addR64R64Effect 0x11a381 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[361, 314]
    (.letOp (n := 366) (.out 0x11a384 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a384 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[359, 364]
    (.letOp (n := 367) (.exec 0x11a384 (fun s => s.RIP = 0x11a384) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a384 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[359, 364]
    (.letOp (n := 368) (.out 0x11a388 (movR64R64Effect 0x11a388 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[363]
    (.letOp (n := 369) (.exec 0x11a388 (fun s => s.RIP = 0x11a388) (movR64R64Effect 0x11a388 0 14) (Reg.operands [.gpr 14] [])) #v[363]
    (.letOp (n := 370) (.out 0x11a38b (andR64R64Effect 0x11a38b 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[368, 318]
    (.letOp (n := 371) (.exec 0x11a38b (fun s => s.RIP = 0x11a38b) (andR64R64Effect 0x11a38b 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[368, 318]
    (.letOp (n := 372) (.out 0x11a38e (movR64R64Effect 0x11a38e 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[318]
    (.letOp (n := 373) (.exec 0x11a38e (fun s => s.RIP = 0x11a38e) (movR64R64Effect 0x11a38e 13 1) (Reg.operands [.gpr 1] [])) #v[318]
    (.letOp (n := 374) (.out 0x11a391 (mulR64Effect 0x11a391 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[320, 370]
    (.letOp (n := 375) (.out 0x11a391 (mulR64Effect 0x11a391 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[320, 370]
    (.letOp (n := 376) (.exec 0x11a391 (fun s => s.RIP = 0x11a391) (mulR64Effect 0x11a391 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[320, 370]
    (.letOp (n := 377) (.out 0x11a394 (movR64R64Effect 0x11a394 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[320]
    (.letOp (n := 378) (.exec 0x11a394 (fun s => s.RIP = 0x11a394) (movR64R64Effect 0x11a394 3 15) (Reg.operands [.gpr 15] [])) #v[320]
    (.letOp (n := 379) (.out 0x11a397 (movR64R64Effect 0x11a397 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[374]
    (.letOp (n := 380) (.exec 0x11a397 (fun s => s.RIP = 0x11a397) (movR64R64Effect 0x11a397 1 0) (Reg.operands [.gpr 0] [])) #v[374]
    (.letOp (n := 381) (.out 0x11a39a (movR64R64Effect 0x11a39a 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[375]
    (.letOp (n := 382) (.exec 0x11a39a (fun s => s.RIP = 0x11a39a) (movR64R64Effect 0x11a39a 15 2) (Reg.operands [.gpr 2] [])) #v[375]
    (.letOp (n := 383) (.out 0x11a39d (movR64M64Effect 0x11a39d 2 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 384) (.exec 0x11a39d (LoadPre 0x11a39d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x11a39d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a39d 2 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 385) (.out 0x11a3a5 (imulR64R64Effect 0x11a3a5 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[259, 383]
    (.letOp (n := 386) (.exec 0x11a3a5 (fun s => s.RIP = 0x11a3a5) (imulR64R64Effect 0x11a3a5 4 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[259, 383]
    (.letOp (n := 387) (.out 0x11a3a9 (movR64M64Effect 0x11a3a9 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 388) (.exec 0x11a3a9 (LoadPre 0x11a3a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11a3a9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11a3a9 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 389) (.out 0x11a3ae (mulR64Effect 0x11a3ae 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[383, 387]
    (.letOp (n := 390) (.out 0x11a3ae (mulR64Effect 0x11a3ae 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[383, 387]
    (.letOp (n := 391) (.exec 0x11a3ae (fun s => s.RIP = 0x11a3ae) (mulR64Effect 0x11a3ae 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[383, 387]
    (.letOp (n := 392) (.out 0x11a3b1 (movR64R64Effect 0x11a3b1 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[389]
    (.letOp (n := 393) (.exec 0x11a3b1 (fun s => s.RIP = 0x11a3b1) (movR64R64Effect 0x11a3b1 9 0) (Reg.operands [.gpr 0] [])) #v[389]
    (.letOp (n := 394) (.out 0x11a3b4 (movR64R64Effect 0x11a3b4 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[390]
    (.letOp (n := 395) (.exec 0x11a3b4 (fun s => s.RIP = 0x11a3b4) (movR64R64Effect 0x11a3b4 5 2) (Reg.operands [.gpr 2] [])) #v[390]
    (.letOp (n := 396) (.out 0x11a3b7 (addR64R64Effect 0x11a3b7 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[394, 385]
    (.letOp (n := 397) (.exec 0x11a3b7 (fun s => s.RIP = 0x11a3b7) (addR64R64Effect 0x11a3b7 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[394, 385]
    (b_l11a14c_8)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11a14c_7 : List UInt8 :=
  [0x49, 0x89, 0xD2, 0x49, 0x89, 0xC6, 0x49, 0x0F, 0xA4, 0xC2, 0x01, 0x49, 0x01, 0xC6, 0x49, 0x01,
    0xEE, 0x49, 0x83, 0xD2, 0x00, 0x4C, 0x89, 0xF0, 0x48, 0x21, 0xC8, 0x49, 0x89, 0xCD, 0x49, 0xF7,
    0xE7, 0x4C, 0x89, 0xFB, 0x48, 0x89, 0xC1, 0x49, 0x89, 0xD7, 0x48, 0x8B, 0x94, 0x24, 0x00, 0x01,
    0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xE2, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0xF7, 0xE2, 0x49, 0x89,
    0xC1, 0x48, 0x89, 0xD5, 0x4C, 0x01, 0xE5] ++ bytes_l11a14c_8

theorem code_l11a14c_7 : ∀ x ∈ codeRange 0x11a373 bytes_l11a14c_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a373 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11a14c_8

def b_l11a14c_6 : Block Op Label signature Reg.count 312 :=
  .letOp (n := 312) (.out 0x11a31b (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a31b 5 0x0)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[307, 310]
    (.letOp (n := 313) (.exec 0x11a31b (fun s => s.RIP = 0x11a31b) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a31b 5 0x0)) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[307, 310]
    (.letOp (n := 314) (.out 0x11a31f (shldR64R64Effect 0x11a31f 5 5 0 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[312, 309]
    (.letOp (n := 315) (.exec 0x11a31f (fun s => s.RIP = 0x11a31f) (shldR64R64Effect 0x11a31f 5 5 0 12) (Reg.operands [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[312, 309]
    (.letOp (n := 316) (.out 0x11a324 (andR64R64Effect 0x11a324 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[309, 280]
    (.letOp (n := 317) (.exec 0x11a324 (fun s => s.RIP = 0x11a324) (andR64R64Effect 0x11a324 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[309, 280]
    (.letOp (n := 318) (.out 0x11a327 (movR64R64Effect 0x11a327 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[280]
    (.letOp (n := 319) (.exec 0x11a327 (fun s => s.RIP = 0x11a327) (movR64R64Effect 0x11a327 1 15) (Reg.operands [.gpr 15] [])) #v[280]
    (.letOp (n := 320) (.out 0x11a32a (movR64Imm64Effect 0x11a32a 15 0x1000003d10) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 321) (.exec 0x11a32a (fun s => s.RIP = 0x11a32a) (movR64Imm64Effect 0x11a32a 15 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 322) (.out 0x11a334 (mulR64Effect 0x11a334 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[320, 316]
    (.letOp (n := 323) (.out 0x11a334 (mulR64Effect 0x11a334 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[320, 316]
    (.letOp (n := 324) (.exec 0x11a334 (fun s => s.RIP = 0x11a334) (mulR64Effect 0x11a334 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[320, 316]
    (.letOp (n := 325) (.out 0x11a337 (movR64R64Effect 0x11a337 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[323]
    (.letOp (n := 326) (.exec 0x11a337 (fun s => s.RIP = 0x11a337) (movR64R64Effect 0x11a337 11 2) (Reg.operands [.gpr 2] [])) #v[323]
    (.letOp (n := 327) (.out 0x11a33a (movR64R64Effect 0x11a33a 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[322]
    (.letOp (n := 328) (.exec 0x11a33a (fun s => s.RIP = 0x11a33a) (movR64R64Effect 0x11a33a 8 0) (Reg.operands [.gpr 0] [])) #v[322]
    (.letOp (n := 329) (.out 0x11a33d (addR64R64Effect 0x11a33d 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[327, 272]
    (.letOp (n := 330) (.out 0x11a33d (addR64R64Effect 0x11a33d 8 14) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 14] []) (.flag .CF)) #v[327, 272]
    (.letOp (n := 331) (.exec 0x11a33d (fun s => s.RIP = 0x11a33d) (addR64R64Effect 0x11a33d 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[327, 272]
    (.letOp (n := 332) (.out 0x11a340 (atFlags StatusFlags.CF (adcR64R64Effect 0x11a340 11 9)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[325, 276, 330]
    (.letOp (n := 333) (.exec 0x11a340 (fun s => s.RIP = 0x11a340) (atFlags StatusFlags.CF (adcR64R64Effect 0x11a340 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[325, 276, 330]
    (.letOp (n := 334) (.out 0x11a343 (addR64R64Effect 0x11a343 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[329, 278]
    (.letOp (n := 335) (.out 0x11a343 (addR64R64Effect 0x11a343 8 10) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 10] []) (.flag .CF)) #v[329, 278]
    (.letOp (n := 336) (.exec 0x11a343 (fun s => s.RIP = 0x11a343) (addR64R64Effect 0x11a343 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[329, 278]
    (.letOp (n := 337) (.out 0x11a346 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a346 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[332, 335]
    (.letOp (n := 338) (.exec 0x11a346 (fun s => s.RIP = 0x11a346) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a346 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[332, 335]
    (.letOp (n := 339) (.out 0x11a34a (shldR64R64Effect 0x11a34a 5 11 8 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[337, 334]
    (.letOp (n := 340) (.exec 0x11a34a (fun s => s.RIP = 0x11a34a) (shldR64R64Effect 0x11a34a 5 11 8 12) (Reg.operands [.gpr 11, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[337, 334]
    (.letOp (n := 341) (.out 0x11a34f (andR64R64Effect 0x11a34f 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[334, 318]
    (.letOp (n := 342) (.exec 0x11a34f (fun s => s.RIP = 0x11a34f) (andR64R64Effect 0x11a34f 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[334, 318]
    (.letOp (n := 343) (.out 0x11a352 (movR64M64Effect 0x11a352 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 344) (.exec 0x11a352 (LoadPre 0x11a352 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11a352 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a352 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 345) (.out 0x11a35a (mulR64Effect 0x11a35a 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[343, 343]
    (.letOp (n := 346) (.out 0x11a35a (mulR64Effect 0x11a35a 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 0] []) (.reg (.gpr 2))) #v[343, 343]
    (.letOp (n := 347) (.exec 0x11a35a (fun s => s.RIP = 0x11a35a) (mulR64Effect 0x11a35a 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[343, 343]
    (.letOp (n := 348) (.exec 0x11a35d (StorePre 0x11a35d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11a35d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11a35d 2 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[346, 4]
    (.letOp (n := 349) (.exec 0x11a365 (StorePre 0x11a365 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11a365 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11a365 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[345, 4]
    (.letOp (n := 350) (.out 0x11a36d (movR64R64Effect 0x11a36d 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[284]
    (.letOp (n := 351) (.exec 0x11a36d (fun s => s.RIP = 0x11a36d) (movR64R64Effect 0x11a36d 0 13) (Reg.operands [.gpr 13] [])) #v[284]
    (.letOp (n := 352) (.out 0x11a370 (mulR64Effect 0x11a370 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[209, 350]
    (.letOp (n := 353) (.out 0x11a370 (mulR64Effect 0x11a370 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[209, 350]
    (.letOp (n := 354) (.exec 0x11a370 (fun s => s.RIP = 0x11a370) (mulR64Effect 0x11a370 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[209, 350]
    (b_l11a14c_7)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11a14c_6 : List UInt8 :=
  [0x48, 0x83, 0xD5, 0x00, 0x48, 0x0F, 0xA4, 0xC5, 0x0C, 0x4C, 0x21, 0xF8, 0x4C, 0x89, 0xF9, 0x49,
    0xBF, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE7, 0x49, 0x89, 0xD3, 0x49,
    0x89, 0xC0, 0x4D, 0x01, 0xF0, 0x4D, 0x11, 0xCB, 0x4D, 0x01, 0xD0, 0x49, 0x83, 0xD3, 0x00, 0x4D,
    0x0F, 0xA4, 0xC3, 0x0C, 0x49, 0x21, 0xC8, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE0, 0x48, 0x89, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xF0, 0x00,
    0x00, 0x00, 0x4C, 0x89, 0xE8, 0x48, 0xF7, 0xE3] ++ bytes_l11a14c_7

theorem code_l11a14c_6 : ∀ x ∈ codeRange 0x11a31b bytes_l11a14c_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a31b 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11a14c_7

def b_l11a14c_5 : Block Op Label signature Reg.count 268 :=
  .letOp (n := 268) (.exec 0x11a2cd (StorePre 0x11a2cd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11a2cd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a2cd 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[266, 4]
    (.letOp (n := 269) (.out 0x11a2d2 (mulR64Effect 0x11a2d2 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[68, 266]
    (.letOp (n := 270) (.out 0x11a2d2 (mulR64Effect 0x11a2d2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[68, 266]
    (.letOp (n := 271) (.exec 0x11a2d2 (fun s => s.RIP = 0x11a2d2) (mulR64Effect 0x11a2d2 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[68, 266]
    (.letOp (n := 272) (.out 0x11a2d5 (movR64R64Effect 0x11a2d5 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[269]
    (.letOp (n := 273) (.exec 0x11a2d5 (fun s => s.RIP = 0x11a2d5) (movR64R64Effect 0x11a2d5 14 0) (Reg.operands [.gpr 0] [])) #v[269]
    (.letOp (n := 274) (.out 0x11a2d8 (movR64R64Effect 0x11a2d8 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[270]
    (.letOp (n := 275) (.exec 0x11a2d8 (fun s => s.RIP = 0x11a2d8) (movR64R64Effect 0x11a2d8 9 2) (Reg.operands [.gpr 2] [])) #v[270]
    (.letOp (n := 276) (.out 0x11a2db (addR64R64Effect 0x11a2db 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[274, 264]
    (.letOp (n := 277) (.exec 0x11a2db (fun s => s.RIP = 0x11a2db) (addR64R64Effect 0x11a2db 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[274, 264]
    (.letOp (n := 278) (.out 0x11a2de (shldR64R64Effect 0x11a2de 5 10 7 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[254, 251]
    (.letOp (n := 279) (.exec 0x11a2de (fun s => s.RIP = 0x11a2de) (shldR64R64Effect 0x11a2de 5 10 7 12) (Reg.operands [.gpr 10, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[254, 251]
    (.letOp (n := 280) (.out 0x11a2e3 (movR64Imm64Effect 0x11a2e3 15 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 281) (.exec 0x11a2e3 (fun s => s.RIP = 0x11a2e3) (movR64Imm64Effect 0x11a2e3 15 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 282) (.out 0x11a2ed (andR64R64Effect 0x11a2ed 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[251, 280]
    (.letOp (n := 283) (.exec 0x11a2ed (fun s => s.RIP = 0x11a2ed) (andR64R64Effect 0x11a2ed 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[251, 280]
    (.letOp (n := 284) (.out 0x11a2f0 (movR64M64Effect 0x11a2f0 13 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 285) (.exec 0x11a2f0 (LoadPre 0x11a2f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11a2f0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a2f0 13 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 286) (.out 0x11a2f8 (movR64R64Effect 0x11a2f8 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[284]
    (.letOp (n := 287) (.exec 0x11a2f8 (fun s => s.RIP = 0x11a2f8) (movR64R64Effect 0x11a2f8 0 13) (Reg.operands [.gpr 13] [])) #v[284]
    (.letOp (n := 288) (.out 0x11a2fb (mulR64Effect 0x11a2fb 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[284, 286]
    (.letOp (n := 289) (.out 0x11a2fb (mulR64Effect 0x11a2fb 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[284, 286]
    (.letOp (n := 290) (.exec 0x11a2fb (fun s => s.RIP = 0x11a2fb) (mulR64Effect 0x11a2fb 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[284, 286]
    (.letOp (n := 291) (.out 0x11a2fe (movR64R64Effect 0x11a2fe 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[289]
    (.letOp (n := 292) (.exec 0x11a2fe (fun s => s.RIP = 0x11a2fe) (movR64R64Effect 0x11a2fe 5 2) (Reg.operands [.gpr 2] [])) #v[289]
    (.letOp (n := 293) (.out 0x11a301 (movR64R64Effect 0x11a301 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[288]
    (.letOp (n := 294) (.exec 0x11a301 (fun s => s.RIP = 0x11a301) (movR64R64Effect 0x11a301 1 0) (Reg.operands [.gpr 0] [])) #v[288]
    (.letOp (n := 295) (.out 0x11a304 (movR64R64Effect 0x11a304 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[202]
    (.letOp (n := 296) (.exec 0x11a304 (fun s => s.RIP = 0x11a304) (movR64R64Effect 0x11a304 0 11) (Reg.operands [.gpr 11] [])) #v[202]
    (.letOp (n := 297) (.out 0x11a307 (mulR64Effect 0x11a307 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[209, 295]
    (.letOp (n := 298) (.out 0x11a307 (mulR64Effect 0x11a307 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[209, 295]
    (.letOp (n := 299) (.exec 0x11a307 (fun s => s.RIP = 0x11a307) (mulR64Effect 0x11a307 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[209, 295]
    (.letOp (n := 300) (.out 0x11a30a (shldR64R64Effect 0x11a30a 5 2 0 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[298, 297]
    (.letOp (n := 301) (.exec 0x11a30a (fun s => s.RIP = 0x11a30a) (shldR64R64Effect 0x11a30a 5 2 0 1) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[298, 297]
    (.letOp (n := 302) (.out 0x11a30f (addR64R64Effect 0x11a30f 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[297, 297]
    (.letOp (n := 303) (.exec 0x11a30f (fun s => s.RIP = 0x11a30f) (addR64R64Effect 0x11a30f 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[297, 297]
    (.letOp (n := 304) (.out 0x11a312 (addR64R64Effect 0x11a312 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[302, 293]
    (.letOp (n := 305) (.out 0x11a312 (addR64R64Effect 0x11a312 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[302, 293]
    (.letOp (n := 306) (.exec 0x11a312 (fun s => s.RIP = 0x11a312) (addR64R64Effect 0x11a312 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[302, 293]
    (.letOp (n := 307) (.out 0x11a315 (atFlags StatusFlags.CF (adcR64R64Effect 0x11a315 5 2)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[291, 300, 305]
    (.letOp (n := 308) (.exec 0x11a315 (fun s => s.RIP = 0x11a315) (atFlags StatusFlags.CF (adcR64R64Effect 0x11a315 5 2)) (Reg.operands [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[291, 300, 305]
    (.letOp (n := 309) (.out 0x11a318 (addR64R64Effect 0x11a318 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[304, 232]
    (.letOp (n := 310) (.out 0x11a318 (addR64R64Effect 0x11a318 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[304, 232]
    (.letOp (n := 311) (.exec 0x11a318 (fun s => s.RIP = 0x11a318) (addR64R64Effect 0x11a318 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[304, 232]
    (b_l11a14c_6))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11a14c_5 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xC6, 0x49, 0x89, 0xD1, 0x49, 0x01,
    0xC9, 0x49, 0x0F, 0xA4, 0xFA, 0x0C, 0x49, 0xBF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x4C, 0x21, 0xFF, 0x4C, 0x8B, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE8, 0x49, 0xF7,
    0xE5, 0x48, 0x89, 0xD5, 0x48, 0x89, 0xC1, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0xE3, 0x48, 0x0F, 0xA4,
    0xC2, 0x01, 0x48, 0x01, 0xC0, 0x48, 0x01, 0xC8, 0x48, 0x11, 0xD5, 0x4C, 0x01, 0xC0] ++ bytes_l11a14c_6

theorem code_l11a14c_5 : ∀ x ∈ codeRange 0x11a2cd bytes_l11a14c_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a2cd 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11a14c_6

def b_l11a14c_4 : Block Op Label signature Reg.count 227 :=
  .letOp (n := 227) (.out 0x11a272 (addR64R64Effect 0x11a272 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[225, 182]
    (.letOp (n := 228) (.out 0x11a272 (addR64R64Effect 0x11a272 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[225, 182]
    (.letOp (n := 229) (.exec 0x11a272 (fun s => s.RIP = 0x11a272) (addR64R64Effect 0x11a272 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[225, 182]
    (.letOp (n := 230) (.out 0x11a275 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a275 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[223, 228]
    (.letOp (n := 231) (.exec 0x11a275 (fun s => s.RIP = 0x11a275) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a275 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[223, 228]
    (.letOp (n := 232) (.out 0x11a279 (shldR64R64Effect 0x11a279 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[230, 227]
    (.letOp (n := 233) (.exec 0x11a279 (fun s => s.RIP = 0x11a279) (shldR64R64Effect 0x11a279 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[230, 227]
    (.letOp (n := 234) (.out 0x11a27e (shlR64Effect 0x11a27e 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[227]
    (.letOp (n := 235) (.exec 0x11a27e (fun s => s.RIP = 0x11a27e) (shlR64Effect 0x11a27e 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[227]
    (.letOp (n := 236) (.out 0x11a282 (movR64Imm64Effect 0x11a282 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 237) (.exec 0x11a282 (fun s => s.RIP = 0x11a282) (movR64Imm64Effect 0x11a282 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 238) (.out 0x11a28c (andR64R64Effect 0x11a28c 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[234, 236]
    (.letOp (n := 239) (.exec 0x11a28c (fun s => s.RIP = 0x11a28c) (andR64R64Effect 0x11a28c 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[234, 236]
    (.letOp (n := 240) (.out 0x11a28f (orR64R64Effect 0x11a28f 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[238, 216]
    (.letOp (n := 241) (.exec 0x11a28f (fun s => s.RIP = 0x11a28f) (orR64R64Effect 0x11a28f 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[238, 216]
    (.letOp (n := 242) (.out 0x11a292 (movR64Imm64Effect 0x11a292 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 243) (.exec 0x11a292 (fun s => s.RIP = 0x11a292) (movR64Imm64Effect 0x11a292 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 244) (.out 0x11a29c (mulR64Effect 0x11a29c 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[242, 240]
    (.letOp (n := 245) (.out 0x11a29c (mulR64Effect 0x11a29c 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[242, 240]
    (.letOp (n := 246) (.exec 0x11a29c (fun s => s.RIP = 0x11a29c) (mulR64Effect 0x11a29c 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[242, 240]
    (.letOp (n := 247) (.out 0x11a29f (movR64R64Effect 0x11a29f 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[245]
    (.letOp (n := 248) (.exec 0x11a29f (fun s => s.RIP = 0x11a29f) (movR64R64Effect 0x11a29f 10 2) (Reg.operands [.gpr 2] [])) #v[245]
    (.letOp (n := 249) (.out 0x11a2a2 (movR64R64Effect 0x11a2a2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[244]
    (.letOp (n := 250) (.exec 0x11a2a2 (fun s => s.RIP = 0x11a2a2) (movR64R64Effect 0x11a2a2 7 0) (Reg.operands [.gpr 0] [])) #v[244]
    (.letOp (n := 251) (.out 0x11a2a5 (addR64R64Effect 0x11a2a5 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[249, 195]
    (.letOp (n := 252) (.out 0x11a2a5 (addR64R64Effect 0x11a2a5 7 13) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 13] []) (.flag .CF)) #v[249, 195]
    (.letOp (n := 253) (.exec 0x11a2a5 (fun s => s.RIP = 0x11a2a5) (addR64R64Effect 0x11a2a5 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[249, 195]
    (.letOp (n := 254) (.out 0x11a2a8 (atFlags StatusFlags.CF (adcR64R64Effect 0x11a2a8 10 9)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[247, 193, 252]
    (.letOp (n := 255) (.exec 0x11a2a8 (fun s => s.RIP = 0x11a2a8) (atFlags StatusFlags.CF (adcR64R64Effect 0x11a2a8 10 9)) (Reg.operands [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[247, 193, 252]
    (.letOp (n := 256) (.exec 0x11a2ab (StorePre 0x11a2ab 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11a2ab + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11a2ab 14 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 257) (.out 0x11a2b3 (movR64R64Effect 0x11a2b3 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 258) (.exec 0x11a2b3 (fun s => s.RIP = 0x11a2b3) (movR64R64Effect 0x11a2b3 12 14) (Reg.operands [.gpr 14] [])) #v[55]
    (.letOp (n := 259) (.out 0x11a2b6 (shrR64Effect 0x11a2b6 4 12 63) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[257]
    (.letOp (n := 260) (.exec 0x11a2b6 (fun s => s.RIP = 0x11a2b6) (shrR64Effect 0x11a2b6 4 12 63) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[257]
    (.letOp (n := 261) (.out 0x11a2ba (movR64R64Effect 0x11a2ba 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[259]
    (.letOp (n := 262) (.exec 0x11a2ba (fun s => s.RIP = 0x11a2ba) (movR64R64Effect 0x11a2ba 1 12) (Reg.operands [.gpr 12] [])) #v[259]
    (.letOp (n := 263) (.exec 0x11a2bd (StorePre 0x11a2bd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11a2bd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11a2bd 5 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 264) (.out 0x11a2c5 (imulR64R64Effect 0x11a2c5 4 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[261, 68]
    (.letOp (n := 265) (.exec 0x11a2c5 (fun s => s.RIP = 0x11a2c5) (imulR64R64Effect 0x11a2c5 4 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[261, 68]
    (.letOp (n := 266) (.out 0x11a2c9 (leaR64Effect 0x11a2c9 0 (.sib 14 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 14] []) (.reg (.gpr 0))) #v[55, 55]
    (.letOp (n := 267) (.exec 0x11a2c9 (fun s => s.RIP = 0x11a2c9) (leaR64Effect 0x11a2c9 0 (.sib 14 (some 14) 0 .none)) (Reg.operands [.gpr 14, .gpr 14] [])) #v[55, 55]
    (b_l11a14c_5)))))))))))))))))))))))))))))))))))))))))

def bytes_l11a14c_4 : List UInt8 :=
  [0x48, 0x01, 0xF8, 0x49, 0x83, 0xD0, 0x00, 0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x48, 0xC1, 0xE0, 0x04,
    0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C, 0x09, 0xD0,
    0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD2,
    0x48, 0x89, 0xC7, 0x4C, 0x01, 0xEF, 0x4D, 0x11, 0xCA, 0x4C, 0x89, 0xB4, 0x24, 0xB0, 0x00, 0x00,
    0x00, 0x4D, 0x89, 0xF4, 0x49, 0xC1, 0xEC, 0x3F, 0x4C, 0x89, 0xE1, 0x48, 0x89, 0xAC, 0x24, 0xA8,
    0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xCD, 0x4B, 0x8D, 0x04, 0x36] ++ bytes_l11a14c_5

theorem code_l11a14c_4 : ∀ x ∈ codeRange 0x11a272 bytes_l11a14c_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a272 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11a14c_5

def b_l11a14c_3 : Block Op Label signature Reg.count 184 :=
  .letOp (n := 184) (.out 0x11a228 (movR64R64Effect 0x11a228 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[177]
    (.letOp (n := 185) (.exec 0x11a228 (fun s => s.RIP = 0x11a228) (movR64R64Effect 0x11a228 10 6) (Reg.operands [.gpr 6] [])) #v[177]
    (.letOp (n := 186) (.out 0x11a22b (shrR64Effect 0x11a22b 4 10 48) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[184]
    (.letOp (n := 187) (.exec 0x11a22b (fun s => s.RIP = 0x11a22b) (shrR64Effect 0x11a22b 4 10 48) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[184]
    (.letOp (n := 188) (.out 0x11a22f (movR64R64Effect 0x11a22f 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 189) (.exec 0x11a22f (fun s => s.RIP = 0x11a22f) (movR64R64Effect 0x11a22f 0 14) (Reg.operands [.gpr 14] [])) #v[55]
    (.letOp (n := 190) (.out 0x11a232 (mulR64Effect 0x11a232 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[55, 188]
    (.letOp (n := 191) (.out 0x11a232 (mulR64Effect 0x11a232 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[55, 188]
    (.letOp (n := 192) (.exec 0x11a232 (fun s => s.RIP = 0x11a232) (mulR64Effect 0x11a232 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[55, 188]
    (.letOp (n := 193) (.out 0x11a235 (movR64R64Effect 0x11a235 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[191]
    (.letOp (n := 194) (.exec 0x11a235 (fun s => s.RIP = 0x11a235) (movR64R64Effect 0x11a235 9 2) (Reg.operands [.gpr 2] [])) #v[191]
    (.letOp (n := 195) (.out 0x11a238 (movR64R64Effect 0x11a238 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[190]
    (.letOp (n := 196) (.exec 0x11a238 (fun s => s.RIP = 0x11a238) (movR64R64Effect 0x11a238 13 0) (Reg.operands [.gpr 0] [])) #v[190]
    (.letOp (n := 197) (.out 0x11a23b (movR64R64Effect 0x11a23b 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 198) (.exec 0x11a23b (fun s => s.RIP = 0x11a23b) (movR64R64Effect 0x11a23b 0 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 199) (.out 0x11a23e (mulR64Effect 0x11a23e 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[121, 197]
    (.letOp (n := 200) (.out 0x11a23e (mulR64Effect 0x11a23e 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[121, 197]
    (.letOp (n := 201) (.exec 0x11a23e (fun s => s.RIP = 0x11a23e) (mulR64Effect 0x11a23e 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[121, 197]
    (.letOp (n := 202) (.out 0x11a241 (movR64R64Effect 0x11a241 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 12] []) (.reg (.gpr 11))) #v[121]
    (.letOp (n := 203) (.exec 0x11a241 (fun s => s.RIP = 0x11a241) (movR64R64Effect 0x11a241 11 12) (Reg.operands [.gpr 12] [])) #v[121]
    (.letOp (n := 204) (.exec 0x11a244 (StorePre 0x11a244 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x11a244 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11a244 12 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[121, 4]
    (.letOp (n := 205) (.out 0x11a24c (movR64R64Effect 0x11a24c 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[200]
    (.letOp (n := 206) (.exec 0x11a24c (fun s => s.RIP = 0x11a24c) (movR64R64Effect 0x11a24c 8 2) (Reg.operands [.gpr 2] [])) #v[200]
    (.letOp (n := 207) (.out 0x11a24f (movR64R64Effect 0x11a24f 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[199]
    (.letOp (n := 208) (.exec 0x11a24f (fun s => s.RIP = 0x11a24f) (movR64R64Effect 0x11a24f 1 0) (Reg.operands [.gpr 0] [])) #v[199]
    (.letOp (n := 209) (.out 0x11a252 (movR64M64Effect 0x11a252 3 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 210) (.exec 0x11a252 (LoadPre 0x11a252 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11a252 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a252 3 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 211) (.out 0x11a25a (movR64R64Effect 0x11a25a 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[209]
    (.letOp (n := 212) (.exec 0x11a25a (fun s => s.RIP = 0x11a25a) (movR64R64Effect 0x11a25a 0 3) (Reg.operands [.gpr 3] [])) #v[209]
    (.letOp (n := 213) (.out 0x11a25d (mulR64Effect 0x11a25d 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[68, 211]
    (.letOp (n := 214) (.out 0x11a25d (mulR64Effect 0x11a25d 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[68, 211]
    (.letOp (n := 215) (.exec 0x11a25d (fun s => s.RIP = 0x11a25d) (mulR64Effect 0x11a25d 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[68, 211]
    (.letOp (n := 216) (.out 0x11a260 (andR32Imm8Effect 0x11a260 4 10 0xf) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[186]
    (.letOp (n := 217) (.exec 0x11a260 (fun s => s.RIP = 0x11a260) (andR32Imm8Effect 0x11a260 4 10 0xf) (Reg.operands [.gpr 10] [])) #v[186]
    (.letOp (n := 218) (.out 0x11a264 (addR64R64Effect 0x11a264 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[213, 207]
    (.letOp (n := 219) (.out 0x11a264 (addR64R64Effect 0x11a264 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[213, 207]
    (.letOp (n := 220) (.exec 0x11a264 (fun s => s.RIP = 0x11a264) (addR64R64Effect 0x11a264 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[213, 207]
    (.letOp (n := 221) (.out 0x11a267 (atFlags StatusFlags.CF (adcR64R64Effect 0x11a267 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[205, 214, 219]
    (.letOp (n := 222) (.exec 0x11a267 (fun s => s.RIP = 0x11a267) (atFlags StatusFlags.CF (adcR64R64Effect 0x11a267 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[205, 214, 219]
    (.letOp (n := 223) (.out 0x11a26a (shldR64R64Effect 0x11a26a 5 8 0 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[221, 218]
    (.letOp (n := 224) (.exec 0x11a26a (fun s => s.RIP = 0x11a26a) (shldR64R64Effect 0x11a26a 5 8 0 1) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[221, 218]
    (.letOp (n := 225) (.out 0x11a26f (addR64R64Effect 0x11a26f 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[218, 218]
    (.letOp (n := 226) (.exec 0x11a26f (fun s => s.RIP = 0x11a26f) (addR64R64Effect 0x11a26f 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[218, 218]
    (b_l11a14c_4)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11a14c_3 : List UInt8 :=
  [0x49, 0x89, 0xF2, 0x49, 0xC1, 0xEA, 0x30, 0x4C, 0x89, 0xF0, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD1,
    0x49, 0x89, 0xC5, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE4, 0x4D, 0x89, 0xE3, 0x4C, 0x89, 0xA4, 0x24,
    0x00, 0x01, 0x00, 0x00, 0x49, 0x89, 0xD0, 0x48, 0x89, 0xC1, 0x48, 0x8B, 0x9C, 0x24, 0xA0, 0x00,
    0x00, 0x00, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0xE5, 0x41, 0x83, 0xE2, 0x0F, 0x48, 0x01, 0xC8, 0x49,
    0x11, 0xD0, 0x49, 0x0F, 0xA4, 0xC0, 0x01, 0x48, 0x01, 0xC0] ++ bytes_l11a14c_4

theorem code_l11a14c_3 : ∀ x ∈ codeRange 0x11a228 bytes_l11a14c_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a228 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11a14c_4

def b_l11a14c_2 : Block Op Label signature Reg.count 139 :=
  .letOp (n := 139) (.out 0x11a1e2 (movR64R64Effect 0x11a1e2 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[134]
    (.letOp (n := 140) (.exec 0x11a1e2 (fun s => s.RIP = 0x11a1e2) (movR64R64Effect 0x11a1e2 11 0) (Reg.operands [.gpr 0] [])) #v[134]
    (.letOp (n := 141) (.out 0x11a1e5 (movR64R64Effect 0x11a1e5 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[88]
    (.letOp (n := 142) (.exec 0x11a1e5 (fun s => s.RIP = 0x11a1e5) (movR64R64Effect 0x11a1e5 0 3) (Reg.operands [.gpr 3] [])) #v[88]
    (.letOp (n := 143) (.out 0x11a1e8 (mulR64Effect 0x11a1e8 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[55, 141]
    (.letOp (n := 144) (.out 0x11a1e8 (mulR64Effect 0x11a1e8 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[55, 141]
    (.letOp (n := 145) (.exec 0x11a1e8 (fun s => s.RIP = 0x11a1e8) (mulR64Effect 0x11a1e8 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[55, 141]
    (.letOp (n := 146) (.out 0x11a1eb (movR64R64Effect 0x11a1eb 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[144]
    (.letOp (n := 147) (.exec 0x11a1eb (fun s => s.RIP = 0x11a1eb) (movR64R64Effect 0x11a1eb 7 2) (Reg.operands [.gpr 2] [])) #v[144]
    (.letOp (n := 148) (.out 0x11a1ee (movR64R64Effect 0x11a1ee 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[143]
    (.letOp (n := 149) (.exec 0x11a1ee (fun s => s.RIP = 0x11a1ee) (movR64R64Effect 0x11a1ee 3 0) (Reg.operands [.gpr 0] [])) #v[143]
    (.letOp (n := 150) (.out 0x11a1f1 (movR64R64Effect 0x11a1f1 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 151) (.exec 0x11a1f1 (fun s => s.RIP = 0x11a1f1) (movR64R64Effect 0x11a1f1 0 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 152) (.exec 0x11a1f4 (StorePre 0x11a1f4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11a1f4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11a1f4 15 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 153) (.out 0x11a1fc (mulR64Effect 0x11a1fc 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[68, 150]
    (.letOp (n := 154) (.out 0x11a1fc (mulR64Effect 0x11a1fc 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[68, 150]
    (.letOp (n := 155) (.exec 0x11a1fc (fun s => s.RIP = 0x11a1fc) (mulR64Effect 0x11a1fc 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[68, 150]
    (.letOp (n := 156) (.out 0x11a1ff (movR64R64Effect 0x11a1ff 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[153]
    (.letOp (n := 157) (.exec 0x11a1ff (fun s => s.RIP = 0x11a1ff) (movR64R64Effect 0x11a1ff 6 0) (Reg.operands [.gpr 0] [])) #v[153]
    (.letOp (n := 158) (.out 0x11a202 (addR64R64Effect 0x11a202 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[156, 148]
    (.letOp (n := 159) (.out 0x11a202 (addR64R64Effect 0x11a202 6 3) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 3] []) (.flag .CF)) #v[156, 148]
    (.letOp (n := 160) (.exec 0x11a202 (fun s => s.RIP = 0x11a202) (addR64R64Effect 0x11a202 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[156, 148]
    (.letOp (n := 161) (.out 0x11a205 (atFlags StatusFlags.CF (adcR64R64Effect 0x11a205 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[146, 154, 159]
    (.letOp (n := 162) (.exec 0x11a205 (fun s => s.RIP = 0x11a205) (atFlags StatusFlags.CF (adcR64R64Effect 0x11a205 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[146, 154, 159]
    (.letOp (n := 163) (.out 0x11a208 (shldR64R64Effect 0x11a208 5 7 6 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[161, 158]
    (.letOp (n := 164) (.exec 0x11a208 (fun s => s.RIP = 0x11a208) (shldR64R64Effect 0x11a208 5 7 6 1) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[161, 158]
    (.letOp (n := 165) (.out 0x11a20d (addR64R64Effect 0x11a20d 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[158, 158]
    (.letOp (n := 166) (.exec 0x11a20d (fun s => s.RIP = 0x11a20d) (addR64R64Effect 0x11a20d 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[158, 158]
    (.letOp (n := 167) (.out 0x11a210 (addR64R64Effect 0x11a210 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[165, 130]
    (.letOp (n := 168) (.out 0x11a210 (addR64R64Effect 0x11a210 6 10) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 10] []) (.flag .CF)) #v[165, 130]
    (.letOp (n := 169) (.exec 0x11a210 (fun s => s.RIP = 0x11a210) (addR64R64Effect 0x11a210 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[165, 130]
    (.letOp (n := 170) (.out 0x11a213 (atFlags StatusFlags.CF (adcR64R64Effect 0x11a213 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[163, 128, 168]
    (.letOp (n := 171) (.exec 0x11a213 (fun s => s.RIP = 0x11a213) (atFlags StatusFlags.CF (adcR64R64Effect 0x11a213 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[163, 128, 168]
    (.letOp (n := 172) (.out 0x11a216 (addR64R64Effect 0x11a216 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[167, 139]
    (.letOp (n := 173) (.out 0x11a216 (addR64R64Effect 0x11a216 6 11) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 11] []) (.flag .CF)) #v[167, 139]
    (.letOp (n := 174) (.exec 0x11a216 (fun s => s.RIP = 0x11a216) (addR64R64Effect 0x11a216 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[167, 139]
    (.letOp (n := 175) (.out 0x11a219 (atFlags StatusFlags.CF (adcR64R64Effect 0x11a219 7 9)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[170, 137, 173]
    (.letOp (n := 176) (.exec 0x11a219 (fun s => s.RIP = 0x11a219) (atFlags StatusFlags.CF (adcR64R64Effect 0x11a219 7 9)) (Reg.operands [.gpr 7, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[170, 137, 173]
    (.letOp (n := 177) (.out 0x11a21c (addR64R64Effect 0x11a21c 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[172, 119]
    (.letOp (n := 178) (.out 0x11a21c (addR64R64Effect 0x11a21c 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[172, 119]
    (.letOp (n := 179) (.exec 0x11a21c (fun s => s.RIP = 0x11a21c) (addR64R64Effect 0x11a21c 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[172, 119]
    (.letOp (n := 180) (.out 0x11a21f (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a21f 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[175, 178]
    (.letOp (n := 181) (.exec 0x11a21f (fun s => s.RIP = 0x11a21f) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11a21f 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[175, 178]
    (.letOp (n := 182) (.out 0x11a223 (shldR64R64Effect 0x11a223 5 7 6 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[180, 177]
    (.letOp (n := 183) (.exec 0x11a223 (fun s => s.RIP = 0x11a223) (shldR64R64Effect 0x11a223 5 7 6 12) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[180, 177]
    (b_l11a14c_3)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11a14c_2 : List UInt8 :=
  [0x49, 0x89, 0xC3, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0xD7, 0x48, 0x89, 0xC3, 0x4C,
    0x89, 0xF8, 0x4C, 0x89, 0xBC, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xC6,
    0x48, 0x01, 0xDE, 0x48, 0x11, 0xD7, 0x48, 0x0F, 0xA4, 0xF7, 0x01, 0x48, 0x01, 0xF6, 0x4C, 0x01,
    0xD6, 0x48, 0x11, 0xCF, 0x4C, 0x01, 0xDE, 0x4C, 0x11, 0xCF, 0x4C, 0x01, 0xC6, 0x48, 0x83, 0xD7,
    0x00, 0x48, 0x0F, 0xA4, 0xF7, 0x0C] ++ bytes_l11a14c_3

theorem code_l11a14c_2 : ∀ x ∈ codeRange 0x11a1e2 bytes_l11a14c_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a1e2 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11a14c_3

def b_l11a14c_1 : Block Op Label signature Reg.count 96 :=
  .letOp (n := 96) (.out 0x11a199 (movR64R64Effect 0x11a199 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[92]
    (.letOp (n := 97) (.exec 0x11a199 (fun s => s.RIP = 0x11a199) (movR64R64Effect 0x11a199 7 0) (Reg.operands [.gpr 0] [])) #v[92]
    (.letOp (n := 98) (.out 0x11a19c (movR64R64Effect 0x11a19c 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[93]
    (.letOp (n := 99) (.exec 0x11a19c (fun s => s.RIP = 0x11a19c) (movR64R64Effect 0x11a19c 9 2) (Reg.operands [.gpr 2] [])) #v[93]
    (.letOp (n := 100) (.out 0x11a19f (movR64Imm64Effect 0x11a19f 0 0xffffffffffffd) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 101) (.exec 0x11a19f (fun s => s.RIP = 0x11a19f) (movR64Imm64Effect 0x11a19f 0 0xffffffffffffd) (Reg.operands [] [])) #v[]
    (.letOp (n := 102) (.out 0x11a1a9 (andR64R64Effect 0x11a1a9 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[100, 96]
    (.letOp (n := 103) (.exec 0x11a1a9 (fun s => s.RIP = 0x11a1a9) (andR64R64Effect 0x11a1a9 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[100, 96]
    (.letOp (n := 104) (.out 0x11a1ac (movR64R64Effect 0x11a1ac 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 12] []) (.reg (.gpr 11))) #v[12]
    (.letOp (n := 105) (.exec 0x11a1ac (fun s => s.RIP = 0x11a1ac) (movR64R64Effect 0x11a1ac 11 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 106) (.out 0x11a1af (mulR64Effect 0x11a1af 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[12, 102]
    (.letOp (n := 107) (.out 0x11a1af (mulR64Effect 0x11a1af 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[12, 102]
    (.letOp (n := 108) (.exec 0x11a1af (fun s => s.RIP = 0x11a1af) (mulR64Effect 0x11a1af 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[12, 102]
    (.letOp (n := 109) (.out 0x11a1b2 (movR64R64Effect 0x11a1b2 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[107]
    (.letOp (n := 110) (.exec 0x11a1b2 (fun s => s.RIP = 0x11a1b2) (movR64R64Effect 0x11a1b2 8 2) (Reg.operands [.gpr 2] [])) #v[107]
    (.letOp (n := 111) (.out 0x11a1b5 (addR64R64Effect 0x11a1b5 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[106, 86]
    (.letOp (n := 112) (.out 0x11a1b5 (addR64R64Effect 0x11a1b5 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[106, 86]
    (.letOp (n := 113) (.exec 0x11a1b5 (fun s => s.RIP = 0x11a1b5) (addR64R64Effect 0x11a1b5 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[106, 86]
    (.letOp (n := 114) (.exec 0x11a1b8 (StorePre 0x11a1b8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11a1b8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11a1b8 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[111, 4]
    (.letOp (n := 115) (.out 0x11a1bd (atFlags StatusFlags.CF (adcR64R64Effect 0x11a1bd 8 1)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[109, 84, 112]
    (.letOp (n := 116) (.exec 0x11a1bd (fun s => s.RIP = 0x11a1bd) (atFlags StatusFlags.CF (adcR64R64Effect 0x11a1bd 8 1)) (Reg.operands [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[109, 84, 112]
    (.letOp (n := 117) (.out 0x11a1c0 (shldR64R64Effect 0x11a1c0 5 9 7 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[98, 96]
    (.letOp (n := 118) (.exec 0x11a1c0 (fun s => s.RIP = 0x11a1c0) (shldR64R64Effect 0x11a1c0 5 9 7 12) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[98, 96]
    (.letOp (n := 119) (.out 0x11a1c5 (shldR64R64Effect 0x11a1c5 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[115, 111]
    (.letOp (n := 120) (.exec 0x11a1c5 (fun s => s.RIP = 0x11a1c5) (shldR64R64Effect 0x11a1c5 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115, 111]
    (.letOp (n := 121) (.out 0x11a1ca (movR64R64Effect 0x11a1ca 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 10] []) (.reg (.gpr 12))) #v[66]
    (.letOp (n := 122) (.exec 0x11a1ca (fun s => s.RIP = 0x11a1ca) (movR64R64Effect 0x11a1ca 12 10) (Reg.operands [.gpr 10] [])) #v[66]
    (.letOp (n := 123) (.out 0x11a1cd (movR64R64Effect 0x11a1cd 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 124) (.exec 0x11a1cd (fun s => s.RIP = 0x11a1cd) (movR64R64Effect 0x11a1cd 0 10) (Reg.operands [.gpr 10] [])) #v[66]
    (.letOp (n := 125) (.out 0x11a1d0 (mulR64Effect 0x11a1d0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[66, 123]
    (.letOp (n := 126) (.out 0x11a1d0 (mulR64Effect 0x11a1d0 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[66, 123]
    (.letOp (n := 127) (.exec 0x11a1d0 (fun s => s.RIP = 0x11a1d0) (mulR64Effect 0x11a1d0 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[66, 123]
    (.letOp (n := 128) (.out 0x11a1d3 (movR64R64Effect 0x11a1d3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[126]
    (.letOp (n := 129) (.exec 0x11a1d3 (fun s => s.RIP = 0x11a1d3) (movR64R64Effect 0x11a1d3 1 2) (Reg.operands [.gpr 2] [])) #v[126]
    (.letOp (n := 130) (.out 0x11a1d6 (movR64R64Effect 0x11a1d6 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[125]
    (.letOp (n := 131) (.exec 0x11a1d6 (fun s => s.RIP = 0x11a1d6) (movR64R64Effect 0x11a1d6 10 0) (Reg.operands [.gpr 0] [])) #v[125]
    (.letOp (n := 132) (.out 0x11a1d9 (movR64R64Effect 0x11a1d9 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[117]
    (.letOp (n := 133) (.exec 0x11a1d9 (fun s => s.RIP = 0x11a1d9) (movR64R64Effect 0x11a1d9 0 9) (Reg.operands [.gpr 9] [])) #v[117]
    (.letOp (n := 134) (.out 0x11a1dc (mulR64Effect 0x11a1dc 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[104, 132]
    (.letOp (n := 135) (.out 0x11a1dc (mulR64Effect 0x11a1dc 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[104, 132]
    (.letOp (n := 136) (.exec 0x11a1dc (fun s => s.RIP = 0x11a1dc) (mulR64Effect 0x11a1dc 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[104, 132]
    (.letOp (n := 137) (.out 0x11a1df (movR64R64Effect 0x11a1df 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[135]
    (.letOp (n := 138) (.exec 0x11a1df (fun s => s.RIP = 0x11a1df) (movR64R64Effect 0x11a1df 9 2) (Reg.operands [.gpr 2] [])) #v[135]
    (b_l11a14c_2)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11a14c_1 : List UInt8 :=
  [0x48, 0x89, 0xC7, 0x49, 0x89, 0xD1, 0x48, 0xB8, 0xFD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x48, 0x21, 0xF8, 0x4D, 0x89, 0xE3, 0x49, 0xF7, 0xE4, 0x49, 0x89, 0xD0, 0x48, 0x01, 0xF0, 0x48,
    0x89, 0x44, 0x24, 0x68, 0x49, 0x11, 0xC8, 0x49, 0x0F, 0xA4, 0xF9, 0x0C, 0x49, 0x0F, 0xA4, 0xC0,
    0x0C, 0x4D, 0x89, 0xD4, 0x4C, 0x89, 0xD0, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC2,
    0x4C, 0x89, 0xC8, 0x49, 0xF7, 0xE3, 0x49, 0x89, 0xD1] ++ bytes_l11a14c_2

theorem code_l11a14c_1 : ∀ x ∈ codeRange 0x11a199 bytes_l11a14c_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a199 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11a14c_2

def b_l11a14c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11a14c (movR64M64Effect 0x11a14c 15 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x11a14c (LoadPre 0x11a14c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11a14c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11a14c 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11a151 (movR64M64Effect 0x11a151 14 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 56) (.exec 0x11a151 (LoadPre 0x11a151 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11a151 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11a151 14 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11a156 (movR64R64Effect 0x11a156 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 58) (.exec 0x11a156 (fun s => s.RIP = 0x11a156) (movR64R64Effect 0x11a156 0 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 59) (.out 0x11a159 (mulR64Effect 0x11a159 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[55, 57]
    (.letOp (n := 60) (.out 0x11a159 (mulR64Effect 0x11a159 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[55, 57]
    (.letOp (n := 61) (.exec 0x11a159 (fun s => s.RIP = 0x11a159) (mulR64Effect 0x11a159 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[55, 57]
    (.letOp (n := 62) (.out 0x11a15c (movR64R64Effect 0x11a15c 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 63) (.exec 0x11a15c (fun s => s.RIP = 0x11a15c) (movR64R64Effect 0x11a15c 7 0) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.out 0x11a15f (movR64R64Effect 0x11a15f 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[60]
    (.letOp (n := 65) (.exec 0x11a15f (fun s => s.RIP = 0x11a15f) (movR64R64Effect 0x11a15f 8 2) (Reg.operands [.gpr 2] [])) #v[60]
    (.letOp (n := 66) (.out 0x11a162 (movR64M64Effect 0x11a162 10 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 67) (.exec 0x11a162 (LoadPre 0x11a162 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11a162 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11a162 10 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x11a167 (movR64M64Effect 0x11a167 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 69) (.exec 0x11a167 (LoadPre 0x11a167 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11a167 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11a167 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x11a16c (movR64R64Effect 0x11a16c 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 71) (.exec 0x11a16c (fun s => s.RIP = 0x11a16c) (movR64R64Effect 0x11a16c 0 10) (Reg.operands [.gpr 10] [])) #v[66]
    (.letOp (n := 72) (.out 0x11a16f (mulR64Effect 0x11a16f 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[68, 70]
    (.letOp (n := 73) (.out 0x11a16f (mulR64Effect 0x11a16f 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[68, 70]
    (.letOp (n := 74) (.exec 0x11a16f (fun s => s.RIP = 0x11a16f) (mulR64Effect 0x11a16f 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[68, 70]
    (.letOp (n := 75) (.out 0x11a172 (movR64R64Effect 0x11a172 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[73]
    (.letOp (n := 76) (.exec 0x11a172 (fun s => s.RIP = 0x11a172) (movR64R64Effect 0x11a172 1 2) (Reg.operands [.gpr 2] [])) #v[73]
    (.letOp (n := 77) (.out 0x11a175 (movR64R64Effect 0x11a175 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[72]
    (.letOp (n := 78) (.exec 0x11a175 (fun s => s.RIP = 0x11a175) (movR64R64Effect 0x11a175 6 0) (Reg.operands [.gpr 0] [])) #v[72]
    (.letOp (n := 79) (.out 0x11a178 (addR64R64Effect 0x11a178 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[77, 62]
    (.letOp (n := 80) (.out 0x11a178 (addR64R64Effect 0x11a178 6 7) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 7] []) (.flag .CF)) #v[77, 62]
    (.letOp (n := 81) (.exec 0x11a178 (fun s => s.RIP = 0x11a178) (addR64R64Effect 0x11a178 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[77, 62]
    (.letOp (n := 82) (.out 0x11a17b (atFlags StatusFlags.CF (adcR64R64Effect 0x11a17b 1 8)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[75, 64, 80]
    (.letOp (n := 83) (.exec 0x11a17b (fun s => s.RIP = 0x11a17b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11a17b 1 8)) (Reg.operands [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[75, 64, 80]
    (.letOp (n := 84) (.out 0x11a17e (shldR64R64Effect 0x11a17e 5 1 6 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[82, 79]
    (.letOp (n := 85) (.exec 0x11a17e (fun s => s.RIP = 0x11a17e) (shldR64R64Effect 0x11a17e 5 1 6 1) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[82, 79]
    (.letOp (n := 86) (.out 0x11a183 (addR64R64Effect 0x11a183 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[79, 79]
    (.letOp (n := 87) (.exec 0x11a183 (fun s => s.RIP = 0x11a183) (addR64R64Effect 0x11a183 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[79, 79]
    (.letOp (n := 88) (.out 0x11a186 (movR64M64Effect 0x11a186 3 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 89) (.exec 0x11a186 (LoadPre 0x11a186 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11a186 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11a186 3 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x11a18b (movR64R64Effect 0x11a18b 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[88]
    (.letOp (n := 91) (.exec 0x11a18b (fun s => s.RIP = 0x11a18b) (movR64R64Effect 0x11a18b 0 3) (Reg.operands [.gpr 3] [])) #v[88]
    (.letOp (n := 92) (.out 0x11a18e (mulR64Effect 0x11a18e 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[88, 90]
    (.letOp (n := 93) (.out 0x11a18e (mulR64Effect 0x11a18e 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[88, 90]
    (.letOp (n := 94) (.exec 0x11a18e (fun s => s.RIP = 0x11a18e) (mulR64Effect 0x11a18e 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[88, 90]
    (.letOp (n := 95) (.exec 0x11a191 (StorePre 0x11a191 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11a191 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11a191 3 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[88, 4]
    (b_l11a14c_1)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11a14c : List UInt8 :=
  [0x4C, 0x8B, 0x7C, 0x24, 0x40, 0x4C, 0x8B, 0x74, 0x24, 0x28, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE6,
    0x48, 0x89, 0xC7, 0x49, 0x89, 0xD0, 0x4C, 0x8B, 0x54, 0x24, 0x38, 0x48, 0x8B, 0x6C, 0x24, 0x30,
    0x4C, 0x89, 0xD0, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x48, 0x01, 0xFE, 0x4C,
    0x11, 0xC1, 0x48, 0x0F, 0xA4, 0xF1, 0x01, 0x48, 0x01, 0xF6, 0x48, 0x8B, 0x5C, 0x24, 0x48, 0x48,
    0x89, 0xD8, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00] ++ bytes_l11a14c_1

theorem code_l11a14c : ∀ x ∈ codeRange 0x11a14c bytes_l11a14c, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1a14c 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11a14c_1

@[cfg_block] def b_l11a51c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11a51c (movR64M64Effect 0x11a51c 1 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x11a51c (LoadPre 0x11a51c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x11a51c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a51c 1 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11a524 (movR64M64Effect 0x11a524 2 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x11a524 (LoadPre 0x11a524 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11a524 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a524 2 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x11a52c (StorePre 0x11a52c 3 (fun s => AddrMode.addr (.base 1 .none) s (0x11a52c + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11a52c 2 (.base 1 .none)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[55, 53]
    (.letOp (n := 58) (.out 0x11a52f (movR64M64Effect 0x11a52f 2 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x11a52f (LoadPre 0x11a52f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11a52f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a52f 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x11a537 (StorePre 0x11a537 4 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x11a537 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11a537 2 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 1] [])) #v[58, 53]
    (.letOp (n := 61) (.out 0x11a53b (movR64M64Effect 0x11a53b 2 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x11a53b (LoadPre 0x11a53b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x11a53b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11a53b 2 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x11a543 (StorePre 0x11a543 4 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x11a543 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11a543 2 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 1] [])) #v[61, 53]
    (.letOp (n := 64) (.exec 0x11a547 (StorePre 0x11a547 4 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x11a547 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11a547 14 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 1] [])) #v[14, 53]
    (.letOp (n := 65) (.exec 0x11a54b (StorePre 0x11a54b 4 (fun s => AddrMode.addr (.base 1 (.d8 0x20)) s (0x11a54b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11a54b 3 (.base 1 (.d8 0x20))) (Reg.operands [.gpr 3, .gpr 1] [])) #v[3, 53]
    (.letOp (n := 66) (.exec 0x11a54f (StorePre 0x11a54f 3 (fun s => AddrMode.addr (.base 1 (.d8 0x28)) s (0x11a54f + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x11a54f 3 0 (.base 1 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 1] [])) #v[0, 53]
    (.letOp (n := 67) (.out 0x11a552 (movR64R64Effect 0x11a552 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 68) (.exec 0x11a552 (fun s => s.RIP = 0x11a552) (movR64R64Effect 0x11a552 0 1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 69) (.out 0x11a555 (addR64Imm32Effect 0x11a555 4 0x188) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x11a555 (fun s => s.RIP = 0x11a555) (addR64Imm32Effect 0x11a555 4 0x188) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x11a55c (popR64Effect 0x11a55c 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[69]
    (.letOp (n := 72) (.out 0x11a55c (popR64Effect 0x11a55c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 73) (.exec 0x11a55c (PopPre 0x11a55c) (popR64Effect 0x11a55c 1 3) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 74) (.out 0x11a55d (popR64Effect 0x11a55d 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[72]
    (.letOp (n := 75) (.out 0x11a55d (popR64Effect 0x11a55d 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[72]
    (.letOp (n := 76) (.exec 0x11a55d (PopPre 0x11a55d) (popR64Effect 0x11a55d 2 12) (Reg.operands [.gpr 4] [])) #v[72]
    (.letOp (n := 77) (.out 0x11a55f (popR64Effect 0x11a55f 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[75]
    (.letOp (n := 78) (.out 0x11a55f (popR64Effect 0x11a55f 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[75]
    (.letOp (n := 79) (.exec 0x11a55f (PopPre 0x11a55f) (popR64Effect 0x11a55f 2 13) (Reg.operands [.gpr 4] [])) #v[75]
    (.letOp (n := 80) (.out 0x11a561 (popR64Effect 0x11a561 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[78]
    (.letOp (n := 81) (.out 0x11a561 (popR64Effect 0x11a561 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[78]
    (.letOp (n := 82) (.exec 0x11a561 (PopPre 0x11a561) (popR64Effect 0x11a561 2 14) (Reg.operands [.gpr 4] [])) #v[78]
    (.letOp (n := 83) (.out 0x11a563 (popR64Effect 0x11a563 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[81]
    (.letOp (n := 84) (.out 0x11a563 (popR64Effect 0x11a563 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[81]
    (.letOp (n := 85) (.exec 0x11a563 (PopPre 0x11a563) (popR64Effect 0x11a563 2 15) (Reg.operands [.gpr 4] [])) #v[81]
    (.letOp (n := 86) (.out 0x11a565 (popR64Effect 0x11a565 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[84]
    (.letOp (n := 87) (.out 0x11a565 (popR64Effect 0x11a565 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[84]
    (.letOp (n := 88) (.exec 0x11a565 (PopPre 0x11a565) (popR64Effect 0x11a565 1 5) (Reg.operands [.gpr 4] [])) #v[84]
    (.letOp (n := 89) (.out 0x11a566 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[87]
    (.letOp (n := 90) (.out 0x11a566 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[87]
    (.letOp (n := 91) (.exec 0x11a566 (RetPre 0x11a566) (retEffect) (Reg.operands [.gpr 4] [])) #v[87]
    (.terminate (.ret (RegMap.args [(0, 67), (1, 53), (2, 61), (3, 71), (4, 90), (5, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 77), (14, 80), (15, 83), (22, 22), (39, 39), (50, 50), (51, 51)] 92) (some ⟨89, by decide⟩)))))))))))))))))))))))))))))))))))))))))

def bytes_l11a51c : List UInt8 :=
  [0x48, 0x8B, 0x8C, 0x24, 0x80, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x11, 0x48, 0x8B, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x51, 0x08, 0x48,
    0x8B, 0x94, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x89, 0x51, 0x10, 0x4C, 0x89, 0x71, 0x18, 0x48,
    0x89, 0x59, 0x20, 0x88, 0x41, 0x28, 0x48, 0x89, 0xC8, 0x48, 0x81, 0xC4, 0x88, 0x01, 0x00, 0x00,
    0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l11a51c : ∀ x ∈ codeRange 0x11a51c bytes_l11a51c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1a51c 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f780_2 : Block Op Label signature Reg.count 134 :=
  .letOp (n := 134) (.out 0x11f818 (atFlags (condHolds 7) (setccR8Effect 0x11f818 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 1))) #v[127, 129, 130]
    (.letOp (n := 135) (.exec 0x11f818 (fun s => s.RIP = 0x11f818) (atFlags (condHolds 7) (setccR8Effect 0x11f818 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[127, 129, 130]
    (.letOp (n := 136) (.out 0x11f81b (andR8R8Effect 0x11f81b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[134, 125]
    (.letOp (n := 137) (.exec 0x11f81b (fun s => s.RIP = 0x11f81b) (andR8R8Effect 0x11f81b 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[134, 125]
    (.letOp (n := 138) (.out 0x11f81d (movzxR32R8Effect 0x11f81d 3 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[136]
    (.letOp (n := 139) (.exec 0x11f81d (fun s => s.RIP = 0x11f81d) (movzxR32R8Effect 0x11f81d 3 7 1) (Reg.operands [.gpr 1] [])) #v[136]
    (.letOp (n := 140) (.out 0x11f820 (callEffect (fun _ => 0x127d50) 0x11f825) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 141) (.exec 0x11f820 (PushPre 0x11f820 5) (callEffect (fun _ => 0x127d50) 0x11f825) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 142) (.const ⟨64, 0x11f825⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 125), (1, 136), (2, 112), (3, 67), (4, 140), (5, 116), (6, 98), (7, 138), (8, 102), (9, 86), (10, 10), (11, 11), (12, 110), (13, 132), (14, 90), (15, 94), (22, 22), (39, 39), (50, 50), (51, 51)] 143⟩ { target := .l11f825, kept := #v[], arity := rfl, guard := some (Fin.last 142) }))))))))))

def bytes_l11f780_2 : List UInt8 :=
  [0x0F, 0x97, 0xC1, 0x20, 0xC1, 0x0F, 0xB6, 0xF9, 0xE8, 0x2B, 0x85, 0x00, 0x00]

theorem code_l11f780_2 : ∀ x ∈ codeRange 0x11f818 bytes_l11f780_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f818 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f780_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x11f7c9 (movR64R64Effect 0x11f7c9 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[80]
    (.letOp (n := 93) (.exec 0x11f7c9 (fun s => s.RIP = 0x11f7c9) (movR64R64Effect 0x11f7c9 1 0) (Reg.operands [.gpr 0] [])) #v[80]
    (.letOp (n := 94) (.out 0x11f7cc (shldR64R64Effect 0x11f7cc 5 15 0 24) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[76, 80]
    (.letOp (n := 95) (.exec 0x11f7cc (fun s => s.RIP = 0x11f7cc) (shldR64R64Effect 0x11f7cc 5 15 0 24) (Reg.operands [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76, 80]
    (.letOp (n := 96) (.out 0x11f7d1 (shldR64R64Effect 0x11f7d1 5 1 6 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[92, 84]
    (.letOp (n := 97) (.exec 0x11f7d1 (fun s => s.RIP = 0x11f7d1) (shldR64R64Effect 0x11f7d1 5 1 6 12) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[92, 84]
    (.letOp (n := 98) (.out 0x11f7d6 (andR64R64Effect 0x11f7d6 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[84, 86]
    (.letOp (n := 99) (.exec 0x11f7d6 (fun s => s.RIP = 0x11f7d6) (andR64R64Effect 0x11f7d6 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[84, 86]
    (.letOp (n := 100) (.out 0x11f7d9 (andR64R64Effect 0x11f7d9 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[96, 86]
    (.letOp (n := 101) (.exec 0x11f7d9 (fun s => s.RIP = 0x11f7d9) (andR64R64Effect 0x11f7d9 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[96, 86]
    (.letOp (n := 102) (.out 0x11f7dc (shrR64Effect 0x11f7dc 4 8 16) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[74]
    (.letOp (n := 103) (.exec 0x11f7dc (fun s => s.RIP = 0x11f7dc) (shrR64Effect 0x11f7dc 4 8 16) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[74]
    (.letOp (n := 104) (.out 0x11f7e0 (movR64R64Effect 0x11f7e0 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[94]
    (.letOp (n := 105) (.exec 0x11f7e0 (fun s => s.RIP = 0x11f7e0) (movR64R64Effect 0x11f7e0 0 15) (Reg.operands [.gpr 15] [])) #v[94]
    (.letOp (n := 106) (.out 0x11f7e3 (andR64R64Effect 0x11f7e3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[104, 90]
    (.letOp (n := 107) (.exec 0x11f7e3 (fun s => s.RIP = 0x11f7e3) (andR64R64Effect 0x11f7e3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[104, 90]
    (.letOp (n := 108) (.out 0x11f7e6 (andR64R64Effect 0x11f7e6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[106, 100]
    (.letOp (n := 109) (.exec 0x11f7e6 (fun s => s.RIP = 0x11f7e6) (andR64R64Effect 0x11f7e6 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[106, 100]
    (.letOp (n := 110) (.out 0x11f7e9 (movR64R64Effect 0x11f7e9 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[100]
    (.letOp (n := 111) (.exec 0x11f7e9 (fun s => s.RIP = 0x11f7e9) (movR64R64Effect 0x11f7e9 12 1) (Reg.operands [.gpr 1] [])) #v[100]
    (.letOp (n := 112) (.out 0x11f7ec (movR64Imm64Effect 0x11f7ec 2 0xffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 113) (.exec 0x11f7ec (fun s => s.RIP = 0x11f7ec) (movR64Imm64Effect 0x11f7ec 2 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 114) (.out 0x11f7f6 (movR64R64Effect 0x11f7f6 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[102]
    (.letOp (n := 115) (.exec 0x11f7f6 (fun s => s.RIP = 0x11f7f6) (movR64R64Effect 0x11f7f6 1 8) (Reg.operands [.gpr 8] [])) #v[102]
    (.letOp (n := 116) (.out 0x11f7f9 (movR64R64Effect 0x11f7f9 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 8] []) (.reg (.gpr 5))) #v[102]
    (.letOp (n := 117) (.exec 0x11f7f9 (fun s => s.RIP = 0x11f7f9) (movR64R64Effect 0x11f7f9 5 8) (Reg.operands [.gpr 8] [])) #v[102]
    (.letOp (n := 118) (.out 0x11f7fc (xorR64R64Effect 0x11f7fc 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[114, 112]
    (.letOp (n := 119) (.exec 0x11f7fc (fun s => s.RIP = 0x11f7fc) (xorR64R64Effect 0x11f7fc 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[114, 112]
    (.letOp (n := 120) (.out 0x11f7ff (xorR64R64Effect 0x11f7ff 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[108, 86]
    (.letOp (n := 121) (.exec 0x11f7ff (fun s => s.RIP = 0x11f7ff) (xorR64R64Effect 0x11f7ff 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[108, 86]
    (.letOp (n := 122) (.out 0x11f802 (orR64R64Effect 0x11f802 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[120, 118]
    (.letOp (n := 123) (.out 0x11f802 (orR64R64Effect 0x11f802 0 1) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 1] []) (.flag .ZF)) #v[120, 118]
    (.letOp (n := 124) (.exec 0x11f802 (fun s => s.RIP = 0x11f802) (orR64R64Effect 0x11f802 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[120, 118]
    (.letOp (n := 125) (.out 0x11f805 (atFlags (condHolds 4) (setccR8Effect 0x11f805 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[122, 123]
    (.letOp (n := 126) (.exec 0x11f805 (fun s => s.RIP = 0x11f805) (atFlags (condHolds 4) (setccR8Effect 0x11f805 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[122, 123]
    (.letOp (n := 127) (.out 0x11f808 (movR64Imm64Effect 0x11f808 1 0xffffefffffc2e) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 128) (.exec 0x11f808 (fun s => s.RIP = 0x11f808) (movR64Imm64Effect 0x11f808 1 0xffffefffffc2e) (Reg.operands [] [])) #v[]
    (.letOp (n := 129) (.out 0x11f812 (cmpR64R64Effect 0x11f812 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[98, 127]
    (.letOp (n := 130) (.out 0x11f812 (cmpR64R64Effect 0x11f812 6 1) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 1] []) (.flag .ZF)) #v[98, 127]
    (.letOp (n := 131) (.exec 0x11f812 (fun s => s.RIP = 0x11f812) (cmpR64R64Effect 0x11f812 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[98, 127]
    (.letOp (n := 132) (.out 0x11f815 (movR64R64Effect 0x11f815 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[98]
    (.letOp (n := 133) (.exec 0x11f815 (fun s => s.RIP = 0x11f815) (movR64R64Effect 0x11f815 13 6) (Reg.operands [.gpr 6] [])) #v[98]
    (b_l11f780_2))))))))))))))))))))))))))))))))))))))))))

def bytes_l11f780_1 : List UInt8 :=
  [0x48, 0x89, 0xC1, 0x49, 0x0F, 0xA4, 0xC7, 0x18, 0x48, 0x0F, 0xA4, 0xF1, 0x0C, 0x4C, 0x21, 0xCE,
    0x4C, 0x21, 0xC9, 0x49, 0xC1, 0xE8, 0x10, 0x4C, 0x89, 0xF8, 0x4C, 0x21, 0xF0, 0x48, 0x21, 0xC8,
    0x49, 0x89, 0xCC, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x4C, 0x89, 0xC1,
    0x4C, 0x89, 0xC5, 0x48, 0x31, 0xD1, 0x4C, 0x31, 0xC8, 0x48, 0x09, 0xC8, 0x0F, 0x94, 0xC0, 0x48,
    0xB9, 0x2E, 0xFC, 0xFF, 0xFF, 0xFE, 0xFF, 0x0F, 0x00, 0x48, 0x39, 0xCE, 0x49, 0x89, 0xF5] ++ bytes_l11f780_2

theorem code_l11f780_1 : ∀ x ∈ codeRange 0x11f7c9 bytes_l11f780_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f7c9 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f780_2

@[cfg_block] def b_l11f780 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f780 (pushR64Effect 0x11f780 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x11f780 (PushPre 0x11f780 1) (pushR64Effect 0x11f780 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x11f781 (pushR64Effect 0x11f781 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x11f781 (PushPre 0x11f781 2) (pushR64Effect 0x11f781 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x11f783 (pushR64Effect 0x11f783 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x11f783 (PushPre 0x11f783 2) (pushR64Effect 0x11f783 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x11f785 (pushR64Effect 0x11f785 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x11f785 (PushPre 0x11f785 2) (pushR64Effect 0x11f785 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x11f787 (pushR64Effect 0x11f787 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x11f787 (PushPre 0x11f787 2) (pushR64Effect 0x11f787 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x11f789 (pushR64Effect 0x11f789 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x11f789 (PushPre 0x11f789 1) (pushR64Effect 0x11f789 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x11f78a (subR64Imm32Effect 0x11f78a 4 0xd8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x11f78a (fun s => s.RIP = 0x11f78a) (subR64Imm32Effect 0x11f78a 4 0xd8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x11f791 (movR64R64Effect 0x11f791 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2]
    (.letOp (n := 68) (.exec 0x11f791 (fun s => s.RIP = 0x11f791) (movR64R64Effect 0x11f791 3 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.exec 0x11f794 (StorePre 0x11f794 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11f794 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f794 7 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 70) (.out 0x11f79c (movR64M64Effect 0x11f79c 8 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 71) (.exec 0x11f79c (LoadPre 0x11f79c (fun s => AddrMode.addr (.base 6 .none) s (0x11f79c + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11f79c 8 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 72) (.out 0x11f79f (movR64M64Effect 0x11f79f 15 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 73) (.exec 0x11f79f (LoadPre 0x11f79f (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11f79f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11f79f 15 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 74) (.out 0x11f7a3 (bswapR64Effect 0x11f7a3 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[70]
    (.letOp (n := 75) (.exec 0x11f7a3 (fun s => s.RIP = 0x11f7a3) (bswapR64Effect 0x11f7a3 3 8) (Reg.operands [.gpr 8] [])) #v[70]
    (.letOp (n := 76) (.out 0x11f7a6 (bswapR64Effect 0x11f7a6 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[72]
    (.letOp (n := 77) (.exec 0x11f7a6 (fun s => s.RIP = 0x11f7a6) (bswapR64Effect 0x11f7a6 3 15) (Reg.operands [.gpr 15] [])) #v[72]
    (.letOp (n := 78) (.out 0x11f7a9 (movR64M64Effect 0x11f7a9 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 79) (.exec 0x11f7a9 (LoadPre 0x11f7a9 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x11f7a9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11f7a9 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 80) (.out 0x11f7ad (bswapR64Effect 0x11f7ad 3 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[78]
    (.letOp (n := 81) (.exec 0x11f7ad (fun s => s.RIP = 0x11f7ad) (bswapR64Effect 0x11f7ad 3 0) (Reg.operands [.gpr 0] [])) #v[78]
    (.letOp (n := 82) (.out 0x11f7b0 (movR64M64Effect 0x11f7b0 6 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 83) (.exec 0x11f7b0 (LoadPre 0x11f7b0 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x11f7b0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11f7b0 6 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 84) (.out 0x11f7b4 (bswapR64Effect 0x11f7b4 3 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[82]
    (.letOp (n := 85) (.exec 0x11f7b4 (fun s => s.RIP = 0x11f7b4) (bswapR64Effect 0x11f7b4 3 6) (Reg.operands [.gpr 6] [])) #v[82]
    (.letOp (n := 86) (.out 0x11f7b7 (movR64Imm64Effect 0x11f7b7 9 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 87) (.exec 0x11f7b7 (fun s => s.RIP = 0x11f7b7) (movR64Imm64Effect 0x11f7b7 9 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 88) (.out 0x11f7c1 (movR64R64Effect 0x11f7c1 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[74]
    (.letOp (n := 89) (.exec 0x11f7c1 (fun s => s.RIP = 0x11f7c1) (movR64R64Effect 0x11f7c1 14 8) (Reg.operands [.gpr 8] [])) #v[74]
    (.letOp (n := 90) (.out 0x11f7c4 (shldR64R64Effect 0x11f7c4 5 14 15 36) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[88, 76]
    (.letOp (n := 91) (.exec 0x11f7c4 (fun s => s.RIP = 0x11f7c4) (shldR64R64Effect 0x11f7c4 5 14 15 36) (Reg.operands [.gpr 14, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[88, 76]
    (b_l11f780_1)))))))))))))))))))))))))))))))))))))))

def bytes_l11f780 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xD8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xD3, 0x48, 0x89, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x06, 0x4C,
    0x8B, 0x7E, 0x08, 0x49, 0x0F, 0xC8, 0x49, 0x0F, 0xCF, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x0F, 0xC8,
    0x48, 0x8B, 0x76, 0x18, 0x48, 0x0F, 0xCE, 0x49, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F,
    0x00, 0x4D, 0x89, 0xC6, 0x4D, 0x0F, 0xA4, 0xFE, 0x24] ++ bytes_l11f780_1

theorem code_l11f780 : ∀ x ∈ codeRange 0x11f780 bytes_l11f780, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f780 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f780_1

@[cfg_block] def b_l11f825 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f825 (notR8Effect 0x11f825 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x11f825 (fun s => s.RIP = 0x11f825) (notR8Effect 0x11f825 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x11f827 (andAlImm8Effect 0x11f827 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x11f827 (fun s => s.RIP = 0x11f827) (andAlImm8Effect 0x11f827 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x11f829 (movzxR32R8Effect 0x11f829 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x11f829 (fun s => s.RIP = 0x11f829) (movzxR32R8Effect 0x11f829 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x11f82c (callEffect (fun _ => 0x127d50) 0x11f831) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11f82c (PushPre 0x11f82c 5) (callEffect (fun _ => 0x127d50) 0x11f831) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11f831⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l11f831, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11f825 : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x1F, 0x85, 0x00, 0x00]

theorem code_l11f825 : ∀ x ∈ codeRange 0x11f825 bytes_l11f825, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f825 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f831_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x11f8d0 (movR64Imm64Effect 0x11f8d0 1 0xffffefffffc2e) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 129) (.exec 0x11f8d0 (fun s => s.RIP = 0x11f8d0) (movR64Imm64Effect 0x11f8d0 1 0xffffefffffc2e) (Reg.operands [] [])) #v[]
    (.letOp (n := 130) (.out 0x11f8da (cmpR64R64Effect 0x11f8da 15 1) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 1] []) (.flag .CF)) #v[101, 128]
    (.letOp (n := 131) (.out 0x11f8da (cmpR64R64Effect 0x11f8da 15 1) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 1] []) (.flag .ZF)) #v[101, 128]
    (.letOp (n := 132) (.exec 0x11f8da (fun s => s.RIP = 0x11f8da) (cmpR64R64Effect 0x11f8da 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[101, 128]
    (.letOp (n := 133) (.out 0x11f8dd (atFlags (condHolds 7) (setccR8Effect 0x11f8dd 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 1))) #v[128, 130, 131]
    (.letOp (n := 134) (.exec 0x11f8dd (fun s => s.RIP = 0x11f8dd) (atFlags (condHolds 7) (setccR8Effect 0x11f8dd 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[128, 130, 131]
    (.letOp (n := 135) (.out 0x11f8e0 (andR8R8Effect 0x11f8e0 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[133, 126]
    (.letOp (n := 136) (.exec 0x11f8e0 (fun s => s.RIP = 0x11f8e0) (andR8R8Effect 0x11f8e0 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[133, 126]
    (.letOp (n := 137) (.out 0x11f8e2 (movzxR32R8Effect 0x11f8e2 3 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[135]
    (.letOp (n := 138) (.exec 0x11f8e2 (fun s => s.RIP = 0x11f8e2) (movzxR32R8Effect 0x11f8e2 3 7 1) (Reg.operands [.gpr 1] [])) #v[135]
    (.letOp (n := 139) (.out 0x11f8e5 (callEffect (fun _ => 0x127d50) 0x11f8ea) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 140) (.exec 0x11f8e5 (PushPre 0x11f8e5 5) (callEffect (fun _ => 0x127d50) 0x11f8ea) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 141) (.const ⟨64, 0x11f8ea⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 126), (1, 135), (2, 117), (3, 95), (4, 139), (5, 75), (6, 6), (7, 137), (8, 8), (9, 9), (10, 10), (11, 11), (12, 97), (13, 103), (14, 115), (15, 101), (22, 22), (39, 39), (50, 50), (51, 51)] 142⟩ { target := .l11f8ea, kept := #v[], arity := rfl, guard := some (Fin.last 141) })))))))))))))))

def bytes_l11f831_2 : List UInt8 :=
  [0x48, 0xB9, 0x2E, 0xFC, 0xFF, 0xFF, 0xFE, 0xFF, 0x0F, 0x00, 0x49, 0x39, 0xCF, 0x0F, 0x97, 0xC1,
    0x20, 0xC1, 0x0F, 0xB6, 0xF9, 0xE8, 0x66, 0x84, 0x00, 0x00]

theorem code_l11f831_2 : ∀ x ∈ codeRange 0x11f8d0 bytes_l11f831_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f8d0 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f831_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.out 0x11f884 (bswapR64Effect 0x11f884 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[86]
    (.letOp (n := 89) (.exec 0x11f884 (fun s => s.RIP = 0x11f884) (bswapR64Effect 0x11f884 3 15) (Reg.operands [.gpr 15] [])) #v[86]
    (.letOp (n := 90) (.out 0x11f887 (andR64R64Effect 0x11f887 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[77, 14]
    (.letOp (n := 91) (.exec 0x11f887 (fun s => s.RIP = 0x11f887) (andR64R64Effect 0x11f887 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[77, 14]
    (.letOp (n := 92) (.exec 0x11f88a (StorePre 0x11f88a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11f88a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f88a 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[90, 4]
    (.letOp (n := 93) (.out 0x11f88f (movR64R64Effect 0x11f88f 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[71]
    (.letOp (n := 94) (.exec 0x11f88f (fun s => s.RIP = 0x11f88f) (movR64R64Effect 0x11f88f 3 2) (Reg.operands [.gpr 2] [])) #v[71]
    (.letOp (n := 95) (.out 0x11f892 (shldR64R64Effect 0x11f892 5 3 12 36) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[93, 73]
    (.letOp (n := 96) (.exec 0x11f892 (fun s => s.RIP = 0x11f892) (shldR64R64Effect 0x11f892 5 3 12 36) (Reg.operands [.gpr 3, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93, 73]
    (.letOp (n := 97) (.out 0x11f897 (shldR64R64Effect 0x11f897 5 12 13 24) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[73, 81]
    (.letOp (n := 98) (.exec 0x11f897 (fun s => s.RIP = 0x11f897) (shldR64R64Effect 0x11f897 5 12 13 24) (Reg.operands [.gpr 12, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73, 81]
    (.letOp (n := 99) (.out 0x11f89c (shldR64R64Effect 0x11f89c 5 13 15 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[81, 88]
    (.letOp (n := 100) (.exec 0x11f89c (fun s => s.RIP = 0x11f89c) (shldR64R64Effect 0x11f89c 5 13 15 12) (Reg.operands [.gpr 13, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81, 88]
    (.letOp (n := 101) (.out 0x11f8a1 (andR64R64Effect 0x11f8a1 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 5] []) (.reg (.gpr 15))) #v[88, 75]
    (.letOp (n := 102) (.exec 0x11f8a1 (fun s => s.RIP = 0x11f8a1) (andR64R64Effect 0x11f8a1 15 5) (Reg.operands [.gpr 15, .gpr 5] [])) #v[88, 75]
    (.letOp (n := 103) (.out 0x11f8a4 (andR64R64Effect 0x11f8a4 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[99, 75]
    (.letOp (n := 104) (.exec 0x11f8a4 (fun s => s.RIP = 0x11f8a4) (andR64R64Effect 0x11f8a4 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[99, 75]
    (.letOp (n := 105) (.out 0x11f8a7 (shrR64Effect 0x11f8a7 4 2 16) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 106) (.exec 0x11f8a7 (fun s => s.RIP = 0x11f8a7) (shrR64Effect 0x11f8a7 4 2 16) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 107) (.out 0x11f8ab (movR64R64Effect 0x11f8ab 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[97]
    (.letOp (n := 108) (.exec 0x11f8ab (fun s => s.RIP = 0x11f8ab) (movR64R64Effect 0x11f8ab 0 12) (Reg.operands [.gpr 12] [])) #v[97]
    (.letOp (n := 109) (.out 0x11f8ae (andR64R64Effect 0x11f8ae 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[107, 95]
    (.letOp (n := 110) (.exec 0x11f8ae (fun s => s.RIP = 0x11f8ae) (andR64R64Effect 0x11f8ae 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[107, 95]
    (.letOp (n := 111) (.out 0x11f8b1 (andR64R64Effect 0x11f8b1 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[109, 103]
    (.letOp (n := 112) (.exec 0x11f8b1 (fun s => s.RIP = 0x11f8b1) (andR64R64Effect 0x11f8b1 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[109, 103]
    (.letOp (n := 113) (.out 0x11f8b4 (movR64R64Effect 0x11f8b4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[105]
    (.letOp (n := 114) (.exec 0x11f8b4 (fun s => s.RIP = 0x11f8b4) (movR64R64Effect 0x11f8b4 1 2) (Reg.operands [.gpr 2] [])) #v[105]
    (.letOp (n := 115) (.out 0x11f8b7 (movR64R64Effect 0x11f8b7 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[105]
    (.letOp (n := 116) (.exec 0x11f8b7 (fun s => s.RIP = 0x11f8b7) (movR64R64Effect 0x11f8b7 14 2) (Reg.operands [.gpr 2] [])) #v[105]
    (.letOp (n := 117) (.out 0x11f8ba (movR64Imm64Effect 0x11f8ba 2 0xffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 118) (.exec 0x11f8ba (fun s => s.RIP = 0x11f8ba) (movR64Imm64Effect 0x11f8ba 2 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 119) (.out 0x11f8c4 (xorR64R64Effect 0x11f8c4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[113, 117]
    (.letOp (n := 120) (.exec 0x11f8c4 (fun s => s.RIP = 0x11f8c4) (xorR64R64Effect 0x11f8c4 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[113, 117]
    (.letOp (n := 121) (.out 0x11f8c7 (xorR64R64Effect 0x11f8c7 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[111, 75]
    (.letOp (n := 122) (.exec 0x11f8c7 (fun s => s.RIP = 0x11f8c7) (xorR64R64Effect 0x11f8c7 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[111, 75]
    (.letOp (n := 123) (.out 0x11f8ca (orR64R64Effect 0x11f8ca 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[121, 119]
    (.letOp (n := 124) (.out 0x11f8ca (orR64R64Effect 0x11f8ca 0 1) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 1] []) (.flag .ZF)) #v[121, 119]
    (.letOp (n := 125) (.exec 0x11f8ca (fun s => s.RIP = 0x11f8ca) (orR64R64Effect 0x11f8ca 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[121, 119]
    (.letOp (n := 126) (.out 0x11f8cd (atFlags (condHolds 4) (setccR8Effect 0x11f8cd 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[123, 124]
    (.letOp (n := 127) (.exec 0x11f8cd (fun s => s.RIP = 0x11f8cd) (atFlags (condHolds 4) (setccR8Effect 0x11f8cd 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[123, 124]
    (b_l11f831_2))))))))))))))))))))))))))))))))))))))))

def bytes_l11f831_1 : List UInt8 :=
  [0x49, 0x0F, 0xCF, 0x4C, 0x21, 0xF0, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x89, 0xD3, 0x4C, 0x0F,
    0xA4, 0xE3, 0x24, 0x4D, 0x0F, 0xA4, 0xEC, 0x18, 0x4D, 0x0F, 0xA4, 0xFD, 0x0C, 0x49, 0x21, 0xEF,
    0x49, 0x21, 0xED, 0x48, 0xC1, 0xEA, 0x10, 0x4C, 0x89, 0xE0, 0x48, 0x21, 0xD8, 0x4C, 0x21, 0xE8,
    0x48, 0x89, 0xD1, 0x49, 0x89, 0xD6, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00,
    0x48, 0x31, 0xD1, 0x48, 0x31, 0xE8, 0x48, 0x09, 0xC8, 0x0F, 0x94, 0xC0] ++ bytes_l11f831_2

theorem code_l11f831_1 : ∀ x ∈ codeRange 0x11f884 bytes_l11f831_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f884 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f831_2

@[cfg_block] def b_l11f831 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f831 (movzxR32R8Effect 0x11f831 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x11f831 (fun s => s.RIP = 0x11f831) (movzxR32R8Effect 0x11f831 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.exec 0x11f834 (StorePre 0x11f834 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11f834 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f834 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11f83c (negR64Effect 0x11f83c 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 57) (.exec 0x11f83c (fun s => s.RIP = 0x11f83c) (negR64Effect 0x11f83c 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 58) (.out 0x11f83f (andR64R64Effect 0x11f83f 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[13, 56]
    (.letOp (n := 59) (.exec 0x11f83f (fun s => s.RIP = 0x11f83f) (andR64R64Effect 0x11f83f 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[13, 56]
    (.letOp (n := 60) (.exec 0x11f842 (StorePre 0x11f842 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11f842 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f842 13 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x11f847 (andR64R64Effect 0x11f847 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[12, 56]
    (.letOp (n := 62) (.exec 0x11f847 (fun s => s.RIP = 0x11f847) (andR64R64Effect 0x11f847 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[12, 56]
    (.letOp (n := 63) (.exec 0x11f84a (StorePre 0x11f84a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11f84a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f84a 12 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x11f84f (andR64R64Effect 0x11f84f 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[5, 56]
    (.letOp (n := 65) (.exec 0x11f84f (fun s => s.RIP = 0x11f84f) (andR64R64Effect 0x11f84f 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[5, 56]
    (.letOp (n := 66) (.exec 0x11f852 (StorePre 0x11f852 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11f852 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f852 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x11f857 (movR64M64Effect 0x11f857 2 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 68) (.exec 0x11f857 (LoadPre 0x11f857 (fun s => AddrMode.addr (.base 3 .none) s (0x11f857 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11f857 2 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 69) (.out 0x11f85a (movR64M64Effect 0x11f85a 12 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[3]
    (.letOp (n := 70) (.exec 0x11f85a (LoadPre 0x11f85a (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x11f85a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11f85a 12 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 71) (.out 0x11f85e (bswapR64Effect 0x11f85e 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[67]
    (.letOp (n := 72) (.exec 0x11f85e (fun s => s.RIP = 0x11f85e) (bswapR64Effect 0x11f85e 3 2) (Reg.operands [.gpr 2] [])) #v[67]
    (.letOp (n := 73) (.out 0x11f861 (bswapR64Effect 0x11f861 3 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[69]
    (.letOp (n := 74) (.exec 0x11f861 (fun s => s.RIP = 0x11f861) (bswapR64Effect 0x11f861 3 12) (Reg.operands [.gpr 12] [])) #v[69]
    (.letOp (n := 75) (.out 0x11f864 (movR64Imm64Effect 0x11f864 5 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 76) (.exec 0x11f864 (fun s => s.RIP = 0x11f864) (movR64Imm64Effect 0x11f864 5 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x11f86e (andR64R64Effect 0x11f86e 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[56, 75]
    (.letOp (n := 78) (.exec 0x11f86e (fun s => s.RIP = 0x11f86e) (andR64R64Effect 0x11f86e 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[56, 75]
    (.letOp (n := 79) (.out 0x11f871 (movR64M64Effect 0x11f871 13 (.base 3 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[3]
    (.letOp (n := 80) (.exec 0x11f871 (LoadPre 0x11f871 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x11f871 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11f871 13 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 81) (.out 0x11f875 (bswapR64Effect 0x11f875 3 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[79]
    (.letOp (n := 82) (.exec 0x11f875 (fun s => s.RIP = 0x11f875) (bswapR64Effect 0x11f875 3 13) (Reg.operands [.gpr 13] [])) #v[79]
    (.letOp (n := 83) (.out 0x11f878 (andR64R64Effect 0x11f878 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[15, 77]
    (.letOp (n := 84) (.exec 0x11f878 (fun s => s.RIP = 0x11f878) (andR64R64Effect 0x11f878 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[15, 77]
    (.letOp (n := 85) (.exec 0x11f87b (StorePre 0x11f87b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11f87b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f87b 15 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 86) (.out 0x11f880 (movR64M64Effect 0x11f880 15 (.base 3 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[3]
    (.letOp (n := 87) (.exec 0x11f880 (LoadPre 0x11f880 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x11f880 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11f880 15 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 3] [])) #v[3]
    (b_l11f831_1)))))))))))))))))))))))))))))))))))

def bytes_l11f831 : List UInt8 :=
  [0x0F, 0xB6, 0xC0, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xD8, 0x49, 0x21,
    0xC5, 0x4C, 0x89, 0x6C, 0x24, 0x50, 0x49, 0x21, 0xC4, 0x4C, 0x89, 0x64, 0x24, 0x30, 0x48, 0x21,
    0xC5, 0x48, 0x89, 0x6C, 0x24, 0x20, 0x48, 0x8B, 0x13, 0x4C, 0x8B, 0x63, 0x08, 0x48, 0x0F, 0xCA,
    0x49, 0x0F, 0xCC, 0x48, 0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xE8,
    0x4C, 0x8B, 0x6B, 0x10, 0x49, 0x0F, 0xCD, 0x49, 0x21, 0xC7, 0x4C, 0x89, 0x7C, 0x24, 0x58, 0x4C,
    0x8B, 0x7B, 0x18] ++ bytes_l11f831_1

theorem code_l11f831 : ∀ x ∈ codeRange 0x11f831 bytes_l11f831, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f831 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11f831_1

@[cfg_block] def b_l11f8ea : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f8ea (notR8Effect 0x11f8ea 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x11f8ea (fun s => s.RIP = 0x11f8ea) (notR8Effect 0x11f8ea 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x11f8ec (andAlImm8Effect 0x11f8ec 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x11f8ec (fun s => s.RIP = 0x11f8ec) (andAlImm8Effect 0x11f8ec 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x11f8ee (movzxR32R8Effect 0x11f8ee 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x11f8ee (fun s => s.RIP = 0x11f8ee) (movzxR32R8Effect 0x11f8ee 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x11f8f1 (callEffect (fun _ => 0x127d50) 0x11f8f6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11f8f1 (PushPre 0x11f8f1 5) (callEffect (fun _ => 0x127d50) 0x11f8f6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11f8f6⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l11f8f6, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11f8ea : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x5A, 0x84, 0x00, 0x00]

theorem code_l11f8ea : ∀ x ∈ codeRange 0x11f8ea bytes_l11f8ea, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f8ea 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Sec1.LIR
