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

@[cfg_block] def b_l11b8f0_7 : Block Op Label signature Reg.count 364 :=
  .letOp (n := 364) (.out 0x11bac7 (leaR64Effect 0x11bac7 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 365) (.exec 0x11bac7 (fun s => s.RIP = 0x11bac7) (leaR64Effect 0x11bac7 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 366) (.out 0x11bacc (movR64Imm32Effect 0x11bacc 2 0x202180) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 367) (.exec 0x11bacc (fun s => s.RIP = 0x11bacc) (movR64Imm32Effect 0x11bacc 2 0x202180) (Reg.operands [] [])) #v[]
    (.letOp (n := 368) (.out 0x11bad3 (movR64Imm32Effect 0x11bad3 1 0x2021a0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 369) (.exec 0x11bad3 (fun s => s.RIP = 0x11bad3) (movR64Imm32Effect 0x11bad3 1 0x2021a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 370) (.out 0x11bada (callEffect (fun _ => 0x1109b0) 0x11badf) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 371) (.exec 0x11bada (PushPre 0x11bada 5) (callEffect (fun _ => 0x1109b0) 0x11badf) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 372) (.const ⟨64, 0x11badf⟩) #v[]
    (.terminate (.call ⟨.l1109b0, RegMap.args [(0, 328), (1, 368), (2, 366), (3, 351), (4, 370), (5, 113), (6, 364), (7, 362), (8, 308), (9, 304), (10, 240), (11, 299), (12, 354), (13, 221), (14, 345), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)] 373⟩ { target := .l11badf, kept := #v[], arity := rfl, guard := some (Fin.last 372) }))))))))))

def bytes_l11b8f0_7 : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x28, 0x48, 0xC7, 0xC2, 0x80, 0x21, 0x20, 0x00, 0x48, 0xC7, 0xC1, 0xA0,
    0x21, 0x20, 0x00, 0xE8, 0xD1, 0x4E, 0xFF, 0xFF]

theorem code_l11b8f0_7 : ∀ x ∈ codeRange 0x11bac7 bytes_l11b8f0_7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1bac7 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11b8f0_6 : Block Op Label signature Reg.count 322 :=
  .letOp (n := 322) (.out 0x11ba76 (movR64R64Effect 0x11ba76 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[320]
    (.letOp (n := 323) (.exec 0x11ba76 (fun s => s.RIP = 0x11ba76) (movR64R64Effect 0x11ba76 1 2) (Reg.operands [.gpr 2] [])) #v[320]
    (.letOp (n := 324) (.out 0x11ba79 (movR64R64Effect 0x11ba79 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[319]
    (.letOp (n := 325) (.exec 0x11ba79 (fun s => s.RIP = 0x11ba79) (movR64R64Effect 0x11ba79 6 0) (Reg.operands [.gpr 0] [])) #v[319]
    (.letOp (n := 326) (.out 0x11ba7c (movR64R64Effect 0x11ba7c 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[308]
    (.letOp (n := 327) (.exec 0x11ba7c (fun s => s.RIP = 0x11ba7c) (movR64R64Effect 0x11ba7c 0 8) (Reg.operands [.gpr 8] [])) #v[308]
    (.letOp (n := 328) (.out 0x11ba7f (mulR64Effect 0x11ba7f 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[212, 326]
    (.letOp (n := 329) (.out 0x11ba7f (mulR64Effect 0x11ba7f 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[212, 326]
    (.letOp (n := 330) (.exec 0x11ba7f (fun s => s.RIP = 0x11ba7f) (mulR64Effect 0x11ba7f 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[212, 326]
    (.letOp (n := 331) (.out 0x11ba82 (addR64R64Effect 0x11ba82 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[315, 299]
    (.letOp (n := 332) (.out 0x11ba82 (addR64R64Effect 0x11ba82 15 11) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 11] []) (.flag .CF)) #v[315, 299]
    (.letOp (n := 333) (.exec 0x11ba82 (fun s => s.RIP = 0x11ba82) (addR64R64Effect 0x11ba82 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[315, 299]
    (.letOp (n := 334) (.out 0x11ba85 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba85 3 9)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[313, 304, 332]
    (.letOp (n := 335) (.out 0x11ba85 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba85 3 9)) (Reg.operands [.gpr 3, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[313, 304, 332]
    (.letOp (n := 336) (.exec 0x11ba85 (fun s => s.RIP = 0x11ba85) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba85 3 9)) (Reg.operands [.gpr 3, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[313, 304, 332]
    (.letOp (n := 337) (.out 0x11ba88 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ba88 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[329, 335]
    (.letOp (n := 338) (.exec 0x11ba88 (fun s => s.RIP = 0x11ba88) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ba88 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[329, 335]
    (.letOp (n := 339) (.out 0x11ba8c (addR64R64Effect 0x11ba8c 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[331, 324]
    (.letOp (n := 340) (.out 0x11ba8c (addR64R64Effect 0x11ba8c 15 6) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 6] []) (.flag .CF)) #v[331, 324]
    (.letOp (n := 341) (.exec 0x11ba8c (fun s => s.RIP = 0x11ba8c) (addR64R64Effect 0x11ba8c 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[331, 324]
    (.letOp (n := 342) (.out 0x11ba8f (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba8f 3 1)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[334, 322, 340]
    (.letOp (n := 343) (.out 0x11ba8f (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba8f 3 1)) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[334, 322, 340]
    (.letOp (n := 344) (.exec 0x11ba8f (fun s => s.RIP = 0x11ba8f) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba8f 3 1)) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[334, 322, 340]
    (.letOp (n := 345) (.out 0x11ba92 (movR64R64Effect 0x11ba92 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 346) (.exec 0x11ba92 (fun s => s.RIP = 0x11ba92) (movR64R64Effect 0x11ba92 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 347) (.out 0x11ba95 (atFlags (condHolds 2) (setccR8Effect 0x11ba95 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[322, 343]
    (.letOp (n := 348) (.exec 0x11ba95 (fun s => s.RIP = 0x11ba95) (atFlags (condHolds 2) (setccR8Effect 0x11ba95 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[322, 343]
    (.letOp (n := 349) (.out 0x11ba98 (movzxR32R8Effect 0x11ba98 4 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[347]
    (.letOp (n := 350) (.exec 0x11ba98 (fun s => s.RIP = 0x11ba98) (movzxR32R8Effect 0x11ba98 4 12 1) (Reg.operands [.gpr 1] [])) #v[347]
    (.letOp (n := 351) (.out 0x11ba9c (addR64R64Effect 0x11ba9c 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[342, 328]
    (.letOp (n := 352) (.out 0x11ba9c (addR64R64Effect 0x11ba9c 3 0) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 0] []) (.flag .CF)) #v[342, 328]
    (.letOp (n := 353) (.exec 0x11ba9c (fun s => s.RIP = 0x11ba9c) (addR64R64Effect 0x11ba9c 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[342, 328]
    (.letOp (n := 354) (.out 0x11ba9f (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba9f 12 2)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[349, 337, 352]
    (.letOp (n := 355) (.exec 0x11ba9f (fun s => s.RIP = 0x11ba9f) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba9f 12 2)) (Reg.operands [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[349, 337, 352]
    (.letOp (n := 356) (.exec 0x11baa2 (StorePre 0x11baa2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11baa2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11baa2 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[351, 65]
    (.letOp (n := 357) (.exec 0x11baa7 (StorePre 0x11baa7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11baa7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11baa7 12 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[354, 65]
    (.letOp (n := 358) (.out 0x11baac (shrR64Effect 0x11baac 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[339]
    (.letOp (n := 359) (.exec 0x11baac (fun s => s.RIP = 0x11baac) (shrR64Effect 0x11baac 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[339]
    (.letOp (n := 360) (.exec 0x11bab0 (StorePre 0x11bab0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11bab0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11bab0 (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 361) (.exec 0x11bab9 (StorePre 0x11bab9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11bab9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11bab9 (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 362) (.out 0x11bac2 (leaR64Effect 0x11bac2 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 363) (.exec 0x11bac2 (fun s => s.RIP = 0x11bac2) (leaR64Effect 0x11bac2 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l11b8f0_7))))))))))))))))))))))))))))))))))))))))))

def bytes_l11b8f0_6 : List UInt8 :=
  [0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE4, 0x4D, 0x01, 0xDF, 0x4C,
    0x11, 0xCB, 0x48, 0x83, 0xD2, 0x00, 0x49, 0x01, 0xF7, 0x48, 0x11, 0xCB, 0x49, 0x89, 0xFE, 0x0F,
    0x92, 0xC1, 0x44, 0x0F, 0xB6, 0xE1, 0x48, 0x01, 0xC3, 0x49, 0x11, 0xD4, 0x48, 0x89, 0x5C, 0x24,
    0x28, 0x4C, 0x89, 0x64, 0x24, 0x30, 0x49, 0xC1, 0xEF, 0x3F, 0x48, 0xC7, 0x44, 0x24, 0x38, 0x00,
    0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24,
    0x48] ++ bytes_l11b8f0_7

theorem code_l11b8f0_6 : ∀ x ∈ codeRange 0x11ba76 bytes_l11b8f0_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ba76 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b8f0_7

@[cfg_block] def b_l11b8f0_5 : Block Op Label signature Reg.count 275 :=
  .letOp (n := 275) (.out 0x11ba38 (movzxR32R8Effect 0x11ba38 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[273]
    (.letOp (n := 276) (.exec 0x11ba38 (fun s => s.RIP = 0x11ba38) (movzxR32R8Effect 0x11ba38 3 1 0) (Reg.operands [.gpr 0] [])) #v[273]
    (.letOp (n := 277) (.out 0x11ba3b (movR64R64Effect 0x11ba3b 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[113]
    (.letOp (n := 278) (.exec 0x11ba3b (fun s => s.RIP = 0x11ba3b) (movR64R64Effect 0x11ba3b 0 5) (Reg.operands [.gpr 5] [])) #v[113]
    (.letOp (n := 279) (.out 0x11ba3e (mulR64Effect 0x11ba3e 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[225, 277]
    (.letOp (n := 280) (.out 0x11ba3e (mulR64Effect 0x11ba3e 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[225, 277]
    (.letOp (n := 281) (.exec 0x11ba3e (fun s => s.RIP = 0x11ba3e) (mulR64Effect 0x11ba3e 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[225, 277]
    (.letOp (n := 282) (.out 0x11ba41 (movR64R64Effect 0x11ba41 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[279]
    (.letOp (n := 283) (.exec 0x11ba41 (fun s => s.RIP = 0x11ba41) (movR64R64Effect 0x11ba41 9 0) (Reg.operands [.gpr 0] [])) #v[279]
    (.letOp (n := 284) (.out 0x11ba44 (addR64R64Effect 0x11ba44 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[282, 267]
    (.letOp (n := 285) (.out 0x11ba44 (addR64R64Effect 0x11ba44 9 6) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[282, 267]
    (.letOp (n := 286) (.exec 0x11ba44 (fun s => s.RIP = 0x11ba44) (addR64R64Effect 0x11ba44 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[282, 267]
    (.letOp (n := 287) (.out 0x11ba47 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba47 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[270, 280, 285]
    (.letOp (n := 288) (.out 0x11ba47 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba47 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[270, 280, 285]
    (.letOp (n := 289) (.exec 0x11ba47 (fun s => s.RIP = 0x11ba47) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba47 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[270, 280, 285]
    (.letOp (n := 290) (.out 0x11ba4a (atFlags (condHolds 2) (setccR8Effect 0x11ba4a 4 6)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[267, 288]
    (.letOp (n := 291) (.exec 0x11ba4a (fun s => s.RIP = 0x11ba4a) (atFlags (condHolds 2) (setccR8Effect 0x11ba4a 4 6)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[267, 288]
    (.letOp (n := 292) (.out 0x11ba4e (movR64R64Effect 0x11ba4e 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[221]
    (.letOp (n := 293) (.exec 0x11ba4e (fun s => s.RIP = 0x11ba4e) (movR64R64Effect 0x11ba4e 0 13) (Reg.operands [.gpr 13] [])) #v[221]
    (.letOp (n := 294) (.out 0x11ba51 (mulR64Effect 0x11ba51 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[212, 292]
    (.letOp (n := 295) (.out 0x11ba51 (mulR64Effect 0x11ba51 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[212, 292]
    (.letOp (n := 296) (.exec 0x11ba51 (fun s => s.RIP = 0x11ba51) (mulR64Effect 0x11ba51 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[212, 292]
    (.letOp (n := 297) (.out 0x11ba54 (addR64R64Effect 0x11ba54 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[294, 284]
    (.letOp (n := 298) (.exec 0x11ba54 (fun s => s.RIP = 0x11ba54) (addR64R64Effect 0x11ba54 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[294, 284]
    (.letOp (n := 299) (.out 0x11ba57 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba57 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[287, 295, 297]
    (.letOp (n := 300) (.out 0x11ba57 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba57 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[287, 295, 297]
    (.letOp (n := 301) (.exec 0x11ba57 (fun s => s.RIP = 0x11ba57) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba57 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[287, 295, 297]
    (.letOp (n := 302) (.out 0x11ba5a (movzxR32R8Effect 0x11ba5a 4 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[290]
    (.letOp (n := 303) (.exec 0x11ba5a (fun s => s.RIP = 0x11ba5a) (movzxR32R8Effect 0x11ba5a 4 9 6) (Reg.operands [.gpr 6] [])) #v[290]
    (.letOp (n := 304) (.out 0x11ba5e (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba5e 9 1)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[302, 275, 300]
    (.letOp (n := 305) (.exec 0x11ba5e (fun s => s.RIP = 0x11ba5e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba5e 9 1)) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[302, 275, 300]
    (.letOp (n := 306) (.out 0x11ba61 (movR64R64Effect 0x11ba61 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[258]
    (.letOp (n := 307) (.exec 0x11ba61 (fun s => s.RIP = 0x11ba61) (movR64R64Effect 0x11ba61 0 3) (Reg.operands [.gpr 3] [])) #v[258]
    (.letOp (n := 308) (.out 0x11ba64 (movR64R64Effect 0x11ba64 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[258]
    (.letOp (n := 309) (.exec 0x11ba64 (fun s => s.RIP = 0x11ba64) (movR64R64Effect 0x11ba64 8 3) (Reg.operands [.gpr 3] [])) #v[258]
    (.letOp (n := 310) (.out 0x11ba67 (mulR64Effect 0x11ba67 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[225, 306]
    (.letOp (n := 311) (.out 0x11ba67 (mulR64Effect 0x11ba67 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[225, 306]
    (.letOp (n := 312) (.exec 0x11ba67 (fun s => s.RIP = 0x11ba67) (mulR64Effect 0x11ba67 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[225, 306]
    (.letOp (n := 313) (.out 0x11ba6a (movR64R64Effect 0x11ba6a 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[311]
    (.letOp (n := 314) (.exec 0x11ba6a (fun s => s.RIP = 0x11ba6a) (movR64R64Effect 0x11ba6a 3 2) (Reg.operands [.gpr 2] [])) #v[311]
    (.letOp (n := 315) (.out 0x11ba6d (movR64R64Effect 0x11ba6d 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[310]
    (.letOp (n := 316) (.exec 0x11ba6d (fun s => s.RIP = 0x11ba6d) (movR64R64Effect 0x11ba6d 15 0) (Reg.operands [.gpr 0] [])) #v[310]
    (.letOp (n := 317) (.out 0x11ba70 (movR64R64Effect 0x11ba70 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[113]
    (.letOp (n := 318) (.exec 0x11ba70 (fun s => s.RIP = 0x11ba70) (movR64R64Effect 0x11ba70 0 5) (Reg.operands [.gpr 5] [])) #v[113]
    (.letOp (n := 319) (.out 0x11ba73 (mulR64Effect 0x11ba73 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[212, 317]
    (.letOp (n := 320) (.out 0x11ba73 (mulR64Effect 0x11ba73 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[212, 317]
    (.letOp (n := 321) (.exec 0x11ba73 (fun s => s.RIP = 0x11ba73) (mulR64Effect 0x11ba73 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[212, 317]
    (b_l11b8f0_6)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11b8f0_5 : List UInt8 :=
  [0x0F, 0xB6, 0xC8, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE7, 0x49, 0x89, 0xC1, 0x49, 0x01, 0xF1, 0x49,
    0x11, 0xD3, 0x40, 0x0F, 0x92, 0xC6, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE4, 0x4C, 0x01, 0xC8, 0x49,
    0x11, 0xD3, 0x44, 0x0F, 0xB6, 0xCE, 0x49, 0x11, 0xC9, 0x48, 0x89, 0xD8, 0x49, 0x89, 0xD8, 0x49,
    0xF7, 0xE7, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC7, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE4] ++ bytes_l11b8f0_6

theorem code_l11b8f0_5 : ∀ x ∈ codeRange 0x11ba38 bytes_l11b8f0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ba38 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b8f0_6

@[cfg_block] def b_l11b8f0_4 : Block Op Label signature Reg.count 227 :=
  .letOp (n := 227) (.out 0x11b9f6 (mulR64Effect 0x11b9f6 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[111, 223]
    (.letOp (n := 228) (.out 0x11b9f6 (mulR64Effect 0x11b9f6 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[111, 223]
    (.letOp (n := 229) (.exec 0x11b9f6 (fun s => s.RIP = 0x11b9f6) (mulR64Effect 0x11b9f6 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[111, 223]
    (.letOp (n := 230) (.out 0x11b9f9 (movR64R64Effect 0x11b9f9 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[228]
    (.letOp (n := 231) (.exec 0x11b9f9 (fun s => s.RIP = 0x11b9f9) (movR64R64Effect 0x11b9f9 6 2) (Reg.operands [.gpr 2] [])) #v[228]
    (.letOp (n := 232) (.out 0x11b9fc (movR64R64Effect 0x11b9fc 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[227]
    (.letOp (n := 233) (.exec 0x11b9fc (fun s => s.RIP = 0x11b9fc) (movR64R64Effect 0x11b9fc 14 0) (Reg.operands [.gpr 0] [])) #v[227]
    (.letOp (n := 234) (.out 0x11b9ff (addR64R64Effect 0x11b9ff 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[232, 202]
    (.letOp (n := 235) (.out 0x11b9ff (addR64R64Effect 0x11b9ff 14 3) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 3] []) (.flag .CF)) #v[232, 202]
    (.letOp (n := 236) (.exec 0x11b9ff (fun s => s.RIP = 0x11b9ff) (addR64R64Effect 0x11b9ff 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[232, 202]
    (.letOp (n := 237) (.out 0x11ba02 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba02 6 11)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[230, 205, 235]
    (.letOp (n := 238) (.out 0x11ba02 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba02 6 11)) (Reg.operands [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[230, 205, 235]
    (.letOp (n := 239) (.exec 0x11ba02 (fun s => s.RIP = 0x11ba02) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba02 6 11)) (Reg.operands [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[230, 205, 235]
    (.letOp (n := 240) (.out 0x11ba05 (atFlags (condHolds 2) (setccR8Effect 0x11ba05 4 10)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[216, 238]
    (.letOp (n := 241) (.exec 0x11ba05 (fun s => s.RIP = 0x11ba05) (atFlags (condHolds 2) (setccR8Effect 0x11ba05 4 10)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[216, 238]
    (.letOp (n := 242) (.out 0x11ba09 (movR64M64Effect 0x11ba09 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 243) (.exec 0x11ba09 (LoadPre 0x11ba09 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ba09 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ba09 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 244) (.out 0x11ba0e (mulR64Effect 0x11ba0e 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[212, 242]
    (.letOp (n := 245) (.out 0x11ba0e (mulR64Effect 0x11ba0e 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[212, 242]
    (.letOp (n := 246) (.exec 0x11ba0e (fun s => s.RIP = 0x11ba0e) (mulR64Effect 0x11ba0e 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[212, 242]
    (.letOp (n := 247) (.out 0x11ba11 (movR64R64Effect 0x11ba11 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[245]
    (.letOp (n := 248) (.exec 0x11ba11 (fun s => s.RIP = 0x11ba11) (movR64R64Effect 0x11ba11 9 2) (Reg.operands [.gpr 2] [])) #v[245]
    (.letOp (n := 249) (.out 0x11ba14 (movzxR32R8Effect 0x11ba14 4 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[240]
    (.letOp (n := 250) (.exec 0x11ba14 (fun s => s.RIP = 0x11ba14) (movzxR32R8Effect 0x11ba14 4 11 10) (Reg.operands [.gpr 10] [])) #v[240]
    (.letOp (n := 251) (.out 0x11ba18 (addR64R64Effect 0x11ba18 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[244, 234]
    (.letOp (n := 252) (.exec 0x11ba18 (fun s => s.RIP = 0x11ba18) (addR64R64Effect 0x11ba18 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[244, 234]
    (.letOp (n := 253) (.out 0x11ba1b (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba1b 9 6)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[247, 237, 251]
    (.letOp (n := 254) (.out 0x11ba1b (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba1b 9 6)) (Reg.operands [.gpr 9, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[247, 237, 251]
    (.letOp (n := 255) (.exec 0x11ba1b (fun s => s.RIP = 0x11ba1b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba1b 9 6)) (Reg.operands [.gpr 9, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[247, 237, 251]
    (.letOp (n := 256) (.out 0x11ba1e (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba1e 11 1)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[249, 219, 254]
    (.letOp (n := 257) (.exec 0x11ba1e (fun s => s.RIP = 0x11ba1e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba1e 11 1)) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[249, 219, 254]
    (.letOp (n := 258) (.out 0x11ba21 (movR64M64Effect 0x11ba21 3 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 259) (.exec 0x11ba21 (LoadPre 0x11ba21 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11ba21 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ba21 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 260) (.out 0x11ba26 (movR64R64Effect 0x11ba26 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[258]
    (.letOp (n := 261) (.exec 0x11ba26 (fun s => s.RIP = 0x11ba26) (movR64R64Effect 0x11ba26 0 3) (Reg.operands [.gpr 3] [])) #v[258]
    (.letOp (n := 262) (.out 0x11ba29 (mulR64Effect 0x11ba29 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[150, 260]
    (.letOp (n := 263) (.out 0x11ba29 (mulR64Effect 0x11ba29 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[150, 260]
    (.letOp (n := 264) (.exec 0x11ba29 (fun s => s.RIP = 0x11ba29) (mulR64Effect 0x11ba29 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[150, 260]
    (.letOp (n := 265) (.out 0x11ba2c (movR64R64Effect 0x11ba2c 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[262]
    (.letOp (n := 266) (.exec 0x11ba2c (fun s => s.RIP = 0x11ba2c) (movR64R64Effect 0x11ba2c 6 0) (Reg.operands [.gpr 0] [])) #v[262]
    (.letOp (n := 267) (.out 0x11ba2f (addR64R64Effect 0x11ba2f 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[265, 253]
    (.letOp (n := 268) (.out 0x11ba2f (addR64R64Effect 0x11ba2f 6 9) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 9] []) (.flag .CF)) #v[265, 253]
    (.letOp (n := 269) (.exec 0x11ba2f (fun s => s.RIP = 0x11ba2f) (addR64R64Effect 0x11ba2f 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[265, 253]
    (.letOp (n := 270) (.out 0x11ba32 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba32 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[256, 263, 268]
    (.letOp (n := 271) (.out 0x11ba32 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba32 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[256, 263, 268]
    (.letOp (n := 272) (.exec 0x11ba32 (fun s => s.RIP = 0x11ba32) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ba32 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[256, 263, 268]
    (.letOp (n := 273) (.out 0x11ba35 (atFlags (condHolds 2) (setccR8Effect 0x11ba35 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[262, 271]
    (.letOp (n := 274) (.exec 0x11ba35 (fun s => s.RIP = 0x11ba35) (atFlags (condHolds 2) (setccR8Effect 0x11ba35 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[262, 271]
    (b_l11b8f0_5))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11b8f0_4 : List UInt8 :=
  [0x48, 0xF7, 0xE6, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC6, 0x49, 0x01, 0xDE, 0x4C, 0x11, 0xDE, 0x41,
    0x0F, 0x92, 0xC2, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x49, 0xF7, 0xE4, 0x49, 0x89, 0xD1, 0x45, 0x0F,
    0xB6, 0xDA, 0x4C, 0x01, 0xF0, 0x49, 0x11, 0xF1, 0x49, 0x11, 0xCB, 0x48, 0x8B, 0x5C, 0x24, 0x10,
    0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0xC6, 0x4C, 0x01, 0xCE, 0x49, 0x11, 0xD3, 0x0F,
    0x92, 0xC0] ++ bytes_l11b8f0_5

theorem code_l11b8f0_4 : ∀ x ∈ codeRange 0x11b9f6 bytes_l11b8f0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b9f6 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b8f0_5

@[cfg_block] def b_l11b8f0_3 : Block Op Label signature Reg.count 180 :=
  .letOp (n := 180) (.out 0x11b9b2 (movR64R64Effect 0x11b9b2 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[136]
    (.letOp (n := 181) (.exec 0x11b9b2 (fun s => s.RIP = 0x11b9b2) (movR64R64Effect 0x11b9b2 0 9) (Reg.operands [.gpr 9] [])) #v[136]
    (.letOp (n := 182) (.out 0x11b9b5 (mulR64Effect 0x11b9b5 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[69, 180]
    (.letOp (n := 183) (.out 0x11b9b5 (mulR64Effect 0x11b9b5 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[69, 180]
    (.letOp (n := 184) (.exec 0x11b9b5 (fun s => s.RIP = 0x11b9b5) (mulR64Effect 0x11b9b5 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[69, 180]
    (.letOp (n := 185) (.out 0x11b9b8 (movR64R64Effect 0x11b9b8 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[183]
    (.letOp (n := 186) (.exec 0x11b9b8 (fun s => s.RIP = 0x11b9b8) (movR64R64Effect 0x11b9b8 11 2) (Reg.operands [.gpr 2] [])) #v[183]
    (.letOp (n := 187) (.out 0x11b9bb (movR64R64Effect 0x11b9bb 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[182]
    (.letOp (n := 188) (.exec 0x11b9bb (fun s => s.RIP = 0x11b9bb) (movR64R64Effect 0x11b9bb 3 0) (Reg.operands [.gpr 0] [])) #v[182]
    (.letOp (n := 189) (.out 0x11b9be (movR64R64Effect 0x11b9be 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[113]
    (.letOp (n := 190) (.exec 0x11b9be (fun s => s.RIP = 0x11b9be) (movR64R64Effect 0x11b9be 0 5) (Reg.operands [.gpr 5] [])) #v[113]
    (.letOp (n := 191) (.out 0x11b9c1 (mulR64Effect 0x11b9c1 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[150, 189]
    (.letOp (n := 192) (.out 0x11b9c1 (mulR64Effect 0x11b9c1 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[150, 189]
    (.letOp (n := 193) (.exec 0x11b9c1 (fun s => s.RIP = 0x11b9c1) (mulR64Effect 0x11b9c1 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[150, 189]
    (.letOp (n := 194) (.out 0x11b9c4 (addR64R64Effect 0x11b9c4 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[187, 175]
    (.letOp (n := 195) (.out 0x11b9c4 (addR64R64Effect 0x11b9c4 3 12) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 12] []) (.flag .CF)) #v[187, 175]
    (.letOp (n := 196) (.exec 0x11b9c4 (fun s => s.RIP = 0x11b9c4) (addR64R64Effect 0x11b9c4 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[187, 175]
    (.letOp (n := 197) (.out 0x11b9c7 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9c7 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[185, 178, 195]
    (.letOp (n := 198) (.out 0x11b9c7 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9c7 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[185, 178, 195]
    (.letOp (n := 199) (.exec 0x11b9c7 (fun s => s.RIP = 0x11b9c7) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9c7 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[185, 178, 195]
    (.letOp (n := 200) (.out 0x11b9ca (atFlags (condHolds 2) (setccR8Effect 0x11b9ca 4 10)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[143, 198]
    (.letOp (n := 201) (.exec 0x11b9ca (fun s => s.RIP = 0x11b9ca) (atFlags (condHolds 2) (setccR8Effect 0x11b9ca 4 10)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[143, 198]
    (.letOp (n := 202) (.out 0x11b9ce (addR64R64Effect 0x11b9ce 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[194, 191]
    (.letOp (n := 203) (.out 0x11b9ce (addR64R64Effect 0x11b9ce 3 0) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 0] []) (.flag .CF)) #v[194, 191]
    (.letOp (n := 204) (.exec 0x11b9ce (fun s => s.RIP = 0x11b9ce) (addR64R64Effect 0x11b9ce 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[194, 191]
    (.letOp (n := 205) (.out 0x11b9d1 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9d1 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[197, 192, 203]
    (.letOp (n := 206) (.out 0x11b9d1 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9d1 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[197, 192, 203]
    (.letOp (n := 207) (.exec 0x11b9d1 (fun s => s.RIP = 0x11b9d1) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9d1 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[197, 192, 203]
    (.letOp (n := 208) (.out 0x11b9d4 (atFlags (condHolds 2) (setccR8Effect 0x11b9d4 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[191, 206]
    (.letOp (n := 209) (.exec 0x11b9d4 (fun s => s.RIP = 0x11b9d4) (atFlags (condHolds 2) (setccR8Effect 0x11b9d4 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[191, 206]
    (.letOp (n := 210) (.out 0x11b9d7 (movR64M64Effect 0x11b9d7 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 211) (.exec 0x11b9d7 (LoadPre 0x11b9d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11b9d7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b9d7 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 212) (.out 0x11b9dc (movR64M64Effect 0x11b9dc 12 (.base 1 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[210]
    (.letOp (n := 213) (.exec 0x11b9dc (LoadPre 0x11b9dc (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x11b9dc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b9dc 12 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 1] [])) #v[210]
    (.letOp (n := 214) (.out 0x11b9e0 (movzxR32R8Effect 0x11b9e0 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[208]
    (.letOp (n := 215) (.exec 0x11b9e0 (fun s => s.RIP = 0x11b9e0) (movzxR32R8Effect 0x11b9e0 3 1 0) (Reg.operands [.gpr 0] [])) #v[208]
    (.letOp (n := 216) (.out 0x11b9e3 (addR8Imm8Effect 0x11b9e3 4 10 0xff) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[200]
    (.letOp (n := 217) (.out 0x11b9e3 (addR8Imm8Effect 0x11b9e3 4 10 0xff) (EffectPart.reads (.flag .CF) [.gpr 10] []) (.flag .CF)) #v[200]
    (.letOp (n := 218) (.exec 0x11b9e3 (fun s => s.RIP = 0x11b9e3) (addR8Imm8Effect 0x11b9e3 4 10 0xff) (Reg.operands [.gpr 10] [])) #v[200]
    (.letOp (n := 219) (.out 0x11b9e7 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11b9e7 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[214, 217]
    (.letOp (n := 220) (.exec 0x11b9e7 (fun s => s.RIP = 0x11b9e7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11b9e7 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[214, 217]
    (.letOp (n := 221) (.out 0x11b9eb (movR64M64Effect 0x11b9eb 13 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 222) (.exec 0x11b9eb (LoadPre 0x11b9eb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b9eb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b9eb 13 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 223) (.out 0x11b9f0 (movR64R64Effect 0x11b9f0 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[221]
    (.letOp (n := 224) (.exec 0x11b9f0 (fun s => s.RIP = 0x11b9f0) (movR64R64Effect 0x11b9f0 0 13) (Reg.operands [.gpr 13] [])) #v[221]
    (.letOp (n := 225) (.out 0x11b9f3 (movR64R64Effect 0x11b9f3 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[111]
    (.letOp (n := 226) (.exec 0x11b9f3 (fun s => s.RIP = 0x11b9f3) (movR64R64Effect 0x11b9f3 15 6) (Reg.operands [.gpr 6] [])) #v[111]
    (b_l11b8f0_4)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11b8f0_3 : List UInt8 :=
  [0x4C, 0x89, 0xC8, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC3, 0x48, 0x89, 0xE8, 0x49,
    0xF7, 0xE0, 0x4C, 0x01, 0xE3, 0x4D, 0x11, 0xEB, 0x41, 0x0F, 0x92, 0xC2, 0x48, 0x01, 0xC3, 0x49,
    0x11, 0xD3, 0x0F, 0x92, 0xC0, 0x48, 0x8B, 0x4C, 0x24, 0x20, 0x4C, 0x8B, 0x61, 0x18, 0x0F, 0xB6,
    0xC8, 0x41, 0x80, 0xC2, 0xFF, 0x48, 0x83, 0xD1, 0x00, 0x4C, 0x8B, 0x6C, 0x24, 0x18, 0x4C, 0x89,
    0xE8, 0x49, 0x89, 0xF7] ++ bytes_l11b8f0_4

theorem code_l11b8f0_3 : ∀ x ∈ codeRange 0x11b9b2 bytes_l11b8f0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b9b2 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b8f0_4

@[cfg_block] def b_l11b8f0_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x11b96e (movR64M64Effect 0x11b96e 9 (.base 8 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[67]
    (.letOp (n := 137) (.exec 0x11b96e (LoadPre 0x11b96e (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x11b96e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b96e 9 (.base 8 (.d8 0x18))) (Reg.operands [.gpr 8] [])) #v[67]
    (.letOp (n := 138) (.exec 0x11b972 (StorePre 0x11b972 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b972 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b972 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[136, 65]
    (.letOp (n := 139) (.out 0x11b977 (xorR32R32Effect 0x11b977 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[108, 108]
    (.letOp (n := 140) (.exec 0x11b977 (fun s => s.RIP = 0x11b977) (xorR32R32Effect 0x11b977 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[108, 108]
    (.letOp (n := 141) (.out 0x11b97a (cmpR64R64Effect 0x11b97a 11 15) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 15] []) (.flag .CF)) #v[134, 120]
    (.letOp (n := 142) (.exec 0x11b97a (fun s => s.RIP = 0x11b97a) (cmpR64R64Effect 0x11b97a 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[134, 120]
    (.letOp (n := 143) (.out 0x11b97d (atFlags (condHolds 2) (setccR8Effect 0x11b97d 4 10)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[139, 141]
    (.letOp (n := 144) (.exec 0x11b97d (fun s => s.RIP = 0x11b97d) (atFlags (condHolds 2) (setccR8Effect 0x11b97d 4 10)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[139, 141]
    (.letOp (n := 145) (.out 0x11b981 (movR64R64Effect 0x11b981 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 146) (.exec 0x11b981 (fun s => s.RIP = 0x11b981) (movR64R64Effect 0x11b981 0 12) (Reg.operands [.gpr 12] [])) #v[73]
    (.letOp (n := 147) (.out 0x11b984 (mulR64Effect 0x11b984 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[92, 145]
    (.letOp (n := 148) (.out 0x11b984 (mulR64Effect 0x11b984 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[92, 145]
    (.letOp (n := 149) (.exec 0x11b984 (fun s => s.RIP = 0x11b984) (mulR64Effect 0x11b984 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[92, 145]
    (.letOp (n := 150) (.out 0x11b987 (movR64R64Effect 0x11b987 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 13] []) (.reg (.gpr 8))) #v[92]
    (.letOp (n := 151) (.exec 0x11b987 (fun s => s.RIP = 0x11b987) (movR64R64Effect 0x11b987 8 13) (Reg.operands [.gpr 13] [])) #v[92]
    (.letOp (n := 152) (.out 0x11b98a (movR64R64Effect 0x11b98a 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[148]
    (.letOp (n := 153) (.exec 0x11b98a (fun s => s.RIP = 0x11b98a) (movR64R64Effect 0x11b98a 14 2) (Reg.operands [.gpr 2] [])) #v[148]
    (.letOp (n := 154) (.out 0x11b98d (movR64R64Effect 0x11b98d 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[147]
    (.letOp (n := 155) (.exec 0x11b98d (fun s => s.RIP = 0x11b98d) (movR64R64Effect 0x11b98d 15 0) (Reg.operands [.gpr 0] [])) #v[147]
    (.letOp (n := 156) (.out 0x11b990 (addR64R64Effect 0x11b990 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[154, 131]
    (.letOp (n := 157) (.out 0x11b990 (addR64R64Effect 0x11b990 15 3) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 3] []) (.flag .CF)) #v[154, 131]
    (.letOp (n := 158) (.exec 0x11b990 (fun s => s.RIP = 0x11b990) (addR64R64Effect 0x11b990 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[154, 131]
    (.letOp (n := 159) (.out 0x11b993 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b993 14 11)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[152, 134, 157]
    (.letOp (n := 160) (.out 0x11b993 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b993 14 11)) (Reg.operands [.gpr 14, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[152, 134, 157]
    (.letOp (n := 161) (.exec 0x11b993 (fun s => s.RIP = 0x11b993) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b993 14 11)) (Reg.operands [.gpr 14, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[152, 134, 157]
    (.letOp (n := 162) (.out 0x11b996 (atFlags (condHolds 2) (setccR8Effect 0x11b996 4 11)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[134, 160]
    (.letOp (n := 163) (.exec 0x11b996 (fun s => s.RIP = 0x11b996) (atFlags (condHolds 2) (setccR8Effect 0x11b996 4 11)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[134, 160]
    (.letOp (n := 164) (.out 0x11b99a (movR64M64Effect 0x11b99a 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 165) (.exec 0x11b99a (LoadPre 0x11b99a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b99a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b99a 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 166) (.out 0x11b99f (mulR64Effect 0x11b99f 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[111, 164]
    (.letOp (n := 167) (.out 0x11b99f (mulR64Effect 0x11b99f 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[111, 164]
    (.letOp (n := 168) (.exec 0x11b99f (fun s => s.RIP = 0x11b99f) (mulR64Effect 0x11b99f 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[111, 164]
    (.letOp (n := 169) (.out 0x11b9a2 (movR64R64Effect 0x11b9a2 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[167]
    (.letOp (n := 170) (.exec 0x11b9a2 (fun s => s.RIP = 0x11b9a2) (movR64R64Effect 0x11b9a2 12 2) (Reg.operands [.gpr 2] [])) #v[167]
    (.letOp (n := 171) (.out 0x11b9a5 (movzxR32R8Effect 0x11b9a5 4 13 11) (EffectPart.reads (.reg (.gpr 13)) [.gpr 11] []) (.reg (.gpr 13))) #v[162]
    (.letOp (n := 172) (.exec 0x11b9a5 (fun s => s.RIP = 0x11b9a5) (movzxR32R8Effect 0x11b9a5 4 13 11) (Reg.operands [.gpr 11] [])) #v[162]
    (.letOp (n := 173) (.out 0x11b9a9 (addR64R64Effect 0x11b9a9 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[166, 156]
    (.letOp (n := 174) (.exec 0x11b9a9 (fun s => s.RIP = 0x11b9a9) (addR64R64Effect 0x11b9a9 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[166, 156]
    (.letOp (n := 175) (.out 0x11b9ac (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9ac 12 14)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[169, 159, 173]
    (.letOp (n := 176) (.out 0x11b9ac (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9ac 12 14)) (Reg.operands [.gpr 12, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[169, 159, 173]
    (.letOp (n := 177) (.exec 0x11b9ac (fun s => s.RIP = 0x11b9ac) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9ac 12 14)) (Reg.operands [.gpr 12, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[169, 159, 173]
    (.letOp (n := 178) (.out 0x11b9af (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9af 13 10)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[171, 143, 176]
    (.letOp (n := 179) (.exec 0x11b9af (fun s => s.RIP = 0x11b9af) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b9af 13 10)) (Reg.operands [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[171, 143, 176]
    (b_l11b8f0_3))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11b8f0_2 : List UInt8 :=
  [0x4D, 0x8B, 0x48, 0x18, 0x4C, 0x89, 0x4C, 0x24, 0x10, 0x45, 0x31, 0xD2, 0x4D, 0x39, 0xFB, 0x41,
    0x0F, 0x92, 0xC2, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE5, 0x4D, 0x89, 0xE8, 0x49, 0x89, 0xD6, 0x49,
    0x89, 0xC7, 0x49, 0x01, 0xDF, 0x4D, 0x11, 0xDE, 0x41, 0x0F, 0x92, 0xC3, 0x48, 0x8B, 0x44, 0x24,
    0x08, 0x48, 0xF7, 0xE6, 0x49, 0x89, 0xD4, 0x45, 0x0F, 0xB6, 0xEB, 0x4C, 0x01, 0xF8, 0x4D, 0x11,
    0xF4, 0x4D, 0x11, 0xD5] ++ bytes_l11b8f0_3

theorem code_l11b8f0_2 : ∀ x ∈ codeRange 0x11b96e bytes_l11b8f0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b96e 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b8f0_3

@[cfg_block] def b_l11b8f0_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x11b92a (movR64M64Effect 0x11b92a 13 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 93) (.exec 0x11b92a (LoadPre 0x11b92a (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11b92a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b92a 13 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 94) (.exec 0x11b92e (StorePre 0x11b92e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11b92e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b92e 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 65]
    (.letOp (n := 95) (.out 0x11b933 (leaR64Effect 0x11b933 15 (.sib 10 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 10, .gpr 0] []) (.reg (.gpr 15))) #v[80, 85]
    (.letOp (n := 96) (.exec 0x11b933 (fun s => s.RIP = 0x11b933) (leaR64Effect 0x11b933 15 (.sib 10 (some 0) 0 .none)) (Reg.operands [.gpr 10, .gpr 0] [])) #v[80, 85]
    (.letOp (n := 97) (.out 0x11b937 (movR64R64Effect 0x11b937 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[71]
    (.letOp (n := 98) (.exec 0x11b937 (fun s => s.RIP = 0x11b937) (movR64R64Effect 0x11b937 0 9) (Reg.operands [.gpr 9] [])) #v[71]
    (.letOp (n := 99) (.out 0x11b93a (mulR64Effect 0x11b93a 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[92, 97]
    (.letOp (n := 100) (.out 0x11b93a (mulR64Effect 0x11b93a 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[92, 97]
    (.letOp (n := 101) (.exec 0x11b93a (fun s => s.RIP = 0x11b93a) (mulR64Effect 0x11b93a 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[92, 97]
    (.letOp (n := 102) (.out 0x11b93d (movR64R64Effect 0x11b93d 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[100]
    (.letOp (n := 103) (.exec 0x11b93d (fun s => s.RIP = 0x11b93d) (movR64R64Effect 0x11b93d 14 2) (Reg.operands [.gpr 2] [])) #v[100]
    (.letOp (n := 104) (.out 0x11b940 (addR64R64Effect 0x11b940 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[99, 95]
    (.letOp (n := 105) (.exec 0x11b940 (fun s => s.RIP = 0x11b940) (addR64R64Effect 0x11b940 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[99, 95]
    (.letOp (n := 106) (.out 0x11b943 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11b943 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[102, 104]
    (.letOp (n := 107) (.exec 0x11b943 (fun s => s.RIP = 0x11b943) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11b943 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[102, 104]
    (.letOp (n := 108) (.out 0x11b947 (addR64R64Effect 0x11b947 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[80, 88]
    (.letOp (n := 109) (.out 0x11b947 (addR64R64Effect 0x11b947 10 11) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 11] []) (.flag .CF)) #v[80, 88]
    (.letOp (n := 110) (.exec 0x11b947 (fun s => s.RIP = 0x11b947) (addR64R64Effect 0x11b947 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[80, 88]
    (.letOp (n := 111) (.out 0x11b94a (movR64M64Effect 0x11b94a 6 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 112) (.exec 0x11b94a (LoadPre 0x11b94a (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x11b94a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b94a 6 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 113) (.out 0x11b94e (movR64M64Effect 0x11b94e 5 (.base 8 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 8] []) (.reg (.gpr 5))) #v[67]
    (.letOp (n := 114) (.exec 0x11b94e (LoadPre 0x11b94e (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x11b94e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b94e 5 (.base 8 (.d8 0x10))) (Reg.operands [.gpr 8] [])) #v[67]
    (.letOp (n := 115) (.out 0x11b952 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b952 14 3)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[106, 90, 109]
    (.letOp (n := 116) (.out 0x11b952 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b952 14 3)) (Reg.operands [.gpr 14, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[106, 90, 109]
    (.letOp (n := 117) (.exec 0x11b952 (fun s => s.RIP = 0x11b952) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b952 14 3)) (Reg.operands [.gpr 14, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[106, 90, 109]
    (.letOp (n := 118) (.out 0x11b955 (atFlags (condHolds 2) (setccR8Effect 0x11b955 3 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[100, 116]
    (.letOp (n := 119) (.exec 0x11b955 (fun s => s.RIP = 0x11b955) (atFlags (condHolds 2) (setccR8Effect 0x11b955 3 2)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[100, 116]
    (.letOp (n := 120) (.out 0x11b958 (movzxR32R8Effect 0x11b958 4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[118]
    (.letOp (n := 121) (.exec 0x11b958 (fun s => s.RIP = 0x11b958) (movzxR32R8Effect 0x11b958 4 15 2) (Reg.operands [.gpr 2] [])) #v[118]
    (.letOp (n := 122) (.out 0x11b95c (movR64R64Effect 0x11b95c 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[113]
    (.letOp (n := 123) (.exec 0x11b95c (fun s => s.RIP = 0x11b95c) (movR64R64Effect 0x11b95c 0 5) (Reg.operands [.gpr 5] [])) #v[113]
    (.letOp (n := 124) (.out 0x11b95f (mulR64Effect 0x11b95f 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[69, 122]
    (.letOp (n := 125) (.out 0x11b95f (mulR64Effect 0x11b95f 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[69, 122]
    (.letOp (n := 126) (.exec 0x11b95f (fun s => s.RIP = 0x11b95f) (mulR64Effect 0x11b95f 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[69, 122]
    (.letOp (n := 127) (.out 0x11b962 (movR64R64Effect 0x11b962 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[125]
    (.letOp (n := 128) (.exec 0x11b962 (fun s => s.RIP = 0x11b962) (movR64R64Effect 0x11b962 11 2) (Reg.operands [.gpr 2] [])) #v[125]
    (.letOp (n := 129) (.out 0x11b965 (movR64R64Effect 0x11b965 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[124]
    (.letOp (n := 130) (.exec 0x11b965 (fun s => s.RIP = 0x11b965) (movR64R64Effect 0x11b965 3 0) (Reg.operands [.gpr 0] [])) #v[124]
    (.letOp (n := 131) (.out 0x11b968 (addR64R64Effect 0x11b968 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[129, 115]
    (.letOp (n := 132) (.out 0x11b968 (addR64R64Effect 0x11b968 3 14) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 14] []) (.flag .CF)) #v[129, 115]
    (.letOp (n := 133) (.exec 0x11b968 (fun s => s.RIP = 0x11b968) (addR64R64Effect 0x11b968 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[129, 115]
    (.letOp (n := 134) (.out 0x11b96b (atFlags StatusFlags.CF (adcR64R64Effect 0x11b96b 11 15)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[127, 120, 132]
    (.letOp (n := 135) (.exec 0x11b96b (fun s => s.RIP = 0x11b96b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b96b 11 15)) (Reg.operands [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[127, 120, 132]
    (b_l11b8f0_2))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11b8f0_1 : List UInt8 :=
  [0x4C, 0x8B, 0x6E, 0x08, 0x48, 0x89, 0x74, 0x24, 0x20, 0x4D, 0x8D, 0x3C, 0x02, 0x4C, 0x89, 0xC8,
    0x49, 0xF7, 0xE5, 0x49, 0x89, 0xD6, 0x4C, 0x01, 0xF8, 0x49, 0x83, 0xD6, 0x00, 0x4D, 0x01, 0xDA,
    0x48, 0x8B, 0x76, 0x10, 0x49, 0x8B, 0x68, 0x10, 0x49, 0x11, 0xDE, 0x0F, 0x92, 0xC2, 0x44, 0x0F,
    0xB6, 0xFA, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC3, 0x4C, 0x01,
    0xF3, 0x4D, 0x11, 0xFB] ++ bytes_l11b8f0_2

theorem code_l11b8f0_1 : ∀ x ∈ codeRange 0x11b92a bytes_l11b8f0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b92a 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b8f0_2

@[cfg_block] def b_l11b8f0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11b8f0 (pushR64Effect 0x11b8f0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x11b8f0 (PushPre 0x11b8f0 1) (pushR64Effect 0x11b8f0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x11b8f1 (pushR64Effect 0x11b8f1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x11b8f1 (PushPre 0x11b8f1 2) (pushR64Effect 0x11b8f1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x11b8f3 (pushR64Effect 0x11b8f3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x11b8f3 (PushPre 0x11b8f3 2) (pushR64Effect 0x11b8f3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x11b8f5 (pushR64Effect 0x11b8f5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x11b8f5 (PushPre 0x11b8f5 2) (pushR64Effect 0x11b8f5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x11b8f7 (pushR64Effect 0x11b8f7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x11b8f7 (PushPre 0x11b8f7 2) (pushR64Effect 0x11b8f7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x11b8f9 (pushR64Effect 0x11b8f9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x11b8f9 (PushPre 0x11b8f9 1) (pushR64Effect 0x11b8f9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x11b8fa (subR64Imm8Effect 0x11b8fa 4 0x68) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x11b8fa (fun s => s.RIP = 0x11b8fa) (subR64Imm8Effect 0x11b8fa 4 0x68) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x11b8fe (movR64R64Effect 0x11b8fe 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2]
    (.letOp (n := 68) (.exec 0x11b8fe (fun s => s.RIP = 0x11b8fe) (movR64R64Effect 0x11b8fe 8 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x11b901 (movR64M64Effect 0x11b901 1 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 70) (.exec 0x11b901 (LoadPre 0x11b901 (fun s => AddrMode.addr (.base 6 .none) s (0x11b901 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11b901 1 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x11b904 (movR64M64Effect 0x11b904 9 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2]
    (.letOp (n := 72) (.exec 0x11b904 (LoadPre 0x11b904 (fun s => AddrMode.addr (.base 2 .none) s (0x11b904 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11b904 9 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.out 0x11b907 (movR64M64Effect 0x11b907 12 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2]
    (.letOp (n := 74) (.exec 0x11b907 (LoadPre 0x11b907 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x11b907 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b907 12 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 75) (.out 0x11b90b (movR64R64Effect 0x11b90b 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[71]
    (.letOp (n := 76) (.exec 0x11b90b (fun s => s.RIP = 0x11b90b) (movR64R64Effect 0x11b90b 0 9) (Reg.operands [.gpr 9] [])) #v[71]
    (.letOp (n := 77) (.exec 0x11b90e (StorePre 0x11b90e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b90e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b90e 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[71, 65]
    (.letOp (n := 78) (.out 0x11b913 (mulR64Effect 0x11b913 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[69, 75]
    (.letOp (n := 79) (.exec 0x11b913 (fun s => s.RIP = 0x11b913) (mulR64Effect 0x11b913 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[69, 75]
    (.letOp (n := 80) (.out 0x11b916 (movR64R64Effect 0x11b916 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[78]
    (.letOp (n := 81) (.exec 0x11b916 (fun s => s.RIP = 0x11b916) (movR64R64Effect 0x11b916 10 2) (Reg.operands [.gpr 2] [])) #v[78]
    (.letOp (n := 82) (.out 0x11b919 (movR64R64Effect 0x11b919 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 83) (.exec 0x11b919 (fun s => s.RIP = 0x11b919) (movR64R64Effect 0x11b919 0 12) (Reg.operands [.gpr 12] [])) #v[73]
    (.letOp (n := 84) (.exec 0x11b91c (StorePre 0x11b91c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b91c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b91c 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[73, 65]
    (.letOp (n := 85) (.out 0x11b921 (mulR64Effect 0x11b921 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[69, 82]
    (.letOp (n := 86) (.out 0x11b921 (mulR64Effect 0x11b921 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[69, 82]
    (.letOp (n := 87) (.exec 0x11b921 (fun s => s.RIP = 0x11b921) (mulR64Effect 0x11b921 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[69, 82]
    (.letOp (n := 88) (.out 0x11b924 (movR64R64Effect 0x11b924 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[85]
    (.letOp (n := 89) (.exec 0x11b924 (fun s => s.RIP = 0x11b924) (movR64R64Effect 0x11b924 11 0) (Reg.operands [.gpr 0] [])) #v[85]
    (.letOp (n := 90) (.out 0x11b927 (movR64R64Effect 0x11b927 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[86]
    (.letOp (n := 91) (.exec 0x11b927 (fun s => s.RIP = 0x11b927) (movR64R64Effect 0x11b927 3 2) (Reg.operands [.gpr 2] [])) #v[86]
    (b_l11b8f0_1)))))))))))))))))))))))))))))))))))))))

def bytes_l11b8f0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x68, 0x49, 0x89,
    0xD0, 0x48, 0x8B, 0x0E, 0x4C, 0x8B, 0x0A, 0x4C, 0x8B, 0x62, 0x08, 0x4C, 0x89, 0xC8, 0x4C, 0x89,
    0x4C, 0x24, 0x08, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD2, 0x4C, 0x89, 0xE0, 0x4C, 0x89, 0x64, 0x24,
    0x18, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xD3] ++ bytes_l11b8f0_1

theorem code_l11b8f0 : ∀ x ∈ codeRange 0x11b8f0 bytes_l11b8f0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b8f0 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b8f0_1

@[cfg_block] def b_l11badf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11badf (movR32R32Effect 0x11badf 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 54) (.exec 0x11badf (fun s => s.RIP = 0x11badf) (movR32R32Effect 0x11badf 3 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x11bae2 (callEffect (fun _ => 0x127d50) 0x11bae7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x11bae2 (PushPre 0x11bae2 5) (callEffect (fun _ => 0x127d50) 0x11bae7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x11bae7⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l11bae7, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l11badf : List UInt8 :=
  [0x44, 0x89, 0xFF, 0xE8, 0x69, 0xC2, 0x00, 0x00]

theorem code_l11badf : ∀ x ∈ codeRange 0x11badf bytes_l11badf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1badf 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11bae7_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.exec 0x11bb30 (StorePre 0x11bb30 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x11bb30 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11bb30 2 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[83, 14]
    (.letOp (n := 89) (.out 0x11bb34 (addR64Imm8Effect 0x11bb34 4 0x68) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 90) (.exec 0x11bb34 (fun s => s.RIP = 0x11bb34) (addR64Imm8Effect 0x11bb34 4 0x68) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.out 0x11bb38 (popR64Effect 0x11bb38 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[89]
    (.letOp (n := 92) (.out 0x11bb38 (popR64Effect 0x11bb38 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[89]
    (.letOp (n := 93) (.exec 0x11bb38 (PopPre 0x11bb38) (popR64Effect 0x11bb38 1 3) (Reg.operands [.gpr 4] [])) #v[89]
    (.letOp (n := 94) (.out 0x11bb39 (popR64Effect 0x11bb39 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[92]
    (.letOp (n := 95) (.out 0x11bb39 (popR64Effect 0x11bb39 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[92]
    (.letOp (n := 96) (.exec 0x11bb39 (PopPre 0x11bb39) (popR64Effect 0x11bb39 2 12) (Reg.operands [.gpr 4] [])) #v[92]
    (.letOp (n := 97) (.out 0x11bb3b (popR64Effect 0x11bb3b 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[95]
    (.letOp (n := 98) (.out 0x11bb3b (popR64Effect 0x11bb3b 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[95]
    (.letOp (n := 99) (.exec 0x11bb3b (PopPre 0x11bb3b) (popR64Effect 0x11bb3b 2 13) (Reg.operands [.gpr 4] [])) #v[95]
    (.letOp (n := 100) (.out 0x11bb3d (popR64Effect 0x11bb3d 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[98]
    (.letOp (n := 101) (.out 0x11bb3d (popR64Effect 0x11bb3d 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[98]
    (.letOp (n := 102) (.exec 0x11bb3d (PopPre 0x11bb3d) (popR64Effect 0x11bb3d 2 14) (Reg.operands [.gpr 4] [])) #v[98]
    (.letOp (n := 103) (.out 0x11bb3f (popR64Effect 0x11bb3f 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[101]
    (.letOp (n := 104) (.out 0x11bb3f (popR64Effect 0x11bb3f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[101]
    (.letOp (n := 105) (.exec 0x11bb3f (PopPre 0x11bb3f) (popR64Effect 0x11bb3f 2 15) (Reg.operands [.gpr 4] [])) #v[101]
    (.letOp (n := 106) (.out 0x11bb41 (popR64Effect 0x11bb41 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[104]
    (.letOp (n := 107) (.out 0x11bb41 (popR64Effect 0x11bb41 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[104]
    (.letOp (n := 108) (.exec 0x11bb41 (PopPre 0x11bb41) (popR64Effect 0x11bb41 1 5) (Reg.operands [.gpr 4] [])) #v[104]
    (.letOp (n := 109) (.out 0x11bb42 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[107]
    (.letOp (n := 110) (.out 0x11bb42 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[107]
    (.letOp (n := 111) (.exec 0x11bb42 (RetPre 0x11bb42) (retEffect) (Reg.operands [.gpr 4] [])) #v[107]
    (.terminate (.ret (RegMap.args [(0, 55), (1, 79), (2, 83), (3, 91), (4, 110), (5, 106), (6, 77), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 94), (13, 97), (14, 100), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)] 112) (some ⟨109, by decide⟩))))))))))))))))))))))))))

def bytes_l11bae7_1 : List UInt8 :=
  [0x49, 0x89, 0x56, 0x18, 0x48, 0x83, 0xC4, 0x68, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41,
    0x5F, 0x5D, 0xC3]

theorem code_l11bae7_1 : ∀ x ∈ codeRange 0x11bb30 bytes_l11bae7_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1bb30 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11bae7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11bae7 (StorePre 0x11bae7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x11bae7 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11bae7 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.exec 0x11baeb (fun s => s.RIP = 0x11baeb) (leaR64Effect 0x11baeb 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11baf0 (movzxR32M8Effect 0x11baf0 5 0 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x11baf0 (LoadPre 0x11baf0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x11baf0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11baf0 5 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11baf5 (movR64M64Effect 0x11baf5 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x11baf5 (LoadPre 0x11baf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11baf5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11baf5 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x11bafa (movR64M64Effect 0x11bafa 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x11bafa (LoadPre 0x11bafa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11bafa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11bafa 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x11baff (testR8R8Effect 0x11baff 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 62) (.exec 0x11baff (fun s => s.RIP = 0x11baff) (testR8R8Effect 0x11baff 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 63) (.out 0x11bb01 (atFlags (condHolds 5) (cmovR64R64Effect 0x11bb01 4 3 1)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 3))) #v[3, 57, 61]
    (.letOp (n := 64) (.exec 0x11bb01 (fun s => s.RIP = 0x11bb01) (atFlags (condHolds 5) (cmovR64R64Effect 0x11bb01 4 3 1)) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[3, 57, 61]
    (.letOp (n := 65) (.out 0x11bb05 (testR8R8Effect 0x11bb05 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 66) (.exec 0x11bb05 (fun s => s.RIP = 0x11bb05) (testR8R8Effect 0x11bb05 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 67) (.out 0x11bb07 (atFlags (condHolds 5) (cmovR64R64Effect 0x11bb07 4 12 2)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 12))) #v[12, 59, 65]
    (.letOp (n := 68) (.exec 0x11bb07 (fun s => s.RIP = 0x11bb07) (atFlags (condHolds 5) (cmovR64R64Effect 0x11bb07 4 12 2)) (Reg.operands [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[12, 59, 65]
    (.letOp (n := 69) (.out 0x11bb0b (movR64M64Effect 0x11bb0b 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 70) (.exec 0x11bb0b (LoadPre 0x11bb0b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11bb0b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11bb0b 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x11bb10 (xorR32R32Effect 0x11bb10 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[59, 59]
    (.letOp (n := 72) (.exec 0x11bb10 (fun s => s.RIP = 0x11bb10) (xorR32R32Effect 0x11bb10 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[59, 59]
    (.letOp (n := 73) (.out 0x11bb12 (xorR32R32Effect 0x11bb12 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 74) (.exec 0x11bb12 (fun s => s.RIP = 0x11bb12) (xorR32R32Effect 0x11bb12 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 75) (.out 0x11bb14 (testR8R8Effect 0x11bb14 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 76) (.exec 0x11bb14 (fun s => s.RIP = 0x11bb14) (testR8R8Effect 0x11bb14 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 77) (.out 0x11bb16 (atFlags (condHolds 5) (cmovR64R64Effect 0x11bb16 4 6 1)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[73, 69, 75]
    (.letOp (n := 78) (.exec 0x11bb16 (fun s => s.RIP = 0x11bb16) (atFlags (condHolds 5) (cmovR64R64Effect 0x11bb16 4 6 1)) (Reg.operands [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[73, 69, 75]
    (.letOp (n := 79) (.out 0x11bb1a (movR64M64Effect 0x11bb1a 1 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 80) (.exec 0x11bb1a (LoadPre 0x11bb1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11bb1a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11bb1a 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x11bb1f (testR8R8Effect 0x11bb1f 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 82) (.exec 0x11bb1f (fun s => s.RIP = 0x11bb1f) (testR8R8Effect 0x11bb1f 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 83) (.out 0x11bb21 (atFlags (condHolds 5) (cmovR64R64Effect 0x11bb21 4 2 1)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[71, 79, 81]
    (.letOp (n := 84) (.exec 0x11bb21 (fun s => s.RIP = 0x11bb21) (atFlags (condHolds 5) (cmovR64R64Effect 0x11bb21 4 2 1)) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[71, 79, 81]
    (.letOp (n := 85) (.exec 0x11bb25 (StorePre 0x11bb25 3 (fun s => AddrMode.addr (.base 14 .none) s (0x11bb25 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11bb25 3 (.base 14 .none)) (Reg.operands [.gpr 3, .gpr 14] [])) #v[63, 14]
    (.letOp (n := 86) (.exec 0x11bb28 (StorePre 0x11bb28 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x11bb28 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11bb28 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 14] [])) #v[67, 14]
    (.letOp (n := 87) (.exec 0x11bb2c (StorePre 0x11bb2c 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x11bb2c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11bb2c 6 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 14] [])) #v[77, 14]
    (b_l11bae7_1)))))))))))))))))))))))))))))))))))

def bytes_l11bae7 : List UInt8 :=
  [0x88, 0x44, 0x24, 0x07, 0x48, 0x8D, 0x44, 0x24, 0x07, 0x0F, 0xB6, 0x44, 0x24, 0x07, 0x48, 0x8B,
    0x4C, 0x24, 0x48, 0x48, 0x8B, 0x54, 0x24, 0x50, 0x84, 0xC0, 0x48, 0x0F, 0x45, 0xD9, 0x84, 0xC0,
    0x4C, 0x0F, 0x45, 0xE2, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0x31, 0xD2, 0x31, 0xF6, 0x84, 0xC0, 0x48,
    0x0F, 0x45, 0xF1, 0x48, 0x8B, 0x4C, 0x24, 0x60, 0x84, 0xC0, 0x48, 0x0F, 0x45, 0xD1, 0x49, 0x89,
    0x1E, 0x4D, 0x89, 0x66, 0x08, 0x49, 0x89, 0x76, 0x10] ++ bytes_l11bae7_1

theorem code_l11bae7 : ∀ x ∈ codeRange 0x11bae7 bytes_l11bae7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1bae7 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11bae7_1

@[cfg_block] def b_l11c0b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c0b0 (pushR64Effect 0x11c0b0 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 54) (.exec 0x11c0b0 (PushPre 0x11c0b0 1) (pushR64Effect 0x11c0b0 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 55) (.out 0x11c0b1 (movR64R64Effect 0x11c0b1 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 56) (.exec 0x11c0b1 (fun s => s.RIP = 0x11c0b1) (movR64R64Effect 0x11c0b1 0 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x11c0b4 (movR64M64Effect 0x11c0b4 1 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 58) (.exec 0x11c0b4 (LoadPre 0x11c0b4 (fun s => AddrMode.addr (.base 7 .none) s (0x11c0b4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c0b4 1 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.out 0x11c0b7 (cmpMImm8Effect 0x11c0b7 5 64 (.base 7 (.d8 0x10)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[7]
    (.letOp (n := 60) (.exec 0x11c0b7 (LoadPre 0x11c0b7 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x11c0b7 + BitVec.ofNat 64 5)) 8) (cmpMImm8Effect 0x11c0b7 5 64 (.base 7 (.d8 0x10)) 0x0) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 61) (.pure (condOp 4)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l11c1ba, RegMap.args [(0, 55), (1, 57), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l11c0c2, RegMap.args [(0, 55), (1, 57), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l11c0b0 : List UInt8 :=
  [0x53, 0x48, 0x89, 0xF0, 0x48, 0x8B, 0x0F, 0x48, 0x83, 0x7F, 0x10, 0x00, 0x0F, 0x84, 0xF8, 0x00,
    0x00, 0x00]

theorem code_l11c0b0 : ∀ x ∈ codeRange 0x11c0b0 bytes_l11c0b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c0b0 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c0c2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c0c2 (movR64M64Effect 0x11c0c2 10 (.base 7 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[7]
    (.letOp (n := 54) (.exec 0x11c0c2 (LoadPre 0x11c0c2 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x11c0c2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c0c2 10 (.base 7 (.d8 0x30))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x11c0c6 (movR64M64Effect 0x11c0c6 11 (.base 7 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[7]
    (.letOp (n := 56) (.exec 0x11c0c6 (LoadPre 0x11c0c6 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x11c0c6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c0c6 11 (.base 7 (.d8 0x38))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x11c0ca (movR64R64Effect 0x11c0ca 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 11] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 58) (.exec 0x11c0ca (fun s => s.RIP = 0x11c0ca) (movR64R64Effect 0x11c0ca 9 11) (Reg.operands [.gpr 11] [])) #v[55]
    (.letOp (n := 59) (.out 0x11c0cd (subR64R64Effect 0x11c0cd 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[57, 53]
    (.letOp (n := 60) (.out 0x11c0cd (subR64R64Effect 0x11c0cd 9 10) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 10] []) (.flag .ZF)) #v[57, 53]
    (.letOp (n := 61) (.exec 0x11c0cd (fun s => s.RIP = 0x11c0cd) (subR64R64Effect 0x11c0cd 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[57, 53]
    (.letOp (n := 62) (.pure (condOp 4)) #v[60]
    (.terminate (.condBr (Fin.last 62) ⟨.l11c1ba, RegMap.args [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 59), (10, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ ⟨.l11c0d6, RegMap.args [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 59), (10, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l11c0c2 : List UInt8 :=
  [0x4C, 0x8B, 0x57, 0x30, 0x4C, 0x8B, 0x5F, 0x38, 0x4D, 0x89, 0xD9, 0x4D, 0x29, 0xD1, 0x0F, 0x84,
    0xE4, 0x00, 0x00, 0x00]

theorem code_l11c0c2 : ∀ x ∈ codeRange 0x11c0c2 bytes_l11c0c2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c0c2 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c0d6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c0d6 (movR64M64Effect 0x11c0d6 2 (.base 7 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 54) (.exec 0x11c0d6 (LoadPre 0x11c0d6 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x11c0d6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c0d6 2 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x11c0da (imulR64R64Imm32Effect 0x11c0da 7 6 10 0x110) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[10]
    (.letOp (n := 56) (.exec 0x11c0da (fun s => s.RIP = 0x11c0da) (imulR64R64Imm32Effect 0x11c0da 7 6 10 0x110) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 57) (.out 0x11c0e1 (movR32R32Effect 0x11c0e1 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[9]
    (.letOp (n := 58) (.exec 0x11c0e1 (fun s => s.RIP = 0x11c0e1) (movR32R32Effect 0x11c0e1 3 8 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 59) (.out 0x11c0e4 (andR32Imm8Effect 0x11c0e4 4 8 0x3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 60) (.exec 0x11c0e4 (fun s => s.RIP = 0x11c0e4) (andR32Imm8Effect 0x11c0e4 4 8 0x3) (Reg.operands [.gpr 8] [])) #v[57]
    (.letOp (n := 61) (.out 0x11c0e8 (subR64R64Effect 0x11c0e8 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[10, 11]
    (.letOp (n := 62) (.exec 0x11c0e8 (fun s => s.RIP = 0x11c0e8) (subR64R64Effect 0x11c0e8 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[10, 11]
    (.letOp (n := 63) (.out 0x11c0eb (cmpR64Imm8Effect 0x11c0eb 10 0xfc) (EffectPart.reads (.flag .CF) [.gpr 10] []) (.flag .CF)) #v[61]
    (.letOp (n := 64) (.out 0x11c0eb (cmpR64Imm8Effect 0x11c0eb 10 0xfc) (EffectPart.reads (.flag .ZF) [.gpr 10] []) (.flag .ZF)) #v[61]
    (.letOp (n := 65) (.exec 0x11c0eb (fun s => s.RIP = 0x11c0eb) (cmpR64Imm8Effect 0x11c0eb 10 0xfc) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 66) (.pure (condOp 6)) #v[63, 64]
    (.terminate (.condBr (Fin.last 66) ⟨.l11c0f9, RegMap.args [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 55), (7, 7), (8, 59), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l11c0f1, RegMap.args [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 55), (7, 7), (8, 59), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l11c0d6 : List UInt8 :=
  [0x48, 0x8B, 0x57, 0x20, 0x49, 0x69, 0xF2, 0x10, 0x01, 0x00, 0x00, 0x45, 0x89, 0xC8, 0x41, 0x83,
    0xE0, 0x03, 0x4D, 0x29, 0xDA, 0x49, 0x83, 0xFA, 0xFC, 0x76, 0x08]

theorem code_l11c0d6 : ∀ x ∈ codeRange 0x11c0d6 bytes_l11c0d6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c0d6 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c0f1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c0f1 (xorR32R32Effect 0x11c0f1 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[10, 10]
    (.letOp (n := 54) (.exec 0x11c0f1 (fun s => s.RIP = 0x11c0f1) (xorR32R32Effect 0x11c0f1 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.terminate (.br ⟨.l11c187, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l11c0f1 : List UInt8 :=
  [0x45, 0x31, 0xD2, 0xE9, 0x8E, 0x00, 0x00, 0x00]

theorem code_l11c0f1 : ∀ x ∈ codeRange 0x11c0f1 bytes_l11c0f1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c0f1 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c0f9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c0f9 (leaR64Effect 0x11c0f9 11 (.sib 2 (some 6) 0 .none)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2, .gpr 6] []) (.reg (.gpr 11))) #v[2, 6]
    (.letOp (n := 54) (.exec 0x11c0f9 (fun s => s.RIP = 0x11c0f9) (leaR64Effect 0x11c0f9 11 (.sib 2 (some 6) 0 .none)) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 6]
    (.letOp (n := 55) (.out 0x11c0fd (andR64Imm8Effect 0x11c0fd 9 0xfc) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 56) (.exec 0x11c0fd (fun s => s.RIP = 0x11c0fd) (andR64Imm8Effect 0x11c0fd 9 0xfc) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 57) (.out 0x11c101 (xorR32R32Effect 0x11c101 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[10, 10]
    (.letOp (n := 58) (.exec 0x11c101 (fun s => s.RIP = 0x11c101) (xorR32R32Effect 0x11c101 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.terminate (.br ⟨.l11c120, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 57), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c0f9 : List UInt8 :=
  [0x4C, 0x8D, 0x1C, 0x32, 0x49, 0x83, 0xE1, 0xFC, 0x45, 0x31, 0xD2, 0xEB, 0x1A]

theorem code_l11c0f9 : ∀ x ∈ codeRange 0x11c0f9 bytes_l11c0f9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c0f9 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c110 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c110 (addR64Imm8Effect 0x11c110 10 0x4) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[10]
    (.letOp (n := 54) (.exec 0x11c110 (fun s => s.RIP = 0x11c110) (addR64Imm8Effect 0x11c110 10 0x4) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x11c114 (addR64Imm32Effect 0x11c114 11 0x440) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[11]
    (.letOp (n := 56) (.exec 0x11c114 (fun s => s.RIP = 0x11c114) (addR64Imm32Effect 0x11c114 11 0x440) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 57) (.out 0x11c11b (cmpR64R64Effect 0x11c11b 9 10) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 10] []) (.flag .ZF)) #v[9, 53]
    (.letOp (n := 58) (.exec 0x11c11b (fun s => s.RIP = 0x11c11b) (cmpR64R64Effect 0x11c11b 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[9, 53]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l11c182, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l11c120, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l11c110 : List UInt8 :=
  [0x49, 0x83, 0xC2, 0x04, 0x49, 0x81, 0xC3, 0x40, 0x04, 0x00, 0x00, 0x4D, 0x39, 0xD1, 0x74, 0x62]

theorem code_l11c110 : ∀ x ∈ codeRange 0x11c110 bytes_l11c110, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c110 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c120 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c120 (movR64M64Effect 0x11c120 3 (.base 11 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[11]
    (.letOp (n := 54) (.exec 0x11c120 (LoadPre 0x11c120 (fun s => AddrMode.addr (.base 11 .none) s (0x11c120 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c120 3 (.base 11 .none)) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 55) (.out 0x11c123 (cmpR64R64Effect 0x11c123 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[0, 53]
    (.letOp (n := 56) (.out 0x11c123 (cmpR64R64Effect 0x11c123 0 3) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 3] []) (.flag .ZF)) #v[0, 53]
    (.letOp (n := 57) (.exec 0x11c123 (fun s => s.RIP = 0x11c123) (cmpR64R64Effect 0x11c123 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 53]
    (.letOp (n := 58) (.pure (condOp 6)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l11c150, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l11c128, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c120 : List UInt8 :=
  [0x49, 0x8B, 0x1B, 0x48, 0x39, 0xD8, 0x76, 0x28]

theorem code_l11c120 : ∀ x ∈ codeRange 0x11c120 bytes_l11c120, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c120 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c128 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c128 (movR64M64Effect 0x11c128 3 (.base 11 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[11]
    (.letOp (n := 54) (.exec 0x11c128 (LoadPre 0x11c128 (fun s => AddrMode.addr (.base 11 (.d32 0x110)) s (0x11c128 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c128 3 (.base 11 (.d32 0x110))) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 55) (.out 0x11c12f (cmpR64R64Effect 0x11c12f 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[0, 53]
    (.letOp (n := 56) (.out 0x11c12f (cmpR64R64Effect 0x11c12f 0 3) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 3] []) (.flag .ZF)) #v[0, 53]
    (.letOp (n := 57) (.exec 0x11c12f (fun s => s.RIP = 0x11c12f) (cmpR64R64Effect 0x11c12f 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 53]
    (.letOp (n := 58) (.pure (condOp 6)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l11c15f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l11c134, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c128 : List UInt8 :=
  [0x49, 0x8B, 0x9B, 0x10, 0x01, 0x00, 0x00, 0x48, 0x39, 0xD8, 0x76, 0x2B]

theorem code_l11c128 : ∀ x ∈ codeRange 0x11c128 bytes_l11c128, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c128 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c134 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c134 (movR64M64Effect 0x11c134 3 (.base 11 (.d32 0x220))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[11]
    (.letOp (n := 54) (.exec 0x11c134 (LoadPre 0x11c134 (fun s => AddrMode.addr (.base 11 (.d32 0x220)) s (0x11c134 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c134 3 (.base 11 (.d32 0x220))) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 55) (.out 0x11c13b (cmpR64R64Effect 0x11c13b 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[0, 53]
    (.letOp (n := 56) (.out 0x11c13b (cmpR64R64Effect 0x11c13b 0 3) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 3] []) (.flag .ZF)) #v[0, 53]
    (.letOp (n := 57) (.exec 0x11c13b (fun s => s.RIP = 0x11c13b) (cmpR64R64Effect 0x11c13b 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 53]
    (.letOp (n := 58) (.pure (condOp 6)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l11c16e, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l11c140, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c134 : List UInt8 :=
  [0x49, 0x8B, 0x9B, 0x20, 0x02, 0x00, 0x00, 0x48, 0x39, 0xD8, 0x76, 0x2E]

theorem code_l11c134 : ∀ x ∈ codeRange 0x11c134 bytes_l11c134, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c134 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c140 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c140 (movR64M64Effect 0x11c140 3 (.base 11 (.d32 0x330))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[11]
    (.letOp (n := 54) (.exec 0x11c140 (LoadPre 0x11c140 (fun s => AddrMode.addr (.base 11 (.d32 0x330)) s (0x11c140 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c140 3 (.base 11 (.d32 0x330))) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 55) (.out 0x11c147 (cmpR64R64Effect 0x11c147 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[0, 53]
    (.letOp (n := 56) (.out 0x11c147 (cmpR64R64Effect 0x11c147 0 3) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 3] []) (.flag .ZF)) #v[0, 53]
    (.letOp (n := 57) (.exec 0x11c147 (fun s => s.RIP = 0x11c147) (cmpR64R64Effect 0x11c147 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 53]
    (.letOp (n := 58) (.pure (condOp 7)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l11c110, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l11c14c, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c140 : List UInt8 :=
  [0x49, 0x8B, 0x9B, 0x30, 0x03, 0x00, 0x00, 0x48, 0x39, 0xD8, 0x77, 0xC4]

theorem code_l11c140 : ∀ x ∈ codeRange 0x11c140 bytes_l11c140, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c140 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c14c : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l11c17d, RegMap.args (entryMap (live .l11c14c)) 53⟩)

def bytes_l11c14c : List UInt8 :=
  [0xEB, 0x2F]

theorem code_l11c14c : ∀ x ∈ codeRange 0x11c14c bytes_l11c14c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c14c 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c150 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c150 (movR64R64Effect 0x11c150 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x11c150 (fun s => s.RIP = 0x11c150) (movR64R64Effect 0x11c150 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x11c153 (movR64M64Effect 0x11c153 3 (.base 11 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[11]
    (.letOp (n := 56) (.exec 0x11c153 (LoadPre 0x11c153 (fun s => AddrMode.addr (.base 11 (.d32 0x110)) s (0x11c153 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c153 3 (.base 11 (.d32 0x110))) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 57) (.out 0x11c15a (cmpR64R64Effect 0x11c15a 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.out 0x11c15a (cmpR64R64Effect 0x11c15a 0 3) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 3] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 59) (.exec 0x11c15a (fun s => s.RIP = 0x11c15a) (cmpR64R64Effect 0x11c15a 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 55]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l11c134, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l11c15f, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l11c150 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x49, 0x8B, 0x9B, 0x10, 0x01, 0x00, 0x00, 0x48, 0x39, 0xD8, 0x77, 0xD5]

theorem code_l11c150 : ∀ x ∈ codeRange 0x11c150 bytes_l11c150, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c150 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c15f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c15f (movR64R64Effect 0x11c15f 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x11c15f (fun s => s.RIP = 0x11c15f) (movR64R64Effect 0x11c15f 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x11c162 (movR64M64Effect 0x11c162 3 (.base 11 (.d32 0x220))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[11]
    (.letOp (n := 56) (.exec 0x11c162 (LoadPre 0x11c162 (fun s => AddrMode.addr (.base 11 (.d32 0x220)) s (0x11c162 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c162 3 (.base 11 (.d32 0x220))) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 57) (.out 0x11c169 (cmpR64R64Effect 0x11c169 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.out 0x11c169 (cmpR64R64Effect 0x11c169 0 3) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 3] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 59) (.exec 0x11c169 (fun s => s.RIP = 0x11c169) (cmpR64R64Effect 0x11c169 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 55]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l11c140, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l11c16e, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l11c15f : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x49, 0x8B, 0x9B, 0x20, 0x02, 0x00, 0x00, 0x48, 0x39, 0xD8, 0x77, 0xD2]

theorem code_l11c15f : ∀ x ∈ codeRange 0x11c15f bytes_l11c15f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c15f 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c16e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c16e (movR64R64Effect 0x11c16e 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x11c16e (fun s => s.RIP = 0x11c16e) (movR64R64Effect 0x11c16e 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x11c171 (movR64M64Effect 0x11c171 3 (.base 11 (.d32 0x330))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[11]
    (.letOp (n := 56) (.exec 0x11c171 (LoadPre 0x11c171 (fun s => AddrMode.addr (.base 11 (.d32 0x330)) s (0x11c171 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c171 3 (.base 11 (.d32 0x330))) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 57) (.out 0x11c178 (cmpR64R64Effect 0x11c178 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.out 0x11c178 (cmpR64R64Effect 0x11c178 0 3) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 3] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 59) (.exec 0x11c178 (fun s => s.RIP = 0x11c178) (cmpR64R64Effect 0x11c178 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 55]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l11c110, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l11c17d, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l11c16e : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x49, 0x8B, 0x9B, 0x30, 0x03, 0x00, 0x00, 0x48, 0x39, 0xD8, 0x77, 0x93]

theorem code_l11c16e : ∀ x ∈ codeRange 0x11c16e bytes_l11c16e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c16e 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c17d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c17d (movR64R64Effect 0x11c17d 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x11c17d (fun s => s.RIP = 0x11c17d) (movR64R64Effect 0x11c17d 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l11c110, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l11c17d : List UInt8 :=
  [0x48, 0x89, 0xD8, 0xEB, 0x8E]

theorem code_l11c17d : ∀ x ∈ codeRange 0x11c17d bytes_l11c17d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c17d 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c182 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c182 (testR64R64Effect 0x11c182 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[8, 8]
    (.letOp (n := 54) (.exec 0x11c182 (fun s => s.RIP = 0x11c182) (testR64R64Effect 0x11c182 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11c1ba, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11c187, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11c182 : List UInt8 :=
  [0x4D, 0x85, 0xC0, 0x74, 0x33]

theorem code_l11c182 : ∀ x ∈ codeRange 0x11c182 bytes_l11c182, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c182 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c187 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c187 (imulR64R64Imm32Effect 0x11c187 7 9 10 0x110) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[10]
    (.letOp (n := 54) (.exec 0x11c187 (fun s => s.RIP = 0x11c187) (imulR64R64Imm32Effect 0x11c187 7 9 10 0x110) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x11c18e (addR64R64Effect 0x11c18e 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[2, 53]
    (.letOp (n := 56) (.exec 0x11c18e (fun s => s.RIP = 0x11c18e) (addR64R64Effect 0x11c18e 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[2, 53]
    (.letOp (n := 57) (.out 0x11c191 (addR64R64Effect 0x11c191 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[55, 6]
    (.letOp (n := 58) (.exec 0x11c191 (fun s => s.RIP = 0x11c191) (addR64R64Effect 0x11c191 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[55, 6]
    (.letOp (n := 59) (.out 0x11c194 (imulR64R64Imm32Effect 0x11c194 7 6 8 0x110) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[8]
    (.letOp (n := 60) (.exec 0x11c194 (fun s => s.RIP = 0x11c194) (imulR64R64Imm32Effect 0x11c194 7 6 8 0x110) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 61) (.out 0x11c19b (xorR32R32Effect 0x11c19b 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 62) (.exec 0x11c19b (fun s => s.RIP = 0x11c19b) (xorR32R32Effect 0x11c19b 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 63) (.exec 0x11c19e (fun s => s.RIP = 0x11c19e) (fun _ => nopEffect 0x11c19e 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l11c1a0, RegMap.args [(0, 0), (1, 1), (2, 57), (4, 4), (5, 5), (6, 59), (7, 7), (8, 61), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l11c187 : List UInt8 :=
  [0x4D, 0x69, 0xCA, 0x10, 0x01, 0x00, 0x00, 0x4C, 0x01, 0xCA, 0x48, 0x01, 0xF2, 0x49, 0x69, 0xF0,
    0x10, 0x01, 0x00, 0x00, 0x45, 0x31, 0xC0, 0x66, 0x90]

theorem code_l11c187 : ∀ x ∈ codeRange 0x11c187 bytes_l11c187, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c187 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c1a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c1a0 (movR64R64Effect 0x11c1a0 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[0]
    (.letOp (n := 54) (.exec 0x11c1a0 (fun s => s.RIP = 0x11c1a0) (movR64R64Effect 0x11c1a0 9 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x11c1a3 (movR64M64Effect 0x11c1a3 0 (.sib 2 (some 8) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 8] []) (.reg (.gpr 0))) #v[2, 8]
    (.letOp (n := 56) (.exec 0x11c1a3 (LoadPre 0x11c1a3 (fun s => AddrMode.addr (.sib 2 (some 8) 0 .none) s (0x11c1a3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c1a3 0 (.sib 2 (some 8) 0 .none)) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 8]
    (.letOp (n := 57) (.out 0x11c1a7 (cmpR64R64Effect 0x11c1a7 9 0) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 0] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.out 0x11c1a7 (cmpR64R64Effect 0x11c1a7 9 0) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 0] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 59) (.exec 0x11c1a7 (fun s => s.RIP = 0x11c1a7) (cmpR64R64Effect 0x11c1a7 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[53, 55]
    (.letOp (n := 60) (.out 0x11c1aa (atFlags (condHolds 7) (cmovR64R64Effect 0x11c1aa 4 0 9)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[55, 53, 57, 58]
    (.letOp (n := 61) (.exec 0x11c1aa (fun s => s.RIP = 0x11c1aa) (atFlags (condHolds 7) (cmovR64R64Effect 0x11c1aa 4 0 9)) (Reg.operands [.gpr 0, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[55, 53, 57, 58]
    (.letOp (n := 62) (.out 0x11c1ae (addR64Imm32Effect 0x11c1ae 8 0x110) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 63) (.exec 0x11c1ae (fun s => s.RIP = 0x11c1ae) (addR64Imm32Effect 0x11c1ae 8 0x110) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 64) (.out 0x11c1b5 (cmpR64R64Effect 0x11c1b5 6 8) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 8] []) (.flag .ZF)) #v[6, 62]
    (.letOp (n := 65) (.exec 0x11c1b5 (fun s => s.RIP = 0x11c1b5) (cmpR64R64Effect 0x11c1b5 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[6, 62]
    (.letOp (n := 66) (.pure (condOp 5)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l11c1a0, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 62), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l11c1ba, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 62), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l11c1a0 : List UInt8 :=
  [0x49, 0x89, 0xC1, 0x4A, 0x8B, 0x04, 0x02, 0x49, 0x39, 0xC1, 0x49, 0x0F, 0x47, 0xC1, 0x49, 0x81,
    0xC0, 0x10, 0x01, 0x00, 0x00, 0x4C, 0x39, 0xC6, 0x75, 0xE6]

theorem code_l11c1a0 : ∀ x ∈ codeRange 0x11c1a0 bytes_l11c1a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c1a0 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c1ba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c1ba (movR64M64Effect 0x11c1ba 2 (.base 7 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 54) (.exec 0x11c1ba (LoadPre 0x11c1ba (fun s => AddrMode.addr (.base 7 (.d8 0x40)) s (0x11c1ba + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c1ba 2 (.base 7 (.d8 0x40))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x11c1be (testR64R64Effect 0x11c1be 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 56) (.exec 0x11c1be (fun s => s.RIP = 0x11c1be) (testR64R64Effect 0x11c1be 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l11c2bc, RegMap.args [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l11c1c7, RegMap.args [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l11c1ba : List UInt8 :=
  [0x48, 0x8B, 0x57, 0x40, 0x48, 0x85, 0xC9, 0x0F, 0x84, 0xF5, 0x00, 0x00, 0x00]

theorem code_l11c1ba : ∀ x ∈ codeRange 0x11c1ba bytes_l11c1ba, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c1ba 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c1c7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c1c7 (movR64M64Effect 0x11c1c7 6 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 54) (.exec 0x11c1c7 (LoadPre 0x11c1c7 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x11c1c7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c1c7 6 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x11c1cb (cmpR64R64Effect 0x11c1cb 1 6) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 6] []) (.flag .ZF)) #v[1, 53]
    (.letOp (n := 56) (.exec 0x11c1cb (fun s => s.RIP = 0x11c1cb) (cmpR64R64Effect 0x11c1cb 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 53]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l11c2bc, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l11c1d4, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l11c1c7 : List UInt8 :=
  [0x48, 0x8B, 0x77, 0x08, 0x48, 0x39, 0xF1, 0x0F, 0x84, 0xE8, 0x00, 0x00, 0x00]

theorem code_l11c1c7 : ∀ x ∈ codeRange 0x11c1c7 bytes_l11c1c7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c1c7 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c1d4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c1d4 (subR64R64Effect 0x11c1d4 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[6, 1]
    (.letOp (n := 54) (.exec 0x11c1d4 (fun s => s.RIP = 0x11c1d4) (subR64R64Effect 0x11c1d4 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[6, 1]
    (.letOp (n := 55) (.out 0x11c1d7 (cmpR64Imm32Effect 0x11c1d7 6 0x9a0) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x11c1d7 (fun s => s.RIP = 0x11c1d7) (cmpR64Imm32Effect 0x11c1d7 6 0x9a0) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l11c1e7, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l11c1e0, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l11c1d4 : List UInt8 :=
  [0x48, 0x29, 0xCE, 0x48, 0x81, 0xFE, 0xA0, 0x09, 0x00, 0x00, 0x75, 0x07]

theorem code_l11c1d4 : ∀ x ∈ codeRange 0x11c1d4 bytes_l11c1d4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c1d4 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c1e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c1e0 (xorR32R32Effect 0x11c1e0 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 54) (.exec 0x11c1e0 (fun s => s.RIP = 0x11c1e0) (xorR32R32Effect 0x11c1e0 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.terminate (.br ⟨.l11c294, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l11c1e0 : List UInt8 :=
  [0x31, 0xF6, 0xE9, 0xAD, 0x00, 0x00, 0x00]

theorem code_l11c1e0 : ∀ x ∈ codeRange 0x11c1e0 bytes_l11c1e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c1e0 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c1e7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c1e7 (shrR64Effect 0x11c1e7 4 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 54) (.exec 0x11c1e7 (fun s => s.RIP = 0x11c1e7) (shrR64Effect 0x11c1e7 4 6 5) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6]
    (.letOp (n := 55) (.out 0x11c1eb (movR64Imm64Effect 0x11c1eb 8 0x4fcace213f2b3885) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 56) (.exec 0x11c1eb (fun s => s.RIP = 0x11c1eb) (movR64Imm64Effect 0x11c1eb 8 0x4fcace213f2b3885) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x11c1f5 (imulR64R64Effect 0x11c1f5 4 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x11c1f5 (fun s => s.RIP = 0x11c1f5) (imulR64R64Effect 0x11c1f5 4 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x11c1f9 (movR64Imm64Effect 0x11c1f9 9 0x1ffffffffffffe) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 60) (.exec 0x11c1f9 (fun s => s.RIP = 0x11c1f9) (movR64Imm64Effect 0x11c1f9 9 0x1ffffffffffffe) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x11c203 (andR64R64Effect 0x11c203 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x11c203 (fun s => s.RIP = 0x11c203) (andR64R64Effect 0x11c203 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x11c206 (leaR64Effect 0x11c206 10 (.base 1 (.d32 0x1230))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[1]
    (.letOp (n := 64) (.exec 0x11c206 (fun s => s.RIP = 0x11c206) (leaR64Effect 0x11c206 10 (.base 1 (.d32 0x1230))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 65) (.out 0x11c20d (xorR32R32Effect 0x11c20d 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[53, 53]
    (.letOp (n := 66) (.exec 0x11c20d (fun s => s.RIP = 0x11c20d) (xorR32R32Effect 0x11c20d 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[53, 53]
    (.terminate (.br ⟨.l11c230, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 65), (7, 7), (8, 57), (9, 61), (10, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l11c1e7 : List UInt8 :=
  [0x48, 0xC1, 0xEE, 0x05, 0x49, 0xB8, 0x85, 0x38, 0x2B, 0x3F, 0x21, 0xCE, 0xCA, 0x4F, 0x4C, 0x0F,
    0xAF, 0xC6, 0x49, 0xB9, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x1F, 0x00, 0x4D, 0x21, 0xC1, 0x4C,
    0x8D, 0x91, 0x30, 0x12, 0x00, 0x00, 0x31, 0xF6, 0xEB, 0x1F]

theorem code_l11c1e7 : ∀ x ∈ codeRange 0x11c1e7 bytes_l11c1e7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c1e7 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c220 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c220 (addR64Imm8Effect 0x11c220 6 0x2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 54) (.exec 0x11c220 (fun s => s.RIP = 0x11c220) (addR64Imm8Effect 0x11c220 6 0x2) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x11c224 (addR64Imm32Effect 0x11c224 10 0x1340) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[10]
    (.letOp (n := 56) (.exec 0x11c224 (fun s => s.RIP = 0x11c224) (addR64Imm32Effect 0x11c224 10 0x1340) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 57) (.out 0x11c22b (cmpR64R64Effect 0x11c22b 9 6) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 6] []) (.flag .ZF)) #v[9, 53]
    (.letOp (n := 58) (.exec 0x11c22b (fun s => s.RIP = 0x11c22b) (cmpR64R64Effect 0x11c22b 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[9, 53]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l11c28e, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l11c230, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l11c220 : List UInt8 :=
  [0x48, 0x83, 0xC6, 0x02, 0x49, 0x81, 0xC2, 0x40, 0x13, 0x00, 0x00, 0x49, 0x39, 0xF1, 0x74, 0x5E]

theorem code_l11c220 : ∀ x ∈ codeRange 0x11c220 bytes_l11c220, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c220 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c230 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c230 (movR64M64Effect 0x11c230 11 (.base 10 (.d32 0xfffff550))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[10]
    (.letOp (n := 54) (.exec 0x11c230 (LoadPre 0x11c230 (fun s => AddrMode.addr (.base 10 (.d32 0xfffff550)) s (0x11c230 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c230 11 (.base 10 (.d32 0xfffff550))) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x11c237 (cmpR64R64Effect 0x11c237 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[0, 53]
    (.letOp (n := 56) (.out 0x11c237 (cmpR64R64Effect 0x11c237 0 11) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 11] []) (.flag .ZF)) #v[0, 53]
    (.letOp (n := 57) (.exec 0x11c237 (fun s => s.RIP = 0x11c237) (cmpR64R64Effect 0x11c237 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[0, 53]
    (.letOp (n := 58) (.pure (condOp 6)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l11c260, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l11c23c, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c230 : List UInt8 :=
  [0x4D, 0x8B, 0x9A, 0x50, 0xF5, 0xFF, 0xFF, 0x4C, 0x39, 0xD8, 0x76, 0x24]

theorem code_l11c230 : ∀ x ∈ codeRange 0x11c230 bytes_l11c230, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c230 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c23c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c23c (movR64M64Effect 0x11c23c 11 (.base 10 (.d32 0xfffff660))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[10]
    (.letOp (n := 54) (.exec 0x11c23c (LoadPre 0x11c23c (fun s => AddrMode.addr (.base 10 (.d32 0xfffff660)) s (0x11c23c + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c23c 11 (.base 10 (.d32 0xfffff660))) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x11c243 (cmpR64R64Effect 0x11c243 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[0, 53]
    (.letOp (n := 56) (.out 0x11c243 (cmpR64R64Effect 0x11c243 0 11) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 11] []) (.flag .ZF)) #v[0, 53]
    (.letOp (n := 57) (.exec 0x11c243 (fun s => s.RIP = 0x11c243) (cmpR64R64Effect 0x11c243 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[0, 53]
    (.letOp (n := 58) (.pure (condOp 6)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l11c26f, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l11c248, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c23c : List UInt8 :=
  [0x4D, 0x8B, 0x9A, 0x60, 0xF6, 0xFF, 0xFF, 0x4C, 0x39, 0xD8, 0x76, 0x27]

theorem code_l11c23c : ∀ x ∈ codeRange 0x11c23c bytes_l11c23c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c23c 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c248 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c248 (movR64M64Effect 0x11c248 11 (.base 10 (.d32 0xfffffef0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[10]
    (.letOp (n := 54) (.exec 0x11c248 (LoadPre 0x11c248 (fun s => AddrMode.addr (.base 10 (.d32 0xfffffef0)) s (0x11c248 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c248 11 (.base 10 (.d32 0xfffffef0))) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x11c24f (cmpR64R64Effect 0x11c24f 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[0, 53]
    (.letOp (n := 56) (.out 0x11c24f (cmpR64R64Effect 0x11c24f 0 11) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 11] []) (.flag .ZF)) #v[0, 53]
    (.letOp (n := 57) (.exec 0x11c24f (fun s => s.RIP = 0x11c24f) (cmpR64R64Effect 0x11c24f 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[0, 53]
    (.letOp (n := 58) (.pure (condOp 6)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l11c27e, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l11c254, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c248 : List UInt8 :=
  [0x4D, 0x8B, 0x9A, 0xF0, 0xFE, 0xFF, 0xFF, 0x4C, 0x39, 0xD8, 0x76, 0x2A]

theorem code_l11c248 : ∀ x ∈ codeRange 0x11c248 bytes_l11c248, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c248 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c254 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c254 (movR64M64Effect 0x11c254 11 (.base 10 .none)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[10]
    (.letOp (n := 54) (.exec 0x11c254 (LoadPre 0x11c254 (fun s => AddrMode.addr (.base 10 .none) s (0x11c254 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c254 11 (.base 10 .none)) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x11c257 (cmpR64R64Effect 0x11c257 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[0, 53]
    (.letOp (n := 56) (.out 0x11c257 (cmpR64R64Effect 0x11c257 0 11) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 11] []) (.flag .ZF)) #v[0, 53]
    (.letOp (n := 57) (.exec 0x11c257 (fun s => s.RIP = 0x11c257) (cmpR64R64Effect 0x11c257 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[0, 53]
    (.letOp (n := 58) (.pure (condOp 7)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l11c220, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l11c25c, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c254 : List UInt8 :=
  [0x4D, 0x8B, 0x1A, 0x4C, 0x39, 0xD8, 0x77, 0xC4]

theorem code_l11c254 : ∀ x ∈ codeRange 0x11c254 bytes_l11c254, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c254 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c25c : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l11c289, RegMap.args (entryMap (live .l11c25c)) 53⟩)

def bytes_l11c25c : List UInt8 :=
  [0xEB, 0x2B]

theorem code_l11c25c : ∀ x ∈ codeRange 0x11c25c bytes_l11c25c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c25c 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c260 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c260 (movR64R64Effect 0x11c260 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[11]
    (.letOp (n := 54) (.exec 0x11c260 (fun s => s.RIP = 0x11c260) (movR64R64Effect 0x11c260 0 11) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 55) (.out 0x11c263 (movR64M64Effect 0x11c263 11 (.base 10 (.d32 0xfffff660))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[10]
    (.letOp (n := 56) (.exec 0x11c263 (LoadPre 0x11c263 (fun s => AddrMode.addr (.base 10 (.d32 0xfffff660)) s (0x11c263 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c263 11 (.base 10 (.d32 0xfffff660))) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 57) (.out 0x11c26a (cmpR64R64Effect 0x11c26a 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.out 0x11c26a (cmpR64R64Effect 0x11c26a 0 11) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 11] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 59) (.exec 0x11c26a (fun s => s.RIP = 0x11c26a) (cmpR64R64Effect 0x11c26a 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[53, 55]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l11c248, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l11c26f, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l11c260 : List UInt8 :=
  [0x4C, 0x89, 0xD8, 0x4D, 0x8B, 0x9A, 0x60, 0xF6, 0xFF, 0xFF, 0x4C, 0x39, 0xD8, 0x77, 0xD9]

theorem code_l11c260 : ∀ x ∈ codeRange 0x11c260 bytes_l11c260, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c260 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c26f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c26f (movR64R64Effect 0x11c26f 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[11]
    (.letOp (n := 54) (.exec 0x11c26f (fun s => s.RIP = 0x11c26f) (movR64R64Effect 0x11c26f 0 11) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 55) (.out 0x11c272 (movR64M64Effect 0x11c272 11 (.base 10 (.d32 0xfffffef0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[10]
    (.letOp (n := 56) (.exec 0x11c272 (LoadPre 0x11c272 (fun s => AddrMode.addr (.base 10 (.d32 0xfffffef0)) s (0x11c272 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c272 11 (.base 10 (.d32 0xfffffef0))) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 57) (.out 0x11c279 (cmpR64R64Effect 0x11c279 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.out 0x11c279 (cmpR64R64Effect 0x11c279 0 11) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 11] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 59) (.exec 0x11c279 (fun s => s.RIP = 0x11c279) (cmpR64R64Effect 0x11c279 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[53, 55]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l11c254, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l11c27e, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l11c26f : List UInt8 :=
  [0x4C, 0x89, 0xD8, 0x4D, 0x8B, 0x9A, 0xF0, 0xFE, 0xFF, 0xFF, 0x4C, 0x39, 0xD8, 0x77, 0xD6]

theorem code_l11c26f : ∀ x ∈ codeRange 0x11c26f bytes_l11c26f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c26f 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c27e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c27e (movR64R64Effect 0x11c27e 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[11]
    (.letOp (n := 54) (.exec 0x11c27e (fun s => s.RIP = 0x11c27e) (movR64R64Effect 0x11c27e 0 11) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 55) (.out 0x11c281 (movR64M64Effect 0x11c281 11 (.base 10 .none)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[10]
    (.letOp (n := 56) (.exec 0x11c281 (LoadPre 0x11c281 (fun s => AddrMode.addr (.base 10 .none) s (0x11c281 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c281 11 (.base 10 .none)) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 57) (.out 0x11c284 (cmpR64R64Effect 0x11c284 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.out 0x11c284 (cmpR64R64Effect 0x11c284 0 11) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 11] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 59) (.exec 0x11c284 (fun s => s.RIP = 0x11c284) (cmpR64R64Effect 0x11c284 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[53, 55]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l11c220, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l11c289, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l11c27e : List UInt8 :=
  [0x4C, 0x89, 0xD8, 0x4D, 0x8B, 0x1A, 0x4C, 0x39, 0xD8, 0x77, 0x97]

theorem code_l11c27e : ∀ x ∈ codeRange 0x11c27e bytes_l11c27e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c27e 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c289 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c289 (movR64R64Effect 0x11c289 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[11]
    (.letOp (n := 54) (.exec 0x11c289 (fun s => s.RIP = 0x11c289) (movR64R64Effect 0x11c289 0 11) (Reg.operands [.gpr 11] [])) #v[11]
    (.terminate (.br ⟨.l11c220, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l11c289 : List UInt8 :=
  [0x4C, 0x89, 0xD8, 0xEB, 0x92]

theorem code_l11c289 : ∀ x ∈ codeRange 0x11c289 bytes_l11c289, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c289 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c28e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c28e (testR8Imm8Effect 0x11c28e 8 0x1) (EffectPart.reads (.flag .ZF) [.gpr 8] []) (.flag .ZF)) #v[8]
    (.letOp (n := 54) (.exec 0x11c28e (fun s => s.RIP = 0x11c28e) (testR8Imm8Effect 0x11c28e 8 0x1) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11c2bc, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11c294, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11c28e : List UInt8 :=
  [0x41, 0xF6, 0xC0, 0x01, 0x74, 0x28]

theorem code_l11c28e : ∀ x ∈ codeRange 0x11c28e bytes_l11c28e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c28e 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c294 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c294 (imulR64R64Imm32Effect 0x11c294 7 6 6 0x9a0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 54) (.exec 0x11c294 (fun s => s.RIP = 0x11c294) (imulR64R64Imm32Effect 0x11c294 7 6 6 0x9a0) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x11c29b (movR64M64Effect 0x11c29b 8 (.sib 1 (some 6) 0 (.d32 0x780))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1, .gpr 6] []) (.reg (.gpr 8))) #v[1, 53]
    (.letOp (n := 56) (.exec 0x11c29b (LoadPre 0x11c29b (fun s => AddrMode.addr (.sib 1 (some 6) 0 (.d32 0x780)) s (0x11c29b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11c29b 8 (.sib 1 (some 6) 0 (.d32 0x780))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 53]
    (.letOp (n := 57) (.out 0x11c2a3 (movR64M64Effect 0x11c2a3 1 (.sib 1 (some 6) 0 (.d32 0x890))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1, 53]
    (.letOp (n := 58) (.exec 0x11c2a3 (LoadPre 0x11c2a3 (fun s => AddrMode.addr (.sib 1 (some 6) 0 (.d32 0x890)) s (0x11c2a3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11c2a3 1 (.sib 1 (some 6) 0 (.d32 0x890))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 53]
    (.letOp (n := 59) (.out 0x11c2ab (cmpR64R64Effect 0x11c2ab 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[0, 55]
    (.letOp (n := 60) (.out 0x11c2ab (cmpR64R64Effect 0x11c2ab 0 8) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 8] []) (.flag .ZF)) #v[0, 55]
    (.letOp (n := 61) (.exec 0x11c2ab (fun s => s.RIP = 0x11c2ab) (cmpR64R64Effect 0x11c2ab 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[0, 55]
    (.letOp (n := 62) (.out 0x11c2ae (atFlags (condHolds 7) (cmovR64R64Effect 0x11c2ae 4 8 0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 8))) #v[55, 0, 59, 60]
    (.letOp (n := 63) (.exec 0x11c2ae (fun s => s.RIP = 0x11c2ae) (atFlags (condHolds 7) (cmovR64R64Effect 0x11c2ae 4 8 0)) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[55, 0, 59, 60]
    (.letOp (n := 64) (.out 0x11c2b2 (cmpR64R64Effect 0x11c2b2 8 1) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 1] []) (.flag .CF)) #v[62, 57]
    (.letOp (n := 65) (.out 0x11c2b2 (cmpR64R64Effect 0x11c2b2 8 1) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 1] []) (.flag .ZF)) #v[62, 57]
    (.letOp (n := 66) (.exec 0x11c2b2 (fun s => s.RIP = 0x11c2b2) (cmpR64R64Effect 0x11c2b2 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[62, 57]
    (.letOp (n := 67) (.out 0x11c2b5 (atFlags (condHolds 6) (cmovR64R64Effect 0x11c2b5 4 8 1)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 8))) #v[62, 57, 64, 65]
    (.letOp (n := 68) (.exec 0x11c2b5 (fun s => s.RIP = 0x11c2b5) (atFlags (condHolds 6) (cmovR64R64Effect 0x11c2b5 4 8 1)) (Reg.operands [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[62, 57, 64, 65]
    (.letOp (n := 69) (.out 0x11c2b9 (movR64R64Effect 0x11c2b9 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 70) (.exec 0x11c2b9 (fun s => s.RIP = 0x11c2b9) (movR64R64Effect 0x11c2b9 0 8) (Reg.operands [.gpr 8] [])) #v[67]
    (.terminate (.br ⟨.l11c2bc, RegMap.args [(0, 69), (1, 57), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 64), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l11c294 : List UInt8 :=
  [0x48, 0x69, 0xF6, 0xA0, 0x09, 0x00, 0x00, 0x4C, 0x8B, 0x84, 0x31, 0x80, 0x07, 0x00, 0x00, 0x48,
    0x8B, 0x8C, 0x31, 0x90, 0x08, 0x00, 0x00, 0x4C, 0x39, 0xC0, 0x4C, 0x0F, 0x47, 0xC0, 0x49, 0x39,
    0xC8, 0x4C, 0x0F, 0x46, 0xC1, 0x4C, 0x89, 0xC0]

theorem code_l11c294 : ∀ x ∈ codeRange 0x11c294 bytes_l11c294, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c294 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c2bc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c2bc (testR64R64Effect 0x11c2bc 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 54) (.exec 0x11c2bc (fun s => s.RIP = 0x11c2bc) (testR64R64Effect 0x11c2bc 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11c3ba, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11c2c5, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11c2bc : List UInt8 :=
  [0x48, 0x85, 0xD2, 0x0F, 0x84, 0xF5, 0x00, 0x00, 0x00]

theorem code_l11c2bc : ∀ x ∈ codeRange 0x11c2bc bytes_l11c2bc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c2bc 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c2c5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c2c5 (movR64M64Effect 0x11c2c5 9 (.base 7 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[7]
    (.letOp (n := 54) (.exec 0x11c2c5 (LoadPre 0x11c2c5 (fun s => AddrMode.addr (.base 7 (.d8 0x60)) s (0x11c2c5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c2c5 9 (.base 7 (.d8 0x60))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x11c2c9 (movR64M64Effect 0x11c2c9 10 (.base 7 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[7]
    (.letOp (n := 56) (.exec 0x11c2c9 (LoadPre 0x11c2c9 (fun s => AddrMode.addr (.base 7 (.d8 0x68)) s (0x11c2c9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c2c9 10 (.base 7 (.d8 0x68))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x11c2cd (movR64R64Effect 0x11c2cd 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 58) (.exec 0x11c2cd (fun s => s.RIP = 0x11c2cd) (movR64R64Effect 0x11c2cd 8 10) (Reg.operands [.gpr 10] [])) #v[55]
    (.letOp (n := 59) (.out 0x11c2d0 (subR64R64Effect 0x11c2d0 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[57, 53]
    (.letOp (n := 60) (.out 0x11c2d0 (subR64R64Effect 0x11c2d0 8 9) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 9] []) (.flag .ZF)) #v[57, 53]
    (.letOp (n := 61) (.exec 0x11c2d0 (fun s => s.RIP = 0x11c2d0) (subR64R64Effect 0x11c2d0 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[57, 53]
    (.letOp (n := 62) (.pure (condOp 4)) #v[60]
    (.terminate (.condBr (Fin.last 62) ⟨.l11c3ba, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 53), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ ⟨.l11c2d9, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 53), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l11c2c5 : List UInt8 :=
  [0x4C, 0x8B, 0x4F, 0x60, 0x4C, 0x8B, 0x57, 0x68, 0x4D, 0x89, 0xD0, 0x4D, 0x29, 0xC8, 0x0F, 0x84,
    0xE1, 0x00, 0x00, 0x00]

theorem code_l11c2c5 : ∀ x ∈ codeRange 0x11c2c5 bytes_l11c2c5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c2c5 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c2d9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c2d9 (movR64M64Effect 0x11c2d9 1 (.base 7 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 54) (.exec 0x11c2d9 (LoadPre 0x11c2d9 (fun s => AddrMode.addr (.base 7 (.d8 0x50)) s (0x11c2d9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c2d9 1 (.base 7 (.d8 0x50))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x11c2dd (imulR64R64Imm32Effect 0x11c2dd 7 6 9 0x110) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[9]
    (.letOp (n := 56) (.exec 0x11c2dd (fun s => s.RIP = 0x11c2dd) (imulR64R64Imm32Effect 0x11c2dd 7 6 9 0x110) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 57) (.out 0x11c2e4 (movR32R32Effect 0x11c2e4 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[8]
    (.letOp (n := 58) (.exec 0x11c2e4 (fun s => s.RIP = 0x11c2e4) (movR32R32Effect 0x11c2e4 3 2 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 59) (.out 0x11c2e7 (andR32Imm8Effect 0x11c2e7 3 2 0x3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x11c2e7 (fun s => s.RIP = 0x11c2e7) (andR32Imm8Effect 0x11c2e7 3 2 0x3) (Reg.operands [.gpr 2] [])) #v[57]
    (.letOp (n := 61) (.out 0x11c2ea (subR64R64Effect 0x11c2ea 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[9, 10]
    (.letOp (n := 62) (.exec 0x11c2ea (fun s => s.RIP = 0x11c2ea) (subR64R64Effect 0x11c2ea 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[9, 10]
    (.letOp (n := 63) (.out 0x11c2ed (cmpR64Imm8Effect 0x11c2ed 9 0xfc) (EffectPart.reads (.flag .CF) [.gpr 9] []) (.flag .CF)) #v[61]
    (.letOp (n := 64) (.out 0x11c2ed (cmpR64Imm8Effect 0x11c2ed 9 0xfc) (EffectPart.reads (.flag .ZF) [.gpr 9] []) (.flag .ZF)) #v[61]
    (.letOp (n := 65) (.exec 0x11c2ed (fun s => s.RIP = 0x11c2ed) (cmpR64Imm8Effect 0x11c2ed 9 0xfc) (Reg.operands [.gpr 9] [])) #v[61]
    (.letOp (n := 66) (.pure (condOp 6)) #v[63, 64]
    (.terminate (.condBr (Fin.last 66) ⟨.l11c2fa, RegMap.args [(0, 0), (1, 53), (2, 59), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l11c2f3, RegMap.args [(0, 0), (1, 53), (2, 59), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l11c2d9 : List UInt8 :=
  [0x48, 0x8B, 0x4F, 0x50, 0x49, 0x69, 0xF1, 0x10, 0x01, 0x00, 0x00, 0x44, 0x89, 0xC2, 0x83, 0xE2,
    0x03, 0x4D, 0x29, 0xD1, 0x49, 0x83, 0xF9, 0xFC, 0x76, 0x07]

theorem code_l11c2d9 : ∀ x ∈ codeRange 0x11c2d9 bytes_l11c2d9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c2d9 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c2f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c2f3 (xorR32R32Effect 0x11c2f3 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x11c2f3 (fun s => s.RIP = 0x11c2f3) (xorR32R32Effect 0x11c2f3 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l11c387, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l11c2f3 : List UInt8 :=
  [0x31, 0xFF, 0xE9, 0x8D, 0x00, 0x00, 0x00]

theorem code_l11c2f3 : ∀ x ∈ codeRange 0x11c2f3 bytes_l11c2f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c2f3 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c2fa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c2fa (leaR64Effect 0x11c2fa 9 (.sib 1 (some 6) 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1, .gpr 6] []) (.reg (.gpr 9))) #v[1, 6]
    (.letOp (n := 54) (.exec 0x11c2fa (fun s => s.RIP = 0x11c2fa) (leaR64Effect 0x11c2fa 9 (.sib 1 (some 6) 0 .none)) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 6]
    (.letOp (n := 55) (.out 0x11c2fe (andR64Imm8Effect 0x11c2fe 8 0xfc) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 56) (.exec 0x11c2fe (fun s => s.RIP = 0x11c2fe) (andR64Imm8Effect 0x11c2fe 8 0xfc) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 57) (.out 0x11c302 (xorR32R32Effect 0x11c302 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 58) (.exec 0x11c302 (fun s => s.RIP = 0x11c302) (xorR32R32Effect 0x11c302 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l11c320, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 57), (8, 55), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c2fa : List UInt8 :=
  [0x4C, 0x8D, 0x0C, 0x31, 0x49, 0x83, 0xE0, 0xFC, 0x31, 0xFF, 0xEB, 0x1A]

theorem code_l11c2fa : ∀ x ∈ codeRange 0x11c2fa bytes_l11c2fa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c2fa 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c310 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c310 (addR64Imm8Effect 0x11c310 7 0x4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 54) (.exec 0x11c310 (fun s => s.RIP = 0x11c310) (addR64Imm8Effect 0x11c310 7 0x4) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x11c314 (addR64Imm32Effect 0x11c314 9 0x440) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 56) (.exec 0x11c314 (fun s => s.RIP = 0x11c314) (addR64Imm32Effect 0x11c314 9 0x440) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 57) (.out 0x11c31b (cmpR64R64Effect 0x11c31b 8 7) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 7] []) (.flag .ZF)) #v[8, 53]
    (.letOp (n := 58) (.exec 0x11c31b (fun s => s.RIP = 0x11c31b) (cmpR64R64Effect 0x11c31b 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[8, 53]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l11c382, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l11c320, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l11c310 : List UInt8 :=
  [0x48, 0x83, 0xC7, 0x04, 0x49, 0x81, 0xC1, 0x40, 0x04, 0x00, 0x00, 0x49, 0x39, 0xF8, 0x74, 0x62]

theorem code_l11c310 : ∀ x ∈ codeRange 0x11c310 bytes_l11c310, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c310 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c320 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c320 (movR64M64Effect 0x11c320 10 (.base 9 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[9]
    (.letOp (n := 54) (.exec 0x11c320 (LoadPre 0x11c320 (fun s => AddrMode.addr (.base 9 .none) s (0x11c320 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c320 10 (.base 9 .none)) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x11c323 (cmpR64R64Effect 0x11c323 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[0, 53]
    (.letOp (n := 56) (.out 0x11c323 (cmpR64R64Effect 0x11c323 0 10) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 10] []) (.flag .ZF)) #v[0, 53]
    (.letOp (n := 57) (.exec 0x11c323 (fun s => s.RIP = 0x11c323) (cmpR64R64Effect 0x11c323 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[0, 53]
    (.letOp (n := 58) (.pure (condOp 6)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l11c350, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l11c328, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c320 : List UInt8 :=
  [0x4D, 0x8B, 0x11, 0x4C, 0x39, 0xD0, 0x76, 0x28]

theorem code_l11c320 : ∀ x ∈ codeRange 0x11c320 bytes_l11c320, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c320 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c328 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c328 (movR64M64Effect 0x11c328 10 (.base 9 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[9]
    (.letOp (n := 54) (.exec 0x11c328 (LoadPre 0x11c328 (fun s => AddrMode.addr (.base 9 (.d32 0x110)) s (0x11c328 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c328 10 (.base 9 (.d32 0x110))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x11c32f (cmpR64R64Effect 0x11c32f 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[0, 53]
    (.letOp (n := 56) (.out 0x11c32f (cmpR64R64Effect 0x11c32f 0 10) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 10] []) (.flag .ZF)) #v[0, 53]
    (.letOp (n := 57) (.exec 0x11c32f (fun s => s.RIP = 0x11c32f) (cmpR64R64Effect 0x11c32f 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[0, 53]
    (.letOp (n := 58) (.pure (condOp 6)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l11c35f, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l11c334, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c328 : List UInt8 :=
  [0x4D, 0x8B, 0x91, 0x10, 0x01, 0x00, 0x00, 0x4C, 0x39, 0xD0, 0x76, 0x2B]

theorem code_l11c328 : ∀ x ∈ codeRange 0x11c328 bytes_l11c328, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c328 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c334 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c334 (movR64M64Effect 0x11c334 10 (.base 9 (.d32 0x220))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[9]
    (.letOp (n := 54) (.exec 0x11c334 (LoadPre 0x11c334 (fun s => AddrMode.addr (.base 9 (.d32 0x220)) s (0x11c334 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c334 10 (.base 9 (.d32 0x220))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x11c33b (cmpR64R64Effect 0x11c33b 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[0, 53]
    (.letOp (n := 56) (.out 0x11c33b (cmpR64R64Effect 0x11c33b 0 10) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 10] []) (.flag .ZF)) #v[0, 53]
    (.letOp (n := 57) (.exec 0x11c33b (fun s => s.RIP = 0x11c33b) (cmpR64R64Effect 0x11c33b 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[0, 53]
    (.letOp (n := 58) (.pure (condOp 6)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l11c36e, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l11c340, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c334 : List UInt8 :=
  [0x4D, 0x8B, 0x91, 0x20, 0x02, 0x00, 0x00, 0x4C, 0x39, 0xD0, 0x76, 0x2E]

theorem code_l11c334 : ∀ x ∈ codeRange 0x11c334 bytes_l11c334, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c334 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c340 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c340 (movR64M64Effect 0x11c340 10 (.base 9 (.d32 0x330))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[9]
    (.letOp (n := 54) (.exec 0x11c340 (LoadPre 0x11c340 (fun s => AddrMode.addr (.base 9 (.d32 0x330)) s (0x11c340 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c340 10 (.base 9 (.d32 0x330))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x11c347 (cmpR64R64Effect 0x11c347 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[0, 53]
    (.letOp (n := 56) (.out 0x11c347 (cmpR64R64Effect 0x11c347 0 10) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 10] []) (.flag .ZF)) #v[0, 53]
    (.letOp (n := 57) (.exec 0x11c347 (fun s => s.RIP = 0x11c347) (cmpR64R64Effect 0x11c347 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[0, 53]
    (.letOp (n := 58) (.pure (condOp 7)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l11c310, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l11c34c, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11c340 : List UInt8 :=
  [0x4D, 0x8B, 0x91, 0x30, 0x03, 0x00, 0x00, 0x4C, 0x39, 0xD0, 0x77, 0xC4]

theorem code_l11c340 : ∀ x ∈ codeRange 0x11c340 bytes_l11c340, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c340 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c34c : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l11c37d, RegMap.args (entryMap (live .l11c34c)) 53⟩)

def bytes_l11c34c : List UInt8 :=
  [0xEB, 0x2F]

theorem code_l11c34c : ∀ x ∈ codeRange 0x11c34c bytes_l11c34c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c34c 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c350 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c350 (movR64R64Effect 0x11c350 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[10]
    (.letOp (n := 54) (.exec 0x11c350 (fun s => s.RIP = 0x11c350) (movR64R64Effect 0x11c350 0 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x11c353 (movR64M64Effect 0x11c353 10 (.base 9 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[9]
    (.letOp (n := 56) (.exec 0x11c353 (LoadPre 0x11c353 (fun s => AddrMode.addr (.base 9 (.d32 0x110)) s (0x11c353 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c353 10 (.base 9 (.d32 0x110))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 57) (.out 0x11c35a (cmpR64R64Effect 0x11c35a 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.out 0x11c35a (cmpR64R64Effect 0x11c35a 0 10) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 10] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 59) (.exec 0x11c35a (fun s => s.RIP = 0x11c35a) (cmpR64R64Effect 0x11c35a 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[53, 55]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l11c334, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l11c35f, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l11c350 : List UInt8 :=
  [0x4C, 0x89, 0xD0, 0x4D, 0x8B, 0x91, 0x10, 0x01, 0x00, 0x00, 0x4C, 0x39, 0xD0, 0x77, 0xD5]

theorem code_l11c350 : ∀ x ∈ codeRange 0x11c350 bytes_l11c350, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c350 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c35f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c35f (movR64R64Effect 0x11c35f 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[10]
    (.letOp (n := 54) (.exec 0x11c35f (fun s => s.RIP = 0x11c35f) (movR64R64Effect 0x11c35f 0 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x11c362 (movR64M64Effect 0x11c362 10 (.base 9 (.d32 0x220))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[9]
    (.letOp (n := 56) (.exec 0x11c362 (LoadPre 0x11c362 (fun s => AddrMode.addr (.base 9 (.d32 0x220)) s (0x11c362 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c362 10 (.base 9 (.d32 0x220))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 57) (.out 0x11c369 (cmpR64R64Effect 0x11c369 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.out 0x11c369 (cmpR64R64Effect 0x11c369 0 10) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 10] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 59) (.exec 0x11c369 (fun s => s.RIP = 0x11c369) (cmpR64R64Effect 0x11c369 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[53, 55]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l11c340, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l11c36e, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l11c35f : List UInt8 :=
  [0x4C, 0x89, 0xD0, 0x4D, 0x8B, 0x91, 0x20, 0x02, 0x00, 0x00, 0x4C, 0x39, 0xD0, 0x77, 0xD2]

theorem code_l11c35f : ∀ x ∈ codeRange 0x11c35f bytes_l11c35f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c35f 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c36e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c36e (movR64R64Effect 0x11c36e 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[10]
    (.letOp (n := 54) (.exec 0x11c36e (fun s => s.RIP = 0x11c36e) (movR64R64Effect 0x11c36e 0 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x11c371 (movR64M64Effect 0x11c371 10 (.base 9 (.d32 0x330))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[9]
    (.letOp (n := 56) (.exec 0x11c371 (LoadPre 0x11c371 (fun s => AddrMode.addr (.base 9 (.d32 0x330)) s (0x11c371 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c371 10 (.base 9 (.d32 0x330))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 57) (.out 0x11c378 (cmpR64R64Effect 0x11c378 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.out 0x11c378 (cmpR64R64Effect 0x11c378 0 10) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 10] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 59) (.exec 0x11c378 (fun s => s.RIP = 0x11c378) (cmpR64R64Effect 0x11c378 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[53, 55]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l11c310, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l11c37d, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l11c36e : List UInt8 :=
  [0x4C, 0x89, 0xD0, 0x4D, 0x8B, 0x91, 0x30, 0x03, 0x00, 0x00, 0x4C, 0x39, 0xD0, 0x77, 0x93]

theorem code_l11c36e : ∀ x ∈ codeRange 0x11c36e bytes_l11c36e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c36e 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c37d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c37d (movR64R64Effect 0x11c37d 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[10]
    (.letOp (n := 54) (.exec 0x11c37d (fun s => s.RIP = 0x11c37d) (movR64R64Effect 0x11c37d 0 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.terminate (.br ⟨.l11c310, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l11c37d : List UInt8 :=
  [0x4C, 0x89, 0xD0, 0xEB, 0x8E]

theorem code_l11c37d : ∀ x ∈ codeRange 0x11c37d bytes_l11c37d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c37d 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c382 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c382 (testR64R64Effect 0x11c382 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 54) (.exec 0x11c382 (fun s => s.RIP = 0x11c382) (testR64R64Effect 0x11c382 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11c3ba, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11c387, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11c382 : List UInt8 :=
  [0x48, 0x85, 0xD2, 0x74, 0x33]

theorem code_l11c382 : ∀ x ∈ codeRange 0x11c382 bytes_l11c382, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c382 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c387 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c387 (imulR64R64Imm32Effect 0x11c387 7 7 7 0x110) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 54) (.exec 0x11c387 (fun s => s.RIP = 0x11c387) (imulR64R64Imm32Effect 0x11c387 7 7 7 0x110) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x11c38e (addR64R64Effect 0x11c38e 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[53, 6]
    (.letOp (n := 56) (.exec 0x11c38e (fun s => s.RIP = 0x11c38e) (addR64R64Effect 0x11c38e 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[53, 6]
    (.letOp (n := 57) (.out 0x11c391 (addR64R64Effect 0x11c391 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[1, 55]
    (.letOp (n := 58) (.exec 0x11c391 (fun s => s.RIP = 0x11c391) (addR64R64Effect 0x11c391 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1, 55]
    (.letOp (n := 59) (.out 0x11c394 (imulR64R64Imm32Effect 0x11c394 7 2 2 0x110) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 60) (.exec 0x11c394 (fun s => s.RIP = 0x11c394) (imulR64R64Imm32Effect 0x11c394 7 2 2 0x110) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 61) (.out 0x11c39b (xorR32R32Effect 0x11c39b 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 62) (.exec 0x11c39b (fun s => s.RIP = 0x11c39b) (xorR32R32Effect 0x11c39b 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 63) (.exec 0x11c39d (fun s => s.RIP = 0x11c39d) (fun _ => nopEffect 0x11c39d 3) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l11c3a0, RegMap.args [(0, 0), (1, 57), (2, 59), (4, 4), (5, 5), (6, 61), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l11c387 : List UInt8 :=
  [0x48, 0x69, 0xFF, 0x10, 0x01, 0x00, 0x00, 0x48, 0x01, 0xF7, 0x48, 0x01, 0xF9, 0x48, 0x69, 0xD2,
    0x10, 0x01, 0x00, 0x00, 0x31, 0xF6, 0x0F, 0x1F, 0x00]

theorem code_l11c387 : ∀ x ∈ codeRange 0x11c387 bytes_l11c387, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c387 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c3a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c3a0 (movR64R64Effect 0x11c3a0 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[0]
    (.letOp (n := 54) (.exec 0x11c3a0 (fun s => s.RIP = 0x11c3a0) (movR64R64Effect 0x11c3a0 7 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x11c3a3 (movR64M64Effect 0x11c3a3 0 (.sib 1 (some 6) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 6] []) (.reg (.gpr 0))) #v[1, 6]
    (.letOp (n := 56) (.exec 0x11c3a3 (LoadPre 0x11c3a3 (fun s => AddrMode.addr (.sib 1 (some 6) 0 .none) s (0x11c3a3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c3a3 0 (.sib 1 (some 6) 0 .none)) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 6]
    (.letOp (n := 57) (.out 0x11c3a7 (cmpR64R64Effect 0x11c3a7 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.out 0x11c3a7 (cmpR64R64Effect 0x11c3a7 7 0) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 0] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 59) (.exec 0x11c3a7 (fun s => s.RIP = 0x11c3a7) (cmpR64R64Effect 0x11c3a7 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[53, 55]
    (.letOp (n := 60) (.out 0x11c3aa (atFlags (condHolds 7) (cmovR64R64Effect 0x11c3aa 4 0 7)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[55, 53, 57, 58]
    (.letOp (n := 61) (.exec 0x11c3aa (fun s => s.RIP = 0x11c3aa) (atFlags (condHolds 7) (cmovR64R64Effect 0x11c3aa 4 0 7)) (Reg.operands [.gpr 0, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[55, 53, 57, 58]
    (.letOp (n := 62) (.out 0x11c3ae (addR64Imm32Effect 0x11c3ae 6 0x110) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 63) (.exec 0x11c3ae (fun s => s.RIP = 0x11c3ae) (addR64Imm32Effect 0x11c3ae 6 0x110) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.out 0x11c3b5 (cmpR64R64Effect 0x11c3b5 2 6) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 6] []) (.flag .ZF)) #v[2, 62]
    (.letOp (n := 65) (.exec 0x11c3b5 (fun s => s.RIP = 0x11c3b5) (cmpR64R64Effect 0x11c3b5 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 62]
    (.letOp (n := 66) (.pure (condOp 5)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l11c3a0, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 62), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l11c3ba, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 62), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l11c3a0 : List UInt8 :=
  [0x48, 0x89, 0xC7, 0x48, 0x8B, 0x04, 0x31, 0x48, 0x39, 0xC7, 0x48, 0x0F, 0x47, 0xC7, 0x48, 0x81,
    0xC6, 0x10, 0x01, 0x00, 0x00, 0x48, 0x39, 0xF2, 0x75, 0xE6]

theorem code_l11c3a0 : ∀ x ∈ codeRange 0x11c3a0 bytes_l11c3a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c3a0 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c3ba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c3ba (popR64Effect 0x11c3ba 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.out 0x11c3ba (popR64Effect 0x11c3ba 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x11c3ba (PopPre 0x11c3ba) (popR64Effect 0x11c3ba 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x11c3bb (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[54]
    (.letOp (n := 57) (.out 0x11c3bb (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 58) (.exec 0x11c3bb (RetPre 0x11c3bb) (retEffect) (Reg.operands [.gpr 4] [])) #v[54]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59) (some ⟨56, by decide⟩))))))))

def bytes_l11c3ba : List UInt8 :=
  [0x5B, 0xC3]

theorem code_l11c3ba : ∀ x ∈ codeRange 0x11c3ba bytes_l11c3ba, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c3ba 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c3c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c3c0 (movR64M64Effect 0x11c3c0 1 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 54) (.exec 0x11c3c0 (LoadPre 0x11c3c0 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x11c3c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c3c0 1 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x11c3c4 (bswapR64Effect 0x11c3c4 3 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x11c3c4 (fun s => s.RIP = 0x11c3c4) (bswapR64Effect 0x11c3c4 3 1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x11c3c7 (movR64M64Effect 0x11c3c7 2 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 58) (.exec 0x11c3c7 (LoadPre 0x11c3c7 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x11c3c7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c3c7 2 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x11c3cb (bswapR64Effect 0x11c3cb 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x11c3cb (fun s => s.RIP = 0x11c3cb) (bswapR64Effect 0x11c3cb 3 2) (Reg.operands [.gpr 2] [])) #v[57]
    (.letOp (n := 61) (.out 0x11c3ce (movR64R64Effect 0x11c3ce 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 62) (.exec 0x11c3ce (fun s => s.RIP = 0x11c3ce) (movR64R64Effect 0x11c3ce 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.out 0x11c3d1 (movR64M64Effect 0x11c3d1 7 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 64) (.exec 0x11c3d1 (LoadPre 0x11c3d1 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11c3d1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c3d1 7 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x11c3d5 (bswapR64Effect 0x11c3d5 3 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x11c3d5 (fun s => s.RIP = 0x11c3d5) (bswapR64Effect 0x11c3d5 3 7) (Reg.operands [.gpr 7] [])) #v[63]
    (.letOp (n := 67) (.out 0x11c3d8 (movR64M64Effect 0x11c3d8 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 68) (.exec 0x11c3d8 (LoadPre 0x11c3d8 (fun s => AddrMode.addr (.base 6 .none) s (0x11c3d8 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c3d8 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x11c3db (bswapR64Effect 0x11c3db 3 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[67]
    (.letOp (n := 70) (.exec 0x11c3db (fun s => s.RIP = 0x11c3db) (bswapR64Effect 0x11c3db 3 6) (Reg.operands [.gpr 6] [])) #v[67]
    (.letOp (n := 71) (.exec 0x11c3de (StorePre 0x11c3de 3 (fun s => AddrMode.addr (.base 0 .none) s (0x11c3de + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11c3de 1 (.base 0 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[55, 61]
    (.letOp (n := 72) (.exec 0x11c3e1 (StorePre 0x11c3e1 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x11c3e1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c3e1 2 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[59, 61]
    (.letOp (n := 73) (.exec 0x11c3e5 (StorePre 0x11c3e5 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x11c3e5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c3e5 7 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[65, 61]
    (.letOp (n := 74) (.exec 0x11c3e9 (StorePre 0x11c3e9 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x11c3e9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c3e9 6 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[69, 61]
    (.letOp (n := 75) (.out 0x11c3ed (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 76) (.out 0x11c3ed (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 77) (.exec 0x11c3ed (RetPre 0x11c3ed) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 61), (1, 55), (2, 59), (3, 3), (4, 76), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l11c3c0 : List UInt8 :=
  [0x48, 0x8B, 0x4E, 0x18, 0x48, 0x0F, 0xC9, 0x48, 0x8B, 0x56, 0x10, 0x48, 0x0F, 0xCA, 0x48, 0x89,
    0xF8, 0x48, 0x8B, 0x7E, 0x08, 0x48, 0x0F, 0xCF, 0x48, 0x8B, 0x36, 0x48, 0x0F, 0xCE, 0x48, 0x89,
    0x08, 0x48, 0x89, 0x50, 0x08, 0x48, 0x89, 0x78, 0x10, 0x48, 0x89, 0x70, 0x18, 0xC3]

theorem code_l11c3c0 : ∀ x ∈ codeRange 0x11c3c0 bytes_l11c3c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c3c0 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c3f0 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l11c400, RegMap.args (entryMap (live .l11c3f0)) 53⟩)

def bytes_l11c3f0 : List UInt8 :=
  [0xE9, 0x0B, 0x00, 0x00, 0x00]

theorem code_l11c3f0 : ∀ x ∈ codeRange 0x11c3f0 bytes_l11c3f0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c3f0 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c400_2 : Block Op Label signature Reg.count 129 :=
  .letOp (n := 129) (.out 0x11c494 (movR64M64Effect 0x11c494 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 130) (.exec 0x11c494 (LoadPre 0x11c494 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c494 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c494 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 131) (.out 0x11c499 (decR64Effect 0x11c499 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[129]
    (.letOp (n := 132) (.exec 0x11c499 (fun s => s.RIP = 0x11c499) (decR64Effect 0x11c499 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[129]
    (.letOp (n := 133) (.out 0x11c49c (shrR64Effect 0x11c49c 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[131]
    (.letOp (n := 134) (.exec 0x11c49c (fun s => s.RIP = 0x11c49c) (shrR64Effect 0x11c49c 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[131]
    (.letOp (n := 135) (.out 0x11c4a0 (addR64R64Effect 0x11c4a0 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[133, 73]
    (.letOp (n := 136) (.exec 0x11c4a0 (fun s => s.RIP = 0x11c4a0) (addR64R64Effect 0x11c4a0 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[133, 73]
    (.letOp (n := 137) (.out 0x11c4a3 (movR64R64Effect 0x11c4a3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[73]
    (.letOp (n := 138) (.exec 0x11c4a3 (fun s => s.RIP = 0x11c4a3) (movR64R64Effect 0x11c4a3 2 13) (Reg.operands [.gpr 13] [])) #v[73]
    (.letOp (n := 139) (.out 0x11c4a6 (notR64Effect 0x11c4a6 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[137]
    (.letOp (n := 140) (.exec 0x11c4a6 (fun s => s.RIP = 0x11c4a6) (notR64Effect 0x11c4a6 2) (Reg.operands [.gpr 2] [])) #v[137]
    (.letOp (n := 141) (.out 0x11c4a9 (orR64R64Effect 0x11c4a9 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[139, 135]
    (.letOp (n := 142) (.exec 0x11c4a9 (fun s => s.RIP = 0x11c4a9) (orR64R64Effect 0x11c4a9 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[139, 135]
    (.letOp (n := 143) (.out 0x11c4ac (shrR64Effect 0x11c4ac 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[141]
    (.letOp (n := 144) (.exec 0x11c4ac (fun s => s.RIP = 0x11c4ac) (shrR64Effect 0x11c4ac 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[141]
    (.letOp (n := 145) (.exec 0x11c4b0 (StorePre 0x11c4b0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c4b0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c4b0 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[143, 63]
    (.letOp (n := 146) (.out 0x11c4b5 (movzxR32M8Effect 0x11c4b5 5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[63]
    (.letOp (n := 147) (.exec 0x11c4b5 (LoadPre 0x11c4b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c4b5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11c4b5 5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 148) (.out 0x11c4ba (andAlImm8Effect 0x11c4ba 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[146]
    (.letOp (n := 149) (.exec 0x11c4ba (fun s => s.RIP = 0x11c4ba) (andAlImm8Effect 0x11c4ba 0x1) (Reg.operands [.gpr 0] [])) #v[146]
    (.letOp (n := 150) (.out 0x11c4bc (movzxR32R8Effect 0x11c4bc 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[148]
    (.letOp (n := 151) (.exec 0x11c4bc (fun s => s.RIP = 0x11c4bc) (movzxR32R8Effect 0x11c4bc 3 7 0) (Reg.operands [.gpr 0] [])) #v[148]
    (.letOp (n := 152) (.out 0x11c4bf (callEffect (fun _ => 0x127d50) 0x11c4c4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 153) (.exec 0x11c4bf (PushPre 0x11c4bf 5) (callEffect (fun _ => 0x127d50) 0x11c4c4) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 154) (.const ⟨64, 0x11c4c4⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 148), (1, 135), (2, 143), (3, 65), (4, 152), (5, 5), (6, 101), (7, 150), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 155⟩ { target := .l11c4c4, kept := #v[], arity := rfl, guard := some (Fin.last 154) })))))))))))))))))))))))))))

def bytes_l11c400_2 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x08, 0x48, 0xFF, 0xC9, 0x48, 0xC1, 0xE9, 0x3F, 0x4C, 0x01, 0xE9, 0x4C,
    0x89, 0xEA, 0x48, 0xF7, 0xD2, 0x48, 0x09, 0xCA, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24,
    0x08, 0x0F, 0xB6, 0x44, 0x24, 0x08, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x8C, 0xB8, 0x00, 0x00]

theorem code_l11c400_2 : ∀ x ∈ codeRange 0x11c494 bytes_l11c400_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c494 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c400_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x11c445 (xorR32R32Effect 0x11c445 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 92) (.exec 0x11c445 (fun s => s.RIP = 0x11c445) (xorR32R32Effect 0x11c445 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 93) (.out 0x11c447 (subR64M64Effect 0x11c447 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[91, 63]
    (.letOp (n := 94) (.exec 0x11c447 (LoadPre 0x11c447 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c447 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c447 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[91, 63]
    (.letOp (n := 95) (.out 0x11c44c (sarR64Effect 0x11c44c 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[93]
    (.letOp (n := 96) (.exec 0x11c44c (fun s => s.RIP = 0x11c44c) (sarR64Effect 0x11c44c 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93]
    (.letOp (n := 97) (.out 0x11c450 (movR64Imm64Effect 0x11c450 6 0x4551231950b75fc5) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 98) (.exec 0x11c450 (fun s => s.RIP = 0x11c450) (movR64Imm64Effect 0x11c450 6 0x4551231950b75fc5) (Reg.operands [] [])) #v[]
    (.letOp (n := 99) (.out 0x11c45a (addR64R64Effect 0x11c45a 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[97, 69]
    (.letOp (n := 100) (.exec 0x11c45a (fun s => s.RIP = 0x11c45a) (addR64R64Effect 0x11c45a 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[97, 69]
    (.letOp (n := 101) (.out 0x11c45d (addR64R64Effect 0x11c45d 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[99, 95]
    (.letOp (n := 102) (.exec 0x11c45d (fun s => s.RIP = 0x11c45d) (addR64R64Effect 0x11c45d 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[99, 95]
    (.letOp (n := 103) (.out 0x11c460 (movR64R64Effect 0x11c460 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 104) (.exec 0x11c460 (fun s => s.RIP = 0x11c460) (movR64R64Effect 0x11c460 2 15) (Reg.operands [.gpr 15] [])) #v[69]
    (.letOp (n := 105) (.out 0x11c463 (notR64Effect 0x11c463 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[103]
    (.letOp (n := 106) (.exec 0x11c463 (fun s => s.RIP = 0x11c463) (notR64Effect 0x11c463 2) (Reg.operands [.gpr 2] [])) #v[103]
    (.letOp (n := 107) (.out 0x11c466 (orR64R64Effect 0x11c466 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[105, 101]
    (.letOp (n := 108) (.exec 0x11c466 (fun s => s.RIP = 0x11c466) (orR64R64Effect 0x11c466 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[105, 101]
    (.letOp (n := 109) (.out 0x11c469 (shrR64Effect 0x11c469 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[107]
    (.letOp (n := 110) (.exec 0x11c469 (fun s => s.RIP = 0x11c469) (shrR64Effect 0x11c469 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[107]
    (.letOp (n := 111) (.exec 0x11c46d (StorePre 0x11c46d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c46d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c46d 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[109, 63]
    (.letOp (n := 112) (.out 0x11c472 (subR64M64Effect 0x11c472 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[89, 63]
    (.letOp (n := 113) (.exec 0x11c472 (LoadPre 0x11c472 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c472 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c472 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[89, 63]
    (.letOp (n := 114) (.out 0x11c477 (sarR64Effect 0x11c477 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[112]
    (.letOp (n := 115) (.exec 0x11c477 (fun s => s.RIP = 0x11c477) (sarR64Effect 0x11c477 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[112]
    (.letOp (n := 116) (.out 0x11c47b (movR64R64Effect 0x11c47b 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 117) (.exec 0x11c47b (fun s => s.RIP = 0x11c47b) (movR64R64Effect 0x11c47b 2 12) (Reg.operands [.gpr 12] [])) #v[71]
    (.letOp (n := 118) (.out 0x11c47e (notR64Effect 0x11c47e 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[116]
    (.letOp (n := 119) (.exec 0x11c47e (fun s => s.RIP = 0x11c47e) (notR64Effect 0x11c47e 2) (Reg.operands [.gpr 2] [])) #v[116]
    (.letOp (n := 120) (.out 0x11c481 (addR64R64Effect 0x11c481 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[114, 71]
    (.letOp (n := 121) (.exec 0x11c481 (fun s => s.RIP = 0x11c481) (addR64R64Effect 0x11c481 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[114, 71]
    (.letOp (n := 122) (.out 0x11c484 (addR64Imm8Effect 0x11c484 1 0x2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[120]
    (.letOp (n := 123) (.exec 0x11c484 (fun s => s.RIP = 0x11c484) (addR64Imm8Effect 0x11c484 1 0x2) (Reg.operands [.gpr 1] [])) #v[120]
    (.letOp (n := 124) (.out 0x11c488 (orR64R64Effect 0x11c488 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[122, 118]
    (.letOp (n := 125) (.exec 0x11c488 (fun s => s.RIP = 0x11c488) (orR64R64Effect 0x11c488 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[122, 118]
    (.letOp (n := 126) (.out 0x11c48b (shrR64Effect 0x11c48b 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[124]
    (.letOp (n := 127) (.exec 0x11c48b (fun s => s.RIP = 0x11c48b) (shrR64Effect 0x11c48b 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[124]
    (.letOp (n := 128) (.exec 0x11c48f (StorePre 0x11c48f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c48f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c48f 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[126, 63]
    (b_l11c400_2))))))))))))))))))))))))))))))))))))))

def bytes_l11c400_1 : List UInt8 :=
  [0x31, 0xD2, 0x48, 0x2B, 0x54, 0x24, 0x08, 0x48, 0xC1, 0xFA, 0x3F, 0x48, 0xBE, 0xC5, 0x5F, 0xB7,
    0x50, 0x19, 0x23, 0x51, 0x45, 0x4C, 0x01, 0xFE, 0x48, 0x01, 0xD6, 0x4C, 0x89, 0xFA, 0x48, 0xF7,
    0xD2, 0x48, 0x09, 0xF2, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x08, 0x48, 0x2B, 0x4C,
    0x24, 0x08, 0x48, 0xC1, 0xF9, 0x3F, 0x4C, 0x89, 0xE2, 0x48, 0xF7, 0xD2, 0x4C, 0x01, 0xE1, 0x48,
    0x83, 0xC1, 0x02, 0x48, 0x09, 0xD1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x08] ++ bytes_l11c400_2

theorem code_l11c400_1 : ∀ x ∈ codeRange 0x11c445 bytes_l11c400_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1c445 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11c400_2

@[cfg_block] def b_l11c400 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c400 (pushR64Effect 0x11c400 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x11c400 (PushPre 0x11c400 2) (pushR64Effect 0x11c400 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x11c402 (pushR64Effect 0x11c402 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x11c402 (PushPre 0x11c402 2) (pushR64Effect 0x11c402 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x11c404 (pushR64Effect 0x11c404 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x11c404 (PushPre 0x11c404 2) (pushR64Effect 0x11c404 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x11c406 (pushR64Effect 0x11c406 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x11c406 (PushPre 0x11c406 2) (pushR64Effect 0x11c406 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x11c408 (pushR64Effect 0x11c408 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x11c408 (PushPre 0x11c408 1) (pushR64Effect 0x11c408 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x11c409 (subR64Imm8Effect 0x11c409 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x11c409 (fun s => s.RIP = 0x11c409) (subR64Imm8Effect 0x11c409 4 0x10) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x11c40d (movR64R64Effect 0x11c40d 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 66) (.exec 0x11c40d (fun s => s.RIP = 0x11c40d) (movR64R64Effect 0x11c40d 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x11c410 (movR64M64Effect 0x11c410 14 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 68) (.exec 0x11c410 (LoadPre 0x11c410 (fun s => AddrMode.addr (.base 6 .none) s (0x11c410 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c410 14 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x11c413 (movR64M64Effect 0x11c413 15 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 70) (.exec 0x11c413 (LoadPre 0x11c413 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11c413 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c413 15 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x11c417 (movR64M64Effect 0x11c417 12 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 72) (.exec 0x11c417 (LoadPre 0x11c417 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x11c417 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c417 12 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x11c41b (movR64M64Effect 0x11c41b 13 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 74) (.exec 0x11c41b (LoadPre 0x11c41b (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x11c41b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c41b 13 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 75) (.out 0x11c41f (movR64Imm64Effect 0x11c41f 0 0x402da1732fc9bebf) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 76) (.exec 0x11c41f (fun s => s.RIP = 0x11c41f) (movR64Imm64Effect 0x11c41f 0 0x402da1732fc9bebf) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x11c429 (addR64R64Effect 0x11c429 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[75, 67]
    (.letOp (n := 78) (.exec 0x11c429 (fun s => s.RIP = 0x11c429) (addR64R64Effect 0x11c429 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[75, 67]
    (.letOp (n := 79) (.out 0x11c42c (movR64R64Effect 0x11c42c 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 80) (.exec 0x11c42c (fun s => s.RIP = 0x11c42c) (movR64R64Effect 0x11c42c 1 14) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 81) (.out 0x11c42f (notR64Effect 0x11c42f 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 82) (.exec 0x11c42f (fun s => s.RIP = 0x11c42f) (notR64Effect 0x11c42f 1) (Reg.operands [.gpr 1] [])) #v[79]
    (.letOp (n := 83) (.out 0x11c432 (orR64R64Effect 0x11c432 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[81, 77]
    (.letOp (n := 84) (.exec 0x11c432 (fun s => s.RIP = 0x11c432) (orR64R64Effect 0x11c432 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[81, 77]
    (.letOp (n := 85) (.out 0x11c435 (shrR64Effect 0x11c435 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[83]
    (.letOp (n := 86) (.exec 0x11c435 (fun s => s.RIP = 0x11c435) (shrR64Effect 0x11c435 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[83]
    (.letOp (n := 87) (.exec 0x11c439 (StorePre 0x11c439 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c439 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c439 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 63]
    (.letOp (n := 88) (.exec 0x11c43e (fun s => s.RIP = 0x11c43e) (leaR64Effect 0x11c43e 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 89) (.out 0x11c443 (xorR32R32Effect 0x11c443 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[85, 85]
    (.letOp (n := 90) (.exec 0x11c443 (fun s => s.RIP = 0x11c443) (xorR32R32Effect 0x11c443 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[85, 85]
    (b_l11c400_1))))))))))))))))))))))))))))))))))))))

def bytes_l11c400 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x10, 0x48, 0x89, 0xFB,
    0x4C, 0x8B, 0x36, 0x4C, 0x8B, 0x7E, 0x08, 0x4C, 0x8B, 0x66, 0x10, 0x4C, 0x8B, 0x6E, 0x18, 0x48,
    0xB8, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40, 0x4C, 0x01, 0xF0, 0x4C, 0x89, 0xF1, 0x48,
    0xF7, 0xD1, 0x48, 0x09, 0xC1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x8D,
    0x44, 0x24, 0x08, 0x31, 0xC9] ++ bytes_l11c400_1

theorem code_l11c400 : ∀ x ∈ codeRange 0x11c400 bytes_l11c400, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1c400 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11c400_1

@[cfg_block] def b_l11c4c4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11c4c4 (StorePre 0x11c4c4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x11c4c4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11c4c4 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x11c4c8 (cmpAlImm8Effect 0x11c4c8 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 55) (.exec 0x11c4c8 (fun s => s.RIP = 0x11c4c8) (cmpAlImm8Effect 0x11c4c8 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 56) (.pure (condOp 5)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l11c4ec, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l11c4cc, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l11c4c4 : List UInt8 :=
  [0x88, 0x44, 0x24, 0x07, 0x3C, 0x01, 0x75, 0x20]

theorem code_l11c4c4 : ∀ x ∈ codeRange 0x11c4c4 bytes_l11c4c4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c4c4 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c4cc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11c4cc (StorePre 0x11c4cc 3 (fun s => AddrMode.addr (.base 3 .none) s (0x11c4cc + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11c4cc 14 (.base 3 .none)) (Reg.operands [.gpr 14, .gpr 3] [])) #v[14, 3]
    (.letOp (n := 54) (.exec 0x11c4cf (StorePre 0x11c4cf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x11c4cf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c4cf 15 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 55) (.exec 0x11c4d3 (StorePre 0x11c4d3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x11c4d3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c4d3 12 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 56) (.exec 0x11c4d7 (StorePre 0x11c4d7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x11c4d7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c4d7 13 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.letOp (n := 57) (.out 0x11c4db (movR64R64Effect 0x11c4db 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 58) (.exec 0x11c4db (fun s => s.RIP = 0x11c4db) (movR64R64Effect 0x11c4db 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x11c4de (addR64Imm8Effect 0x11c4de 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11c4de (fun s => s.RIP = 0x11c4de) (addR64Imm8Effect 0x11c4de 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x11c4e2 (popR64Effect 0x11c4e2 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[59]
    (.letOp (n := 62) (.out 0x11c4e2 (popR64Effect 0x11c4e2 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x11c4e2 (PopPre 0x11c4e2) (popR64Effect 0x11c4e2 1 3) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x11c4e3 (popR64Effect 0x11c4e3 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[62]
    (.letOp (n := 65) (.out 0x11c4e3 (popR64Effect 0x11c4e3 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x11c4e3 (PopPre 0x11c4e3) (popR64Effect 0x11c4e3 2 12) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x11c4e5 (popR64Effect 0x11c4e5 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 68) (.out 0x11c4e5 (popR64Effect 0x11c4e5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x11c4e5 (PopPre 0x11c4e5) (popR64Effect 0x11c4e5 2 13) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x11c4e7 (popR64Effect 0x11c4e7 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[68]
    (.letOp (n := 71) (.out 0x11c4e7 (popR64Effect 0x11c4e7 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x11c4e7 (PopPre 0x11c4e7) (popR64Effect 0x11c4e7 2 14) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x11c4e9 (popR64Effect 0x11c4e9 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[71]
    (.letOp (n := 74) (.out 0x11c4e9 (popR64Effect 0x11c4e9 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x11c4e9 (PopPre 0x11c4e9) (popR64Effect 0x11c4e9 2 15) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x11c4eb (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[74]
    (.letOp (n := 77) (.out 0x11c4eb (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x11c4eb (RetPre 0x11c4eb) (retEffect) (Reg.operands [.gpr 4] [])) #v[74]
    (.terminate (.ret (RegMap.args [(0, 57), (1, 1), (2, 2), (3, 61), (4, 77), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 70), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)] 79) (some ⟨76, by decide⟩))))))))))))))))))))))))))))

def bytes_l11c4cc : List UInt8 :=
  [0x4C, 0x89, 0x33, 0x4C, 0x89, 0x7B, 0x08, 0x4C, 0x89, 0x63, 0x10, 0x4C, 0x89, 0x6B, 0x18, 0x48,
    0x89, 0xD8, 0x48, 0x83, 0xC4, 0x10, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0xC3]

theorem code_l11c4cc : ∀ x ∈ codeRange 0x11c4cc bytes_l11c4cc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c4cc 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c4ec : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c4ec (leaR64Effect 0x11c4ec 6 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x11c4ec (fun s => s.RIP = 0x11c4ec) (leaR64Effect 0x11c4ec 6 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11c4f1 (xorR32R32Effect 0x11c4f1 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 56) (.exec 0x11c4f1 (fun s => s.RIP = 0x11c4f1) (xorR32R32Effect 0x11c4f1 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 57) (.out 0x11c4f3 (movR64Imm32Effect 0x11c4f3 2 0x2031dd) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x11c4f3 (fun s => s.RIP = 0x11c4f3) (movR64Imm32Effect 0x11c4f3 2 0x2031dd) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x11c4fa (xorR32R32Effect 0x11c4fa 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 60) (.exec 0x11c4fa (fun s => s.RIP = 0x11c4fa) (xorR32R32Effect 0x11c4fa 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 61) (.out 0x11c4fc (movR64Imm32Effect 0x11c4fc 9 0x2031e0) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 62) (.exec 0x11c4fc (fun s => s.RIP = 0x11c4fc) (movR64Imm32Effect 0x11c4fc 9 0x2031e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x11c503 (callEffect (fun _ => 0x115408) 0x11c508) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x11c503 (PushPre 0x11c503 5) (callEffect (fun _ => 0x115408) 0x11c508) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x11c508⟩) #v[]
    (.terminate (.call ⟨.l115408, RegMap.args [(1, 59), (2, 57), (4, 63), (5, 5), (6, 53), (7, 55), (8, 8), (9, 61)] 66⟩ { target := .l11c508, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l11c4ec : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x07, 0x31, 0xFF, 0x48, 0xC7, 0xC2, 0xDD, 0x31, 0x20, 0x00, 0x31, 0xC9,
    0x49, 0xC7, 0xC1, 0xE0, 0x31, 0x20, 0x00, 0xE8, 0x00, 0x8F, 0xFF, 0xFF]

theorem code_l11c4ec : ∀ x ∈ codeRange 0x11c4ec bytes_l11c4ec, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c4ec 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c508 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11c508 (fun s => s.RIP = 0x11c508) (fun _ => nopEffect 0x11c508 8) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l11c510, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l11c508 : List UInt8 :=
  [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l11c508 : ∀ x ∈ codeRange 0x11c508 bytes_l11c508, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c508 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c510_1 : Block Op Label signature Reg.count 95 :=
  .letOp (n := 95) (.out 0x11c54c (xorR32R32Effect 0x11c54c 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[82, 82]
    (.letOp (n := 96) (.exec 0x11c54c (fun s => s.RIP = 0x11c54c) (xorR32R32Effect 0x11c54c 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[82, 82]
    (.letOp (n := 97) (.out 0x11c54e (cmpR8Imm8Effect 0x11c54e 4 13 0x1) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[93]
    (.letOp (n := 98) (.exec 0x11c54e (fun s => s.RIP = 0x11c54e) (cmpR8Imm8Effect 0x11c54e 4 13 0x1) (Reg.operands [.gpr 13] [])) #v[93]
    (.letOp (n := 99) (.out 0x11c552 (atFlags (condHolds 4) (setccR8Effect 0x11c552 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[95, 97]
    (.letOp (n := 100) (.exec 0x11c552 (fun s => s.RIP = 0x11c552) (atFlags (condHolds 4) (setccR8Effect 0x11c552 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[95, 97]
    (.letOp (n := 101) (.out 0x11c556 (callEffect (fun _ => 0x127d50) 0x11c55b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 102) (.exec 0x11c556 (PushPre 0x11c556 5) (callEffect (fun _ => 0x127d50) 0x11c55b) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 103) (.const ⟨64, 0x11c55b⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 87), (1, 83), (2, 2), (3, 71), (4, 101), (5, 67), (6, 81), (7, 99), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 93), (14, 73), (15, 69), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)] 104⟩ { target := .l11c55b, kept := #v[], arity := rfl, guard := some (Fin.last 103) }))))))))))

def bytes_l11c510_1 : List UInt8 :=
  [0x31, 0xFF, 0x41, 0x80, 0xFD, 0x01, 0x40, 0x0F, 0x94, 0xC7, 0xE8, 0xF5, 0xB7, 0x00, 0x00]

theorem code_l11c510_1 : ∀ x ∈ codeRange 0x11c54c bytes_l11c510_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c54c 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c510 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c510 (pushR64Effect 0x11c510 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x11c510 (PushPre 0x11c510 1) (pushR64Effect 0x11c510 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x11c511 (pushR64Effect 0x11c511 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x11c511 (PushPre 0x11c511 2) (pushR64Effect 0x11c511 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x11c513 (pushR64Effect 0x11c513 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x11c513 (PushPre 0x11c513 2) (pushR64Effect 0x11c513 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x11c515 (pushR64Effect 0x11c515 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x11c515 (PushPre 0x11c515 2) (pushR64Effect 0x11c515 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x11c517 (pushR64Effect 0x11c517 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x11c517 (PushPre 0x11c517 2) (pushR64Effect 0x11c517 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x11c519 (pushR64Effect 0x11c519 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x11c519 (PushPre 0x11c519 1) (pushR64Effect 0x11c519 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x11c51a (subR64Imm32Effect 0x11c51a 4 0x168) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x11c51a (fun s => s.RIP = 0x11c51a) (subR64Imm32Effect 0x11c51a 4 0x168) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x11c521 (movR32R32Effect 0x11c521 2 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 68) (.exec 0x11c521 (fun s => s.RIP = 0x11c521) (movR32R32Effect 0x11c521 2 5 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x11c523 (movR64R64Effect 0x11c523 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 70) (.exec 0x11c523 (fun s => s.RIP = 0x11c523) (movR64R64Effect 0x11c523 15 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x11c526 (movR64R64Effect 0x11c526 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 72) (.exec 0x11c526 (fun s => s.RIP = 0x11c526) (movR64R64Effect 0x11c526 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.out 0x11c529 (movR64R64Effect 0x11c529 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 74) (.exec 0x11c529 (fun s => s.RIP = 0x11c529) (movR64R64Effect 0x11c529 14 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.out 0x11c52c (movR32Imm32Effect 0x11c52c 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 76) (.exec 0x11c52c (fun s => s.RIP = 0x11c52c) (movR32Imm32Effect 0x11c52c 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x11c531 (movR64R64Effect 0x11c531 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[73]
    (.letOp (n := 78) (.exec 0x11c531 (fun s => s.RIP = 0x11c531) (movR64R64Effect 0x11c531 7 14) (Reg.operands [.gpr 14] [])) #v[73]
    (.letOp (n := 79) (.out 0x11c534 (movR64Imm32Effect 0x11c534 6 0x203258) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 80) (.exec 0x11c534 (fun s => s.RIP = 0x11c534) (movR64Imm32Effect 0x11c534 6 0x203258) (Reg.operands [] [])) #v[]
    (.letOp (n := 81) (.out 0x11c53b (repMovsqEffect 0x11c53b) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[79, 77, 75, 22]
    (.letOp (n := 82) (.out 0x11c53b (repMovsqEffect 0x11c53b) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[79, 77, 75, 22]
    (.letOp (n := 83) (.out 0x11c53b (repMovsqEffect 0x11c53b) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[79, 77, 75, 22]
    (.letOp (n := 84) (.exec 0x11c53b (RepPre 0x11c53b (RepMovsqPre 0x11c53b)) (repMovsqEffect 0x11c53b) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[79, 77, 75, 22]
    (.letOp (n := 85) (.out 0x11c53e (movR32R32Effect 0x11c53e 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 86) (.exec 0x11c53e (fun s => s.RIP = 0x11c53e) (movR32R32Effect 0x11c53e 2 0 5) (Reg.operands [.gpr 5] [])) #v[67]
    (.letOp (n := 87) (.out 0x11c540 (sarR8Effect 0x11c540 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[85]
    (.letOp (n := 88) (.exec 0x11c540 (fun s => s.RIP = 0x11c540) (sarR8Effect 0x11c540 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[85]
    (.letOp (n := 89) (.out 0x11c543 (movR32R32Effect 0x11c543 3 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 5] []) (.reg (.gpr 13))) #v[67]
    (.letOp (n := 90) (.exec 0x11c543 (fun s => s.RIP = 0x11c543) (movR32R32Effect 0x11c543 3 13 5) (Reg.operands [.gpr 5] [])) #v[67]
    (.letOp (n := 91) (.out 0x11c546 (xorR8R8Effect 0x11c546 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[89, 87]
    (.letOp (n := 92) (.exec 0x11c546 (fun s => s.RIP = 0x11c546) (xorR8R8Effect 0x11c546 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[89, 87]
    (.letOp (n := 93) (.out 0x11c549 (subR8R8Effect 0x11c549 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[91, 87]
    (.letOp (n := 94) (.exec 0x11c549 (fun s => s.RIP = 0x11c549) (subR8R8Effect 0x11c549 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[91, 87]
    (b_l11c510_1))))))))))))))))))))))))))))))))))))))))))

def bytes_l11c510 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x68, 0x01, 0x00,
    0x00, 0x89, 0xD5, 0x49, 0x89, 0xF7, 0x48, 0x89, 0xFB, 0x49, 0x89, 0xE6, 0xB9, 0x0F, 0x00, 0x00,
    0x00, 0x4C, 0x89, 0xF7, 0x48, 0xC7, 0xC6, 0x58, 0x32, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x89, 0xE8,
    0xC0, 0xF8, 0x07, 0x41, 0x89, 0xED, 0x41, 0x30, 0xC5, 0x41, 0x28, 0xC5] ++ bytes_l11c510_1

theorem code_l11c510 : ∀ x ∈ codeRange 0x11c510 bytes_l11c510, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1c510 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11c510_1

@[cfg_block] def b_l11c55b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c55b (movzxR32R8Effect 0x11c55b 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 54) (.exec 0x11c55b (fun s => s.RIP = 0x11c55b) (movzxR32R8Effect 0x11c55b 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x11c55e (leaR64Effect 0x11c55e 12 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 56) (.exec 0x11c55e (fun s => s.RIP = 0x11c55e) (leaR64Effect 0x11c55e 12 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11c566 (movR64R64Effect 0x11c566 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x11c566 (fun s => s.RIP = 0x11c566) (movR64R64Effect 0x11c566 7 12) (Reg.operands [.gpr 12] [])) #v[55]
    (.letOp (n := 59) (.out 0x11c569 (movR64R64Effect 0x11c569 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x11c569 (fun s => s.RIP = 0x11c569) (movR64R64Effect 0x11c569 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x11c56c (movR64R64Effect 0x11c56c 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 62) (.exec 0x11c56c (fun s => s.RIP = 0x11c56c) (movR64R64Effect 0x11c56c 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 63) (.out 0x11c56f (callEffect (fun _ => 0x10fcc0) 0x11c574) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x11c56f (PushPre 0x11c56f 5) (callEffect (fun _ => 0x10fcc0) 0x11c574) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x11c574⟩) #v[]
    (.terminate (.call ⟨.l10fcc0, RegMap.args [(0, 0), (1, 53), (2, 61), (3, 3), (4, 63), (5, 5), (6, 59), (7, 57), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l11c574, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l11c55b : List UInt8 :=
  [0x0F, 0xB6, 0xC8, 0x4C, 0x8D, 0xA4, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0x4C, 0x89,
    0xF6, 0x4C, 0x89, 0xFA, 0xE8, 0x4C, 0x37, 0xFF, 0xFF]

theorem code_l11c55b : ∀ x ∈ codeRange 0x11c55b bytes_l11c55b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c55b 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c574 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c574 (movR32Imm32Effect 0x11c574 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11c574 (fun s => s.RIP = 0x11c574) (movR32Imm32Effect 0x11c574 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11c579 (movR64R64Effect 0x11c579 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x11c579 (fun s => s.RIP = 0x11c579) (movR64R64Effect 0x11c579 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x11c57c (movR64R64Effect 0x11c57c 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x11c57c (fun s => s.RIP = 0x11c57c) (movR64R64Effect 0x11c57c 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c57f (repMovsqEffect 0x11c57f) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11c57f (repMovsqEffect 0x11c57f) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[57, 55, 53, 22]
    (.letOp (n := 61) (.out 0x11c57f (repMovsqEffect 0x11c57f) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[57, 55, 53, 22]
    (.letOp (n := 62) (.exec 0x11c57f (RepPre 0x11c57f (RepMovsqPre 0x11c57f)) (repMovsqEffect 0x11c57f) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 63) (.out 0x11c582 (xorR32R32Effect 0x11c582 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[60, 60]
    (.letOp (n := 64) (.exec 0x11c582 (fun s => s.RIP = 0x11c582) (xorR32R32Effect 0x11c582 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[60, 60]
    (.letOp (n := 65) (.out 0x11c584 (cmpR8Imm8Effect 0x11c584 4 13 0x2) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[13]
    (.letOp (n := 66) (.exec 0x11c584 (fun s => s.RIP = 0x11c584) (cmpR8Imm8Effect 0x11c584 4 13 0x2) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 67) (.out 0x11c588 (atFlags (condHolds 4) (setccR8Effect 0x11c588 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[63, 65]
    (.letOp (n := 68) (.exec 0x11c588 (fun s => s.RIP = 0x11c588) (atFlags (condHolds 4) (setccR8Effect 0x11c588 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[63, 65]
    (.letOp (n := 69) (.out 0x11c58c (callEffect (fun _ => 0x127d50) 0x11c591) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x11c58c (PushPre 0x11c58c 5) (callEffect (fun _ => 0x127d50) 0x11c591) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x11c591⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l11c591, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l11c574 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0xF3, 0x48, 0xA5, 0x31, 0xFF,
    0x41, 0x80, 0xFD, 0x02, 0x40, 0x0F, 0x94, 0xC7, 0xE8, 0xBF, 0xB7, 0x00, 0x00]

theorem code_l11c574 : ∀ x ∈ codeRange 0x11c574 bytes_l11c574, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c574 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c591 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c591 (leaR64Effect 0x11c591 2 (.base 15 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 54) (.exec 0x11c591 (fun s => s.RIP = 0x11c591) (leaR64Effect 0x11c591 2 (.base 15 (.d8 0x78))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x11c595 (movzxR32R8Effect 0x11c595 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 56) (.exec 0x11c595 (fun s => s.RIP = 0x11c595) (movzxR32R8Effect 0x11c595 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x11c598 (movR64R64Effect 0x11c598 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 58) (.exec 0x11c598 (fun s => s.RIP = 0x11c598) (movR64R64Effect 0x11c598 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c59b (movR64R64Effect 0x11c59b 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x11c59b (fun s => s.RIP = 0x11c59b) (movR64R64Effect 0x11c59b 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x11c59e (callEffect (fun _ => 0x10fcc0) 0x11c5a3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x11c59e (PushPre 0x11c59e 5) (callEffect (fun _ => 0x10fcc0) 0x11c5a3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x11c5a3⟩) #v[]
    (.terminate (.call ⟨.l10fcc0, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l11c5a3, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l11c591 : List UInt8 :=
  [0x49, 0x8D, 0x57, 0x78, 0x0F, 0xB6, 0xC8, 0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xE8, 0x1D, 0x37,
    0xFF, 0xFF]

theorem code_l11c591 : ∀ x ∈ codeRange 0x11c591 bytes_l11c591, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c591 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c5a3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c5a3 (movR32Imm32Effect 0x11c5a3 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11c5a3 (fun s => s.RIP = 0x11c5a3) (movR32Imm32Effect 0x11c5a3 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11c5a8 (movR64R64Effect 0x11c5a8 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x11c5a8 (fun s => s.RIP = 0x11c5a8) (movR64R64Effect 0x11c5a8 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x11c5ab (movR64R64Effect 0x11c5ab 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x11c5ab (fun s => s.RIP = 0x11c5ab) (movR64R64Effect 0x11c5ab 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c5ae (repMovsqEffect 0x11c5ae) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11c5ae (repMovsqEffect 0x11c5ae) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[57, 55, 53, 22]
    (.letOp (n := 61) (.out 0x11c5ae (repMovsqEffect 0x11c5ae) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[57, 55, 53, 22]
    (.letOp (n := 62) (.exec 0x11c5ae (RepPre 0x11c5ae (RepMovsqPre 0x11c5ae)) (repMovsqEffect 0x11c5ae) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 63) (.out 0x11c5b1 (xorR32R32Effect 0x11c5b1 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[60, 60]
    (.letOp (n := 64) (.exec 0x11c5b1 (fun s => s.RIP = 0x11c5b1) (xorR32R32Effect 0x11c5b1 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[60, 60]
    (.letOp (n := 65) (.out 0x11c5b3 (cmpR8Imm8Effect 0x11c5b3 4 13 0x3) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[13]
    (.letOp (n := 66) (.exec 0x11c5b3 (fun s => s.RIP = 0x11c5b3) (cmpR8Imm8Effect 0x11c5b3 4 13 0x3) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 67) (.out 0x11c5b7 (atFlags (condHolds 4) (setccR8Effect 0x11c5b7 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[63, 65]
    (.letOp (n := 68) (.exec 0x11c5b7 (fun s => s.RIP = 0x11c5b7) (atFlags (condHolds 4) (setccR8Effect 0x11c5b7 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[63, 65]
    (.letOp (n := 69) (.out 0x11c5bb (callEffect (fun _ => 0x127d50) 0x11c5c0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x11c5bb (PushPre 0x11c5bb 5) (callEffect (fun _ => 0x127d50) 0x11c5c0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x11c5c0⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l11c5c0, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l11c5a3 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0xF3, 0x48, 0xA5, 0x31, 0xFF,
    0x41, 0x80, 0xFD, 0x03, 0x40, 0x0F, 0x94, 0xC7, 0xE8, 0x90, 0xB7, 0x00, 0x00]

theorem code_l11c5a3 : ∀ x ∈ codeRange 0x11c5a3 bytes_l11c5a3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c5a3 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c5c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c5c0 (leaR64Effect 0x11c5c0 2 (.base 15 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 54) (.exec 0x11c5c0 (fun s => s.RIP = 0x11c5c0) (leaR64Effect 0x11c5c0 2 (.base 15 (.d32 0xf0))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x11c5c7 (movzxR32R8Effect 0x11c5c7 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 56) (.exec 0x11c5c7 (fun s => s.RIP = 0x11c5c7) (movzxR32R8Effect 0x11c5c7 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x11c5ca (movR64R64Effect 0x11c5ca 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 58) (.exec 0x11c5ca (fun s => s.RIP = 0x11c5ca) (movR64R64Effect 0x11c5ca 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c5cd (movR64R64Effect 0x11c5cd 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x11c5cd (fun s => s.RIP = 0x11c5cd) (movR64R64Effect 0x11c5cd 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x11c5d0 (callEffect (fun _ => 0x10fcc0) 0x11c5d5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x11c5d0 (PushPre 0x11c5d0 5) (callEffect (fun _ => 0x10fcc0) 0x11c5d5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x11c5d5⟩) #v[]
    (.terminate (.call ⟨.l10fcc0, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l11c5d5, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l11c5c0 : List UInt8 :=
  [0x49, 0x8D, 0x97, 0xF0, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0xC8, 0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xF6,
    0xE8, 0xEB, 0x36, 0xFF, 0xFF]

theorem code_l11c5c0 : ∀ x ∈ codeRange 0x11c5c0 bytes_l11c5c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c5c0 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c5d5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c5d5 (movR32Imm32Effect 0x11c5d5 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11c5d5 (fun s => s.RIP = 0x11c5d5) (movR32Imm32Effect 0x11c5d5 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11c5da (movR64R64Effect 0x11c5da 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x11c5da (fun s => s.RIP = 0x11c5da) (movR64R64Effect 0x11c5da 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x11c5dd (movR64R64Effect 0x11c5dd 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x11c5dd (fun s => s.RIP = 0x11c5dd) (movR64R64Effect 0x11c5dd 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c5e0 (repMovsqEffect 0x11c5e0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11c5e0 (repMovsqEffect 0x11c5e0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[57, 55, 53, 22]
    (.letOp (n := 61) (.out 0x11c5e0 (repMovsqEffect 0x11c5e0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[57, 55, 53, 22]
    (.letOp (n := 62) (.exec 0x11c5e0 (RepPre 0x11c5e0 (RepMovsqPre 0x11c5e0)) (repMovsqEffect 0x11c5e0) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 63) (.out 0x11c5e3 (xorR32R32Effect 0x11c5e3 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[60, 60]
    (.letOp (n := 64) (.exec 0x11c5e3 (fun s => s.RIP = 0x11c5e3) (xorR32R32Effect 0x11c5e3 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[60, 60]
    (.letOp (n := 65) (.out 0x11c5e5 (cmpR8Imm8Effect 0x11c5e5 4 13 0x4) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[13]
    (.letOp (n := 66) (.exec 0x11c5e5 (fun s => s.RIP = 0x11c5e5) (cmpR8Imm8Effect 0x11c5e5 4 13 0x4) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 67) (.out 0x11c5e9 (atFlags (condHolds 4) (setccR8Effect 0x11c5e9 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[63, 65]
    (.letOp (n := 68) (.exec 0x11c5e9 (fun s => s.RIP = 0x11c5e9) (atFlags (condHolds 4) (setccR8Effect 0x11c5e9 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[63, 65]
    (.letOp (n := 69) (.out 0x11c5ed (callEffect (fun _ => 0x127d50) 0x11c5f2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x11c5ed (PushPre 0x11c5ed 5) (callEffect (fun _ => 0x127d50) 0x11c5f2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x11c5f2⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l11c5f2, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l11c5d5 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0xF3, 0x48, 0xA5, 0x31, 0xFF,
    0x41, 0x80, 0xFD, 0x04, 0x40, 0x0F, 0x94, 0xC7, 0xE8, 0x5E, 0xB7, 0x00, 0x00]

theorem code_l11c5d5 : ∀ x ∈ codeRange 0x11c5d5 bytes_l11c5d5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c5d5 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c5f2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c5f2 (leaR64Effect 0x11c5f2 2 (.base 15 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 54) (.exec 0x11c5f2 (fun s => s.RIP = 0x11c5f2) (leaR64Effect 0x11c5f2 2 (.base 15 (.d32 0x168))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x11c5f9 (movzxR32R8Effect 0x11c5f9 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 56) (.exec 0x11c5f9 (fun s => s.RIP = 0x11c5f9) (movzxR32R8Effect 0x11c5f9 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x11c5fc (movR64R64Effect 0x11c5fc 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 58) (.exec 0x11c5fc (fun s => s.RIP = 0x11c5fc) (movR64R64Effect 0x11c5fc 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c5ff (movR64R64Effect 0x11c5ff 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x11c5ff (fun s => s.RIP = 0x11c5ff) (movR64R64Effect 0x11c5ff 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x11c602 (callEffect (fun _ => 0x10fcc0) 0x11c607) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x11c602 (PushPre 0x11c602 5) (callEffect (fun _ => 0x10fcc0) 0x11c607) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x11c607⟩) #v[]
    (.terminate (.call ⟨.l10fcc0, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l11c607, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l11c5f2 : List UInt8 :=
  [0x49, 0x8D, 0x97, 0x68, 0x01, 0x00, 0x00, 0x0F, 0xB6, 0xC8, 0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xF6,
    0xE8, 0xB9, 0x36, 0xFF, 0xFF]

theorem code_l11c5f2 : ∀ x ∈ codeRange 0x11c5f2 bytes_l11c5f2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c5f2 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c607 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c607 (movR32Imm32Effect 0x11c607 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11c607 (fun s => s.RIP = 0x11c607) (movR32Imm32Effect 0x11c607 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11c60c (movR64R64Effect 0x11c60c 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x11c60c (fun s => s.RIP = 0x11c60c) (movR64R64Effect 0x11c60c 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x11c60f (movR64R64Effect 0x11c60f 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x11c60f (fun s => s.RIP = 0x11c60f) (movR64R64Effect 0x11c60f 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c612 (repMovsqEffect 0x11c612) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11c612 (repMovsqEffect 0x11c612) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[57, 55, 53, 22]
    (.letOp (n := 61) (.out 0x11c612 (repMovsqEffect 0x11c612) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[57, 55, 53, 22]
    (.letOp (n := 62) (.exec 0x11c612 (RepPre 0x11c612 (RepMovsqPre 0x11c612)) (repMovsqEffect 0x11c612) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 63) (.out 0x11c615 (xorR32R32Effect 0x11c615 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[60, 60]
    (.letOp (n := 64) (.exec 0x11c615 (fun s => s.RIP = 0x11c615) (xorR32R32Effect 0x11c615 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[60, 60]
    (.letOp (n := 65) (.out 0x11c617 (cmpR8Imm8Effect 0x11c617 4 13 0x5) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[13]
    (.letOp (n := 66) (.exec 0x11c617 (fun s => s.RIP = 0x11c617) (cmpR8Imm8Effect 0x11c617 4 13 0x5) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 67) (.out 0x11c61b (atFlags (condHolds 4) (setccR8Effect 0x11c61b 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[63, 65]
    (.letOp (n := 68) (.exec 0x11c61b (fun s => s.RIP = 0x11c61b) (atFlags (condHolds 4) (setccR8Effect 0x11c61b 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[63, 65]
    (.letOp (n := 69) (.out 0x11c61f (callEffect (fun _ => 0x127d50) 0x11c624) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x11c61f (PushPre 0x11c61f 5) (callEffect (fun _ => 0x127d50) 0x11c624) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x11c624⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l11c624, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l11c607 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0xF3, 0x48, 0xA5, 0x31, 0xFF,
    0x41, 0x80, 0xFD, 0x05, 0x40, 0x0F, 0x94, 0xC7, 0xE8, 0x2C, 0xB7, 0x00, 0x00]

theorem code_l11c607 : ∀ x ∈ codeRange 0x11c607 bytes_l11c607, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c607 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c624 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c624 (leaR64Effect 0x11c624 2 (.base 15 (.d32 0x1e0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 54) (.exec 0x11c624 (fun s => s.RIP = 0x11c624) (leaR64Effect 0x11c624 2 (.base 15 (.d32 0x1e0))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x11c62b (movzxR32R8Effect 0x11c62b 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 56) (.exec 0x11c62b (fun s => s.RIP = 0x11c62b) (movzxR32R8Effect 0x11c62b 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x11c62e (movR64R64Effect 0x11c62e 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 58) (.exec 0x11c62e (fun s => s.RIP = 0x11c62e) (movR64R64Effect 0x11c62e 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c631 (movR64R64Effect 0x11c631 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x11c631 (fun s => s.RIP = 0x11c631) (movR64R64Effect 0x11c631 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x11c634 (callEffect (fun _ => 0x10fcc0) 0x11c639) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x11c634 (PushPre 0x11c634 5) (callEffect (fun _ => 0x10fcc0) 0x11c639) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x11c639⟩) #v[]
    (.terminate (.call ⟨.l10fcc0, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l11c639, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l11c624 : List UInt8 :=
  [0x49, 0x8D, 0x97, 0xE0, 0x01, 0x00, 0x00, 0x0F, 0xB6, 0xC8, 0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xF6,
    0xE8, 0x87, 0x36, 0xFF, 0xFF]

theorem code_l11c624 : ∀ x ∈ codeRange 0x11c624 bytes_l11c624, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c624 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c639 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c639 (movR32Imm32Effect 0x11c639 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11c639 (fun s => s.RIP = 0x11c639) (movR32Imm32Effect 0x11c639 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11c63e (movR64R64Effect 0x11c63e 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x11c63e (fun s => s.RIP = 0x11c63e) (movR64R64Effect 0x11c63e 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x11c641 (movR64R64Effect 0x11c641 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x11c641 (fun s => s.RIP = 0x11c641) (movR64R64Effect 0x11c641 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c644 (repMovsqEffect 0x11c644) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11c644 (repMovsqEffect 0x11c644) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[57, 55, 53, 22]
    (.letOp (n := 61) (.out 0x11c644 (repMovsqEffect 0x11c644) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[57, 55, 53, 22]
    (.letOp (n := 62) (.exec 0x11c644 (RepPre 0x11c644 (RepMovsqPre 0x11c644)) (repMovsqEffect 0x11c644) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 63) (.out 0x11c647 (xorR32R32Effect 0x11c647 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[60, 60]
    (.letOp (n := 64) (.exec 0x11c647 (fun s => s.RIP = 0x11c647) (xorR32R32Effect 0x11c647 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[60, 60]
    (.letOp (n := 65) (.out 0x11c649 (cmpR8Imm8Effect 0x11c649 4 13 0x6) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[13]
    (.letOp (n := 66) (.exec 0x11c649 (fun s => s.RIP = 0x11c649) (cmpR8Imm8Effect 0x11c649 4 13 0x6) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 67) (.out 0x11c64d (atFlags (condHolds 4) (setccR8Effect 0x11c64d 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[63, 65]
    (.letOp (n := 68) (.exec 0x11c64d (fun s => s.RIP = 0x11c64d) (atFlags (condHolds 4) (setccR8Effect 0x11c64d 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[63, 65]
    (.letOp (n := 69) (.out 0x11c651 (callEffect (fun _ => 0x127d50) 0x11c656) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x11c651 (PushPre 0x11c651 5) (callEffect (fun _ => 0x127d50) 0x11c656) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x11c656⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l11c656, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l11c639 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0xF3, 0x48, 0xA5, 0x31, 0xFF,
    0x41, 0x80, 0xFD, 0x06, 0x40, 0x0F, 0x94, 0xC7, 0xE8, 0xFA, 0xB6, 0x00, 0x00]

theorem code_l11c639 : ∀ x ∈ codeRange 0x11c639 bytes_l11c639, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c639 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c656 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c656 (leaR64Effect 0x11c656 2 (.base 15 (.d32 0x258))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 54) (.exec 0x11c656 (fun s => s.RIP = 0x11c656) (leaR64Effect 0x11c656 2 (.base 15 (.d32 0x258))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x11c65d (movzxR32R8Effect 0x11c65d 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 56) (.exec 0x11c65d (fun s => s.RIP = 0x11c65d) (movzxR32R8Effect 0x11c65d 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x11c660 (movR64R64Effect 0x11c660 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 58) (.exec 0x11c660 (fun s => s.RIP = 0x11c660) (movR64R64Effect 0x11c660 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c663 (movR64R64Effect 0x11c663 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x11c663 (fun s => s.RIP = 0x11c663) (movR64R64Effect 0x11c663 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x11c666 (callEffect (fun _ => 0x10fcc0) 0x11c66b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x11c666 (PushPre 0x11c666 5) (callEffect (fun _ => 0x10fcc0) 0x11c66b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x11c66b⟩) #v[]
    (.terminate (.call ⟨.l10fcc0, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l11c66b, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l11c656 : List UInt8 :=
  [0x49, 0x8D, 0x97, 0x58, 0x02, 0x00, 0x00, 0x0F, 0xB6, 0xC8, 0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xF6,
    0xE8, 0x55, 0x36, 0xFF, 0xFF]

theorem code_l11c656 : ∀ x ∈ codeRange 0x11c656 bytes_l11c656, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c656 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c66b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c66b (movR32Imm32Effect 0x11c66b 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11c66b (fun s => s.RIP = 0x11c66b) (movR32Imm32Effect 0x11c66b 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11c670 (movR64R64Effect 0x11c670 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x11c670 (fun s => s.RIP = 0x11c670) (movR64R64Effect 0x11c670 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x11c673 (movR64R64Effect 0x11c673 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x11c673 (fun s => s.RIP = 0x11c673) (movR64R64Effect 0x11c673 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c676 (repMovsqEffect 0x11c676) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11c676 (repMovsqEffect 0x11c676) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[57, 55, 53, 22]
    (.letOp (n := 61) (.out 0x11c676 (repMovsqEffect 0x11c676) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[57, 55, 53, 22]
    (.letOp (n := 62) (.exec 0x11c676 (RepPre 0x11c676 (RepMovsqPre 0x11c676)) (repMovsqEffect 0x11c676) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 63) (.out 0x11c679 (xorR32R32Effect 0x11c679 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[60, 60]
    (.letOp (n := 64) (.exec 0x11c679 (fun s => s.RIP = 0x11c679) (xorR32R32Effect 0x11c679 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[60, 60]
    (.letOp (n := 65) (.out 0x11c67b (cmpR8Imm8Effect 0x11c67b 4 13 0x7) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[13]
    (.letOp (n := 66) (.exec 0x11c67b (fun s => s.RIP = 0x11c67b) (cmpR8Imm8Effect 0x11c67b 4 13 0x7) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 67) (.out 0x11c67f (atFlags (condHolds 4) (setccR8Effect 0x11c67f 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[63, 65]
    (.letOp (n := 68) (.exec 0x11c67f (fun s => s.RIP = 0x11c67f) (atFlags (condHolds 4) (setccR8Effect 0x11c67f 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[63, 65]
    (.letOp (n := 69) (.out 0x11c683 (callEffect (fun _ => 0x127d50) 0x11c688) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x11c683 (PushPre 0x11c683 5) (callEffect (fun _ => 0x127d50) 0x11c688) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x11c688⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l11c688, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l11c66b : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0xF3, 0x48, 0xA5, 0x31, 0xFF,
    0x41, 0x80, 0xFD, 0x07, 0x40, 0x0F, 0x94, 0xC7, 0xE8, 0xC8, 0xB6, 0x00, 0x00]

theorem code_l11c66b : ∀ x ∈ codeRange 0x11c66b bytes_l11c66b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c66b 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c688 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c688 (leaR64Effect 0x11c688 2 (.base 15 (.d32 0x2d0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 54) (.exec 0x11c688 (fun s => s.RIP = 0x11c688) (leaR64Effect 0x11c688 2 (.base 15 (.d32 0x2d0))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x11c68f (movzxR32R8Effect 0x11c68f 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 56) (.exec 0x11c68f (fun s => s.RIP = 0x11c68f) (movzxR32R8Effect 0x11c68f 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x11c692 (movR64R64Effect 0x11c692 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 58) (.exec 0x11c692 (fun s => s.RIP = 0x11c692) (movR64R64Effect 0x11c692 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c695 (movR64R64Effect 0x11c695 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x11c695 (fun s => s.RIP = 0x11c695) (movR64R64Effect 0x11c695 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x11c698 (callEffect (fun _ => 0x10fcc0) 0x11c69d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x11c698 (PushPre 0x11c698 5) (callEffect (fun _ => 0x10fcc0) 0x11c69d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x11c69d⟩) #v[]
    (.terminate (.call ⟨.l10fcc0, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l11c69d, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l11c688 : List UInt8 :=
  [0x49, 0x8D, 0x97, 0xD0, 0x02, 0x00, 0x00, 0x0F, 0xB6, 0xC8, 0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xF6,
    0xE8, 0x23, 0x36, 0xFF, 0xFF]

theorem code_l11c688 : ∀ x ∈ codeRange 0x11c688 bytes_l11c688, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c688 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c69d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c69d (movR32Imm32Effect 0x11c69d 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11c69d (fun s => s.RIP = 0x11c69d) (movR32Imm32Effect 0x11c69d 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11c6a2 (movR64R64Effect 0x11c6a2 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x11c6a2 (fun s => s.RIP = 0x11c6a2) (movR64R64Effect 0x11c6a2 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x11c6a5 (movR64R64Effect 0x11c6a5 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x11c6a5 (fun s => s.RIP = 0x11c6a5) (movR64R64Effect 0x11c6a5 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c6a8 (repMovsqEffect 0x11c6a8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11c6a8 (repMovsqEffect 0x11c6a8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[57, 55, 53, 22]
    (.letOp (n := 61) (.out 0x11c6a8 (repMovsqEffect 0x11c6a8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[57, 55, 53, 22]
    (.letOp (n := 62) (.exec 0x11c6a8 (RepPre 0x11c6a8 (RepMovsqPre 0x11c6a8)) (repMovsqEffect 0x11c6a8) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 63) (.out 0x11c6ab (xorR32R32Effect 0x11c6ab 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[60, 60]
    (.letOp (n := 64) (.exec 0x11c6ab (fun s => s.RIP = 0x11c6ab) (xorR32R32Effect 0x11c6ab 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[60, 60]
    (.letOp (n := 65) (.out 0x11c6ad (cmpR8Imm8Effect 0x11c6ad 4 13 0x8) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[13]
    (.letOp (n := 66) (.exec 0x11c6ad (fun s => s.RIP = 0x11c6ad) (cmpR8Imm8Effect 0x11c6ad 4 13 0x8) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 67) (.out 0x11c6b1 (atFlags (condHolds 4) (setccR8Effect 0x11c6b1 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[63, 65]
    (.letOp (n := 68) (.exec 0x11c6b1 (fun s => s.RIP = 0x11c6b1) (atFlags (condHolds 4) (setccR8Effect 0x11c6b1 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[63, 65]
    (.letOp (n := 69) (.out 0x11c6b5 (callEffect (fun _ => 0x127d50) 0x11c6ba) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x11c6b5 (PushPre 0x11c6b5 5) (callEffect (fun _ => 0x127d50) 0x11c6ba) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x11c6ba⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 59), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l11c6ba, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l11c69d : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0xF3, 0x48, 0xA5, 0x31, 0xFF,
    0x41, 0x80, 0xFD, 0x08, 0x40, 0x0F, 0x94, 0xC7, 0xE8, 0x96, 0xB6, 0x00, 0x00]

theorem code_l11c69d : ∀ x ∈ codeRange 0x11c69d bytes_l11c69d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c69d 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c6ba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c6ba (addR64Imm32Effect 0x11c6ba 15 0x348) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 54) (.exec 0x11c6ba (fun s => s.RIP = 0x11c6ba) (addR64Imm32Effect 0x11c6ba 15 0x348) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x11c6c1 (movzxR32R8Effect 0x11c6c1 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 56) (.exec 0x11c6c1 (fun s => s.RIP = 0x11c6c1) (movzxR32R8Effect 0x11c6c1 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x11c6c4 (movR64R64Effect 0x11c6c4 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 58) (.exec 0x11c6c4 (fun s => s.RIP = 0x11c6c4) (movR64R64Effect 0x11c6c4 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c6c7 (movR64R64Effect 0x11c6c7 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x11c6c7 (fun s => s.RIP = 0x11c6c7) (movR64R64Effect 0x11c6c7 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x11c6ca (movR64R64Effect 0x11c6ca 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 62) (.exec 0x11c6ca (fun s => s.RIP = 0x11c6ca) (movR64R64Effect 0x11c6ca 2 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 63) (.out 0x11c6cd (callEffect (fun _ => 0x10fcc0) 0x11c6d2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x11c6cd (PushPre 0x11c6cd 5) (callEffect (fun _ => 0x10fcc0) 0x11c6d2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x11c6d2⟩) #v[]
    (.terminate (.call ⟨.l10fcc0, RegMap.args [(0, 0), (1, 55), (2, 61), (3, 3), (4, 63), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l11c6d2, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l11c6ba : List UInt8 :=
  [0x49, 0x81, 0xC7, 0x48, 0x03, 0x00, 0x00, 0x0F, 0xB6, 0xC8, 0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xF6,
    0x4C, 0x89, 0xFA, 0xE8, 0xEE, 0x35, 0xFF, 0xFF]

theorem code_l11c6ba : ∀ x ∈ codeRange 0x11c6ba bytes_l11c6ba, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c6ba 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c6d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c6d2 (movR32Imm32Effect 0x11c6d2 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11c6d2 (fun s => s.RIP = 0x11c6d2) (movR32Imm32Effect 0x11c6d2 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11c6d7 (movR64R64Effect 0x11c6d7 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x11c6d7 (fun s => s.RIP = 0x11c6d7) (movR64R64Effect 0x11c6d7 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x11c6da (movR64R64Effect 0x11c6da 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x11c6da (fun s => s.RIP = 0x11c6da) (movR64R64Effect 0x11c6da 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c6dd (repMovsqEffect 0x11c6dd) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11c6dd (repMovsqEffect 0x11c6dd) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[57, 55, 53, 22]
    (.letOp (n := 61) (.exec 0x11c6dd (RepPre 0x11c6dd (RepMovsqPre 0x11c6dd)) (repMovsqEffect 0x11c6dd) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 62) (.out 0x11c6e0 (shrR8Effect 0x11c6e0 4 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 63) (.exec 0x11c6e0 (fun s => s.RIP = 0x11c6e0) (shrR8Effect 0x11c6e0 4 5 7) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 64) (.out 0x11c6e4 (movzxR32R8Effect 0x11c6e4 4 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 65) (.exec 0x11c6e4 (fun s => s.RIP = 0x11c6e4) (movzxR32R8Effect 0x11c6e4 4 7 5) (Reg.operands [.gpr 5] [])) #v[62]
    (.letOp (n := 66) (.out 0x11c6e8 (callEffect (fun _ => 0x127d50) 0x11c6ed) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 67) (.exec 0x11c6e8 (PushPre 0x11c6e8 5) (callEffect (fun _ => 0x127d50) 0x11c6ed) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.const ⟨64, 0x11c6ed⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 60), (2, 2), (3, 3), (4, 66), (5, 62), (6, 59), (7, 64), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l11c6ed, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l11c6d2 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0xF3, 0x48, 0xA5, 0x40, 0xC0,
    0xED, 0x07, 0x40, 0x0F, 0xB6, 0xFD, 0xE8, 0x63, 0xB6, 0x00, 0x00]

theorem code_l11c6d2 : ∀ x ∈ codeRange 0x11c6d2 bytes_l11c6d2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c6d2 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c6ed_3 : Block Op Label signature Reg.count 158 :=
  .letOp (n := 158) (.out 0x11c83d (movR64R64Effect 0x11c83d 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 159) (.exec 0x11c83d (fun s => s.RIP = 0x11c83d) (movR64R64Effect 0x11c83d 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 160) (.out 0x11c840 (callEffect (fun _ => 0x10fcc0) 0x11c845) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 161) (.exec 0x11c840 (PushPre 0x11c840 5) (callEffect (fun _ => 0x10fcc0) 0x11c845) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 162) (.const ⟨64, 0x11c845⟩) #v[]
    (.terminate (.call ⟨.l10fcc0, RegMap.args [(0, 0), (1, 150), (2, 154), (3, 3), (4, 160), (5, 5), (6, 158), (7, 156), (8, 113), (9, 135), (10, 143), (12, 12), (13, 13), (14, 14), (15, 152), (22, 22), (39, 39), (50, 50), (51, 51)] 163⟩ { target := .l11c845, kept := #v[], arity := rfl, guard := some (Fin.last 162) }))))))

def bytes_l11c6ed_3 : List UInt8 :=
  [0x4C, 0x89, 0xF6, 0xE8, 0x7B, 0x34, 0xFF, 0xFF]

theorem code_l11c6ed_3 : ∀ x ∈ codeRange 0x11c83d bytes_l11c6ed_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c83d 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c6ed_2 : Block Op Label signature Reg.count 123 :=
  .letOp (n := 123) (.out 0x11c7dd (addR64R64Effect 0x11c7dd 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[121, 109]
    (.letOp (n := 124) (.exec 0x11c7dd (fun s => s.RIP = 0x11c7dd) (addR64R64Effect 0x11c7dd 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[121, 109]
    (.letOp (n := 125) (.out 0x11c7e0 (movR64R64Effect 0x11c7e0 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[123]
    (.letOp (n := 126) (.exec 0x11c7e0 (fun s => s.RIP = 0x11c7e0) (movR64R64Effect 0x11c7e0 10 9) (Reg.operands [.gpr 9] [])) #v[123]
    (.letOp (n := 127) (.out 0x11c7e3 (shrR64Effect 0x11c7e3 4 10 52) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[125]
    (.letOp (n := 128) (.exec 0x11c7e3 (fun s => s.RIP = 0x11c7e3) (shrR64Effect 0x11c7e3 4 10 52) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[125]
    (.letOp (n := 129) (.out 0x11c7e7 (subR64M64Effect 0x11c7e7 10 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[127, 4]
    (.letOp (n := 130) (.exec 0x11c7e7 (LoadPre 0x11c7e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11c7e7 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c7e7 10 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[127, 4]
    (.letOp (n := 131) (.out 0x11c7ec (andR64R64Effect 0x11c7ec 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[111, 113]
    (.letOp (n := 132) (.exec 0x11c7ec (fun s => s.RIP = 0x11c7ec) (andR64R64Effect 0x11c7ec 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[111, 113]
    (.letOp (n := 133) (.out 0x11c7ef (addR64R64Effect 0x11c7ef 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[129, 109]
    (.letOp (n := 134) (.exec 0x11c7ef (fun s => s.RIP = 0x11c7ef) (addR64R64Effect 0x11c7ef 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[129, 109]
    (.letOp (n := 135) (.out 0x11c7f2 (andR64R64Effect 0x11c7f2 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[123, 113]
    (.letOp (n := 136) (.exec 0x11c7f2 (fun s => s.RIP = 0x11c7f2) (andR64R64Effect 0x11c7f2 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[123, 113]
    (.letOp (n := 137) (.out 0x11c7f5 (movR64R64Effect 0x11c7f5 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 10] []) (.reg (.gpr 7))) #v[133]
    (.letOp (n := 138) (.exec 0x11c7f5 (fun s => s.RIP = 0x11c7f5) (movR64R64Effect 0x11c7f5 7 10) (Reg.operands [.gpr 10] [])) #v[133]
    (.letOp (n := 139) (.out 0x11c7f8 (shrR64Effect 0x11c7f8 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[137]
    (.letOp (n := 140) (.exec 0x11c7f8 (fun s => s.RIP = 0x11c7f8) (shrR64Effect 0x11c7f8 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[137]
    (.letOp (n := 141) (.out 0x11c7fc (addR64R64Effect 0x11c7fc 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[139, 88]
    (.letOp (n := 142) (.exec 0x11c7fc (fun s => s.RIP = 0x11c7fc) (addR64R64Effect 0x11c7fc 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[139, 88]
    (.letOp (n := 143) (.out 0x11c7ff (andR64R64Effect 0x11c7ff 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[133, 113]
    (.letOp (n := 144) (.exec 0x11c7ff (fun s => s.RIP = 0x11c7ff) (andR64R64Effect 0x11c7ff 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[133, 113]
    (.letOp (n := 145) (.exec 0x11c802 (StorePre 0x11c802 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11c802 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c802 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[115, 4]
    (.letOp (n := 146) (.exec 0x11c80a (StorePre 0x11c80a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11c80a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c80a 6 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[131, 4]
    (.letOp (n := 147) (.exec 0x11c812 (StorePre 0x11c812 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11c812 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c812 9 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[135, 4]
    (.letOp (n := 148) (.exec 0x11c81a (StorePre 0x11c81a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11c81a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c81a 10 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[143, 4]
    (.letOp (n := 149) (.exec 0x11c822 (StorePre 0x11c822 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11c822 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c822 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[141, 4]
    (.letOp (n := 150) (.out 0x11c82a (movzxR32R8Effect 0x11c82a 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 151) (.exec 0x11c82a (fun s => s.RIP = 0x11c82a) (movzxR32R8Effect 0x11c82a 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 152) (.out 0x11c82d (leaR64Effect 0x11c82d 15 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 153) (.exec 0x11c82d (fun s => s.RIP = 0x11c82d) (leaR64Effect 0x11c82d 15 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 154) (.out 0x11c835 (leaR64Effect 0x11c835 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 155) (.exec 0x11c835 (fun s => s.RIP = 0x11c835) (leaR64Effect 0x11c835 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 156) (.out 0x11c83a (movR64R64Effect 0x11c83a 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[152]
    (.letOp (n := 157) (.exec 0x11c83a (fun s => s.RIP = 0x11c83a) (movR64R64Effect 0x11c83a 7 15) (Reg.operands [.gpr 15] [])) #v[152]
    (b_l11c6ed_3)))))))))))))))))))))))))))))))))))

def bytes_l11c6ed_2 : List UInt8 :=
  [0x49, 0x01, 0xF9, 0x4D, 0x89, 0xCA, 0x49, 0xC1, 0xEA, 0x34, 0x4C, 0x2B, 0x54, 0x24, 0x40, 0x4C,
    0x21, 0xC6, 0x49, 0x01, 0xFA, 0x4D, 0x21, 0xC1, 0x4C, 0x89, 0xD7, 0x48, 0xC1, 0xEF, 0x34, 0x48,
    0x01, 0xCF, 0x4D, 0x21, 0xC2, 0x48, 0x89, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xB4,
    0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x94,
    0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0xC8,
    0x4C, 0x8D, 0xBC, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x54, 0x24, 0x78, 0x4C, 0x89, 0xFF] ++ bytes_l11c6ed_3

theorem code_l11c6ed_2 : ∀ x ∈ codeRange 0x11c7dd bytes_l11c6ed_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1c7dd 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11c6ed_3

@[cfg_block] def b_l11c6ed_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x11c76d (subR64M64Effect 0x11c76d 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[82, 4]
    (.letOp (n := 85) (.exec 0x11c76d (LoadPre 0x11c76d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11c76d + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c76d 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[82, 4]
    (.letOp (n := 86) (.out 0x11c772 (movR64Imm64Effect 0x11c772 1 0xffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 87) (.exec 0x11c772 (fun s => s.RIP = 0x11c772) (movR64Imm64Effect 0x11c772 1 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 88) (.out 0x11c77c (andR64R64Effect 0x11c77c 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[86, 84]
    (.letOp (n := 89) (.exec 0x11c77c (fun s => s.RIP = 0x11c77c) (andR64R64Effect 0x11c77c 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[86, 84]
    (.letOp (n := 90) (.out 0x11c77f (shrR64Effect 0x11c77f 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[84]
    (.letOp (n := 91) (.exec 0x11c77f (fun s => s.RIP = 0x11c77f) (shrR64Effect 0x11c77f 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[84]
    (.letOp (n := 92) (.out 0x11c783 (movR64Imm64Effect 0x11c783 7 0x1000003d1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 93) (.exec 0x11c783 (fun s => s.RIP = 0x11c783) (movR64Imm64Effect 0x11c783 7 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 94) (.out 0x11c78d (imulR64R64Effect 0x11c78d 4 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[92, 90]
    (.letOp (n := 95) (.exec 0x11c78d (fun s => s.RIP = 0x11c78d) (imulR64R64Effect 0x11c78d 4 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[92, 90]
    (.letOp (n := 96) (.out 0x11c791 (subR64M64Effect 0x11c791 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[94, 4]
    (.letOp (n := 97) (.exec 0x11c791 (LoadPre 0x11c791 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11c791 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c791 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[94, 4]
    (.letOp (n := 98) (.exec 0x11c796 (StorePre 0x11c796 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11c796 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c796 2 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 99) (.out 0x11c79e (movR64Imm64Effect 0x11c79e 2 0x3ffffbfffff0bc) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 100) (.exec 0x11c79e (fun s => s.RIP = 0x11c79e) (movR64Imm64Effect 0x11c79e 2 0x3ffffbfffff0bc) (Reg.operands [] [])) #v[]
    (.letOp (n := 101) (.out 0x11c7a8 (addR64R64Effect 0x11c7a8 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[99, 96]
    (.letOp (n := 102) (.exec 0x11c7a8 (fun s => s.RIP = 0x11c7a8) (addR64R64Effect 0x11c7a8 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[99, 96]
    (.letOp (n := 103) (.out 0x11c7ab (movR64R64Effect 0x11c7ab 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[101]
    (.letOp (n := 104) (.exec 0x11c7ab (fun s => s.RIP = 0x11c7ab) (movR64R64Effect 0x11c7ab 6 2) (Reg.operands [.gpr 2] [])) #v[101]
    (.letOp (n := 105) (.out 0x11c7ae (shrR64Effect 0x11c7ae 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[103]
    (.letOp (n := 106) (.exec 0x11c7ae (fun s => s.RIP = 0x11c7ae) (shrR64Effect 0x11c7ae 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[103]
    (.letOp (n := 107) (.out 0x11c7b2 (subR64M64Effect 0x11c7b2 6 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[105, 4]
    (.letOp (n := 108) (.exec 0x11c7b2 (LoadPre 0x11c7b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11c7b2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c7b2 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[105, 4]
    (.letOp (n := 109) (.out 0x11c7b7 (movR64Imm64Effect 0x11c7b7 7 0x3ffffffffffffc) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 110) (.exec 0x11c7b7 (fun s => s.RIP = 0x11c7b7) (movR64Imm64Effect 0x11c7b7 7 0x3ffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 111) (.out 0x11c7c1 (addR64R64Effect 0x11c7c1 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[107, 109]
    (.letOp (n := 112) (.exec 0x11c7c1 (fun s => s.RIP = 0x11c7c1) (addR64R64Effect 0x11c7c1 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[107, 109]
    (.letOp (n := 113) (.out 0x11c7c4 (movR64Imm64Effect 0x11c7c4 8 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 114) (.exec 0x11c7c4 (fun s => s.RIP = 0x11c7c4) (movR64Imm64Effect 0x11c7c4 8 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 115) (.out 0x11c7ce (andR64R64Effect 0x11c7ce 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[101, 113]
    (.letOp (n := 116) (.exec 0x11c7ce (fun s => s.RIP = 0x11c7ce) (andR64R64Effect 0x11c7ce 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[101, 113]
    (.letOp (n := 117) (.out 0x11c7d1 (movR64R64Effect 0x11c7d1 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[111]
    (.letOp (n := 118) (.exec 0x11c7d1 (fun s => s.RIP = 0x11c7d1) (movR64R64Effect 0x11c7d1 9 6) (Reg.operands [.gpr 6] [])) #v[111]
    (.letOp (n := 119) (.out 0x11c7d4 (shrR64Effect 0x11c7d4 4 9 52) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[117]
    (.letOp (n := 120) (.exec 0x11c7d4 (fun s => s.RIP = 0x11c7d4) (shrR64Effect 0x11c7d4 4 9 52) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[117]
    (.letOp (n := 121) (.out 0x11c7d8 (subR64M64Effect 0x11c7d8 9 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[119, 4]
    (.letOp (n := 122) (.exec 0x11c7d8 (LoadPre 0x11c7d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11c7d8 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11c7d8 9 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[119, 4]
    (b_l11c6ed_2)))))))))))))))))))))))))))))))))))))))

def bytes_l11c6ed_1 : List UInt8 :=
  [0x48, 0x2B, 0x74, 0x24, 0x48, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48,
    0x21, 0xF1, 0x48, 0xC1, 0xEE, 0x30, 0x48, 0xBF, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
    0x48, 0x0F, 0xAF, 0xFE, 0x48, 0x2B, 0x7C, 0x24, 0x28, 0x48, 0x89, 0x94, 0x24, 0xE8, 0x00, 0x00,
    0x00, 0x48, 0xBA, 0xBC, 0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00, 0x48, 0x01, 0xFA, 0x48, 0x89,
    0xD6, 0x48, 0xC1, 0xEE, 0x34, 0x48, 0x2B, 0x74, 0x24, 0x30, 0x48, 0xBF, 0xFC, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x3F, 0x00, 0x48, 0x01, 0xFE, 0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F,
    0x00, 0x4C, 0x21, 0xC2, 0x49, 0x89, 0xF1, 0x49, 0xC1, 0xE9, 0x34, 0x4C, 0x2B, 0x4C, 0x24, 0x38] ++ bytes_l11c6ed_2

theorem code_l11c6ed_1 : ∀ x ∈ codeRange 0x11c76d bytes_l11c6ed_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1c76d 112 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11c6ed_2

@[cfg_block] def b_l11c6ed : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c6ed (movR64M64Effect 0x11c6ed 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x11c6ed (LoadPre 0x11c6ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11c6ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c6ed 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11c6f2 (StorePre 0x11c6f2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11c6f2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c6f2 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11c6fa (movR64M64Effect 0x11c6fa 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x11c6fa (LoadPre 0x11c6fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11c6fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c6fa 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11c6ff (StorePre 0x11c6ff 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11c6ff + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c6ff 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11c707 (movR64M64Effect 0x11c707 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x11c707 (LoadPre 0x11c707 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11c707 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c707 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11c70c (StorePre 0x11c70c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11c70c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c70c 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11c714 (movR64M64Effect 0x11c714 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x11c714 (LoadPre 0x11c714 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11c714 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c714 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11c718 (movR64M64Effect 0x11c718 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x11c718 (LoadPre 0x11c718 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c718 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c718 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11c71d (StorePre 0x11c71d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11c71d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c71d 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11c725 (StorePre 0x11c725 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11c725 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c725 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11c72a (movR64M64Effect 0x11c72a 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 69) (.exec 0x11c72a (LoadPre 0x11c72a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11c72a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c72a 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x11c72f (StorePre 0x11c72f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11c72f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c72f 1 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x11c737 (movR64M64Effect 0x11c737 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 72) (.exec 0x11c737 (LoadPre 0x11c737 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11c737 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c737 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x11c73c (StorePre 0x11c73c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11c73c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c73c 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x11c744 (movR64M64Effect 0x11c744 1 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 75) (.exec 0x11c744 (LoadPre 0x11c744 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11c744 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c744 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x11c749 (StorePre 0x11c749 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11c749 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c749 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x11c751 (movR64M64Effect 0x11c751 1 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 78) (.exec 0x11c751 (LoadPre 0x11c751 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11c751 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c751 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x11c756 (StorePre 0x11c756 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x11c756 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c756 1 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[77, 4]
    (.letOp (n := 80) (.out 0x11c75e (movR64M64Effect 0x11c75e 2 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 81) (.exec 0x11c75e (LoadPre 0x11c75e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11c75e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11c75e 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.out 0x11c763 (movR64Imm64Effect 0x11c763 6 0x3fffffffffffc) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 83) (.exec 0x11c763 (fun s => s.RIP = 0x11c763) (movR64Imm64Effect 0x11c763 6 0x3fffffffffffc) (Reg.operands [] [])) #v[]
    (b_l11c6ed_1)))))))))))))))))))))))))))))))

def bytes_l11c6ed : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x20, 0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C,
    0x24, 0x18, 0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48,
    0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x0C, 0x24, 0x48, 0x8B, 0x54, 0x24, 0x08,
    0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x78, 0x48, 0x8B, 0x4C,
    0x24, 0x50, 0x48, 0x89, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0x48,
    0x89, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x60, 0x48, 0x89, 0x8C, 0x24,
    0xD8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x68, 0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x54, 0x24, 0x70, 0x48, 0xBE, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00] ++ bytes_l11c6ed_1

theorem code_l11c6ed : ∀ x ∈ codeRange 0x11c6ed bytes_l11c6ed, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1c6ed 128 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11c6ed_1

end K256.Proofs.Verify.LIR
