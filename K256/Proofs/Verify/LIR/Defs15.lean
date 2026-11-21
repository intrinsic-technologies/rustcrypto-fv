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

def b_l11d880_83 : Block Op Label signature Reg.count 3583 :=
  .letOp (n := 3583) (.out 0x11f5bc (shrR64Effect 0x11f5bc 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3581]
    (.letOp (n := 3584) (.exec 0x11f5bc (fun s => s.RIP = 0x11f5bc) (shrR64Effect 0x11f5bc 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3581]
    (.letOp (n := 3585) (.out 0x11f5c0 (addR64R64Effect 0x11f5c0 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[3583, 3576]
    (.letOp (n := 3586) (.exec 0x11f5c0 (fun s => s.RIP = 0x11f5c0) (addR64R64Effect 0x11f5c0 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3583, 3576]
    (.letOp (n := 3587) (.out 0x11f5c3 (andR64R64Effect 0x11f5c3 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[3568, 3474]
    (.letOp (n := 3588) (.exec 0x11f5c3 (fun s => s.RIP = 0x11f5c3) (andR64R64Effect 0x11f5c3 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[3568, 3474]
    (.letOp (n := 3589) (.exec 0x11f5c6 (StorePre 0x11f5c6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x11f5c6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f5c6 8 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[3587, 4]
    (.letOp (n := 3590) (.exec 0x11f5ce (StorePre 0x11f5ce 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x11f5ce + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f5ce 1 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[3585, 4]
    (.letOp (n := 3591) (.out 0x11f5d6 (movR32M32LowEffect 0x11f5d6 1 (.sib 4 none 0 (.d32 0x1bc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 3592) (.exec 0x11f5d6 (LoadPre 0x11f5d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1bc)) s (0x11f5d6 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x11f5d6 1 (.sib 4 none 0 (.d32 0x1bc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3593) (.out 0x11f5dd (decR32Effect 0x11f5dd 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3591]
    (.letOp (n := 3594) (.out 0x11f5dd (decR32Effect 0x11f5dd 2 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[3591]
    (.letOp (n := 3595) (.exec 0x11f5dd (fun s => s.RIP = 0x11f5dd) (decR32Effect 0x11f5dd 2 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3591]
    (.letOp (n := 3596) (.pure (condOp 5)) #v[3594]
    (.terminate (.condBr (Fin.last 3596) ⟨.l11d810, RegMap.args [(0, 3576), (1, 3593), (2, 3573), (3, 3344), (4, 4), (5, 3420), (6, 3556), (7, 3578), (8, 3587), (9, 3526), (10, 3504), (11, 3483), (12, 3449), (13, 3474), (14, 3476), (15, 3472), (19, 3594), (22, 22), (39, 39), (50, 50), (51, 51)] 3597⟩ ⟨.l11f5e5, RegMap.args [(0, 3576), (1, 3593), (2, 3573), (3, 3344), (4, 4), (5, 3420), (6, 3556), (7, 3578), (8, 3587), (9, 3526), (10, 3504), (11, 3483), (12, 3449), (13, 3474), (14, 3476), (15, 3472), (19, 3594), (22, 22), (39, 39), (50, 50), (51, 51)] 3597⟩)))))))))))))))

def bytes_l11d880_83 : List UInt8 :=
  [0x48, 0xC1, 0xE9, 0x34, 0x48, 0x01, 0xC1, 0x4D, 0x21, 0xE8, 0x4C, 0x89, 0x84, 0x24, 0x68, 0x01,
    0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0x70, 0x01, 0x00, 0x00, 0x8B, 0x8C, 0x24, 0xBC, 0x01, 0x00,
    0x00, 0xFF, 0xC9, 0x0F, 0x85, 0x2B, 0xE2, 0xFF, 0xFF]

theorem code_l11d880_83 : ∀ x ∈ codeRange 0x11f5bc bytes_l11d880_83, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f5bc 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l11d880_82 : Block Op Label signature Reg.count 3546 :=
  .letOp (n := 3546) (.out 0x11f568 (shrR64Effect 0x11f568 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3544]
    (.letOp (n := 3547) (.exec 0x11f568 (fun s => s.RIP = 0x11f568) (shrR64Effect 0x11f568 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3544]
    (.letOp (n := 3548) (.out 0x11f56c (addR64R64Effect 0x11f56c 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[3546, 3520]
    (.letOp (n := 3549) (.exec 0x11f56c (fun s => s.RIP = 0x11f56c) (addR64R64Effect 0x11f56c 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[3546, 3520]
    (.letOp (n := 3550) (.out 0x11f56f (andR64R64Effect 0x11f56f 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[3494, 3474]
    (.letOp (n := 3551) (.exec 0x11f56f (fun s => s.RIP = 0x11f56f) (andR64R64Effect 0x11f56f 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[3494, 3474]
    (.letOp (n := 3552) (.out 0x11f572 (movR64M64Effect 0x11f572 7 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 3553) (.exec 0x11f572 (LoadPre 0x11f572 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11f572 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f572 7 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3554) (.out 0x11f57a (leaR64Effect 0x11f57a 6 (.sib 6 (some 7) 3 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[3550, 3552]
    (.letOp (n := 3555) (.exec 0x11f57a (fun s => s.RIP = 0x11f57a) (leaR64Effect 0x11f57a 6 (.sib 6 (some 7) 3 .none)) (Reg.operands [.gpr 6, .gpr 7] [])) #v[3550, 3552]
    (.letOp (n := 3556) (.out 0x11f57e (subR64R64Effect 0x11f57e 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[3554, 3552]
    (.letOp (n := 3557) (.exec 0x11f57e (fun s => s.RIP = 0x11f57e) (subR64R64Effect 0x11f57e 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[3554, 3552]
    (.letOp (n := 3558) (.out 0x11f581 (movR64R64Effect 0x11f581 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[3548]
    (.letOp (n := 3559) (.exec 0x11f581 (fun s => s.RIP = 0x11f581) (movR64R64Effect 0x11f581 7 2) (Reg.operands [.gpr 2] [])) #v[3548]
    (.letOp (n := 3560) (.out 0x11f584 (shrR64Effect 0x11f584 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3558]
    (.letOp (n := 3561) (.exec 0x11f584 (fun s => s.RIP = 0x11f584) (shrR64Effect 0x11f584 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3558]
    (.letOp (n := 3562) (.out 0x11f588 (addR64R64Effect 0x11f588 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[3560, 3526]
    (.letOp (n := 3563) (.exec 0x11f588 (fun s => s.RIP = 0x11f588) (addR64R64Effect 0x11f588 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[3560, 3526]
    (.letOp (n := 3564) (.out 0x11f58b (movR64R64Effect 0x11f58b 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[3562]
    (.letOp (n := 3565) (.exec 0x11f58b (fun s => s.RIP = 0x11f58b) (movR64R64Effect 0x11f58b 8 7) (Reg.operands [.gpr 7] [])) #v[3562]
    (.letOp (n := 3566) (.out 0x11f58e (shrR64Effect 0x11f58e 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[3564]
    (.letOp (n := 3567) (.exec 0x11f58e (fun s => s.RIP = 0x11f58e) (shrR64Effect 0x11f58e 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3564]
    (.letOp (n := 3568) (.out 0x11f592 (addR64R64Effect 0x11f592 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[3566, 3556]
    (.letOp (n := 3569) (.exec 0x11f592 (fun s => s.RIP = 0x11f592) (addR64R64Effect 0x11f592 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[3566, 3556]
    (.letOp (n := 3570) (.out 0x11f595 (andR64R64Effect 0x11f595 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[3542, 3474]
    (.letOp (n := 3571) (.exec 0x11f595 (fun s => s.RIP = 0x11f595) (andR64R64Effect 0x11f595 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[3542, 3474]
    (.letOp (n := 3572) (.exec 0x11f598 (StorePre 0x11f598 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x11f598 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f598 1 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[3570, 4]
    (.letOp (n := 3573) (.out 0x11f5a0 (andR64R64Effect 0x11f5a0 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[3548, 3474]
    (.letOp (n := 3574) (.exec 0x11f5a0 (fun s => s.RIP = 0x11f5a0) (andR64R64Effect 0x11f5a0 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[3548, 3474]
    (.letOp (n := 3575) (.exec 0x11f5a3 (StorePre 0x11f5a3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x11f5a3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f5a3 2 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3573, 4]
    (.letOp (n := 3576) (.out 0x11f5ab (andR64R64Effect 0x11f5ab 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[3532, 3504]
    (.letOp (n := 3577) (.exec 0x11f5ab (fun s => s.RIP = 0x11f5ab) (andR64R64Effect 0x11f5ab 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[3532, 3504]
    (.letOp (n := 3578) (.out 0x11f5ae (andR64R64Effect 0x11f5ae 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[3562, 3474]
    (.letOp (n := 3579) (.exec 0x11f5ae (fun s => s.RIP = 0x11f5ae) (andR64R64Effect 0x11f5ae 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[3562, 3474]
    (.letOp (n := 3580) (.exec 0x11f5b1 (StorePre 0x11f5b1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x11f5b1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f5b1 7 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[3578, 4]
    (.letOp (n := 3581) (.out 0x11f5b9 (movR64R64Effect 0x11f5b9 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[3568]
    (.letOp (n := 3582) (.exec 0x11f5b9 (fun s => s.RIP = 0x11f5b9) (movR64R64Effect 0x11f5b9 1 8) (Reg.operands [.gpr 8] [])) #v[3568]
    (b_l11d880_83)))))))))))))))))))))))))))))))))))))

def bytes_l11d880_82 : List UInt8 :=
  [0x48, 0xC1, 0xEA, 0x34, 0x4C, 0x01, 0xC2, 0x4C, 0x21, 0xEE, 0x48, 0x8B, 0xBC, 0x24, 0xE8, 0x00,
    0x00, 0x00, 0x48, 0x8D, 0x34, 0xFE, 0x48, 0x29, 0xFE, 0x48, 0x89, 0xD7, 0x48, 0xC1, 0xEF, 0x34,
    0x4C, 0x01, 0xCF, 0x49, 0x89, 0xF8, 0x49, 0xC1, 0xE8, 0x34, 0x49, 0x01, 0xF0, 0x4C, 0x21, 0xE9,
    0x48, 0x89, 0x8C, 0x24, 0x50, 0x01, 0x00, 0x00, 0x4C, 0x21, 0xEA, 0x48, 0x89, 0x94, 0x24, 0x58,
    0x01, 0x00, 0x00, 0x4C, 0x21, 0xD0, 0x4C, 0x21, 0xEF, 0x48, 0x89, 0xBC, 0x24, 0x60, 0x01, 0x00,
    0x00, 0x4C, 0x89, 0xC1] ++ bytes_l11d880_83

theorem code_l11d880_82 : ∀ x ∈ codeRange 0x11f568 bytes_l11d880_82, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f568 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_83

def b_l11d880_81 : Block Op Label signature Reg.count 3506 :=
  .letOp (n := 3506) (.out 0x11f50b (andR64R64Effect 0x11f50b 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[3175, 3504]
    (.letOp (n := 3507) (.exec 0x11f50b (fun s => s.RIP = 0x11f50b) (andR64R64Effect 0x11f50b 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[3175, 3504]
    (.letOp (n := 3508) (.out 0x11f50e (addR64R64Effect 0x11f50e 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[3506, 3502]
    (.letOp (n := 3509) (.exec 0x11f50e (fun s => s.RIP = 0x11f50e) (addR64R64Effect 0x11f50e 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[3506, 3502]
    (.letOp (n := 3510) (.out 0x11f511 (movR64M64Effect 0x11f511 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3511) (.exec 0x11f511 (LoadPre 0x11f511 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11f511 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f511 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3512) (.out 0x11f519 (leaR64Effect 0x11f519 2 (.sib 8 (some 0) 3 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[3311, 3510]
    (.letOp (n := 3513) (.exec 0x11f519 (fun s => s.RIP = 0x11f519) (leaR64Effect 0x11f519 2 (.sib 8 (some 0) 3 .none)) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3311, 3510]
    (.letOp (n := 3514) (.out 0x11f51d (subR64R64Effect 0x11f51d 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3512, 3510]
    (.letOp (n := 3515) (.exec 0x11f51d (fun s => s.RIP = 0x11f51d) (subR64R64Effect 0x11f51d 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3512, 3510]
    (.letOp (n := 3516) (.out 0x11f520 (movR64M64Effect 0x11f520 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3517) (.exec 0x11f520 (LoadPre 0x11f520 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x11f520 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f520 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3518) (.out 0x11f528 (leaR64Effect 0x11f528 8 (.sib 9 (some 0) 3 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9, .gpr 0] []) (.reg (.gpr 8))) #v[3399, 3516]
    (.letOp (n := 3519) (.exec 0x11f528 (fun s => s.RIP = 0x11f528) (leaR64Effect 0x11f528 8 (.sib 9 (some 0) 3 .none)) (Reg.operands [.gpr 9, .gpr 0] [])) #v[3399, 3516]
    (.letOp (n := 3520) (.out 0x11f52c (subR64R64Effect 0x11f52c 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[3518, 3516]
    (.letOp (n := 3521) (.exec 0x11f52c (fun s => s.RIP = 0x11f52c) (subR64R64Effect 0x11f52c 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3518, 3516]
    (.letOp (n := 3522) (.out 0x11f52f (movR64M64Effect 0x11f52f 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3523) (.exec 0x11f52f (LoadPre 0x11f52f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11f52f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f52f 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3524) (.out 0x11f537 (leaR64Effect 0x11f537 9 (.sib 11 (some 0) 3 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 11, .gpr 0] []) (.reg (.gpr 9))) #v[3483, 3522]
    (.letOp (n := 3525) (.exec 0x11f537 (fun s => s.RIP = 0x11f537) (leaR64Effect 0x11f537 9 (.sib 11 (some 0) 3 .none)) (Reg.operands [.gpr 11, .gpr 0] [])) #v[3483, 3522]
    (.letOp (n := 3526) (.out 0x11f53b (subR64R64Effect 0x11f53b 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[3524, 3522]
    (.letOp (n := 3527) (.exec 0x11f53b (fun s => s.RIP = 0x11f53b) (subR64R64Effect 0x11f53b 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[3524, 3522]
    (.letOp (n := 3528) (.out 0x11f53e (movR64M64Effect 0x11f53e 1 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 3529) (.exec 0x11f53e (LoadPre 0x11f53e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x11f53e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f53e 1 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3530) (.out 0x11f546 (leaR64Effect 0x11f546 0 (.sib 7 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 1] []) (.reg (.gpr 0))) #v[3508, 3528]
    (.letOp (n := 3531) (.exec 0x11f546 (fun s => s.RIP = 0x11f546) (leaR64Effect 0x11f546 0 (.sib 7 (some 1) 3 .none)) (Reg.operands [.gpr 7, .gpr 1] [])) #v[3508, 3528]
    (.letOp (n := 3532) (.out 0x11f54a (subR64R64Effect 0x11f54a 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3530, 3528]
    (.letOp (n := 3533) (.exec 0x11f54a (fun s => s.RIP = 0x11f54a) (subR64R64Effect 0x11f54a 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3530, 3528]
    (.letOp (n := 3534) (.out 0x11f54d (movR64R64Effect 0x11f54d 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[3532]
    (.letOp (n := 3535) (.exec 0x11f54d (fun s => s.RIP = 0x11f54d) (movR64R64Effect 0x11f54d 1 0) (Reg.operands [.gpr 0] [])) #v[3532]
    (.letOp (n := 3536) (.out 0x11f550 (shrR64Effect 0x11f550 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3534]
    (.letOp (n := 3537) (.exec 0x11f550 (fun s => s.RIP = 0x11f550) (shrR64Effect 0x11f550 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3534]
    (.letOp (n := 3538) (.out 0x11f554 (movR64Imm64Effect 0x11f554 7 0x1000003d1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 3539) (.exec 0x11f554 (fun s => s.RIP = 0x11f554) (movR64Imm64Effect 0x11f554 7 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 3540) (.out 0x11f55e (imulR64R64Effect 0x11f55e 4 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[3536, 3538]
    (.letOp (n := 3541) (.exec 0x11f55e (fun s => s.RIP = 0x11f55e) (imulR64R64Effect 0x11f55e 4 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[3536, 3538]
    (.letOp (n := 3542) (.out 0x11f562 (addR64R64Effect 0x11f562 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[3540, 3514]
    (.letOp (n := 3543) (.exec 0x11f562 (fun s => s.RIP = 0x11f562) (addR64R64Effect 0x11f562 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[3540, 3514]
    (.letOp (n := 3544) (.out 0x11f565 (movR64R64Effect 0x11f565 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[3542]
    (.letOp (n := 3545) (.exec 0x11f565 (fun s => s.RIP = 0x11f565) (movR64R64Effect 0x11f565 2 1) (Reg.operands [.gpr 1] [])) #v[3542]
    (b_l11d880_82))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_81 : List UInt8 :=
  [0x4C, 0x21, 0xD7, 0x48, 0x01, 0xD7, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x49, 0x8D,
    0x14, 0xC0, 0x48, 0x29, 0xC2, 0x48, 0x8B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x4D, 0x8D, 0x04,
    0xC1, 0x49, 0x29, 0xC0, 0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4D, 0x8D, 0x0C, 0xC3,
    0x49, 0x29, 0xC1, 0x48, 0x8B, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x04, 0xCF, 0x48,
    0x29, 0xC8, 0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x30, 0x48, 0xBF, 0xD1, 0x03, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xCF, 0x48, 0x01, 0xD1, 0x48, 0x89, 0xCA] ++ bytes_l11d880_82

theorem code_l11d880_81 : ∀ x ∈ codeRange 0x11f50b bytes_l11d880_81, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f50b 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_82

def b_l11d880_80 : Block Op Label signature Reg.count 3464 :=
  .letOp (n := 3464) (.out 0x11f4a8 (movR64M64Effect 0x11f4a8 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3465) (.exec 0x11f4a8 (LoadPre 0x11f4a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11f4a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f4a8 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3466) (.exec 0x11f4ad (StorePre 0x11f4ad 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x11f4ad + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f4ad 0 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3464, 4]
    (.letOp (n := 3467) (.out 0x11f4b5 (addR64R64Effect 0x11f4b5 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[3456, 3395]
    (.letOp (n := 3468) (.out 0x11f4b5 (addR64R64Effect 0x11f4b5 11 10) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 10] []) (.flag .CF)) #v[3456, 3395]
    (.letOp (n := 3469) (.exec 0x11f4b5 (fun s => s.RIP = 0x11f4b5) (addR64R64Effect 0x11f4b5 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[3456, 3395]
    (.letOp (n := 3470) (.out 0x11f4b8 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f4b8 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[3459, 3468]
    (.letOp (n := 3471) (.exec 0x11f4b8 (fun s => s.RIP = 0x11f4b8) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f4b8 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3459, 3468]
    (.letOp (n := 3472) (.out 0x11f4bc (shldR64R64Effect 0x11f4bc 5 15 13 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[3427, 3424]
    (.letOp (n := 3473) (.exec 0x11f4bc (fun s => s.RIP = 0x11f4bc) (shldR64R64Effect 0x11f4bc 5 15 13 12) (Reg.operands [.gpr 15, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3427, 3424]
    (.letOp (n := 3474) (.out 0x11f4c1 (movR64Imm64Effect 0x11f4c1 13 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 3475) (.exec 0x11f4c1 (fun s => s.RIP = 0x11f4c1) (movR64Imm64Effect 0x11f4c1 13 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 3476) (.out 0x11f4cb (shldR64R64Effect 0x11f4cb 5 14 11 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[3470, 3467]
    (.letOp (n := 3477) (.exec 0x11f4cb (fun s => s.RIP = 0x11f4cb) (shldR64R64Effect 0x11f4cb 5 14 11 12) (Reg.operands [.gpr 14, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3470, 3467]
    (.letOp (n := 3478) (.out 0x11f4d0 (movR64R64Effect 0x11f4d0 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[3472]
    (.letOp (n := 3479) (.exec 0x11f4d0 (fun s => s.RIP = 0x11f4d0) (movR64R64Effect 0x11f4d0 0 15) (Reg.operands [.gpr 15] [])) #v[3472]
    (.letOp (n := 3480) (.out 0x11f4d3 (mulR64Effect 0x11f4d3 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[3420, 3478]
    (.letOp (n := 3481) (.out 0x11f4d3 (mulR64Effect 0x11f4d3 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[3420, 3478]
    (.letOp (n := 3482) (.exec 0x11f4d3 (fun s => s.RIP = 0x11f4d3) (mulR64Effect 0x11f4d3 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[3420, 3478]
    (.letOp (n := 3483) (.out 0x11f4d6 (andR64R64Effect 0x11f4d6 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13] []) (.reg (.gpr 11))) #v[3467, 3474]
    (.letOp (n := 3484) (.exec 0x11f4d6 (fun s => s.RIP = 0x11f4d6) (andR64R64Effect 0x11f4d6 11 13) (Reg.operands [.gpr 11, .gpr 13] [])) #v[3467, 3474]
    (.letOp (n := 3485) (.out 0x11f4d9 (movR64M64Effect 0x11f4d9 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 3486) (.exec 0x11f4d9 (LoadPre 0x11f4d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11f4d9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f4d9 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3487) (.out 0x11f4de (andR64R64Effect 0x11f4de 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[3485, 3474]
    (.letOp (n := 3488) (.exec 0x11f4de (fun s => s.RIP = 0x11f4de) (andR64R64Effect 0x11f4de 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[3485, 3474]
    (.letOp (n := 3489) (.out 0x11f4e1 (addR64R64Effect 0x11f4e1 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[3487, 3480]
    (.letOp (n := 3490) (.out 0x11f4e1 (addR64R64Effect 0x11f4e1 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[3487, 3480]
    (.letOp (n := 3491) (.exec 0x11f4e1 (fun s => s.RIP = 0x11f4e1) (addR64R64Effect 0x11f4e1 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3487, 3480]
    (.letOp (n := 3492) (.out 0x11f4e4 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f4e4 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[3481, 3490]
    (.letOp (n := 3493) (.exec 0x11f4e4 (fun s => s.RIP = 0x11f4e4) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f4e4 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3481, 3490]
    (.letOp (n := 3494) (.out 0x11f4e8 (addR64R64Effect 0x11f4e8 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[3489, 3476]
    (.letOp (n := 3495) (.out 0x11f4e8 (addR64R64Effect 0x11f4e8 6 14) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 14] []) (.flag .CF)) #v[3489, 3476]
    (.letOp (n := 3496) (.exec 0x11f4e8 (fun s => s.RIP = 0x11f4e8) (addR64R64Effect 0x11f4e8 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[3489, 3476]
    (.letOp (n := 3497) (.out 0x11f4eb (movR64M64Effect 0x11f4eb 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3498) (.exec 0x11f4eb (LoadPre 0x11f4eb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11f4eb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f4eb 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3499) (.exec 0x11f4f0 (StorePre 0x11f4f0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x11f4f0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f4f0 0 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3497, 4]
    (.letOp (n := 3500) (.out 0x11f4f8 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f4f8 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[3492, 3495]
    (.letOp (n := 3501) (.exec 0x11f4f8 (fun s => s.RIP = 0x11f4f8) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f4f8 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3492, 3495]
    (.letOp (n := 3502) (.out 0x11f4fc (shldR64R64Effect 0x11f4fc 5 2 6 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3500, 3494]
    (.letOp (n := 3503) (.exec 0x11f4fc (fun s => s.RIP = 0x11f4fc) (shldR64R64Effect 0x11f4fc 5 2 6 12) (Reg.operands [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3500, 3494]
    (.letOp (n := 3504) (.out 0x11f501 (movR64Imm64Effect 0x11f501 10 0xffffffffffff) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 3505) (.exec 0x11f501 (fun s => s.RIP = 0x11f501) (movR64Imm64Effect 0x11f501 10 0xffffffffffff) (Reg.operands [] [])) #v[]
    (b_l11d880_81))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_80 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00, 0x4D, 0x01, 0xD3,
    0x49, 0x83, 0xD6, 0x00, 0x4D, 0x0F, 0xA4, 0xEF, 0x0C, 0x49, 0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x0F, 0x00, 0x4D, 0x0F, 0xA4, 0xDE, 0x0C, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0xE5, 0x4D, 0x21,
    0xEB, 0x48, 0x8B, 0x74, 0x24, 0x58, 0x4C, 0x21, 0xEE, 0x48, 0x01, 0xC6, 0x48, 0x83, 0xD2, 0x00,
    0x4C, 0x01, 0xF6, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00,
    0x48, 0x83, 0xD2, 0x00, 0x48, 0x0F, 0xA4, 0xF2, 0x0C, 0x49, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x00, 0x00] ++ bytes_l11d880_81

theorem code_l11d880_80 : ∀ x ∈ codeRange 0x11f4a8 bytes_l11d880_80, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f4a8 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_81

def b_l11d880_79 : Block Op Label signature Reg.count 3422 :=
  .letOp (n := 3422) (.out 0x11f446 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f446 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[3408, 3413, 3418]
    (.letOp (n := 3423) (.exec 0x11f446 (fun s => s.RIP = 0x11f446) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f446 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3408, 3413, 3418]
    (.letOp (n := 3424) (.out 0x11f449 (addR64R64Effect 0x11f449 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[3417, 3344]
    (.letOp (n := 3425) (.out 0x11f449 (addR64R64Effect 0x11f449 13 3) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 3] []) (.flag .CF)) #v[3417, 3344]
    (.letOp (n := 3426) (.exec 0x11f449 (fun s => s.RIP = 0x11f449) (addR64R64Effect 0x11f449 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[3417, 3344]
    (.letOp (n := 3427) (.out 0x11f44c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f44c 15 0x0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[3422, 3425]
    (.letOp (n := 3428) (.exec 0x11f44c (fun s => s.RIP = 0x11f44c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f44c 15 0x0)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3422, 3425]
    (.letOp (n := 3429) (.out 0x11f450 (movR64R64Effect 0x11f450 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[3424]
    (.letOp (n := 3430) (.exec 0x11f450 (fun s => s.RIP = 0x11f450) (movR64R64Effect 0x11f450 0 13) (Reg.operands [.gpr 13] [])) #v[3424]
    (.letOp (n := 3431) (.out 0x11f453 (movR64Imm64Effect 0x11f453 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 3432) (.exec 0x11f453 (fun s => s.RIP = 0x11f453) (movR64Imm64Effect 0x11f453 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 3433) (.out 0x11f45d (andR64R64Effect 0x11f45d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3429, 3431]
    (.letOp (n := 3434) (.exec 0x11f45d (fun s => s.RIP = 0x11f45d) (andR64R64Effect 0x11f45d 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3429, 3431]
    (.letOp (n := 3435) (.out 0x11f460 (mulR64Effect 0x11f460 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[3420, 3433]
    (.letOp (n := 3436) (.out 0x11f460 (mulR64Effect 0x11f460 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[3420, 3433]
    (.letOp (n := 3437) (.exec 0x11f460 (fun s => s.RIP = 0x11f460) (mulR64Effect 0x11f460 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[3420, 3433]
    (.letOp (n := 3438) (.out 0x11f463 (addR64M64Effect 0x11f463 11 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4] []) (.reg (.gpr 11))) #v[3385, 4]
    (.letOp (n := 3439) (.out 0x11f463 (addR64M64Effect 0x11f463 11 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 4] []) (.flag .CF)) #v[3385, 4]
    (.letOp (n := 3440) (.exec 0x11f463 (LoadPre 0x11f463 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11f463 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11f463 11 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[3385, 4]
    (.letOp (n := 3441) (.out 0x11f468 (movR64M64Effect 0x11f468 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 3442) (.exec 0x11f468 (LoadPre 0x11f468 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11f468 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f468 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3443) (.exec 0x11f46d (StorePre 0x11f46d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x11f46d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f46d 1 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[3441, 4]
    (.letOp (n := 3444) (.out 0x11f475 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f475 14 6)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[3383, 3375, 3439]
    (.letOp (n := 3445) (.exec 0x11f475 (fun s => s.RIP = 0x11f475) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f475 14 6)) (Reg.operands [.gpr 14, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3383, 3375, 3439]
    (.letOp (n := 3446) (.out 0x11f478 (addR64R64Effect 0x11f478 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 12] []) (.reg (.gpr 11))) #v[3438, 3392]
    (.letOp (n := 3447) (.out 0x11f478 (addR64R64Effect 0x11f478 11 12) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 12] []) (.flag .CF)) #v[3438, 3392]
    (.letOp (n := 3448) (.exec 0x11f478 (fun s => s.RIP = 0x11f478) (addR64R64Effect 0x11f478 11 12) (Reg.operands [.gpr 11, .gpr 12] [])) #v[3438, 3392]
    (.letOp (n := 3449) (.out 0x11f47b (leaR64Effect 0x11f47b 12 (.sib 4 none 0 (.d32 0x490))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 3450) (.exec 0x11f47b (fun s => s.RIP = 0x11f47b) (leaR64Effect 0x11f47b 12 (.sib 4 none 0 (.d32 0x490))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3451) (.out 0x11f483 (movR64M64Effect 0x11f483 1 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 3452) (.exec 0x11f483 (LoadPre 0x11f483 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11f483 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f483 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3453) (.exec 0x11f488 (StorePre 0x11f488 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x11f488 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f488 1 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[3451, 4]
    (.letOp (n := 3454) (.out 0x11f490 (atFlags StatusFlags.CF (adcR64M64Effect 0x11f490 14 (.sib 4 none 0 (.d8 0x70)))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 14))) #v[3444, 4, 3447]
    (.letOp (n := 3455) (.exec 0x11f490 (LoadPre 0x11f490 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11f490 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11f490 14 (.sib 4 none 0 (.d8 0x70)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3444, 4, 3447]
    (.letOp (n := 3456) (.out 0x11f495 (addR64R64Effect 0x11f495 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[3446, 3435]
    (.letOp (n := 3457) (.out 0x11f495 (addR64R64Effect 0x11f495 11 0) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 0] []) (.flag .CF)) #v[3446, 3435]
    (.letOp (n := 3458) (.exec 0x11f495 (fun s => s.RIP = 0x11f495) (addR64R64Effect 0x11f495 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[3446, 3435]
    (.letOp (n := 3459) (.out 0x11f498 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f498 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[3454, 3436, 3457]
    (.letOp (n := 3460) (.exec 0x11f498 (fun s => s.RIP = 0x11f498) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f498 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3454, 3436, 3457]
    (.letOp (n := 3461) (.out 0x11f49b (movR64M64Effect 0x11f49b 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3462) (.exec 0x11f49b (LoadPre 0x11f49b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11f49b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f49b 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3463) (.exec 0x11f4a0 (StorePre 0x11f4a0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x11f4a0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f4a0 0 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3461, 4]
    (b_l11d880_80))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_79 : List UInt8 :=
  [0x49, 0x11, 0xD7, 0x49, 0x01, 0xDD, 0x49, 0x83, 0xD7, 0x00, 0x4C, 0x89, 0xE8, 0x48, 0xB9, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8, 0x48, 0xF7, 0xE5, 0x4C, 0x03, 0x5C,
    0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0x89, 0x8C, 0x24, 0x78, 0x01, 0x00, 0x00, 0x49,
    0x11, 0xF6, 0x4D, 0x01, 0xE3, 0x4C, 0x8D, 0xA4, 0x24, 0x90, 0x04, 0x00, 0x00, 0x48, 0x8B, 0x4C,
    0x24, 0x60, 0x48, 0x89, 0x8C, 0x24, 0x80, 0x01, 0x00, 0x00, 0x4C, 0x13, 0x74, 0x24, 0x70, 0x49,
    0x01, 0xC3, 0x49, 0x11, 0xD6, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x89, 0x84, 0x24, 0x88, 0x01,
    0x00, 0x00] ++ bytes_l11d880_80

theorem code_l11d880_79 : ∀ x ∈ codeRange 0x11f446 bytes_l11d880_79, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f446 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_80

def b_l11d880_78 : Block Op Label signature Reg.count 3378 :=
  .letOp (n := 3378) (.out 0x11f3db (movR64M64Effect 0x11f3db 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3379) (.exec 0x11f3db (LoadPre 0x11f3db (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11f3db + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f3db 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3380) (.out 0x11f3e3 (mulM64Effect 0x11f3e3 8 (.sib 4 none 0 (.d32 0x1b0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3378, 4]
    (.letOp (n := 3381) (.out 0x11f3e3 (mulM64Effect 0x11f3e3 8 (.sib 4 none 0 (.d32 0x1b0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3378, 4]
    (.letOp (n := 3382) (.exec 0x11f3e3 (LoadPre 0x11f3e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x11f3e3 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11f3e3 8 (.sib 4 none 0 (.d32 0x1b0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3378, 4]
    (.letOp (n := 3383) (.out 0x11f3eb (movR64R64Effect 0x11f3eb 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[3381]
    (.letOp (n := 3384) (.exec 0x11f3eb (fun s => s.RIP = 0x11f3eb) (movR64R64Effect 0x11f3eb 14 2) (Reg.operands [.gpr 2] [])) #v[3381]
    (.letOp (n := 3385) (.out 0x11f3ee (movR64R64Effect 0x11f3ee 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[3380]
    (.letOp (n := 3386) (.exec 0x11f3ee (fun s => s.RIP = 0x11f3ee) (movR64R64Effect 0x11f3ee 11 0) (Reg.operands [.gpr 0] [])) #v[3380]
    (.letOp (n := 3387) (.out 0x11f3f1 (movR64R64Effect 0x11f3f1 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[3296]
    (.letOp (n := 3388) (.exec 0x11f3f1 (fun s => s.RIP = 0x11f3f1) (movR64R64Effect 0x11f3f1 0 12) (Reg.operands [.gpr 12] [])) #v[3296]
    (.letOp (n := 3389) (.out 0x11f3f4 (mulM64Effect 0x11f3f4 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3387, 4]
    (.letOp (n := 3390) (.out 0x11f3f4 (mulM64Effect 0x11f3f4 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3387, 4]
    (.letOp (n := 3391) (.exec 0x11f3f4 (LoadPre 0x11f3f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x11f3f4 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11f3f4 8 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3387, 4]
    (.letOp (n := 3392) (.out 0x11f3fc (movR64R64Effect 0x11f3fc 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[3389]
    (.letOp (n := 3393) (.exec 0x11f3fc (fun s => s.RIP = 0x11f3fc) (movR64R64Effect 0x11f3fc 12 0) (Reg.operands [.gpr 0] [])) #v[3389]
    (.letOp (n := 3394) (.exec 0x11f3ff (StorePre 0x11f3ff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11f3ff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f3ff 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3390, 4]
    (.letOp (n := 3395) (.out 0x11f404 (shldR64R64Effect 0x11f404 5 10 9 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[3368, 3365]
    (.letOp (n := 3396) (.exec 0x11f404 (fun s => s.RIP = 0x11f404) (shldR64R64Effect 0x11f404 5 10 9 12) (Reg.operands [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3368, 3365]
    (.letOp (n := 3397) (.out 0x11f409 (movR64Imm64Effect 0x11f409 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 3398) (.exec 0x11f409 (fun s => s.RIP = 0x11f409) (movR64Imm64Effect 0x11f409 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 3399) (.out 0x11f413 (andR64R64Effect 0x11f413 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[3365, 3397]
    (.letOp (n := 3400) (.exec 0x11f413 (fun s => s.RIP = 0x11f413) (andR64R64Effect 0x11f413 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[3365, 3397]
    (.letOp (n := 3401) (.out 0x11f416 (movR64M64Effect 0x11f416 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3402) (.exec 0x11f416 (LoadPre 0x11f416 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11f416 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f416 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3403) (.out 0x11f41b (mulM64Effect 0x11f41b 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3401, 4]
    (.letOp (n := 3404) (.out 0x11f41b (mulM64Effect 0x11f41b 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3401, 4]
    (.letOp (n := 3405) (.exec 0x11f41b (LoadPre 0x11f41b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11f41b + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11f41b 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3401, 4]
    (.letOp (n := 3406) (.out 0x11f423 (movR64R64Effect 0x11f423 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[3403]
    (.letOp (n := 3407) (.exec 0x11f423 (fun s => s.RIP = 0x11f423) (movR64R64Effect 0x11f423 5 0) (Reg.operands [.gpr 0] [])) #v[3403]
    (.letOp (n := 3408) (.out 0x11f426 (movR64R64Effect 0x11f426 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[3404]
    (.letOp (n := 3409) (.exec 0x11f426 (fun s => s.RIP = 0x11f426) (movR64R64Effect 0x11f426 15 2) (Reg.operands [.gpr 2] [])) #v[3404]
    (.letOp (n := 3410) (.out 0x11f429 (movR64M64Effect 0x11f429 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3411) (.exec 0x11f429 (LoadPre 0x11f429 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11f429 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f429 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3412) (.out 0x11f42e (mulM64Effect 0x11f42e 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3410, 4]
    (.letOp (n := 3413) (.out 0x11f42e (mulM64Effect 0x11f42e 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3410, 4]
    (.letOp (n := 3414) (.exec 0x11f42e (LoadPre 0x11f42e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11f42e + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11f42e 8 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3410, 4]
    (.letOp (n := 3415) (.out 0x11f436 (movR64R64Effect 0x11f436 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[3412]
    (.letOp (n := 3416) (.exec 0x11f436 (fun s => s.RIP = 0x11f436) (movR64R64Effect 0x11f436 13 0) (Reg.operands [.gpr 0] [])) #v[3412]
    (.letOp (n := 3417) (.out 0x11f439 (addR64R64Effect 0x11f439 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[3415, 3406]
    (.letOp (n := 3418) (.out 0x11f439 (addR64R64Effect 0x11f439 13 5) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 5] []) (.flag .CF)) #v[3415, 3406]
    (.letOp (n := 3419) (.exec 0x11f439 (fun s => s.RIP = 0x11f439) (addR64R64Effect 0x11f439 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[3415, 3406]
    (.letOp (n := 3420) (.out 0x11f43c (movR64Imm64Effect 0x11f43c 5 0x1000003d10) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 3421) (.exec 0x11f43c (fun s => s.RIP = 0x11f43c) (movR64Imm64Effect 0x11f43c 5 0x1000003d10) (Reg.operands [] [])) #v[]
    (b_l11d880_79))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_78 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0xB0, 0x01, 0x00, 0x00,
    0x49, 0x89, 0xD6, 0x49, 0x89, 0xC3, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0xA4, 0x24, 0x20, 0x01, 0x00,
    0x00, 0x49, 0x89, 0xC4, 0x48, 0x89, 0x54, 0x24, 0x70, 0x4D, 0x0F, 0xA4, 0xCA, 0x0C, 0x48, 0xB8,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xC1, 0x48, 0x8B, 0x44, 0x24, 0x38,
    0x48, 0xF7, 0xA4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC5, 0x49, 0x89, 0xD7, 0x48, 0x8B,
    0x44, 0x24, 0x08, 0x48, 0xF7, 0xA4, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC5, 0x49, 0x01,
    0xED, 0x48, 0xBD, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] ++ bytes_l11d880_79

theorem code_l11d880_78 : ∀ x ∈ codeRange 0x11f3db bytes_l11d880_78, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f3db 107 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_79

def b_l11d880_77 : Block Op Label signature Reg.count 3332 :=
  .letOp (n := 3332) (.out 0x11f385 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f385 3 5)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[3320, 3305, 3330]
    (.letOp (n := 3333) (.exec 0x11f385 (fun s => s.RIP = 0x11f385) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f385 3 5)) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3320, 3305, 3330]
    (.letOp (n := 3334) (.out 0x11f388 (addR64R64Effect 0x11f388 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[3326, 3329]
    (.letOp (n := 3335) (.out 0x11f388 (addR64R64Effect 0x11f388 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[3326, 3329]
    (.letOp (n := 3336) (.exec 0x11f388 (fun s => s.RIP = 0x11f388) (addR64R64Effect 0x11f388 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[3326, 3329]
    (.letOp (n := 3337) (.out 0x11f38b (atFlags StatusFlags.CF (adcR64R64Effect 0x11f38b 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[3332, 3327, 3335]
    (.letOp (n := 3338) (.exec 0x11f38b (fun s => s.RIP = 0x11f38b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f38b 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3332, 3327, 3335]
    (.letOp (n := 3339) (.out 0x11f38e (addR64R64Effect 0x11f38e 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[3334, 3256]
    (.letOp (n := 3340) (.out 0x11f38e (addR64R64Effect 0x11f38e 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[3334, 3256]
    (.letOp (n := 3341) (.exec 0x11f38e (fun s => s.RIP = 0x11f38e) (addR64R64Effect 0x11f38e 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[3334, 3256]
    (.letOp (n := 3342) (.out 0x11f391 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f391 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[3337, 3340]
    (.letOp (n := 3343) (.exec 0x11f391 (fun s => s.RIP = 0x11f391) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f391 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3337, 3340]
    (.letOp (n := 3344) (.out 0x11f395 (shldR64R64Effect 0x11f395 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[3342, 3339]
    (.letOp (n := 3345) (.exec 0x11f395 (fun s => s.RIP = 0x11f395) (shldR64R64Effect 0x11f395 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3342, 3339]
    (.letOp (n := 3346) (.out 0x11f39a (movR64Imm64Effect 0x11f39a 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 3347) (.exec 0x11f39a (fun s => s.RIP = 0x11f39a) (movR64Imm64Effect 0x11f39a 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 3348) (.out 0x11f3a4 (andR64R64Effect 0x11f3a4 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3339, 3346]
    (.letOp (n := 3349) (.exec 0x11f3a4 (fun s => s.RIP = 0x11f3a4) (andR64R64Effect 0x11f3a4 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3339, 3346]
    (.letOp (n := 3350) (.out 0x11f3a7 (movR64Imm64Effect 0x11f3a7 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 3351) (.exec 0x11f3a7 (fun s => s.RIP = 0x11f3a7) (movR64Imm64Effect 0x11f3a7 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 3352) (.out 0x11f3b1 (mulR64Effect 0x11f3b1 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[3350, 3348]
    (.letOp (n := 3353) (.out 0x11f3b1 (mulR64Effect 0x11f3b1 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[3350, 3348]
    (.letOp (n := 3354) (.exec 0x11f3b1 (fun s => s.RIP = 0x11f3b1) (mulR64Effect 0x11f3b1 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3350, 3348]
    (.letOp (n := 3355) (.out 0x11f3b4 (addR64M64Effect 0x11f3b4 9 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[3294, 4]
    (.letOp (n := 3356) (.out 0x11f3b4 (addR64M64Effect 0x11f3b4 9 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 4] []) (.flag .CF)) #v[3294, 4]
    (.letOp (n := 3357) (.exec 0x11f3b4 (LoadPre 0x11f3b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11f3b4 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11f3b4 9 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[3294, 4]
    (.letOp (n := 3358) (.out 0x11f3b9 (atFlags StatusFlags.CF (adcR64M64Effect 0x11f3b9 10 (.sib 4 none 0 (.d8 0x28)))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 10))) #v[3292, 4, 3356]
    (.letOp (n := 3359) (.exec 0x11f3b9 (LoadPre 0x11f3b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11f3b9 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11f3b9 10 (.sib 4 none 0 (.d8 0x28)))) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3292, 4, 3356]
    (.letOp (n := 3360) (.out 0x11f3be (addR64R64Effect 0x11f3be 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[3355, 3352]
    (.letOp (n := 3361) (.out 0x11f3be (addR64R64Effect 0x11f3be 9 0) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 0] []) (.flag .CF)) #v[3355, 3352]
    (.letOp (n := 3362) (.exec 0x11f3be (fun s => s.RIP = 0x11f3be) (addR64R64Effect 0x11f3be 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[3355, 3352]
    (.letOp (n := 3363) (.out 0x11f3c1 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f3c1 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[3358, 3353, 3361]
    (.letOp (n := 3364) (.exec 0x11f3c1 (fun s => s.RIP = 0x11f3c1) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f3c1 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3358, 3353, 3361]
    (.letOp (n := 3365) (.out 0x11f3c4 (addR64R64Effect 0x11f3c4 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[3360, 3307]
    (.letOp (n := 3366) (.out 0x11f3c4 (addR64R64Effect 0x11f3c4 9 14) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 14] []) (.flag .CF)) #v[3360, 3307]
    (.letOp (n := 3367) (.exec 0x11f3c4 (fun s => s.RIP = 0x11f3c4) (addR64R64Effect 0x11f3c4 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[3360, 3307]
    (.letOp (n := 3368) (.out 0x11f3c7 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f3c7 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[3363, 3366]
    (.letOp (n := 3369) (.exec 0x11f3c7 (fun s => s.RIP = 0x11f3c7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f3c7 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3363, 3366]
    (.letOp (n := 3370) (.out 0x11f3cb (movR64M64Effect 0x11f3cb 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3371) (.exec 0x11f3cb (LoadPre 0x11f3cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11f3cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f3cb 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3372) (.out 0x11f3d0 (mulR64Effect 0x11f3d0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[3324, 3370]
    (.letOp (n := 3373) (.out 0x11f3d0 (mulR64Effect 0x11f3d0 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[3324, 3370]
    (.letOp (n := 3374) (.exec 0x11f3d0 (fun s => s.RIP = 0x11f3d0) (mulR64Effect 0x11f3d0 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3324, 3370]
    (.letOp (n := 3375) (.out 0x11f3d3 (movR64R64Effect 0x11f3d3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[3373]
    (.letOp (n := 3376) (.exec 0x11f3d3 (fun s => s.RIP = 0x11f3d3) (movR64R64Effect 0x11f3d3 6 2) (Reg.operands [.gpr 2] [])) #v[3373]
    (.letOp (n := 3377) (.exec 0x11f3d6 (StorePre 0x11f3d6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11f3d6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f3d6 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3372, 4]
    (b_l11d880_78))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_77 : List UInt8 :=
  [0x48, 0x11, 0xEB, 0x4C, 0x01, 0xF8, 0x48, 0x11, 0xD3, 0x4C, 0x01, 0xD8, 0x48, 0x83, 0xD3, 0x00,
    0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48,
    0x21, 0xC8, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x4C,
    0x03, 0x4C, 0x24, 0x50, 0x4C, 0x13, 0x54, 0x24, 0x28, 0x49, 0x01, 0xC1, 0x49, 0x11, 0xD2, 0x4D,
    0x01, 0xF1, 0x49, 0x83, 0xD2, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0xF7, 0xE6, 0x48, 0x89,
    0xD6, 0x48, 0x89, 0x44, 0x24, 0x28] ++ bytes_l11d880_78

theorem code_l11d880_77 : ∀ x ∈ codeRange 0x11f385 bytes_l11d880_77, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f385 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_78

def b_l11d880_76 : Block Op Label signature Reg.count 3287 :=
  .letOp (n := 3287) (.out 0x11f32b (movR64R64Effect 0x11f32b 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[3192]
    (.letOp (n := 3288) (.exec 0x11f32b (fun s => s.RIP = 0x11f32b) (movR64R64Effect 0x11f32b 0 6) (Reg.operands [.gpr 6] [])) #v[3192]
    (.letOp (n := 3289) (.out 0x11f32e (mulR64Effect 0x11f32e 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[3187, 3287]
    (.letOp (n := 3290) (.out 0x11f32e (mulR64Effect 0x11f32e 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[3187, 3287]
    (.letOp (n := 3291) (.exec 0x11f32e (fun s => s.RIP = 0x11f32e) (mulR64Effect 0x11f32e 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[3187, 3287]
    (.letOp (n := 3292) (.out 0x11f331 (movR64R64Effect 0x11f331 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[3290]
    (.letOp (n := 3293) (.exec 0x11f331 (fun s => s.RIP = 0x11f331) (movR64R64Effect 0x11f331 10 2) (Reg.operands [.gpr 2] [])) #v[3290]
    (.letOp (n := 3294) (.out 0x11f334 (movR64R64Effect 0x11f334 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[3289]
    (.letOp (n := 3295) (.exec 0x11f334 (fun s => s.RIP = 0x11f334) (movR64R64Effect 0x11f334 9 0) (Reg.operands [.gpr 0] [])) #v[3289]
    (.letOp (n := 3296) (.out 0x11f337 (movR64M64Effect 0x11f337 12 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 3297) (.exec 0x11f337 (LoadPre 0x11f337 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11f337 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f337 12 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3298) (.out 0x11f33c (movR64R64Effect 0x11f33c 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[3296]
    (.letOp (n := 3299) (.exec 0x11f33c (fun s => s.RIP = 0x11f33c) (movR64R64Effect 0x11f33c 0 12) (Reg.operands [.gpr 12] [])) #v[3296]
    (.letOp (n := 3300) (.out 0x11f33f (mulM64Effect 0x11f33f 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3298, 4]
    (.letOp (n := 3301) (.out 0x11f33f (mulM64Effect 0x11f33f 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3298, 4]
    (.letOp (n := 3302) (.exec 0x11f33f (LoadPre 0x11f33f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11f33f + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11f33f 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3298, 4]
    (.letOp (n := 3303) (.out 0x11f347 (movR64R64Effect 0x11f347 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[3300]
    (.letOp (n := 3304) (.exec 0x11f347 (fun s => s.RIP = 0x11f347) (movR64R64Effect 0x11f347 13 0) (Reg.operands [.gpr 0] [])) #v[3300]
    (.letOp (n := 3305) (.out 0x11f34a (movR64R64Effect 0x11f34a 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[3301]
    (.letOp (n := 3306) (.exec 0x11f34a (fun s => s.RIP = 0x11f34a) (movR64R64Effect 0x11f34a 5 2) (Reg.operands [.gpr 2] [])) #v[3301]
    (.letOp (n := 3307) (.out 0x11f34d (shldR64R64Effect 0x11f34d 5 14 8 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[3278, 3275]
    (.letOp (n := 3308) (.exec 0x11f34d (fun s => s.RIP = 0x11f34d) (shldR64R64Effect 0x11f34d 5 14 8 12) (Reg.operands [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3278, 3275]
    (.letOp (n := 3309) (.out 0x11f352 (movR64Imm64Effect 0x11f352 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 3310) (.exec 0x11f352 (fun s => s.RIP = 0x11f352) (movR64Imm64Effect 0x11f352 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 3311) (.out 0x11f35c (andR64R64Effect 0x11f35c 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[3275, 3309]
    (.letOp (n := 3312) (.exec 0x11f35c (fun s => s.RIP = 0x11f35c) (andR64R64Effect 0x11f35c 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3275, 3309]
    (.letOp (n := 3313) (.out 0x11f35f (movR64M64Effect 0x11f35f 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3314) (.exec 0x11f35f (LoadPre 0x11f35f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11f35f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f35f 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3315) (.out 0x11f364 (mulM64Effect 0x11f364 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3313, 4]
    (.letOp (n := 3316) (.out 0x11f364 (mulM64Effect 0x11f364 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3313, 4]
    (.letOp (n := 3317) (.exec 0x11f364 (LoadPre 0x11f364 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11f364 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11f364 8 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3313, 4]
    (.letOp (n := 3318) (.out 0x11f36c (movR64R64Effect 0x11f36c 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[3315]
    (.letOp (n := 3319) (.exec 0x11f36c (fun s => s.RIP = 0x11f36c) (movR64R64Effect 0x11f36c 15 0) (Reg.operands [.gpr 0] [])) #v[3315]
    (.letOp (n := 3320) (.out 0x11f36f (movR64R64Effect 0x11f36f 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[3316]
    (.letOp (n := 3321) (.exec 0x11f36f (fun s => s.RIP = 0x11f36f) (movR64R64Effect 0x11f36f 3 2) (Reg.operands [.gpr 2] [])) #v[3316]
    (.letOp (n := 3322) (.out 0x11f372 (movR64M64Effect 0x11f372 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3323) (.exec 0x11f372 (LoadPre 0x11f372 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11f372 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f372 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3324) (.out 0x11f377 (movR64M64Effect 0x11f377 6 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 3325) (.exec 0x11f377 (LoadPre 0x11f377 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x11f377 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f377 6 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3326) (.out 0x11f37f (mulR64Effect 0x11f37f 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[3324, 3322]
    (.letOp (n := 3327) (.out 0x11f37f (mulR64Effect 0x11f37f 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[3324, 3322]
    (.letOp (n := 3328) (.exec 0x11f37f (fun s => s.RIP = 0x11f37f) (mulR64Effect 0x11f37f 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3324, 3322]
    (.letOp (n := 3329) (.out 0x11f382 (addR64R64Effect 0x11f382 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[3318, 3303]
    (.letOp (n := 3330) (.out 0x11f382 (addR64R64Effect 0x11f382 15 13) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 13] []) (.flag .CF)) #v[3318, 3303]
    (.letOp (n := 3331) (.exec 0x11f382 (fun s => s.RIP = 0x11f382) (addR64R64Effect 0x11f382 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[3318, 3303]
    (b_l11d880_77)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_76 : List UInt8 :=
  [0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC1, 0x4C, 0x8B, 0x64, 0x24,
    0x70, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0xA4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC5, 0x48,
    0x89, 0xD5, 0x4D, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F,
    0x00, 0x49, 0x21, 0xC0, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0xF7, 0xA4, 0x24, 0xD8, 0x00, 0x00,
    0x00, 0x49, 0x89, 0xC7, 0x48, 0x89, 0xD3, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x8B, 0xB4, 0x24,
    0x18, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE6, 0x4D, 0x01, 0xEF] ++ bytes_l11d880_77

theorem code_l11d880_76 : ∀ x ∈ codeRange 0x11f32b bytes_l11d880_76, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f32b 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_77

def b_l11d880_75 : Block Op Label signature Reg.count 3244 :=
  .letOp (n := 3244) (.out 0x11f2d5 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f2d5 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3239, 3219, 3242]
    (.letOp (n := 3245) (.exec 0x11f2d5 (fun s => s.RIP = 0x11f2d5) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f2d5 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3239, 3219, 3242]
    (.letOp (n := 3246) (.out 0x11f2d8 (addR64R64Effect 0x11f2d8 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[3231, 3241]
    (.letOp (n := 3247) (.out 0x11f2d8 (addR64R64Effect 0x11f2d8 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[3231, 3241]
    (.letOp (n := 3248) (.exec 0x11f2d8 (fun s => s.RIP = 0x11f2d8) (addR64R64Effect 0x11f2d8 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[3231, 3241]
    (.letOp (n := 3249) (.out 0x11f2db (atFlags StatusFlags.CF (adcR64R64Effect 0x11f2db 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3244, 3232, 3247]
    (.letOp (n := 3250) (.exec 0x11f2db (fun s => s.RIP = 0x11f2db) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f2db 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3244, 3232, 3247]
    (.letOp (n := 3251) (.out 0x11f2de (addR64R64Effect 0x11f2de 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[3246, 3234]
    (.letOp (n := 3252) (.out 0x11f2de (addR64R64Effect 0x11f2de 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[3246, 3234]
    (.letOp (n := 3253) (.exec 0x11f2de (fun s => s.RIP = 0x11f2de) (addR64R64Effect 0x11f2de 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[3246, 3234]
    (.letOp (n := 3254) (.out 0x11f2e1 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f2e1 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3249, 3252]
    (.letOp (n := 3255) (.exec 0x11f2e1 (fun s => s.RIP = 0x11f2e1) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f2e1 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3249, 3252]
    (.letOp (n := 3256) (.out 0x11f2e5 (shldR64R64Effect 0x11f2e5 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[3254, 3251]
    (.letOp (n := 3257) (.exec 0x11f2e5 (fun s => s.RIP = 0x11f2e5) (shldR64R64Effect 0x11f2e5 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3254, 3251]
    (.letOp (n := 3258) (.out 0x11f2ea (shlR64Effect 0x11f2ea 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3251]
    (.letOp (n := 3259) (.exec 0x11f2ea (fun s => s.RIP = 0x11f2ea) (shlR64Effect 0x11f2ea 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3251]
    (.letOp (n := 3260) (.out 0x11f2ee (movR64Imm64Effect 0x11f2ee 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 3261) (.exec 0x11f2ee (fun s => s.RIP = 0x11f2ee) (movR64Imm64Effect 0x11f2ee 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 3262) (.out 0x11f2f8 (andR64R64Effect 0x11f2f8 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3258, 3260]
    (.letOp (n := 3263) (.exec 0x11f2f8 (fun s => s.RIP = 0x11f2f8) (andR64R64Effect 0x11f2f8 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3258, 3260]
    (.letOp (n := 3264) (.out 0x11f2fb (orR64R64Effect 0x11f2fb 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3262, 3225]
    (.letOp (n := 3265) (.exec 0x11f2fb (fun s => s.RIP = 0x11f2fb) (orR64R64Effect 0x11f2fb 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3262, 3225]
    (.letOp (n := 3266) (.out 0x11f2fe (movR64Imm64Effect 0x11f2fe 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 3267) (.exec 0x11f2fe (fun s => s.RIP = 0x11f2fe) (movR64Imm64Effect 0x11f2fe 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 3268) (.out 0x11f308 (mulR64Effect 0x11f308 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[3266, 3264]
    (.letOp (n := 3269) (.out 0x11f308 (mulR64Effect 0x11f308 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[3266, 3264]
    (.letOp (n := 3270) (.exec 0x11f308 (fun s => s.RIP = 0x11f308) (mulR64Effect 0x11f308 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3266, 3264]
    (.letOp (n := 3271) (.out 0x11f30b (movR64R64Effect 0x11f30b 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[3269]
    (.letOp (n := 3272) (.exec 0x11f30b (fun s => s.RIP = 0x11f30b) (movR64R64Effect 0x11f30b 14 2) (Reg.operands [.gpr 2] [])) #v[3269]
    (.letOp (n := 3273) (.out 0x11f30e (movR64R64Effect 0x11f30e 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[3268]
    (.letOp (n := 3274) (.exec 0x11f30e (fun s => s.RIP = 0x11f30e) (movR64R64Effect 0x11f30e 8 0) (Reg.operands [.gpr 0] [])) #v[3268]
    (.letOp (n := 3275) (.out 0x11f311 (addR64M64Effect 0x11f311 8 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[3273, 4]
    (.letOp (n := 3276) (.out 0x11f311 (addR64M64Effect 0x11f311 8 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[3273, 4]
    (.letOp (n := 3277) (.exec 0x11f311 (LoadPre 0x11f311 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11f311 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11f311 8 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[3273, 4]
    (.letOp (n := 3278) (.out 0x11f316 (atFlags StatusFlags.CF (adcR64M64Effect 0x11f316 14 (.sib 4 none 0 (.d8 0x28)))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 14))) #v[3271, 4, 3276]
    (.letOp (n := 3279) (.exec 0x11f316 (LoadPre 0x11f316 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11f316 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11f316 14 (.sib 4 none 0 (.d8 0x28)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3271, 4, 3276]
    (.letOp (n := 3280) (.out 0x11f31b (movR64R64Effect 0x11f31b 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[3180]
    (.letOp (n := 3281) (.exec 0x11f31b (fun s => s.RIP = 0x11f31b) (movR64R64Effect 0x11f31b 0 9) (Reg.operands [.gpr 9] [])) #v[3180]
    (.letOp (n := 3282) (.out 0x11f31e (mulR64Effect 0x11f31e 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[3229, 3280]
    (.letOp (n := 3283) (.out 0x11f31e (mulR64Effect 0x11f31e 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[3229, 3280]
    (.letOp (n := 3284) (.exec 0x11f31e (fun s => s.RIP = 0x11f31e) (mulR64Effect 0x11f31e 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[3229, 3280]
    (.letOp (n := 3285) (.exec 0x11f321 (StorePre 0x11f321 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11f321 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f321 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3283, 4]
    (.letOp (n := 3286) (.exec 0x11f326 (StorePre 0x11f326 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11f326 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f326 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3282, 4]
    (b_l11d880_76)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_75 : List UInt8 :=
  [0x4D, 0x11, 0xEB, 0x4C, 0x01, 0xF0, 0x49, 0x11, 0xD3, 0x4C, 0x01, 0xC0, 0x49, 0x83, 0xD3, 0x00,
    0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x48, 0x09, 0xC8, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC0, 0x4C, 0x03, 0x44, 0x24,
    0x50, 0x4C, 0x13, 0x74, 0x24, 0x28, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0x54, 0x24,
    0x28, 0x48, 0x89, 0x44, 0x24, 0x50] ++ bytes_l11d880_76

theorem code_l11d880_75 : ∀ x ∈ codeRange 0x11f2d5 bytes_l11d880_75, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f2d5 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_76

def b_l11d880_74 : Block Op Label signature Reg.count 3199 :=
  .letOp (n := 3199) (.out 0x11f281 (movR64R64Effect 0x11f281 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[3197]
    (.letOp (n := 3200) (.exec 0x11f281 (fun s => s.RIP = 0x11f281) (movR64R64Effect 0x11f281 3 2) (Reg.operands [.gpr 2] [])) #v[3197]
    (.letOp (n := 3201) (.out 0x11f284 (movR64R64Effect 0x11f284 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[3196]
    (.letOp (n := 3202) (.exec 0x11f284 (fun s => s.RIP = 0x11f284) (movR64R64Effect 0x11f284 15 0) (Reg.operands [.gpr 0] [])) #v[3196]
    (.letOp (n := 3203) (.out 0x11f287 (movR64M64Effect 0x11f287 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3204) (.exec 0x11f287 (LoadPre 0x11f287 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11f287 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f287 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3205) (.out 0x11f28c (mulM64Effect 0x11f28c 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3203, 4]
    (.letOp (n := 3206) (.out 0x11f28c (mulM64Effect 0x11f28c 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3203, 4]
    (.letOp (n := 3207) (.exec 0x11f28c (LoadPre 0x11f28c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11f28c + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11f28c 8 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3203, 4]
    (.letOp (n := 3208) (.out 0x11f294 (movR64R64Effect 0x11f294 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[3206]
    (.letOp (n := 3209) (.exec 0x11f294 (fun s => s.RIP = 0x11f294) (movR64R64Effect 0x11f294 11 2) (Reg.operands [.gpr 2] [])) #v[3206]
    (.letOp (n := 3210) (.out 0x11f297 (movR64R64Effect 0x11f297 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[3205]
    (.letOp (n := 3211) (.exec 0x11f297 (fun s => s.RIP = 0x11f297) (movR64R64Effect 0x11f297 14 0) (Reg.operands [.gpr 0] [])) #v[3205]
    (.letOp (n := 3212) (.out 0x11f29a (movR64M64Effect 0x11f29a 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3213) (.exec 0x11f29a (LoadPre 0x11f29a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11f29a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f29a 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3214) (.out 0x11f29f (mulM64Effect 0x11f29f 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3212, 4]
    (.letOp (n := 3215) (.out 0x11f29f (mulM64Effect 0x11f29f 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3212, 4]
    (.letOp (n := 3216) (.exec 0x11f29f (LoadPre 0x11f29f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x11f29f + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11f29f 8 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3212, 4]
    (.letOp (n := 3217) (.out 0x11f2a7 (movR64R64Effect 0x11f2a7 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[3214]
    (.letOp (n := 3218) (.exec 0x11f2a7 (fun s => s.RIP = 0x11f2a7) (movR64R64Effect 0x11f2a7 12 0) (Reg.operands [.gpr 0] [])) #v[3214]
    (.letOp (n := 3219) (.out 0x11f2aa (movR64R64Effect 0x11f2aa 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[3215]
    (.letOp (n := 3220) (.exec 0x11f2aa (fun s => s.RIP = 0x11f2aa) (movR64R64Effect 0x11f2aa 13 2) (Reg.operands [.gpr 2] [])) #v[3215]
    (.letOp (n := 3221) (.out 0x11f2ad (movR64R64Effect 0x11f2ad 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[3175]
    (.letOp (n := 3222) (.exec 0x11f2ad (fun s => s.RIP = 0x11f2ad) (movR64R64Effect 0x11f2ad 1 7) (Reg.operands [.gpr 7] [])) #v[3175]
    (.letOp (n := 3223) (.out 0x11f2b0 (shrR64Effect 0x11f2b0 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3221]
    (.letOp (n := 3224) (.exec 0x11f2b0 (fun s => s.RIP = 0x11f2b0) (shrR64Effect 0x11f2b0 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3221]
    (.letOp (n := 3225) (.out 0x11f2b4 (andR32Imm8Effect 0x11f2b4 3 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[3223]
    (.letOp (n := 3226) (.exec 0x11f2b4 (fun s => s.RIP = 0x11f2b4) (andR32Imm8Effect 0x11f2b4 3 1 0xf) (Reg.operands [.gpr 1] [])) #v[3223]
    (.letOp (n := 3227) (.out 0x11f2b7 (movR64M64Effect 0x11f2b7 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3228) (.exec 0x11f2b7 (LoadPre 0x11f2b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11f2b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f2b7 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3229) (.out 0x11f2bc (movR64M64Effect 0x11f2bc 5 (.sib 4 none 0 (.d32 0x1b0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 3230) (.exec 0x11f2bc (LoadPre 0x11f2bc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x11f2bc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f2bc 5 (.sib 4 none 0 (.d32 0x1b0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3231) (.out 0x11f2c4 (mulR64Effect 0x11f2c4 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[3229, 3227]
    (.letOp (n := 3232) (.out 0x11f2c4 (mulR64Effect 0x11f2c4 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[3229, 3227]
    (.letOp (n := 3233) (.exec 0x11f2c4 (fun s => s.RIP = 0x11f2c4) (mulR64Effect 0x11f2c4 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[3229, 3227]
    (.letOp (n := 3234) (.out 0x11f2c7 (shldR64R64Effect 0x11f2c7 5 8 7 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[3178, 3175]
    (.letOp (n := 3235) (.exec 0x11f2c7 (fun s => s.RIP = 0x11f2c7) (shldR64R64Effect 0x11f2c7 5 8 7 12) (Reg.operands [.gpr 8, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3178, 3175]
    (.letOp (n := 3236) (.out 0x11f2cc (addR64R64Effect 0x11f2cc 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[3210, 3201]
    (.letOp (n := 3237) (.out 0x11f2cc (addR64R64Effect 0x11f2cc 14 15) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 15] []) (.flag .CF)) #v[3210, 3201]
    (.letOp (n := 3238) (.exec 0x11f2cc (fun s => s.RIP = 0x11f2cc) (addR64R64Effect 0x11f2cc 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[3210, 3201]
    (.letOp (n := 3239) (.out 0x11f2cf (atFlags StatusFlags.CF (adcR64R64Effect 0x11f2cf 11 3)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3208, 3199, 3237]
    (.letOp (n := 3240) (.exec 0x11f2cf (fun s => s.RIP = 0x11f2cf) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f2cf 11 3)) (Reg.operands [.gpr 11, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3208, 3199, 3237]
    (.letOp (n := 3241) (.out 0x11f2d2 (addR64R64Effect 0x11f2d2 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[3236, 3217]
    (.letOp (n := 3242) (.out 0x11f2d2 (addR64R64Effect 0x11f2d2 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[3236, 3217]
    (.letOp (n := 3243) (.exec 0x11f2d2 (fun s => s.RIP = 0x11f2d2) (addR64R64Effect 0x11f2d2 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[3236, 3217]
    (b_l11d880_75)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_74 : List UInt8 :=
  [0x48, 0x89, 0xD3, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x48, 0xF7, 0xA4, 0x24, 0xD8,
    0x00, 0x00, 0x00, 0x49, 0x89, 0xD3, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0xF7,
    0xA4, 0x24, 0x18, 0x01, 0x00, 0x00, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD5, 0x48, 0x89, 0xF9, 0x48,
    0xC1, 0xE9, 0x30, 0x83, 0xE1, 0x0F, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x8B, 0xAC, 0x24, 0xB0,
    0x01, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x49, 0x0F, 0xA4, 0xF8, 0x0C, 0x4D, 0x01, 0xFE, 0x49, 0x11,
    0xDB, 0x4D, 0x01, 0xE6] ++ bytes_l11d880_75

theorem code_l11d880_74 : ∀ x ∈ codeRange 0x11f281 bytes_l11d880_74, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f281 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_75

def b_l11d880_73 : Block Op Label signature Reg.count 3155 :=
  .letOp (n := 3155) (.out 0x11f22f (addR64R64Effect 0x11f22f 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[3150, 3117]
    (.letOp (n := 3156) (.out 0x11f22f (addR64R64Effect 0x11f22f 7 15) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 15] []) (.flag .CF)) #v[3150, 3117]
    (.letOp (n := 3157) (.exec 0x11f22f (fun s => s.RIP = 0x11f22f) (addR64R64Effect 0x11f22f 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[3150, 3117]
    (.letOp (n := 3158) (.out 0x11f232 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f232 8 14)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[3153, 3119, 3156]
    (.letOp (n := 3159) (.exec 0x11f232 (fun s => s.RIP = 0x11f232) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f232 8 14)) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3153, 3119, 3156]
    (.letOp (n := 3160) (.out 0x11f235 (addR64R64Effect 0x11f235 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[3155, 3128]
    (.letOp (n := 3161) (.out 0x11f235 (addR64R64Effect 0x11f235 7 12) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 12] []) (.flag .CF)) #v[3155, 3128]
    (.letOp (n := 3162) (.exec 0x11f235 (fun s => s.RIP = 0x11f235) (addR64R64Effect 0x11f235 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[3155, 3128]
    (.letOp (n := 3163) (.out 0x11f238 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f238 8 13)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[3158, 3130, 3161]
    (.letOp (n := 3164) (.exec 0x11f238 (fun s => s.RIP = 0x11f238) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f238 8 13)) (Reg.operands [.gpr 8, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3158, 3130, 3161]
    (.letOp (n := 3165) (.out 0x11f23b (addR64R64Effect 0x11f23b 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[3160, 3141]
    (.letOp (n := 3166) (.out 0x11f23b (addR64R64Effect 0x11f23b 7 11) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 11] []) (.flag .CF)) #v[3160, 3141]
    (.letOp (n := 3167) (.exec 0x11f23b (fun s => s.RIP = 0x11f23b) (addR64R64Effect 0x11f23b 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[3160, 3141]
    (.letOp (n := 3168) (.out 0x11f23e (atFlags StatusFlags.CF (adcR64R64Effect 0x11f23e 8 5)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[3163, 3139, 3166]
    (.letOp (n := 3169) (.exec 0x11f23e (fun s => s.RIP = 0x11f23e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f23e 8 5)) (Reg.operands [.gpr 8, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3163, 3139, 3166]
    (.letOp (n := 3170) (.out 0x11f241 (addR64R64Effect 0x11f241 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[3165, 3147]
    (.letOp (n := 3171) (.out 0x11f241 (addR64R64Effect 0x11f241 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[3165, 3147]
    (.letOp (n := 3172) (.exec 0x11f241 (fun s => s.RIP = 0x11f241) (addR64R64Effect 0x11f241 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[3165, 3147]
    (.letOp (n := 3173) (.out 0x11f244 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f244 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[3168, 3148, 3171]
    (.letOp (n := 3174) (.exec 0x11f244 (fun s => s.RIP = 0x11f244) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f244 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3168, 3148, 3171]
    (.letOp (n := 3175) (.out 0x11f247 (addR64R64Effect 0x11f247 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[3170, 3121]
    (.letOp (n := 3176) (.out 0x11f247 (addR64R64Effect 0x11f247 7 9) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 9] []) (.flag .CF)) #v[3170, 3121]
    (.letOp (n := 3177) (.exec 0x11f247 (fun s => s.RIP = 0x11f247) (addR64R64Effect 0x11f247 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[3170, 3121]
    (.letOp (n := 3178) (.out 0x11f24a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f24a 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[3173, 3176]
    (.letOp (n := 3179) (.exec 0x11f24a (fun s => s.RIP = 0x11f24a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f24a 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3173, 3176]
    (.letOp (n := 3180) (.out 0x11f24e (movR64M64Effect 0x11f24e 9 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 3181) (.exec 0x11f24e (LoadPre 0x11f24e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11f24e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f24e 9 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3182) (.out 0x11f253 (movR64R64Effect 0x11f253 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[3180]
    (.letOp (n := 3183) (.exec 0x11f253 (fun s => s.RIP = 0x11f253) (movR64R64Effect 0x11f253 0 9) (Reg.operands [.gpr 9] [])) #v[3180]
    (.letOp (n := 3184) (.out 0x11f256 (mulR64Effect 0x11f256 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[3137, 3182]
    (.letOp (n := 3185) (.out 0x11f256 (mulR64Effect 0x11f256 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[3137, 3182]
    (.letOp (n := 3186) (.exec 0x11f256 (fun s => s.RIP = 0x11f256) (mulR64Effect 0x11f256 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3137, 3182]
    (.letOp (n := 3187) (.out 0x11f259 (movR64R64Effect 0x11f259 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[3137]
    (.letOp (n := 3188) (.exec 0x11f259 (fun s => s.RIP = 0x11f259) (movR64R64Effect 0x11f259 10 6) (Reg.operands [.gpr 6] [])) #v[3137]
    (.letOp (n := 3189) (.exec 0x11f25c (StorePre 0x11f25c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x11f25c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11f25c 6 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[3137, 4]
    (.letOp (n := 3190) (.exec 0x11f264 (StorePre 0x11f264 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11f264 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f264 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3184, 4]
    (.letOp (n := 3191) (.exec 0x11f269 (StorePre 0x11f269 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11f269 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f269 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3185, 4]
    (.letOp (n := 3192) (.out 0x11f26e (movR64M64Effect 0x11f26e 6 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 3193) (.exec 0x11f26e (LoadPre 0x11f26e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11f26e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f26e 6 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3194) (.out 0x11f276 (movR64R64Effect 0x11f276 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[3192]
    (.letOp (n := 3195) (.exec 0x11f276 (fun s => s.RIP = 0x11f276) (movR64R64Effect 0x11f276 0 6) (Reg.operands [.gpr 6] [])) #v[3192]
    (.letOp (n := 3196) (.out 0x11f279 (mulM64Effect 0x11f279 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3194, 4]
    (.letOp (n := 3197) (.out 0x11f279 (mulM64Effect 0x11f279 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3194, 4]
    (.letOp (n := 3198) (.exec 0x11f279 (LoadPre 0x11f279 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11f279 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11f279 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3194, 4]
    (b_l11d880_74))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_73 : List UInt8 :=
  [0x4C, 0x01, 0xFF, 0x4D, 0x11, 0xF0, 0x4C, 0x01, 0xE7, 0x4D, 0x11, 0xE8, 0x4C, 0x01, 0xDF, 0x49,
    0x11, 0xE8, 0x48, 0x01, 0xC7, 0x49, 0x11, 0xD0, 0x4C, 0x01, 0xCF, 0x49, 0x83, 0xD0, 0x00, 0x4C,
    0x8B, 0x4C, 0x24, 0x68, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0xE6, 0x49, 0x89, 0xF2, 0x48, 0x89, 0xB4,
    0x24, 0x20, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0x89, 0x54, 0x24, 0x28, 0x48,
    0x8B, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0xA4, 0x24, 0xB0, 0x00,
    0x00, 0x00] ++ bytes_l11d880_74

theorem code_l11d880_73 : ∀ x ∈ codeRange 0x11f22f bytes_l11d880_73, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f22f 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_74

def b_l11d880_72 : Block Op Label signature Reg.count 3110 :=
  .letOp (n := 3110) (.out 0x11f1e3 (movR64R64Effect 0x11f1e3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[3105]
    (.letOp (n := 3111) (.exec 0x11f1e3 (fun s => s.RIP = 0x11f1e3) (movR64R64Effect 0x11f1e3 7 0) (Reg.operands [.gpr 0] [])) #v[3105]
    (.letOp (n := 3112) (.out 0x11f1e6 (movR64R64Effect 0x11f1e6 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[3027]
    (.letOp (n := 3113) (.exec 0x11f1e6 (fun s => s.RIP = 0x11f1e6) (movR64R64Effect 0x11f1e6 0 14) (Reg.operands [.gpr 14] [])) #v[3027]
    (.letOp (n := 3114) (.out 0x11f1e9 (mulM64Effect 0x11f1e9 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3112, 4]
    (.letOp (n := 3115) (.out 0x11f1e9 (mulM64Effect 0x11f1e9 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3112, 4]
    (.letOp (n := 3116) (.exec 0x11f1e9 (LoadPre 0x11f1e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x11f1e9 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11f1e9 8 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3112, 4]
    (.letOp (n := 3117) (.out 0x11f1f1 (movR64R64Effect 0x11f1f1 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[3114]
    (.letOp (n := 3118) (.exec 0x11f1f1 (fun s => s.RIP = 0x11f1f1) (movR64R64Effect 0x11f1f1 15 0) (Reg.operands [.gpr 0] [])) #v[3114]
    (.letOp (n := 3119) (.out 0x11f1f4 (movR64R64Effect 0x11f1f4 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[3115]
    (.letOp (n := 3120) (.exec 0x11f1f4 (fun s => s.RIP = 0x11f1f4) (movR64R64Effect 0x11f1f4 14 2) (Reg.operands [.gpr 2] [])) #v[3115]
    (.letOp (n := 3121) (.out 0x11f1f7 (shldR64R64Effect 0x11f1f7 5 9 1 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[3093, 3090]
    (.letOp (n := 3122) (.exec 0x11f1f7 (fun s => s.RIP = 0x11f1f7) (shldR64R64Effect 0x11f1f7 5 9 1 12) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3093, 3090]
    (.letOp (n := 3123) (.out 0x11f1fc (movR64R64Effect 0x11f1fc 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[3045]
    (.letOp (n := 3124) (.exec 0x11f1fc (fun s => s.RIP = 0x11f1fc) (movR64R64Effect 0x11f1fc 0 12) (Reg.operands [.gpr 12] [])) #v[3045]
    (.letOp (n := 3125) (.out 0x11f1ff (mulR64Effect 0x11f1ff 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[3031, 3123]
    (.letOp (n := 3126) (.out 0x11f1ff (mulR64Effect 0x11f1ff 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[3031, 3123]
    (.letOp (n := 3127) (.exec 0x11f1ff (fun s => s.RIP = 0x11f1ff) (mulR64Effect 0x11f1ff 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[3031, 3123]
    (.letOp (n := 3128) (.out 0x11f202 (movR64R64Effect 0x11f202 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[3125]
    (.letOp (n := 3129) (.exec 0x11f202 (fun s => s.RIP = 0x11f202) (movR64R64Effect 0x11f202 12 0) (Reg.operands [.gpr 0] [])) #v[3125]
    (.letOp (n := 3130) (.out 0x11f205 (movR64R64Effect 0x11f205 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[3126]
    (.letOp (n := 3131) (.exec 0x11f205 (fun s => s.RIP = 0x11f205) (movR64R64Effect 0x11f205 13 2) (Reg.operands [.gpr 2] [])) #v[3126]
    (.letOp (n := 3132) (.out 0x11f208 (movR64R64Effect 0x11f208 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[3063]
    (.letOp (n := 3133) (.exec 0x11f208 (fun s => s.RIP = 0x11f208) (movR64R64Effect 0x11f208 0 6) (Reg.operands [.gpr 6] [])) #v[3063]
    (.letOp (n := 3134) (.out 0x11f20b (mulR64Effect 0x11f20b 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[3049, 3132]
    (.letOp (n := 3135) (.out 0x11f20b (mulR64Effect 0x11f20b 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[3049, 3132]
    (.letOp (n := 3136) (.exec 0x11f20b (fun s => s.RIP = 0x11f20b) (mulR64Effect 0x11f20b 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[3049, 3132]
    (.letOp (n := 3137) (.out 0x11f20e (movR64R64Effect 0x11f20e 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[3049]
    (.letOp (n := 3138) (.exec 0x11f20e (fun s => s.RIP = 0x11f20e) (movR64R64Effect 0x11f20e 6 5) (Reg.operands [.gpr 5] [])) #v[3049]
    (.letOp (n := 3139) (.out 0x11f211 (movR64R64Effect 0x11f211 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[3135]
    (.letOp (n := 3140) (.exec 0x11f211 (fun s => s.RIP = 0x11f211) (movR64R64Effect 0x11f211 5 2) (Reg.operands [.gpr 2] [])) #v[3135]
    (.letOp (n := 3141) (.out 0x11f214 (movR64R64Effect 0x11f214 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[3134]
    (.letOp (n := 3142) (.exec 0x11f214 (fun s => s.RIP = 0x11f214) (movR64R64Effect 0x11f214 11 0) (Reg.operands [.gpr 0] [])) #v[3134]
    (.letOp (n := 3143) (.out 0x11f217 (movR64R64Effect 0x11f217 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[3074]
    (.letOp (n := 3144) (.exec 0x11f217 (fun s => s.RIP = 0x11f217) (movR64R64Effect 0x11f217 0 10) (Reg.operands [.gpr 10] [])) #v[3074]
    (.letOp (n := 3145) (.out 0x11f21a (movR64Imm64Effect 0x11f21a 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 3146) (.exec 0x11f21a (fun s => s.RIP = 0x11f21a) (movR64Imm64Effect 0x11f21a 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 3147) (.out 0x11f224 (mulR64Effect 0x11f224 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[3145, 3143]
    (.letOp (n := 3148) (.out 0x11f224 (mulR64Effect 0x11f224 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[3145, 3143]
    (.letOp (n := 3149) (.exec 0x11f224 (fun s => s.RIP = 0x11f224) (mulR64Effect 0x11f224 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3145, 3143]
    (.letOp (n := 3150) (.out 0x11f227 (addR64R64Effect 0x11f227 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[3110, 3101]
    (.letOp (n := 3151) (.out 0x11f227 (addR64R64Effect 0x11f227 7 3) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 3] []) (.flag .CF)) #v[3110, 3101]
    (.letOp (n := 3152) (.exec 0x11f227 (fun s => s.RIP = 0x11f227) (addR64R64Effect 0x11f227 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[3110, 3101]
    (.letOp (n := 3153) (.out 0x11f22a (atFlags StatusFlags.CF (adcR64M64Effect 0x11f22a 8 (.sib 4 none 0 (.d8 0x28)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[3108, 4, 3151]
    (.letOp (n := 3154) (.exec 0x11f22a (LoadPre 0x11f22a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11f22a + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11f22a 8 (.sib 4 none 0 (.d8 0x28)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3108, 4, 3151]
    (b_l11d880_73)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_72 : List UInt8 :=
  [0x48, 0x89, 0xC7, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xA4, 0x24, 0x18, 0x01, 0x00, 0x00, 0x49, 0x89,
    0xC7, 0x49, 0x89, 0xD6, 0x49, 0x0F, 0xA4, 0xC9, 0x0C, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE5, 0x49,
    0x89, 0xC4, 0x49, 0x89, 0xD5, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xEE, 0x48, 0x89,
    0xD5, 0x49, 0x89, 0xC3, 0x4C, 0x89, 0xD0, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00,
    0x00, 0x48, 0xF7, 0xE1, 0x48, 0x01, 0xDF, 0x4C, 0x13, 0x44, 0x24, 0x28] ++ bytes_l11d880_73

theorem code_l11d880_72 : ∀ x ∈ codeRange 0x11f1e3 bytes_l11d880_72, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f1e3 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_73

def b_l11d880_71 : Block Op Label signature Reg.count 3067 :=
  .letOp (n := 3067) (.out 0x11f189 (movR64M64Effect 0x11f189 7 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 3068) (.exec 0x11f189 (LoadPre 0x11f189 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11f189 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f189 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3069) (.out 0x11f191 (mulR64Effect 0x11f191 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[3067, 3065]
    (.letOp (n := 3070) (.out 0x11f191 (mulR64Effect 0x11f191 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[3067, 3065]
    (.letOp (n := 3071) (.exec 0x11f191 (fun s => s.RIP = 0x11f191) (mulR64Effect 0x11f191 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[3067, 3065]
    (.letOp (n := 3072) (.out 0x11f194 (movR64R64Effect 0x11f194 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[3070]
    (.letOp (n := 3073) (.exec 0x11f194 (fun s => s.RIP = 0x11f194) (movR64R64Effect 0x11f194 10 2) (Reg.operands [.gpr 2] [])) #v[3070]
    (.letOp (n := 3074) (.out 0x11f197 (shldR64R64Effect 0x11f197 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[3072, 3069]
    (.letOp (n := 3075) (.exec 0x11f197 (fun s => s.RIP = 0x11f197) (shldR64R64Effect 0x11f197 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3072, 3069]
    (.letOp (n := 3076) (.out 0x11f19c (movR64Imm64Effect 0x11f19c 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 3077) (.exec 0x11f19c (fun s => s.RIP = 0x11f19c) (movR64Imm64Effect 0x11f19c 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 3078) (.out 0x11f1a6 (andR64R64Effect 0x11f1a6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3069, 3076]
    (.letOp (n := 3079) (.exec 0x11f1a6 (fun s => s.RIP = 0x11f1a6) (andR64R64Effect 0x11f1a6 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3069, 3076]
    (.letOp (n := 3080) (.out 0x11f1a9 (movR64Imm64Effect 0x11f1a9 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 3081) (.exec 0x11f1a9 (fun s => s.RIP = 0x11f1a9) (movR64Imm64Effect 0x11f1a9 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 3082) (.out 0x11f1b3 (mulR64Effect 0x11f1b3 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[3080, 3078]
    (.letOp (n := 3083) (.out 0x11f1b3 (mulR64Effect 0x11f1b3 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[3080, 3078]
    (.letOp (n := 3084) (.exec 0x11f1b3 (fun s => s.RIP = 0x11f1b3) (mulR64Effect 0x11f1b3 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3080, 3078]
    (.letOp (n := 3085) (.out 0x11f1b6 (movR64R64Effect 0x11f1b6 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[3083]
    (.letOp (n := 3086) (.exec 0x11f1b6 (fun s => s.RIP = 0x11f1b6) (movR64R64Effect 0x11f1b6 9 2) (Reg.operands [.gpr 2] [])) #v[3083]
    (.letOp (n := 3087) (.out 0x11f1b9 (addR64R64Effect 0x11f1b9 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[3082, 3058]
    (.letOp (n := 3088) (.out 0x11f1b9 (addR64R64Effect 0x11f1b9 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[3082, 3058]
    (.letOp (n := 3089) (.exec 0x11f1b9 (fun s => s.RIP = 0x11f1b9) (addR64R64Effect 0x11f1b9 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[3082, 3058]
    (.letOp (n := 3090) (.out 0x11f1bc (movR64R64Effect 0x11f1bc 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[3087]
    (.letOp (n := 3091) (.exec 0x11f1bc (fun s => s.RIP = 0x11f1bc) (movR64R64Effect 0x11f1bc 1 0) (Reg.operands [.gpr 0] [])) #v[3087]
    (.letOp (n := 3092) (.exec 0x11f1bf (StorePre 0x11f1bf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11f1bf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f1bf 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3087, 4]
    (.letOp (n := 3093) (.out 0x11f1c4 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f1c4 9 8)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[3085, 3061, 3088]
    (.letOp (n := 3094) (.exec 0x11f1c4 (fun s => s.RIP = 0x11f1c4) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f1c4 9 8)) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3085, 3061, 3088]
    (.letOp (n := 3095) (.out 0x11f1c7 (movR64R64Effect 0x11f1c7 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3000]
    (.letOp (n := 3096) (.exec 0x11f1c7 (fun s => s.RIP = 0x11f1c7) (movR64R64Effect 0x11f1c7 0 3) (Reg.operands [.gpr 3] [])) #v[3000]
    (.letOp (n := 3097) (.out 0x11f1ca (mulR64Effect 0x11f1ca 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[3067, 3095]
    (.letOp (n := 3098) (.out 0x11f1ca (mulR64Effect 0x11f1ca 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[3067, 3095]
    (.letOp (n := 3099) (.exec 0x11f1ca (fun s => s.RIP = 0x11f1ca) (mulR64Effect 0x11f1ca 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[3067, 3095]
    (.letOp (n := 3100) (.exec 0x11f1cd (StorePre 0x11f1cd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11f1cd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f1cd 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3098, 4]
    (.letOp (n := 3101) (.out 0x11f1d2 (movR64R64Effect 0x11f1d2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[3097]
    (.letOp (n := 3102) (.exec 0x11f1d2 (fun s => s.RIP = 0x11f1d2) (movR64R64Effect 0x11f1d2 3 0) (Reg.operands [.gpr 0] [])) #v[3097]
    (.letOp (n := 3103) (.out 0x11f1d5 (movR64R64Effect 0x11f1d5 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[3011]
    (.letOp (n := 3104) (.exec 0x11f1d5 (fun s => s.RIP = 0x11f1d5) (movR64R64Effect 0x11f1d5 0 15) (Reg.operands [.gpr 15] [])) #v[3011]
    (.letOp (n := 3105) (.out 0x11f1d8 (mulM64Effect 0x11f1d8 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3103, 4]
    (.letOp (n := 3106) (.out 0x11f1d8 (mulM64Effect 0x11f1d8 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3103, 4]
    (.letOp (n := 3107) (.exec 0x11f1d8 (LoadPre 0x11f1d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11f1d8 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11f1d8 8 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3103, 4]
    (.letOp (n := 3108) (.out 0x11f1e0 (movR64R64Effect 0x11f1e0 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[3106]
    (.letOp (n := 3109) (.exec 0x11f1e0 (fun s => s.RIP = 0x11f1e0) (movR64R64Effect 0x11f1e0 8 2) (Reg.operands [.gpr 2] [])) #v[3106]
    (b_l11d880_72)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_71 : List UInt8 :=
  [0x48, 0x8B, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xD2, 0x49, 0x0F,
    0xA4, 0xC2, 0x0C, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8,
    0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD1,
    0x4C, 0x01, 0xD8, 0x48, 0x89, 0xC1, 0x48, 0x89, 0x44, 0x24, 0x58, 0x4D, 0x11, 0xC1, 0x48, 0x89,
    0xD8, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0x54, 0x24, 0x28, 0x48, 0x89, 0xC3, 0x4C, 0x89, 0xF8, 0x48,
    0xF7, 0xA4, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD0] ++ bytes_l11d880_72

theorem code_l11d880_71 : ∀ x ∈ codeRange 0x11f189 bytes_l11d880_71, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f189 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_72

def b_l11d880_70 : Block Op Label signature Reg.count 3022 :=
  .letOp (n := 3022) (.out 0x11f13d (addR64R64Effect 0x11f13d 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[3020, 3007]
    (.letOp (n := 3023) (.out 0x11f13d (addR64R64Effect 0x11f13d 9 6) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[3020, 3007]
    (.letOp (n := 3024) (.exec 0x11f13d (fun s => s.RIP = 0x11f13d) (addR64R64Effect 0x11f13d 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[3020, 3007]
    (.letOp (n := 3025) (.out 0x11f140 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f140 8 7)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[3018, 3009, 3023]
    (.letOp (n := 3026) (.exec 0x11f140 (fun s => s.RIP = 0x11f140) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f140 8 7)) (Reg.operands [.gpr 8, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3018, 3009, 3023]
    (.letOp (n := 3027) (.out 0x11f143 (movR64M64Effect 0x11f143 14 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 3028) (.exec 0x11f143 (LoadPre 0x11f143 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11f143 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f143 14 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3029) (.out 0x11f148 (movR64R64Effect 0x11f148 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[3027]
    (.letOp (n := 3030) (.exec 0x11f148 (fun s => s.RIP = 0x11f148) (movR64R64Effect 0x11f148 0 14) (Reg.operands [.gpr 14] [])) #v[3027]
    (.letOp (n := 3031) (.out 0x11f14b (movR64M64Effect 0x11f14b 13 (.sib 4 none 0 (.d32 0x1b0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 3032) (.exec 0x11f14b (LoadPre 0x11f14b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x11f14b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f14b 13 (.sib 4 none 0 (.d32 0x1b0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3033) (.out 0x11f153 (mulR64Effect 0x11f153 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[3031, 3029]
    (.letOp (n := 3034) (.out 0x11f153 (mulR64Effect 0x11f153 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[3031, 3029]
    (.letOp (n := 3035) (.exec 0x11f153 (fun s => s.RIP = 0x11f153) (mulR64Effect 0x11f153 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[3031, 3029]
    (.letOp (n := 3036) (.out 0x11f156 (movR64R64Effect 0x11f156 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[3034]
    (.letOp (n := 3037) (.exec 0x11f156 (fun s => s.RIP = 0x11f156) (movR64R64Effect 0x11f156 6 2) (Reg.operands [.gpr 2] [])) #v[3034]
    (.letOp (n := 3038) (.out 0x11f159 (movR64R64Effect 0x11f159 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[3033]
    (.letOp (n := 3039) (.exec 0x11f159 (fun s => s.RIP = 0x11f159) (movR64R64Effect 0x11f159 7 0) (Reg.operands [.gpr 0] [])) #v[3033]
    (.letOp (n := 3040) (.out 0x11f15c (addR64R64Effect 0x11f15c 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[3038, 3022]
    (.letOp (n := 3041) (.out 0x11f15c (addR64R64Effect 0x11f15c 7 9) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 9] []) (.flag .CF)) #v[3038, 3022]
    (.letOp (n := 3042) (.exec 0x11f15c (fun s => s.RIP = 0x11f15c) (addR64R64Effect 0x11f15c 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[3038, 3022]
    (.letOp (n := 3043) (.out 0x11f15f (atFlags StatusFlags.CF (adcR64R64Effect 0x11f15f 6 8)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[3036, 3025, 3041]
    (.letOp (n := 3044) (.exec 0x11f15f (fun s => s.RIP = 0x11f15f) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f15f 6 8)) (Reg.operands [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3036, 3025, 3041]
    (.letOp (n := 3045) (.out 0x11f162 (movR64M64Effect 0x11f162 12 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 3046) (.exec 0x11f162 (LoadPre 0x11f162 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11f162 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f162 12 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3047) (.out 0x11f167 (movR64R64Effect 0x11f167 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[3045]
    (.letOp (n := 3048) (.exec 0x11f167 (fun s => s.RIP = 0x11f167) (movR64R64Effect 0x11f167 0 12) (Reg.operands [.gpr 12] [])) #v[3045]
    (.letOp (n := 3049) (.out 0x11f16a (movR64M64Effect 0x11f16a 5 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 3050) (.exec 0x11f16a (LoadPre 0x11f16a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x11f16a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f16a 5 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3051) (.out 0x11f172 (mulR64Effect 0x11f172 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[3049, 3047]
    (.letOp (n := 3052) (.out 0x11f172 (mulR64Effect 0x11f172 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[3049, 3047]
    (.letOp (n := 3053) (.exec 0x11f172 (fun s => s.RIP = 0x11f172) (mulR64Effect 0x11f172 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[3049, 3047]
    (.letOp (n := 3054) (.out 0x11f175 (movR64R64Effect 0x11f175 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[3052]
    (.letOp (n := 3055) (.exec 0x11f175 (fun s => s.RIP = 0x11f175) (movR64R64Effect 0x11f175 8 2) (Reg.operands [.gpr 2] [])) #v[3052]
    (.letOp (n := 3056) (.out 0x11f178 (movR64R64Effect 0x11f178 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[3051]
    (.letOp (n := 3057) (.exec 0x11f178 (fun s => s.RIP = 0x11f178) (movR64R64Effect 0x11f178 11 0) (Reg.operands [.gpr 0] [])) #v[3051]
    (.letOp (n := 3058) (.out 0x11f17b (addR64R64Effect 0x11f17b 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[3056, 3040]
    (.letOp (n := 3059) (.out 0x11f17b (addR64R64Effect 0x11f17b 11 7) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 7] []) (.flag .CF)) #v[3056, 3040]
    (.letOp (n := 3060) (.exec 0x11f17b (fun s => s.RIP = 0x11f17b) (addR64R64Effect 0x11f17b 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[3056, 3040]
    (.letOp (n := 3061) (.out 0x11f17e (atFlags StatusFlags.CF (adcR64R64Effect 0x11f17e 8 6)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[3054, 3043, 3059]
    (.letOp (n := 3062) (.exec 0x11f17e (fun s => s.RIP = 0x11f17e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f17e 8 6)) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3054, 3043, 3059]
    (.letOp (n := 3063) (.out 0x11f181 (movR64M64Effect 0x11f181 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 3064) (.exec 0x11f181 (LoadPre 0x11f181 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11f181 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f181 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3065) (.out 0x11f186 (movR64R64Effect 0x11f186 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[3063]
    (.letOp (n := 3066) (.exec 0x11f186 (fun s => s.RIP = 0x11f186) (movR64R64Effect 0x11f186 0 6) (Reg.operands [.gpr 6] [])) #v[3063]
    (b_l11d880_71)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_70 : List UInt8 :=
  [0x49, 0x01, 0xF1, 0x49, 0x11, 0xF8, 0x4C, 0x8B, 0x74, 0x24, 0x70, 0x4C, 0x89, 0xF0, 0x4C, 0x8B,
    0xAC, 0x24, 0xB0, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0xD6, 0x48, 0x89, 0xC7, 0x4C,
    0x01, 0xCF, 0x4C, 0x11, 0xC6, 0x4C, 0x8B, 0x64, 0x24, 0x38, 0x4C, 0x89, 0xE0, 0x48, 0x8B, 0xAC,
    0x24, 0x20, 0x01, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC3, 0x49, 0x01,
    0xFB, 0x49, 0x11, 0xF0, 0x48, 0x8B, 0x74, 0x24, 0x08, 0x48, 0x89, 0xF0] ++ bytes_l11d880_71

theorem code_l11d880_70 : ∀ x ∈ codeRange 0x11f13d bytes_l11d880_70, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f13d 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_71

def b_l11d880_69 : Block Op Label signature Reg.count 2985 :=
  .letOp (n := 2985) (.exec 0x11f0df (StorePre 0x11f0df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11f0df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f0df 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2983, 4]
    (.letOp (n := 2986) (.out 0x11f0e4 (movR64Imm64Effect 0x11f0e4 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 2987) (.exec 0x11f0e4 (fun s => s.RIP = 0x11f0e4) (movR64Imm64Effect 0x11f0e4 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2988) (.out 0x11f0ee (andR64R64Effect 0x11f0ee 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[2943, 2986]
    (.letOp (n := 2989) (.exec 0x11f0ee (fun s => s.RIP = 0x11f0ee) (andR64R64Effect 0x11f0ee 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[2943, 2986]
    (.letOp (n := 2990) (.exec 0x11f0f1 (StorePre 0x11f0f1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11f0f1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f0f1 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[2988, 4]
    (.letOp (n := 2991) (.out 0x11f0f6 (andR64R64Effect 0x11f0f6 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[2961, 2986]
    (.letOp (n := 2992) (.exec 0x11f0f6 (fun s => s.RIP = 0x11f0f6) (andR64R64Effect 0x11f0f6 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2961, 2986]
    (.letOp (n := 2993) (.exec 0x11f0f9 (StorePre 0x11f0f9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11f0f9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f0f9 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[2991, 4]
    (.letOp (n := 2994) (.out 0x11f0fe (andR64R64Effect 0x11f0fe 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2965, 2986]
    (.letOp (n := 2995) (.exec 0x11f0fe (fun s => s.RIP = 0x11f0fe) (andR64R64Effect 0x11f0fe 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2965, 2986]
    (.letOp (n := 2996) (.exec 0x11f101 (StorePre 0x11f101 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11f101 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f101 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2994, 4]
    (.letOp (n := 2997) (.out 0x11f106 (andR64R64Effect 0x11f106 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[2975, 2986]
    (.letOp (n := 2998) (.exec 0x11f106 (fun s => s.RIP = 0x11f106) (andR64R64Effect 0x11f106 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[2975, 2986]
    (.letOp (n := 2999) (.exec 0x11f109 (StorePre 0x11f109 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11f109 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11f109 8 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[2997, 4]
    (.letOp (n := 3000) (.out 0x11f10e (movR64M64Effect 0x11f10e 3 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 3001) (.exec 0x11f10e (LoadPre 0x11f10e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11f10e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f10e 3 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3002) (.out 0x11f113 (movR64R64Effect 0x11f113 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3000]
    (.letOp (n := 3003) (.exec 0x11f113 (fun s => s.RIP = 0x11f113) (movR64R64Effect 0x11f113 0 3) (Reg.operands [.gpr 3] [])) #v[3000]
    (.letOp (n := 3004) (.out 0x11f116 (mulM64Effect 0x11f116 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3002, 4]
    (.letOp (n := 3005) (.out 0x11f116 (mulM64Effect 0x11f116 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3002, 4]
    (.letOp (n := 3006) (.exec 0x11f116 (LoadPre 0x11f116 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11f116 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11f116 8 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3002, 4]
    (.letOp (n := 3007) (.out 0x11f11e (movR64R64Effect 0x11f11e 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[3004]
    (.letOp (n := 3008) (.exec 0x11f11e (fun s => s.RIP = 0x11f11e) (movR64R64Effect 0x11f11e 6 0) (Reg.operands [.gpr 0] [])) #v[3004]
    (.letOp (n := 3009) (.out 0x11f121 (movR64R64Effect 0x11f121 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[3005]
    (.letOp (n := 3010) (.exec 0x11f121 (fun s => s.RIP = 0x11f121) (movR64R64Effect 0x11f121 7 2) (Reg.operands [.gpr 2] [])) #v[3005]
    (.letOp (n := 3011) (.out 0x11f124 (movR64M64Effect 0x11f124 15 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 3012) (.exec 0x11f124 (LoadPre 0x11f124 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11f124 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f124 15 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3013) (.out 0x11f12c (movR64R64Effect 0x11f12c 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[3011]
    (.letOp (n := 3014) (.exec 0x11f12c (fun s => s.RIP = 0x11f12c) (movR64R64Effect 0x11f12c 0 15) (Reg.operands [.gpr 15] [])) #v[3011]
    (.letOp (n := 3015) (.out 0x11f12f (mulM64Effect 0x11f12f 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3013, 4]
    (.letOp (n := 3016) (.out 0x11f12f (mulM64Effect 0x11f12f 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3013, 4]
    (.letOp (n := 3017) (.exec 0x11f12f (LoadPre 0x11f12f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x11f12f + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11f12f 8 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3013, 4]
    (.letOp (n := 3018) (.out 0x11f137 (movR64R64Effect 0x11f137 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[3016]
    (.letOp (n := 3019) (.exec 0x11f137 (fun s => s.RIP = 0x11f137) (movR64R64Effect 0x11f137 8 2) (Reg.operands [.gpr 2] [])) #v[3016]
    (.letOp (n := 3020) (.out 0x11f13a (movR64R64Effect 0x11f13a 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[3015]
    (.letOp (n := 3021) (.exec 0x11f13a (fun s => s.RIP = 0x11f13a) (movR64R64Effect 0x11f13a 9 0) (Reg.operands [.gpr 0] [])) #v[3015]
    (b_l11d880_70)))))))))))))))))))))))))))))))))))))

def bytes_l11d880_69 : List UInt8 :=
  [0x48, 0x89, 0x4C, 0x24, 0x30, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48,
    0x21, 0xC6, 0x48, 0x89, 0x74, 0x24, 0x48, 0x49, 0x21, 0xC1, 0x4C, 0x89, 0x4C, 0x24, 0x60, 0x48,
    0x21, 0xC2, 0x48, 0x89, 0x54, 0x24, 0x10, 0x49, 0x21, 0xC0, 0x4C, 0x89, 0x44, 0x24, 0x40, 0x48,
    0x8B, 0x5C, 0x24, 0x68, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0xA4, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48,
    0x89, 0xC6, 0x48, 0x89, 0xD7, 0x4C, 0x8B, 0xBC, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF8,
    0x48, 0xF7, 0xA4, 0x24, 0x18, 0x01, 0x00, 0x00, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC1] ++ bytes_l11d880_70

theorem code_l11d880_69 : ∀ x ∈ codeRange 0x11f0df bytes_l11d880_69, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f0df 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_70

def b_l11d880_68 : Block Op Label signature Reg.count 2945 :=
  .letOp (n := 2945) (.out 0x11f097 (shlR64Effect 0x11f097 4 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2805]
    (.letOp (n := 2946) (.exec 0x11f097 (fun s => s.RIP = 0x11f097) (shlR64Effect 0x11f097 4 10 3) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2805]
    (.letOp (n := 2947) (.out 0x11f09b (andR64R64Effect 0x11f09b 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[2945, 2931]
    (.letOp (n := 2948) (.exec 0x11f09b (fun s => s.RIP = 0x11f09b) (andR64R64Effect 0x11f09b 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[2945, 2931]
    (.letOp (n := 2949) (.out 0x11f09e (movR64R64Effect 0x11f09e 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[2943]
    (.letOp (n := 2950) (.exec 0x11f09e (fun s => s.RIP = 0x11f09e) (movR64R64Effect 0x11f09e 8 6) (Reg.operands [.gpr 6] [])) #v[2943]
    (.letOp (n := 2951) (.out 0x11f0a1 (shrR64Effect 0x11f0a1 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2949]
    (.letOp (n := 2952) (.exec 0x11f0a1 (fun s => s.RIP = 0x11f0a1) (shrR64Effect 0x11f0a1 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2949]
    (.letOp (n := 2953) (.out 0x11f0a5 (addR64R64Effect 0x11f0a5 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[2951, 2947]
    (.letOp (n := 2954) (.exec 0x11f0a5 (fun s => s.RIP = 0x11f0a5) (addR64R64Effect 0x11f0a5 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[2951, 2947]
    (.letOp (n := 2955) (.out 0x11f0a8 (shlR64Effect 0x11f0a8 4 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[2889]
    (.letOp (n := 2956) (.exec 0x11f0a8 (fun s => s.RIP = 0x11f0a8) (shlR64Effect 0x11f0a8 4 14 3) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2889]
    (.letOp (n := 2957) (.out 0x11f0ac (andR64R64Effect 0x11f0ac 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[2955, 2931]
    (.letOp (n := 2958) (.exec 0x11f0ac (fun s => s.RIP = 0x11f0ac) (andR64R64Effect 0x11f0ac 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[2955, 2931]
    (.letOp (n := 2959) (.out 0x11f0af (movR64R64Effect 0x11f0af 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[2953]
    (.letOp (n := 2960) (.exec 0x11f0af (fun s => s.RIP = 0x11f0af) (movR64R64Effect 0x11f0af 2 8) (Reg.operands [.gpr 8] [])) #v[2953]
    (.letOp (n := 2961) (.out 0x11f0b2 (movR64R64Effect 0x11f0b2 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[2953]
    (.letOp (n := 2962) (.exec 0x11f0b2 (fun s => s.RIP = 0x11f0b2) (movR64R64Effect 0x11f0b2 9 8) (Reg.operands [.gpr 8] [])) #v[2953]
    (.letOp (n := 2963) (.out 0x11f0b5 (shrR64Effect 0x11f0b5 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2959]
    (.letOp (n := 2964) (.exec 0x11f0b5 (fun s => s.RIP = 0x11f0b5) (shrR64Effect 0x11f0b5 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2959]
    (.letOp (n := 2965) (.out 0x11f0b9 (addR64R64Effect 0x11f0b9 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[2963, 2957]
    (.letOp (n := 2966) (.exec 0x11f0b9 (fun s => s.RIP = 0x11f0b9) (addR64R64Effect 0x11f0b9 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[2963, 2957]
    (.letOp (n := 2967) (.out 0x11f0bc (shlR64Effect 0x11f0bc 4 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[2914]
    (.letOp (n := 2968) (.exec 0x11f0bc (fun s => s.RIP = 0x11f0bc) (shlR64Effect 0x11f0bc 4 7 3) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2914]
    (.letOp (n := 2969) (.out 0x11f0c0 (andR64R64Effect 0x11f0c0 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[2967, 2931]
    (.letOp (n := 2970) (.exec 0x11f0c0 (fun s => s.RIP = 0x11f0c0) (andR64R64Effect 0x11f0c0 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[2967, 2931]
    (.letOp (n := 2971) (.out 0x11f0c3 (movR64R64Effect 0x11f0c3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2965]
    (.letOp (n := 2972) (.exec 0x11f0c3 (fun s => s.RIP = 0x11f0c3) (movR64R64Effect 0x11f0c3 8 2) (Reg.operands [.gpr 2] [])) #v[2965]
    (.letOp (n := 2973) (.out 0x11f0c6 (shrR64Effect 0x11f0c6 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2971]
    (.letOp (n := 2974) (.exec 0x11f0c6 (fun s => s.RIP = 0x11f0c6) (shrR64Effect 0x11f0c6 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2971]
    (.letOp (n := 2975) (.out 0x11f0ca (addR64R64Effect 0x11f0ca 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[2973, 2969]
    (.letOp (n := 2976) (.exec 0x11f0ca (fun s => s.RIP = 0x11f0ca) (addR64R64Effect 0x11f0ca 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[2973, 2969]
    (.letOp (n := 2977) (.out 0x11f0cd (andR64M64Effect 0x11f0cd 0 (.sib 4 none 0 (.d32 0x1c8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2935, 4]
    (.letOp (n := 2978) (.exec 0x11f0cd (LoadPre 0x11f0cd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x11f0cd + BitVec.ofNat 64 8)) 8) (andR64M64Effect 0x11f0cd 0 (.sib 4 none 0 (.d32 0x1c8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2935, 4]
    (.letOp (n := 2979) (.out 0x11f0d5 (movR64R64Effect 0x11f0d5 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[2975]
    (.letOp (n := 2980) (.exec 0x11f0d5 (fun s => s.RIP = 0x11f0d5) (movR64R64Effect 0x11f0d5 1 8) (Reg.operands [.gpr 8] [])) #v[2975]
    (.letOp (n := 2981) (.out 0x11f0d8 (shrR64Effect 0x11f0d8 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2979]
    (.letOp (n := 2982) (.exec 0x11f0d8 (fun s => s.RIP = 0x11f0d8) (shrR64Effect 0x11f0d8 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2979]
    (.letOp (n := 2983) (.out 0x11f0dc (addR64R64Effect 0x11f0dc 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2981, 2977]
    (.letOp (n := 2984) (.exec 0x11f0dc (fun s => s.RIP = 0x11f0dc) (addR64R64Effect 0x11f0dc 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2981, 2977]
    (b_l11d880_69))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_68 : List UInt8 :=
  [0x49, 0xC1, 0xE2, 0x03, 0x49, 0x21, 0xCA, 0x49, 0x89, 0xF0, 0x49, 0xC1, 0xE8, 0x34, 0x4D, 0x01,
    0xD0, 0x49, 0xC1, 0xE6, 0x03, 0x49, 0x21, 0xCE, 0x4C, 0x89, 0xC2, 0x4D, 0x89, 0xC1, 0x48, 0xC1,
    0xEA, 0x34, 0x4C, 0x01, 0xF2, 0x48, 0xC1, 0xE7, 0x03, 0x48, 0x21, 0xCF, 0x49, 0x89, 0xD0, 0x49,
    0xC1, 0xE8, 0x34, 0x49, 0x01, 0xF8, 0x48, 0x23, 0x84, 0x24, 0xC8, 0x01, 0x00, 0x00, 0x4C, 0x89,
    0xC1, 0x48, 0xC1, 0xE9, 0x34, 0x48, 0x01, 0xC1] ++ bytes_l11d880_69

theorem code_l11d880_68 : ∀ x ∈ codeRange 0x11f097 bytes_l11d880_68, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f097 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_69

def b_l11d880_67 : Block Op Label signature Reg.count 2903 :=
  .letOp (n := 2903) (.out 0x11f02c (movR64Imm64Effect 0x11f02c 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2904) (.exec 0x11f02c (fun s => s.RIP = 0x11f02c) (movR64Imm64Effect 0x11f02c 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2905) (.out 0x11f036 (movR64M64Effect 0x11f036 7 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 2906) (.exec 0x11f036 (LoadPre 0x11f036 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11f036 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f036 7 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2907) (.out 0x11f03e (andR64R64Effect 0x11f03e 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[2905, 2903]
    (.letOp (n := 2908) (.exec 0x11f03e (fun s => s.RIP = 0x11f03e) (andR64R64Effect 0x11f03e 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[2905, 2903]
    (.letOp (n := 2909) (.out 0x11f041 (addR64R64Effect 0x11f041 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[2907, 2898]
    (.letOp (n := 2910) (.out 0x11f041 (addR64R64Effect 0x11f041 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[2907, 2898]
    (.letOp (n := 2911) (.exec 0x11f041 (fun s => s.RIP = 0x11f041) (addR64R64Effect 0x11f041 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2907, 2898]
    (.letOp (n := 2912) (.out 0x11f044 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f044 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2899, 2910]
    (.letOp (n := 2913) (.exec 0x11f044 (fun s => s.RIP = 0x11f044) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f044 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2899, 2910]
    (.letOp (n := 2914) (.out 0x11f048 (addR64R64Effect 0x11f048 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[2909, 2901]
    (.letOp (n := 2915) (.out 0x11f048 (addR64R64Effect 0x11f048 7 12) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 12] []) (.flag .CF)) #v[2909, 2901]
    (.letOp (n := 2916) (.exec 0x11f048 (fun s => s.RIP = 0x11f048) (addR64R64Effect 0x11f048 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[2909, 2901]
    (.letOp (n := 2917) (.out 0x11f04b (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f04b 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2912, 2915]
    (.letOp (n := 2918) (.exec 0x11f04b (fun s => s.RIP = 0x11f04b) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f04b 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2912, 2915]
    (.letOp (n := 2919) (.out 0x11f04f (shldR64R64Effect 0x11f04f 5 2 7 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2917, 2914]
    (.letOp (n := 2920) (.exec 0x11f04f (fun s => s.RIP = 0x11f04f) (shldR64R64Effect 0x11f04f 5 2 7 12) (Reg.operands [.gpr 2, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2917, 2914]
    (.letOp (n := 2921) (.out 0x11f054 (movR64Imm64Effect 0x11f054 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 2922) (.exec 0x11f054 (fun s => s.RIP = 0x11f054) (movR64Imm64Effect 0x11f054 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2923) (.out 0x11f05e (movR64M64Effect 0x11f05e 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 2924) (.exec 0x11f05e (LoadPre 0x11f05e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11f05e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11f05e 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2925) (.out 0x11f063 (andR64R64Effect 0x11f063 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[2923, 2921]
    (.letOp (n := 2926) (.exec 0x11f063 (fun s => s.RIP = 0x11f063) (andR64R64Effect 0x11f063 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[2923, 2921]
    (.letOp (n := 2927) (.out 0x11f066 (addR64R64Effect 0x11f066 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[2925, 2919]
    (.letOp (n := 2928) (.exec 0x11f066 (fun s => s.RIP = 0x11f066) (addR64R64Effect 0x11f066 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[2925, 2919]
    (.letOp (n := 2929) (.out 0x11f069 (shlR64Effect 0x11f069 4 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2717]
    (.letOp (n := 2930) (.exec 0x11f069 (fun s => s.RIP = 0x11f069) (shlR64Effect 0x11f069 4 8 3) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2717]
    (.letOp (n := 2931) (.out 0x11f06d (movR64Imm64Effect 0x11f06d 1 0x7ffffffffffff8) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2932) (.exec 0x11f06d (fun s => s.RIP = 0x11f06d) (movR64Imm64Effect 0x11f06d 1 0x7ffffffffffff8) (Reg.operands [] [])) #v[]
    (.letOp (n := 2933) (.out 0x11f077 (andR64R64Effect 0x11f077 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[2929, 2931]
    (.letOp (n := 2934) (.exec 0x11f077 (fun s => s.RIP = 0x11f077) (andR64R64Effect 0x11f077 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[2929, 2931]
    (.letOp (n := 2935) (.out 0x11f07a (leaR64Effect 0x11f07a 0 (.abs (some 6) 3 0x0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2927]
    (.letOp (n := 2936) (.exec 0x11f07a (fun s => s.RIP = 0x11f07a) (leaR64Effect 0x11f07a 0 (.abs (some 6) 3 0x0)) (Reg.operands [.gpr 6] [])) #v[2927]
    (.letOp (n := 2937) (.out 0x11f082 (shrR64Effect 0x11f082 4 6 45) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[2927]
    (.letOp (n := 2938) (.exec 0x11f082 (fun s => s.RIP = 0x11f082) (shrR64Effect 0x11f082 4 6 45) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2927]
    (.letOp (n := 2939) (.out 0x11f086 (movR64Imm64Effect 0x11f086 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2940) (.exec 0x11f086 (fun s => s.RIP = 0x11f086) (movR64Imm64Effect 0x11f086 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 2941) (.out 0x11f090 (imulR64R64Effect 0x11f090 4 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[2937, 2939]
    (.letOp (n := 2942) (.exec 0x11f090 (fun s => s.RIP = 0x11f090) (imulR64R64Effect 0x11f090 4 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[2937, 2939]
    (.letOp (n := 2943) (.out 0x11f094 (addR64R64Effect 0x11f094 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[2941, 2933]
    (.letOp (n := 2944) (.exec 0x11f094 (fun s => s.RIP = 0x11f094) (addR64R64Effect 0x11f094 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[2941, 2933]
    (b_l11d880_68))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_67 : List UInt8 :=
  [0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x8B, 0xBC, 0x24, 0xA0, 0x00,
    0x00, 0x00, 0x48, 0x21, 0xCF, 0x48, 0x01, 0xC7, 0x48, 0x83, 0xD2, 0x00, 0x4C, 0x01, 0xE7, 0x48,
    0x83, 0xD2, 0x00, 0x48, 0x0F, 0xA4, 0xFA, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x48, 0x48, 0x21, 0xC6, 0x48, 0x01, 0xD6, 0x49, 0xC1, 0xE0,
    0x03, 0x48, 0xB9, 0xF8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x00, 0x49, 0x21, 0xC8, 0x48, 0x8D,
    0x04, 0xF5, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC1, 0xEE, 0x2D, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xF2, 0x4C, 0x01, 0xC6] ++ bytes_l11d880_68

theorem code_l11d880_67 : ∀ x ∈ codeRange 0x11f02c bytes_l11d880_67, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f02c 107 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_68

def b_l11d880_66 : Block Op Label signature Reg.count 2856 :=
  .letOp (n := 2856) (.out 0x11efd8 (atFlags StatusFlags.CF (adcR64R64Effect 0x11efd8 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[2844, 2849, 2854]
    (.letOp (n := 2857) (.exec 0x11efd8 (fun s => s.RIP = 0x11efd8) (atFlags StatusFlags.CF (adcR64R64Effect 0x11efd8 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2844, 2849, 2854]
    (.letOp (n := 2858) (.out 0x11efdb (addR64R64Effect 0x11efdb 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[2853, 2784]
    (.letOp (n := 2859) (.out 0x11efdb (addR64R64Effect 0x11efdb 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[2853, 2784]
    (.letOp (n := 2860) (.exec 0x11efdb (fun s => s.RIP = 0x11efdb) (addR64R64Effect 0x11efdb 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[2853, 2784]
    (.letOp (n := 2861) (.out 0x11efde (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11efde 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[2856, 2859]
    (.letOp (n := 2862) (.exec 0x11efde (fun s => s.RIP = 0x11efde) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11efde 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2856, 2859]
    (.letOp (n := 2863) (.out 0x11efe2 (movR64R64Effect 0x11efe2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[2858]
    (.letOp (n := 2864) (.exec 0x11efe2 (fun s => s.RIP = 0x11efe2) (movR64R64Effect 0x11efe2 0 5) (Reg.operands [.gpr 5] [])) #v[2858]
    (.letOp (n := 2865) (.out 0x11efe5 (movR64Imm64Effect 0x11efe5 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2866) (.exec 0x11efe5 (fun s => s.RIP = 0x11efe5) (movR64Imm64Effect 0x11efe5 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2867) (.out 0x11efef (andR64R64Effect 0x11efef 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2863, 2865]
    (.letOp (n := 2868) (.exec 0x11efef (fun s => s.RIP = 0x11efef) (andR64R64Effect 0x11efef 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2863, 2865]
    (.letOp (n := 2869) (.out 0x11eff2 (movR64Imm64Effect 0x11eff2 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2870) (.exec 0x11eff2 (fun s => s.RIP = 0x11eff2) (movR64Imm64Effect 0x11eff2 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2871) (.out 0x11effc (mulR64Effect 0x11effc 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2869, 2867]
    (.letOp (n := 2872) (.out 0x11effc (mulR64Effect 0x11effc 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2869, 2867]
    (.letOp (n := 2873) (.exec 0x11effc (fun s => s.RIP = 0x11effc) (mulR64Effect 0x11effc 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2869, 2867]
    (.letOp (n := 2874) (.out 0x11efff (addR64M64Effect 0x11efff 14 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[2824, 4]
    (.letOp (n := 2875) (.out 0x11efff (addR64M64Effect 0x11efff 14 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 4] []) (.flag .CF)) #v[2824, 4]
    (.letOp (n := 2876) (.exec 0x11efff (LoadPre 0x11efff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11efff + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11efff 14 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[2824, 4]
    (.letOp (n := 2877) (.out 0x11f004 (atFlags StatusFlags.CF (adcR64M64Effect 0x11f004 12 (.sib 4 none 0 (.d8 0x58)))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 12))) #v[2822, 4, 2875]
    (.letOp (n := 2878) (.exec 0x11f004 (LoadPre 0x11f004 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11f004 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11f004 12 (.sib 4 none 0 (.d8 0x58)))) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2822, 4, 2875]
    (.letOp (n := 2879) (.out 0x11f009 (addR64R64Effect 0x11f009 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[2874, 2831]
    (.letOp (n := 2880) (.out 0x11f009 (addR64R64Effect 0x11f009 14 13) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 13] []) (.flag .CF)) #v[2874, 2831]
    (.letOp (n := 2881) (.exec 0x11f009 (fun s => s.RIP = 0x11f009) (addR64R64Effect 0x11f009 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[2874, 2831]
    (.letOp (n := 2882) (.out 0x11f00c (atFlags StatusFlags.CF (adcR64R64Effect 0x11f00c 12 11)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[2877, 2833, 2880]
    (.letOp (n := 2883) (.exec 0x11f00c (fun s => s.RIP = 0x11f00c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f00c 12 11)) (Reg.operands [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2877, 2833, 2880]
    (.letOp (n := 2884) (.out 0x11f00f (addR64R64Effect 0x11f00f 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[2879, 2871]
    (.letOp (n := 2885) (.out 0x11f00f (addR64R64Effect 0x11f00f 14 0) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 0] []) (.flag .CF)) #v[2879, 2871]
    (.letOp (n := 2886) (.exec 0x11f00f (fun s => s.RIP = 0x11f00f) (addR64R64Effect 0x11f00f 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[2879, 2871]
    (.letOp (n := 2887) (.out 0x11f012 (atFlags StatusFlags.CF (adcR64R64Effect 0x11f012 12 2)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[2882, 2872, 2885]
    (.letOp (n := 2888) (.exec 0x11f012 (fun s => s.RIP = 0x11f012) (atFlags StatusFlags.CF (adcR64R64Effect 0x11f012 12 2)) (Reg.operands [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2882, 2872, 2885]
    (.letOp (n := 2889) (.out 0x11f015 (addR64R64Effect 0x11f015 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[2884, 2835]
    (.letOp (n := 2890) (.out 0x11f015 (addR64R64Effect 0x11f015 14 3) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 3] []) (.flag .CF)) #v[2884, 2835]
    (.letOp (n := 2891) (.exec 0x11f015 (fun s => s.RIP = 0x11f015) (addR64R64Effect 0x11f015 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[2884, 2835]
    (.letOp (n := 2892) (.out 0x11f018 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f018 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[2887, 2890]
    (.letOp (n := 2893) (.exec 0x11f018 (fun s => s.RIP = 0x11f018) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11f018 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2887, 2890]
    (.letOp (n := 2894) (.out 0x11f01c (shldR64R64Effect 0x11f01c 5 9 5 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2861, 2858]
    (.letOp (n := 2895) (.exec 0x11f01c (fun s => s.RIP = 0x11f01c) (shldR64R64Effect 0x11f01c 5 9 5 12) (Reg.operands [.gpr 9, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2861, 2858]
    (.letOp (n := 2896) (.out 0x11f021 (movR64R64Effect 0x11f021 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2894]
    (.letOp (n := 2897) (.exec 0x11f021 (fun s => s.RIP = 0x11f021) (movR64R64Effect 0x11f021 0 9) (Reg.operands [.gpr 9] [])) #v[2894]
    (.letOp (n := 2898) (.out 0x11f024 (mulR64Effect 0x11f024 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2869, 2896]
    (.letOp (n := 2899) (.out 0x11f024 (mulR64Effect 0x11f024 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2869, 2896]
    (.letOp (n := 2900) (.exec 0x11f024 (fun s => s.RIP = 0x11f024) (mulR64Effect 0x11f024 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2869, 2896]
    (.letOp (n := 2901) (.out 0x11f027 (shldR64R64Effect 0x11f027 5 12 14 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[2892, 2889]
    (.letOp (n := 2902) (.exec 0x11f027 (fun s => s.RIP = 0x11f027) (shldR64R64Effect 0x11f027 5 12 14 12) (Reg.operands [.gpr 12, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2892, 2889]
    (b_l11d880_67)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_66 : List UInt8 :=
  [0x49, 0x11, 0xD1, 0x4C, 0x01, 0xFD, 0x49, 0x83, 0xD1, 0x00, 0x48, 0x89, 0xE8, 0x48, 0xB9, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x4C, 0x03, 0x74, 0x24, 0x18, 0x4C, 0x13, 0x64, 0x24,
    0x58, 0x4D, 0x01, 0xEE, 0x4D, 0x11, 0xDC, 0x49, 0x01, 0xC6, 0x49, 0x11, 0xD4, 0x49, 0x01, 0xDE,
    0x49, 0x83, 0xD4, 0x00, 0x49, 0x0F, 0xA4, 0xE9, 0x0C, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0xE1, 0x4D,
    0x0F, 0xA4, 0xF4, 0x0C] ++ bytes_l11d880_67

theorem code_l11d880_66 : ∀ x ∈ codeRange 0x11efd8 bytes_l11d880_66, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1efd8 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_67

def b_l11d880_65 : Block Op Label signature Reg.count 2812 :=
  .letOp (n := 2812) (.out 0x11ef87 (mulR64Effect 0x11ef87 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[2764, 2810]
    (.letOp (n := 2813) (.out 0x11ef87 (mulR64Effect 0x11ef87 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[2764, 2810]
    (.letOp (n := 2814) (.exec 0x11ef87 (fun s => s.RIP = 0x11ef87) (mulR64Effect 0x11ef87 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2764, 2810]
    (.letOp (n := 2815) (.exec 0x11ef8a (StorePre 0x11ef8a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11ef8a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ef8a 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2813, 4]
    (.letOp (n := 2816) (.exec 0x11ef8f (StorePre 0x11ef8f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11ef8f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ef8f 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2812, 4]
    (.letOp (n := 2817) (.out 0x11ef94 (movR64M64Effect 0x11ef94 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2818) (.exec 0x11ef94 (LoadPre 0x11ef94 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11ef94 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ef94 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2819) (.out 0x11ef9c (mulM64Effect 0x11ef9c 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2817, 4]
    (.letOp (n := 2820) (.out 0x11ef9c (mulM64Effect 0x11ef9c 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2817, 4]
    (.letOp (n := 2821) (.exec 0x11ef9c (LoadPre 0x11ef9c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11ef9c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11ef9c 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2817, 4]
    (.letOp (n := 2822) (.out 0x11efa1 (movR64R64Effect 0x11efa1 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2820]
    (.letOp (n := 2823) (.exec 0x11efa1 (fun s => s.RIP = 0x11efa1) (movR64R64Effect 0x11efa1 12 2) (Reg.operands [.gpr 2] [])) #v[2820]
    (.letOp (n := 2824) (.out 0x11efa4 (movR64R64Effect 0x11efa4 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[2819]
    (.letOp (n := 2825) (.exec 0x11efa4 (fun s => s.RIP = 0x11efa4) (movR64R64Effect 0x11efa4 14 0) (Reg.operands [.gpr 0] [])) #v[2819]
    (.letOp (n := 2826) (.out 0x11efa7 (movR64R64Effect 0x11efa7 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2738]
    (.letOp (n := 2827) (.exec 0x11efa7 (fun s => s.RIP = 0x11efa7) (movR64R64Effect 0x11efa7 0 11) (Reg.operands [.gpr 11] [])) #v[2738]
    (.letOp (n := 2828) (.out 0x11efaa (mulM64Effect 0x11efaa 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2826, 4]
    (.letOp (n := 2829) (.out 0x11efaa (mulM64Effect 0x11efaa 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2826, 4]
    (.letOp (n := 2830) (.exec 0x11efaa (LoadPre 0x11efaa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11efaa + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11efaa 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2826, 4]
    (.letOp (n := 2831) (.out 0x11efaf (movR64R64Effect 0x11efaf 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[2828]
    (.letOp (n := 2832) (.exec 0x11efaf (fun s => s.RIP = 0x11efaf) (movR64R64Effect 0x11efaf 13 0) (Reg.operands [.gpr 0] [])) #v[2828]
    (.letOp (n := 2833) (.out 0x11efb2 (movR64R64Effect 0x11efb2 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2829]
    (.letOp (n := 2834) (.exec 0x11efb2 (fun s => s.RIP = 0x11efb2) (movR64R64Effect 0x11efb2 11 2) (Reg.operands [.gpr 2] [])) #v[2829]
    (.letOp (n := 2835) (.out 0x11efb5 (shldR64R64Effect 0x11efb5 5 3 10 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[2808, 2805]
    (.letOp (n := 2836) (.exec 0x11efb5 (fun s => s.RIP = 0x11efb5) (shldR64R64Effect 0x11efb5 5 3 10 12) (Reg.operands [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2808, 2805]
    (.letOp (n := 2837) (.out 0x11efba (movR64R64Effect 0x11efba 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[2751]
    (.letOp (n := 2838) (.exec 0x11efba (fun s => s.RIP = 0x11efba) (movR64R64Effect 0x11efba 0 7) (Reg.operands [.gpr 7] [])) #v[2751]
    (.letOp (n := 2839) (.out 0x11efbd (mulM64Effect 0x11efbd 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2837, 4]
    (.letOp (n := 2840) (.out 0x11efbd (mulM64Effect 0x11efbd 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2837, 4]
    (.letOp (n := 2841) (.exec 0x11efbd (LoadPre 0x11efbd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11efbd + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11efbd 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2837, 4]
    (.letOp (n := 2842) (.out 0x11efc2 (movR64R64Effect 0x11efc2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2839]
    (.letOp (n := 2843) (.exec 0x11efc2 (fun s => s.RIP = 0x11efc2) (movR64R64Effect 0x11efc2 6 0) (Reg.operands [.gpr 0] [])) #v[2839]
    (.letOp (n := 2844) (.out 0x11efc5 (movR64R64Effect 0x11efc5 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2840]
    (.letOp (n := 2845) (.exec 0x11efc5 (fun s => s.RIP = 0x11efc5) (movR64R64Effect 0x11efc5 9 2) (Reg.operands [.gpr 2] [])) #v[2840]
    (.letOp (n := 2846) (.out 0x11efc8 (movR64M64Effect 0x11efc8 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2847) (.exec 0x11efc8 (LoadPre 0x11efc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11efc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11efc8 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2848) (.out 0x11efcd (mulM64Effect 0x11efcd 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2846, 4]
    (.letOp (n := 2849) (.out 0x11efcd (mulM64Effect 0x11efcd 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2846, 4]
    (.letOp (n := 2850) (.exec 0x11efcd (LoadPre 0x11efcd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11efcd + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11efcd 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2846, 4]
    (.letOp (n := 2851) (.out 0x11efd2 (movR64R64Effect 0x11efd2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[2848]
    (.letOp (n := 2852) (.exec 0x11efd2 (fun s => s.RIP = 0x11efd2) (movR64R64Effect 0x11efd2 5 0) (Reg.operands [.gpr 0] [])) #v[2848]
    (.letOp (n := 2853) (.out 0x11efd5 (addR64R64Effect 0x11efd5 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 6] []) (.reg (.gpr 5))) #v[2851, 2842]
    (.letOp (n := 2854) (.out 0x11efd5 (addR64R64Effect 0x11efd5 5 6) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 6] []) (.flag .CF)) #v[2851, 2842]
    (.letOp (n := 2855) (.exec 0x11efd5 (fun s => s.RIP = 0x11efd5) (addR64R64Effect 0x11efd5 5 6) (Reg.operands [.gpr 5, .gpr 6] [])) #v[2851, 2842]
    (b_l11d880_66))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_65 : List UInt8 :=
  [0x49, 0xF7, 0xE1, 0x48, 0x89, 0x54, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84,
    0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x50, 0x49, 0x89, 0xD4, 0x49, 0x89, 0xC6,
    0x4C, 0x89, 0xD8, 0x48, 0xF7, 0x64, 0x24, 0x60, 0x49, 0x89, 0xC5, 0x49, 0x89, 0xD3, 0x4C, 0x0F,
    0xA4, 0xD3, 0x0C, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x40, 0x48, 0x89, 0xC6, 0x49, 0x89,
    0xD1, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0xF7, 0x64, 0x24, 0x30, 0x48, 0x89, 0xC5, 0x48, 0x01,
    0xF5] ++ bytes_l11d880_66

theorem code_l11d880_65 : ∀ x ∈ codeRange 0x11ef87 bytes_l11d880_65, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ef87 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_66

def b_l11d880_64 : Block Op Label signature Reg.count 2764 :=
  .letOp (n := 2764) (.out 0x11ef2b (movR64M64Effect 0x11ef2b 9 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 2765) (.exec 0x11ef2b (LoadPre 0x11ef2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11ef2b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ef2b 9 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2766) (.out 0x11ef30 (mulR64Effect 0x11ef30 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[2764, 2762]
    (.letOp (n := 2767) (.out 0x11ef30 (mulR64Effect 0x11ef30 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[2764, 2762]
    (.letOp (n := 2768) (.exec 0x11ef30 (fun s => s.RIP = 0x11ef30) (mulR64Effect 0x11ef30 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2764, 2762]
    (.letOp (n := 2769) (.out 0x11ef33 (addR64R64Effect 0x11ef33 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[2758, 2745]
    (.letOp (n := 2770) (.out 0x11ef33 (addR64R64Effect 0x11ef33 12 6) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 6] []) (.flag .CF)) #v[2758, 2745]
    (.letOp (n := 2771) (.exec 0x11ef33 (fun s => s.RIP = 0x11ef33) (addR64R64Effect 0x11ef33 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[2758, 2745]
    (.letOp (n := 2772) (.out 0x11ef36 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ef36 15 13)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[2760, 2747, 2770]
    (.letOp (n := 2773) (.exec 0x11ef36 (fun s => s.RIP = 0x11ef36) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ef36 15 13)) (Reg.operands [.gpr 15, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2760, 2747, 2770]
    (.letOp (n := 2774) (.out 0x11ef39 (addR64R64Effect 0x11ef39 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[2766, 2769]
    (.letOp (n := 2775) (.out 0x11ef39 (addR64R64Effect 0x11ef39 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[2766, 2769]
    (.letOp (n := 2776) (.exec 0x11ef39 (fun s => s.RIP = 0x11ef39) (addR64R64Effect 0x11ef39 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[2766, 2769]
    (.letOp (n := 2777) (.out 0x11ef3c (atFlags StatusFlags.CF (adcR64R64Effect 0x11ef3c 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[2772, 2767, 2775]
    (.letOp (n := 2778) (.exec 0x11ef3c (fun s => s.RIP = 0x11ef3c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ef3c 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2772, 2767, 2775]
    (.letOp (n := 2779) (.out 0x11ef3f (addR64R64Effect 0x11ef3f 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[2774, 2698]
    (.letOp (n := 2780) (.out 0x11ef3f (addR64R64Effect 0x11ef3f 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[2774, 2698]
    (.letOp (n := 2781) (.exec 0x11ef3f (fun s => s.RIP = 0x11ef3f) (addR64R64Effect 0x11ef3f 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[2774, 2698]
    (.letOp (n := 2782) (.out 0x11ef42 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ef42 15 0x0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[2777, 2780]
    (.letOp (n := 2783) (.exec 0x11ef42 (fun s => s.RIP = 0x11ef42) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ef42 15 0x0)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2777, 2780]
    (.letOp (n := 2784) (.out 0x11ef46 (shldR64R64Effect 0x11ef46 5 15 0 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[2782, 2779]
    (.letOp (n := 2785) (.exec 0x11ef46 (fun s => s.RIP = 0x11ef46) (shldR64R64Effect 0x11ef46 5 15 0 12) (Reg.operands [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2782, 2779]
    (.letOp (n := 2786) (.out 0x11ef4b (movR64Imm64Effect 0x11ef4b 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2787) (.exec 0x11ef4b (fun s => s.RIP = 0x11ef4b) (movR64Imm64Effect 0x11ef4b 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2788) (.out 0x11ef55 (andR64R64Effect 0x11ef55 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2779, 2786]
    (.letOp (n := 2789) (.exec 0x11ef55 (fun s => s.RIP = 0x11ef55) (andR64R64Effect 0x11ef55 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2779, 2786]
    (.letOp (n := 2790) (.out 0x11ef58 (movR64Imm64Effect 0x11ef58 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2791) (.exec 0x11ef58 (fun s => s.RIP = 0x11ef58) (movR64Imm64Effect 0x11ef58 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2792) (.out 0x11ef62 (mulR64Effect 0x11ef62 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2790, 2788]
    (.letOp (n := 2793) (.out 0x11ef62 (mulR64Effect 0x11ef62 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2790, 2788]
    (.letOp (n := 2794) (.exec 0x11ef62 (fun s => s.RIP = 0x11ef62) (mulR64Effect 0x11ef62 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2790, 2788]
    (.letOp (n := 2795) (.out 0x11ef65 (addR64M64Effect 0x11ef65 10 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[2736, 4]
    (.letOp (n := 2796) (.out 0x11ef65 (addR64M64Effect 0x11ef65 10 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[2736, 4]
    (.letOp (n := 2797) (.exec 0x11ef65 (LoadPre 0x11ef65 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11ef65 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11ef65 10 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[2736, 4]
    (.letOp (n := 2798) (.out 0x11ef6d (atFlags StatusFlags.CF (adcR64M64Effect 0x11ef6d 3 (.sib 4 none 0 (.d32 0xb8)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[2734, 4, 2796]
    (.letOp (n := 2799) (.exec 0x11ef6d (LoadPre 0x11ef6d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11ef6d + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11ef6d 3 (.sib 4 none 0 (.d32 0xb8)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2734, 4, 2796]
    (.letOp (n := 2800) (.out 0x11ef75 (addR64R64Effect 0x11ef75 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[2795, 2792]
    (.letOp (n := 2801) (.out 0x11ef75 (addR64R64Effect 0x11ef75 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[2795, 2792]
    (.letOp (n := 2802) (.exec 0x11ef75 (fun s => s.RIP = 0x11ef75) (addR64R64Effect 0x11ef75 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2795, 2792]
    (.letOp (n := 2803) (.out 0x11ef78 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ef78 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[2798, 2793, 2801]
    (.letOp (n := 2804) (.exec 0x11ef78 (fun s => s.RIP = 0x11ef78) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ef78 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2798, 2793, 2801]
    (.letOp (n := 2805) (.out 0x11ef7b (addR64R64Effect 0x11ef7b 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[2800, 2749]
    (.letOp (n := 2806) (.out 0x11ef7b (addR64R64Effect 0x11ef7b 10 5) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 5] []) (.flag .CF)) #v[2800, 2749]
    (.letOp (n := 2807) (.exec 0x11ef7b (fun s => s.RIP = 0x11ef7b) (addR64R64Effect 0x11ef7b 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[2800, 2749]
    (.letOp (n := 2808) (.out 0x11ef7e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ef7e 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[2803, 2806]
    (.letOp (n := 2809) (.exec 0x11ef7e (fun s => s.RIP = 0x11ef7e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ef7e 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2803, 2806]
    (.letOp (n := 2810) (.out 0x11ef82 (movR64M64Effect 0x11ef82 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2811) (.exec 0x11ef82 (LoadPre 0x11ef82 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11ef82 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ef82 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11d880_65))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_64 : List UInt8 :=
  [0x4C, 0x8B, 0x4C, 0x24, 0x58, 0x49, 0xF7, 0xE1, 0x49, 0x01, 0xF4, 0x4D, 0x11, 0xEF, 0x4C, 0x01,
    0xE0, 0x49, 0x11, 0xD7, 0x4C, 0x01, 0xF0, 0x49, 0x83, 0xD7, 0x00, 0x49, 0x0F, 0xA4, 0xC7, 0x0C,
    0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8, 0x48, 0xB9, 0x10,
    0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x4C, 0x03, 0x94, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x48, 0x13, 0x9C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC2, 0x48, 0x11, 0xD3,
    0x49, 0x01, 0xEA, 0x48, 0x83, 0xD3, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x18] ++ bytes_l11d880_65

theorem code_l11d880_64 : ∀ x ∈ codeRange 0x11ef2b bytes_l11d880_64, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ef2b 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_65

def b_l11d880_63 : Block Op Label signature Reg.count 2722 :=
  .letOp (n := 2722) (.out 0x11eed6 (movR64R64Effect 0x11eed6 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2622]
    (.letOp (n := 2723) (.exec 0x11eed6 (fun s => s.RIP = 0x11eed6) (movR64R64Effect 0x11eed6 0 11) (Reg.operands [.gpr 11] [])) #v[2622]
    (.letOp (n := 2724) (.out 0x11eed9 (mulR64Effect 0x11eed9 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2671, 2722]
    (.letOp (n := 2725) (.out 0x11eed9 (mulR64Effect 0x11eed9 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2671, 2722]
    (.letOp (n := 2726) (.exec 0x11eed9 (fun s => s.RIP = 0x11eed9) (mulR64Effect 0x11eed9 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2671, 2722]
    (.letOp (n := 2727) (.exec 0x11eedc (StorePre 0x11eedc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11eedc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11eedc 2 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2725, 4]
    (.letOp (n := 2728) (.exec 0x11eee4 (StorePre 0x11eee4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11eee4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11eee4 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2724, 4]
    (.letOp (n := 2729) (.out 0x11eeec (movR64R64Effect 0x11eeec 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[2631]
    (.letOp (n := 2730) (.exec 0x11eeec (fun s => s.RIP = 0x11eeec) (movR64R64Effect 0x11eeec 0 10) (Reg.operands [.gpr 10] [])) #v[2631]
    (.letOp (n := 2731) (.out 0x11eeef (mulM64Effect 0x11eeef 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2729, 4]
    (.letOp (n := 2732) (.out 0x11eeef (mulM64Effect 0x11eeef 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2729, 4]
    (.letOp (n := 2733) (.exec 0x11eeef (LoadPre 0x11eeef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11eeef + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11eeef 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2729, 4]
    (.letOp (n := 2734) (.out 0x11eef4 (movR64R64Effect 0x11eef4 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2732]
    (.letOp (n := 2735) (.exec 0x11eef4 (fun s => s.RIP = 0x11eef4) (movR64R64Effect 0x11eef4 3 2) (Reg.operands [.gpr 2] [])) #v[2732]
    (.letOp (n := 2736) (.out 0x11eef7 (movR64R64Effect 0x11eef7 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2731]
    (.letOp (n := 2737) (.exec 0x11eef7 (fun s => s.RIP = 0x11eef7) (movR64R64Effect 0x11eef7 10 0) (Reg.operands [.gpr 0] [])) #v[2731]
    (.letOp (n := 2738) (.out 0x11eefa (movR64M64Effect 0x11eefa 11 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 2739) (.exec 0x11eefa (LoadPre 0x11eefa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11eefa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11eefa 11 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2740) (.out 0x11eeff (movR64R64Effect 0x11eeff 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2738]
    (.letOp (n := 2741) (.exec 0x11eeff (fun s => s.RIP = 0x11eeff) (movR64R64Effect 0x11eeff 0 11) (Reg.operands [.gpr 11] [])) #v[2738]
    (.letOp (n := 2742) (.out 0x11ef02 (mulM64Effect 0x11ef02 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2740, 4]
    (.letOp (n := 2743) (.out 0x11ef02 (mulM64Effect 0x11ef02 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2740, 4]
    (.letOp (n := 2744) (.exec 0x11ef02 (LoadPre 0x11ef02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11ef02 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11ef02 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2740, 4]
    (.letOp (n := 2745) (.out 0x11ef07 (movR64R64Effect 0x11ef07 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2742]
    (.letOp (n := 2746) (.exec 0x11ef07 (fun s => s.RIP = 0x11ef07) (movR64R64Effect 0x11ef07 6 0) (Reg.operands [.gpr 0] [])) #v[2742]
    (.letOp (n := 2747) (.out 0x11ef0a (movR64R64Effect 0x11ef0a 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2743]
    (.letOp (n := 2748) (.exec 0x11ef0a (fun s => s.RIP = 0x11ef0a) (movR64R64Effect 0x11ef0a 13 2) (Reg.operands [.gpr 2] [])) #v[2743]
    (.letOp (n := 2749) (.out 0x11ef0d (shldR64R64Effect 0x11ef0d 5 5 8 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[2720, 2717]
    (.letOp (n := 2750) (.exec 0x11ef0d (fun s => s.RIP = 0x11ef0d) (shldR64R64Effect 0x11ef0d 5 5 8 12) (Reg.operands [.gpr 5, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2720, 2717]
    (.letOp (n := 2751) (.out 0x11ef12 (movR64M64Effect 0x11ef12 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 2752) (.exec 0x11ef12 (LoadPre 0x11ef12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11ef12 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ef12 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2753) (.out 0x11ef1a (movR64R64Effect 0x11ef1a 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[2751]
    (.letOp (n := 2754) (.exec 0x11ef1a (fun s => s.RIP = 0x11ef1a) (movR64R64Effect 0x11ef1a 0 7) (Reg.operands [.gpr 7] [])) #v[2751]
    (.letOp (n := 2755) (.out 0x11ef1d (mulM64Effect 0x11ef1d 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2753, 4]
    (.letOp (n := 2756) (.out 0x11ef1d (mulM64Effect 0x11ef1d 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2753, 4]
    (.letOp (n := 2757) (.exec 0x11ef1d (LoadPre 0x11ef1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11ef1d + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11ef1d 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2753, 4]
    (.letOp (n := 2758) (.out 0x11ef22 (movR64R64Effect 0x11ef22 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[2755]
    (.letOp (n := 2759) (.exec 0x11ef22 (fun s => s.RIP = 0x11ef22) (movR64R64Effect 0x11ef22 12 0) (Reg.operands [.gpr 0] [])) #v[2755]
    (.letOp (n := 2760) (.out 0x11ef25 (movR64R64Effect 0x11ef25 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2756]
    (.letOp (n := 2761) (.exec 0x11ef25 (fun s => s.RIP = 0x11ef25) (movR64R64Effect 0x11ef25 15 2) (Reg.operands [.gpr 2] [])) #v[2756]
    (.letOp (n := 2762) (.out 0x11ef28 (movR64R64Effect 0x11ef28 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2667]
    (.letOp (n := 2763) (.exec 0x11ef28 (fun s => s.RIP = 0x11ef28) (movR64R64Effect 0x11ef28 0 9) (Reg.operands [.gpr 9] [])) #v[2667]
    (b_l11d880_64))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_63 : List UInt8 :=
  [0x4C, 0x89, 0xD8, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89,
    0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0x64, 0x24, 0x60, 0x48, 0x89,
    0xD3, 0x49, 0x89, 0xC2, 0x4C, 0x8B, 0x5C, 0x24, 0x28, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0x64, 0x24,
    0x40, 0x48, 0x89, 0xC6, 0x49, 0x89, 0xD5, 0x4C, 0x0F, 0xA4, 0xC5, 0x0C, 0x48, 0x8B, 0xBC, 0x24,
    0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x30, 0x49, 0x89, 0xC4, 0x49,
    0x89, 0xD7, 0x4C, 0x89, 0xC8] ++ bytes_l11d880_64

theorem code_l11d880_63 : ∀ x ∈ codeRange 0x11eed6 bytes_l11d880_63, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1eed6 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_64

def b_l11d880_62 : Block Op Label signature Reg.count 2676 :=
  .letOp (n := 2676) (.out 0x11ee7c (shldR64R64Effect 0x11ee7c 5 8 1 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2620, 2617]
    (.letOp (n := 2677) (.exec 0x11ee7c (fun s => s.RIP = 0x11ee7c) (shldR64R64Effect 0x11ee7c 5 8 1 12) (Reg.operands [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2620, 2617]
    (.letOp (n := 2678) (.out 0x11ee81 (addR64R64Effect 0x11ee81 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[2649, 2640]
    (.letOp (n := 2679) (.out 0x11ee81 (addR64R64Effect 0x11ee81 15 12) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 12] []) (.flag .CF)) #v[2649, 2640]
    (.letOp (n := 2680) (.exec 0x11ee81 (fun s => s.RIP = 0x11ee81) (addR64R64Effect 0x11ee81 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[2649, 2640]
    (.letOp (n := 2681) (.out 0x11ee84 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ee84 14 3)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2647, 2638, 2679]
    (.letOp (n := 2682) (.exec 0x11ee84 (fun s => s.RIP = 0x11ee84) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ee84 14 3)) (Reg.operands [.gpr 14, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2647, 2638, 2679]
    (.letOp (n := 2683) (.out 0x11ee87 (addR64R64Effect 0x11ee87 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[2678, 2656]
    (.letOp (n := 2684) (.out 0x11ee87 (addR64R64Effect 0x11ee87 15 13) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 13] []) (.flag .CF)) #v[2678, 2656]
    (.letOp (n := 2685) (.exec 0x11ee87 (fun s => s.RIP = 0x11ee87) (addR64R64Effect 0x11ee87 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[2678, 2656]
    (.letOp (n := 2686) (.out 0x11ee8a (atFlags StatusFlags.CF (adcR64R64Effect 0x11ee8a 14 5)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2681, 2658, 2684]
    (.letOp (n := 2687) (.exec 0x11ee8a (fun s => s.RIP = 0x11ee8a) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ee8a 14 5)) (Reg.operands [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2681, 2658, 2684]
    (.letOp (n := 2688) (.out 0x11ee8d (addR64R64Effect 0x11ee8d 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[2673, 2683]
    (.letOp (n := 2689) (.out 0x11ee8d (addR64R64Effect 0x11ee8d 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[2673, 2683]
    (.letOp (n := 2690) (.exec 0x11ee8d (fun s => s.RIP = 0x11ee8d) (addR64R64Effect 0x11ee8d 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[2673, 2683]
    (.letOp (n := 2691) (.out 0x11ee90 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ee90 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2686, 2674, 2689]
    (.letOp (n := 2692) (.exec 0x11ee90 (fun s => s.RIP = 0x11ee90) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ee90 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2686, 2674, 2689]
    (.letOp (n := 2693) (.out 0x11ee93 (addR64R64Effect 0x11ee93 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[2688, 2676]
    (.letOp (n := 2694) (.out 0x11ee93 (addR64R64Effect 0x11ee93 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[2688, 2676]
    (.letOp (n := 2695) (.exec 0x11ee93 (fun s => s.RIP = 0x11ee93) (addR64R64Effect 0x11ee93 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[2688, 2676]
    (.letOp (n := 2696) (.out 0x11ee96 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ee96 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2691, 2694]
    (.letOp (n := 2697) (.exec 0x11ee96 (fun s => s.RIP = 0x11ee96) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ee96 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2691, 2694]
    (.letOp (n := 2698) (.out 0x11ee9a (shldR64R64Effect 0x11ee9a 5 14 0 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[2696, 2693]
    (.letOp (n := 2699) (.exec 0x11ee9a (fun s => s.RIP = 0x11ee9a) (shldR64R64Effect 0x11ee9a 5 14 0 12) (Reg.operands [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2696, 2693]
    (.letOp (n := 2700) (.out 0x11ee9f (shlR64Effect 0x11ee9f 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2693]
    (.letOp (n := 2701) (.exec 0x11ee9f (fun s => s.RIP = 0x11ee9f) (shlR64Effect 0x11ee9f 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2693]
    (.letOp (n := 2702) (.out 0x11eea3 (movR64Imm64Effect 0x11eea3 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2703) (.exec 0x11eea3 (fun s => s.RIP = 0x11eea3) (movR64Imm64Effect 0x11eea3 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 2704) (.out 0x11eead (andR64R64Effect 0x11eead 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[2700, 2702]
    (.letOp (n := 2705) (.exec 0x11eead (fun s => s.RIP = 0x11eead) (andR64R64Effect 0x11eead 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[2700, 2702]
    (.letOp (n := 2706) (.out 0x11eeb0 (orR64R64Effect 0x11eeb0 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[2704, 2665]
    (.letOp (n := 2707) (.exec 0x11eeb0 (fun s => s.RIP = 0x11eeb0) (orR64R64Effect 0x11eeb0 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[2704, 2665]
    (.letOp (n := 2708) (.out 0x11eeb3 (movR64Imm64Effect 0x11eeb3 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2709) (.exec 0x11eeb3 (fun s => s.RIP = 0x11eeb3) (movR64Imm64Effect 0x11eeb3 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 2710) (.out 0x11eebd (mulR64Effect 0x11eebd 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2708, 2706]
    (.letOp (n := 2711) (.out 0x11eebd (mulR64Effect 0x11eebd 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2708, 2706]
    (.letOp (n := 2712) (.exec 0x11eebd (fun s => s.RIP = 0x11eebd) (mulR64Effect 0x11eebd 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2708, 2706]
    (.letOp (n := 2713) (.out 0x11eec0 (movR64R64Effect 0x11eec0 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2711]
    (.letOp (n := 2714) (.exec 0x11eec0 (fun s => s.RIP = 0x11eec0) (movR64R64Effect 0x11eec0 5 2) (Reg.operands [.gpr 2] [])) #v[2711]
    (.letOp (n := 2715) (.out 0x11eec3 (movR64R64Effect 0x11eec3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[2710]
    (.letOp (n := 2716) (.exec 0x11eec3 (fun s => s.RIP = 0x11eec3) (movR64R64Effect 0x11eec3 8 0) (Reg.operands [.gpr 0] [])) #v[2710]
    (.letOp (n := 2717) (.out 0x11eec6 (addR64M64Effect 0x11eec6 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[2715, 4]
    (.letOp (n := 2718) (.out 0x11eec6 (addR64M64Effect 0x11eec6 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[2715, 4]
    (.letOp (n := 2719) (.exec 0x11eec6 (LoadPre 0x11eec6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11eec6 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11eec6 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[2715, 4]
    (.letOp (n := 2720) (.out 0x11eece (atFlags StatusFlags.CF (adcR64M64Effect 0x11eece 5 (.sib 4 none 0 (.d32 0xb8)))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 5))) #v[2713, 4, 2718]
    (.letOp (n := 2721) (.exec 0x11eece (LoadPre 0x11eece (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11eece + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11eece 5 (.sib 4 none 0 (.d32 0xb8)))) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2713, 4, 2718]
    (b_l11d880_63))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_62 : List UInt8 :=
  [0x49, 0x0F, 0xA4, 0xC8, 0x0C, 0x4D, 0x01, 0xE7, 0x49, 0x11, 0xDE, 0x4D, 0x01, 0xEF, 0x49, 0x11,
    0xEE, 0x4C, 0x01, 0xF8, 0x49, 0x11, 0xD6, 0x4C, 0x01, 0xC0, 0x49, 0x83, 0xD6, 0x00, 0x49, 0x0F,
    0xA4, 0xC6, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x00, 0x48, 0x21, 0xD0, 0x48, 0x09, 0xF0, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00,
    0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD5, 0x49, 0x89, 0xC0, 0x4C, 0x03, 0x84, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x48, 0x13, 0xAC, 0x24, 0xB8, 0x00, 0x00, 0x00] ++ bytes_l11d880_63

theorem code_l11d880_62 : ∀ x ∈ codeRange 0x11ee7c bytes_l11d880_62, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ee7c 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_63

def b_l11d880_61 : Block Op Label signature Reg.count 2633 :=
  .letOp (n := 2633) (.out 0x11ee31 (movR64R64Effect 0x11ee31 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[2631]
    (.letOp (n := 2634) (.exec 0x11ee31 (fun s => s.RIP = 0x11ee31) (movR64R64Effect 0x11ee31 0 10) (Reg.operands [.gpr 10] [])) #v[2631]
    (.letOp (n := 2635) (.out 0x11ee34 (mulM64Effect 0x11ee34 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2633, 4]
    (.letOp (n := 2636) (.out 0x11ee34 (mulM64Effect 0x11ee34 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2633, 4]
    (.letOp (n := 2637) (.exec 0x11ee34 (LoadPre 0x11ee34 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11ee34 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11ee34 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2633, 4]
    (.letOp (n := 2638) (.out 0x11ee39 (movR64R64Effect 0x11ee39 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2636]
    (.letOp (n := 2639) (.exec 0x11ee39 (fun s => s.RIP = 0x11ee39) (movR64R64Effect 0x11ee39 3 2) (Reg.operands [.gpr 2] [])) #v[2636]
    (.letOp (n := 2640) (.out 0x11ee3c (movR64R64Effect 0x11ee3c 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[2635]
    (.letOp (n := 2641) (.exec 0x11ee3c (fun s => s.RIP = 0x11ee3c) (movR64R64Effect 0x11ee3c 12 0) (Reg.operands [.gpr 0] [])) #v[2635]
    (.letOp (n := 2642) (.out 0x11ee3f (movR64M64Effect 0x11ee3f 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2643) (.exec 0x11ee3f (LoadPre 0x11ee3f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11ee3f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ee3f 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2644) (.out 0x11ee44 (mulM64Effect 0x11ee44 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2642, 4]
    (.letOp (n := 2645) (.out 0x11ee44 (mulM64Effect 0x11ee44 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2642, 4]
    (.letOp (n := 2646) (.exec 0x11ee44 (LoadPre 0x11ee44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11ee44 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11ee44 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2642, 4]
    (.letOp (n := 2647) (.out 0x11ee49 (movR64R64Effect 0x11ee49 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2645]
    (.letOp (n := 2648) (.exec 0x11ee49 (fun s => s.RIP = 0x11ee49) (movR64R64Effect 0x11ee49 14 2) (Reg.operands [.gpr 2] [])) #v[2645]
    (.letOp (n := 2649) (.out 0x11ee4c (movR64R64Effect 0x11ee4c 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[2644]
    (.letOp (n := 2650) (.exec 0x11ee4c (fun s => s.RIP = 0x11ee4c) (movR64R64Effect 0x11ee4c 15 0) (Reg.operands [.gpr 0] [])) #v[2644]
    (.letOp (n := 2651) (.out 0x11ee4f (movR64R64Effect 0x11ee4f 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[2551]
    (.letOp (n := 2652) (.exec 0x11ee4f (fun s => s.RIP = 0x11ee4f) (movR64R64Effect 0x11ee4f 0 7) (Reg.operands [.gpr 7] [])) #v[2551]
    (.letOp (n := 2653) (.out 0x11ee52 (mulM64Effect 0x11ee52 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2651, 4]
    (.letOp (n := 2654) (.out 0x11ee52 (mulM64Effect 0x11ee52 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2651, 4]
    (.letOp (n := 2655) (.exec 0x11ee52 (LoadPre 0x11ee52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11ee52 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11ee52 5 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2651, 4]
    (.letOp (n := 2656) (.out 0x11ee57 (movR64R64Effect 0x11ee57 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[2653]
    (.letOp (n := 2657) (.exec 0x11ee57 (fun s => s.RIP = 0x11ee57) (movR64R64Effect 0x11ee57 13 0) (Reg.operands [.gpr 0] [])) #v[2653]
    (.letOp (n := 2658) (.out 0x11ee5a (movR64R64Effect 0x11ee5a 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2654]
    (.letOp (n := 2659) (.exec 0x11ee5a (fun s => s.RIP = 0x11ee5a) (movR64R64Effect 0x11ee5a 5 2) (Reg.operands [.gpr 2] [])) #v[2654]
    (.letOp (n := 2660) (.exec 0x11ee5d (StorePre 0x11ee5d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11ee5d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ee5d 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2617, 4]
    (.letOp (n := 2661) (.out 0x11ee62 (movR64R64Effect 0x11ee62 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[2617]
    (.letOp (n := 2662) (.exec 0x11ee62 (fun s => s.RIP = 0x11ee62) (movR64R64Effect 0x11ee62 6 1) (Reg.operands [.gpr 1] [])) #v[2617]
    (.letOp (n := 2663) (.out 0x11ee65 (shrR64Effect 0x11ee65 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[2661]
    (.letOp (n := 2664) (.exec 0x11ee65 (fun s => s.RIP = 0x11ee65) (shrR64Effect 0x11ee65 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2661]
    (.letOp (n := 2665) (.out 0x11ee69 (andR32Imm8Effect 0x11ee69 3 6 0xf) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[2663]
    (.letOp (n := 2666) (.exec 0x11ee69 (fun s => s.RIP = 0x11ee69) (andR32Imm8Effect 0x11ee69 3 6 0xf) (Reg.operands [.gpr 6] [])) #v[2663]
    (.letOp (n := 2667) (.out 0x11ee6c (movR64M64Effect 0x11ee6c 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 2668) (.exec 0x11ee6c (LoadPre 0x11ee6c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11ee6c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ee6c 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2669) (.out 0x11ee71 (movR64R64Effect 0x11ee71 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2667]
    (.letOp (n := 2670) (.exec 0x11ee71 (fun s => s.RIP = 0x11ee71) (movR64R64Effect 0x11ee71 0 9) (Reg.operands [.gpr 9] [])) #v[2667]
    (.letOp (n := 2671) (.out 0x11ee74 (movR64M64Effect 0x11ee74 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 2672) (.exec 0x11ee74 (LoadPre 0x11ee74 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11ee74 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ee74 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2673) (.out 0x11ee79 (mulR64Effect 0x11ee79 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2671, 2669]
    (.letOp (n := 2674) (.out 0x11ee79 (mulR64Effect 0x11ee79 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2671, 2669]
    (.letOp (n := 2675) (.exec 0x11ee79 (fun s => s.RIP = 0x11ee79) (mulR64Effect 0x11ee79 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2671, 2669]
    (b_l11d880_62)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_61 : List UInt8 :=
  [0x4C, 0x89, 0xD0, 0x48, 0xF7, 0x64, 0x24, 0x40, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC4, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0xF7, 0x64, 0x24, 0x30, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC7, 0x48, 0x89,
    0xF8, 0x48, 0xF7, 0x64, 0x24, 0x58, 0x49, 0x89, 0xC5, 0x48, 0x89, 0xD5, 0x48, 0x89, 0x4C, 0x24,
    0x48, 0x48, 0x89, 0xCE, 0x48, 0xC1, 0xEE, 0x30, 0x83, 0xE6, 0x0F, 0x4C, 0x8B, 0x4C, 0x24, 0x10,
    0x4C, 0x89, 0xC8, 0x48, 0x8B, 0x7C, 0x24, 0x50, 0x48, 0xF7, 0xE7] ++ bytes_l11d880_62

theorem code_l11d880_61 : ∀ x ∈ codeRange 0x11ee31 bytes_l11d880_61, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ee31 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_62

def b_l11d880_60 : Block Op Label signature Reg.count 2588 :=
  .letOp (n := 2588) (.out 0x11edd5 (addR64R64Effect 0x11edd5 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[2579, 2586]
    (.letOp (n := 2589) (.exec 0x11edd5 (fun s => s.RIP = 0x11edd5) (addR64R64Effect 0x11edd5 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[2579, 2586]
    (.letOp (n := 2590) (.out 0x11edd8 (movR64M64Effect 0x11edd8 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 2591) (.exec 0x11edd8 (LoadPre 0x11edd8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11edd8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11edd8 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2592) (.out 0x11eddd (addR64M64Effect 0x11eddd 1 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[2590, 4]
    (.letOp (n := 2593) (.out 0x11eddd (addR64M64Effect 0x11eddd 1 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 4] []) (.flag .CF)) #v[2590, 4]
    (.letOp (n := 2594) (.exec 0x11eddd (LoadPre 0x11eddd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11eddd + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11eddd 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2590, 4]
    (.letOp (n := 2595) (.out 0x11ede5 (atFlags StatusFlags.CF (adcR64M64Effect 0x11ede5 8 (.sib 4 none 0 (.d32 0xb8)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[2541, 4, 2593]
    (.letOp (n := 2596) (.exec 0x11ede5 (LoadPre 0x11ede5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11ede5 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11ede5 8 (.sib 4 none 0 (.d32 0xb8)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2541, 4, 2593]
    (.letOp (n := 2597) (.out 0x11eded (addR64R64Effect 0x11eded 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[2592, 2549]
    (.letOp (n := 2598) (.out 0x11eded (addR64R64Effect 0x11eded 1 9) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 9] []) (.flag .CF)) #v[2592, 2549]
    (.letOp (n := 2599) (.exec 0x11eded (fun s => s.RIP = 0x11eded) (addR64R64Effect 0x11eded 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[2592, 2549]
    (.letOp (n := 2600) (.out 0x11edf0 (atFlags StatusFlags.CF (adcR64M64Effect 0x11edf0 8 (.sib 4 none 0 (.d8 0x78)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[2595, 4, 2598]
    (.letOp (n := 2601) (.exec 0x11edf0 (LoadPre 0x11edf0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11edf0 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11edf0 8 (.sib 4 none 0 (.d8 0x78)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2595, 4, 2598]
    (.letOp (n := 2602) (.out 0x11edf5 (addR64R64Effect 0x11edf5 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[2597, 2560]
    (.letOp (n := 2603) (.out 0x11edf5 (addR64R64Effect 0x11edf5 1 13) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 13] []) (.flag .CF)) #v[2597, 2560]
    (.letOp (n := 2604) (.exec 0x11edf5 (fun s => s.RIP = 0x11edf5) (addR64R64Effect 0x11edf5 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[2597, 2560]
    (.letOp (n := 2605) (.out 0x11edf8 (atFlags StatusFlags.CF (adcR64R64Effect 0x11edf8 8 5)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2600, 2558, 2603]
    (.letOp (n := 2606) (.exec 0x11edf8 (fun s => s.RIP = 0x11edf8) (atFlags StatusFlags.CF (adcR64R64Effect 0x11edf8 8 5)) (Reg.operands [.gpr 8, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2600, 2558, 2603]
    (.letOp (n := 2607) (.out 0x11edfb (addR64R64Effect 0x11edfb 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[2602, 2569]
    (.letOp (n := 2608) (.out 0x11edfb (addR64R64Effect 0x11edfb 1 12) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 12] []) (.flag .CF)) #v[2602, 2569]
    (.letOp (n := 2609) (.exec 0x11edfb (fun s => s.RIP = 0x11edfb) (addR64R64Effect 0x11edfb 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[2602, 2569]
    (.letOp (n := 2610) (.out 0x11edfe (atFlags StatusFlags.CF (adcR64R64Effect 0x11edfe 8 15)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2605, 2571, 2608]
    (.letOp (n := 2611) (.exec 0x11edfe (fun s => s.RIP = 0x11edfe) (atFlags StatusFlags.CF (adcR64R64Effect 0x11edfe 8 15)) (Reg.operands [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2605, 2571, 2608]
    (.letOp (n := 2612) (.out 0x11ee01 (addR64R64Effect 0x11ee01 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2607, 2585]
    (.letOp (n := 2613) (.out 0x11ee01 (addR64R64Effect 0x11ee01 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[2607, 2585]
    (.letOp (n := 2614) (.exec 0x11ee01 (fun s => s.RIP = 0x11ee01) (addR64R64Effect 0x11ee01 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2607, 2585]
    (.letOp (n := 2615) (.out 0x11ee04 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ee04 8 10)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2610, 2588, 2613]
    (.letOp (n := 2616) (.exec 0x11ee04 (fun s => s.RIP = 0x11ee04) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ee04 8 10)) (Reg.operands [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2610, 2588, 2613]
    (.letOp (n := 2617) (.out 0x11ee07 (addR64R64Effect 0x11ee07 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[2612, 2573]
    (.letOp (n := 2618) (.out 0x11ee07 (addR64R64Effect 0x11ee07 1 3) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 3] []) (.flag .CF)) #v[2612, 2573]
    (.letOp (n := 2619) (.exec 0x11ee07 (fun s => s.RIP = 0x11ee07) (addR64R64Effect 0x11ee07 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[2612, 2573]
    (.letOp (n := 2620) (.out 0x11ee0a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ee0a 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[2615, 2618]
    (.letOp (n := 2621) (.exec 0x11ee0a (fun s => s.RIP = 0x11ee0a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ee0a 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2615, 2618]
    (.letOp (n := 2622) (.out 0x11ee0e (movR64M64Effect 0x11ee0e 11 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 2623) (.exec 0x11ee0e (LoadPre 0x11ee0e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11ee0e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ee0e 11 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2624) (.out 0x11ee13 (movR64R64Effect 0x11ee13 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2622]
    (.letOp (n := 2625) (.exec 0x11ee13 (fun s => s.RIP = 0x11ee13) (movR64R64Effect 0x11ee13 0 11) (Reg.operands [.gpr 11] [])) #v[2622]
    (.letOp (n := 2626) (.out 0x11ee16 (mulR64Effect 0x11ee16 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[2564, 2624]
    (.letOp (n := 2627) (.out 0x11ee16 (mulR64Effect 0x11ee16 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[2564, 2624]
    (.letOp (n := 2628) (.exec 0x11ee16 (fun s => s.RIP = 0x11ee16) (mulR64Effect 0x11ee16 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[2564, 2624]
    (.letOp (n := 2629) (.exec 0x11ee19 (StorePre 0x11ee19 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11ee19 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ee19 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2626, 4]
    (.letOp (n := 2630) (.exec 0x11ee21 (StorePre 0x11ee21 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11ee21 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ee21 2 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2627, 4]
    (.letOp (n := 2631) (.out 0x11ee29 (movR64M64Effect 0x11ee29 10 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 2632) (.exec 0x11ee29 (LoadPre 0x11ee29 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11ee29 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ee29 10 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11d880_61)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_60 : List UInt8 :=
  [0x49, 0x01, 0xD2, 0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0x03, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x4C, 0x13, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xC9, 0x4C, 0x13, 0x44, 0x24, 0x78,
    0x4C, 0x01, 0xE9, 0x49, 0x11, 0xE8, 0x4C, 0x01, 0xE1, 0x4D, 0x11, 0xF8, 0x48, 0x01, 0xC1, 0x4D,
    0x11, 0xD0, 0x48, 0x01, 0xD9, 0x49, 0x83, 0xD0, 0x00, 0x4C, 0x8B, 0x5C, 0x24, 0x18, 0x4C, 0x89,
    0xD8, 0x48, 0xF7, 0xE6, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24,
    0xB8, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x94, 0x24, 0xC0, 0x00, 0x00, 0x00] ++ bytes_l11d880_61

theorem code_l11d880_60 : ∀ x ∈ codeRange 0x11edd5 bytes_l11d880_60, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1edd5 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_61

def b_l11d880_59 : Block Op Label signature Reg.count 2545 :=
  .letOp (n := 2545) (.out 0x11ed7e (mulR64Effect 0x11ed7e 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[2445, 2543]
    (.letOp (n := 2546) (.out 0x11ed7e (mulR64Effect 0x11ed7e 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[2445, 2543]
    (.letOp (n := 2547) (.exec 0x11ed7e (fun s => s.RIP = 0x11ed7e) (mulR64Effect 0x11ed7e 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[2445, 2543]
    (.letOp (n := 2548) (.exec 0x11ed81 (StorePre 0x11ed81 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11ed81 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ed81 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2546, 4]
    (.letOp (n := 2549) (.out 0x11ed86 (movR64R64Effect 0x11ed86 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[2545]
    (.letOp (n := 2550) (.exec 0x11ed86 (fun s => s.RIP = 0x11ed86) (movR64R64Effect 0x11ed86 9 0) (Reg.operands [.gpr 0] [])) #v[2545]
    (.letOp (n := 2551) (.out 0x11ed89 (movR64M64Effect 0x11ed89 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 2552) (.exec 0x11ed89 (LoadPre 0x11ed89 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11ed89 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ed89 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2553) (.out 0x11ed91 (movR64R64Effect 0x11ed91 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[2551]
    (.letOp (n := 2554) (.exec 0x11ed91 (fun s => s.RIP = 0x11ed91) (movR64R64Effect 0x11ed91 0 7) (Reg.operands [.gpr 7] [])) #v[2551]
    (.letOp (n := 2555) (.out 0x11ed94 (mulR64Effect 0x11ed94 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[2457, 2553]
    (.letOp (n := 2556) (.out 0x11ed94 (mulR64Effect 0x11ed94 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[2457, 2553]
    (.letOp (n := 2557) (.exec 0x11ed94 (fun s => s.RIP = 0x11ed94) (mulR64Effect 0x11ed94 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[2457, 2553]
    (.letOp (n := 2558) (.out 0x11ed97 (movR64R64Effect 0x11ed97 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2556]
    (.letOp (n := 2559) (.exec 0x11ed97 (fun s => s.RIP = 0x11ed97) (movR64R64Effect 0x11ed97 5 2) (Reg.operands [.gpr 2] [])) #v[2556]
    (.letOp (n := 2560) (.out 0x11ed9a (movR64R64Effect 0x11ed9a 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[2555]
    (.letOp (n := 2561) (.exec 0x11ed9a (fun s => s.RIP = 0x11ed9a) (movR64R64Effect 0x11ed9a 13 0) (Reg.operands [.gpr 0] [])) #v[2555]
    (.letOp (n := 2562) (.out 0x11ed9d (movR64R64Effect 0x11ed9d 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2496]
    (.letOp (n := 2563) (.exec 0x11ed9d (fun s => s.RIP = 0x11ed9d) (movR64R64Effect 0x11ed9d 0 6) (Reg.operands [.gpr 6] [])) #v[2496]
    (.letOp (n := 2564) (.out 0x11eda0 (movR64M64Effect 0x11eda0 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 2565) (.exec 0x11eda0 (LoadPre 0x11eda0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11eda0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11eda0 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2566) (.out 0x11eda5 (mulR64Effect 0x11eda5 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[2564, 2562]
    (.letOp (n := 2567) (.out 0x11eda5 (mulR64Effect 0x11eda5 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[2564, 2562]
    (.letOp (n := 2568) (.exec 0x11eda5 (fun s => s.RIP = 0x11eda5) (mulR64Effect 0x11eda5 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[2564, 2562]
    (.letOp (n := 2569) (.out 0x11eda8 (movR64R64Effect 0x11eda8 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[2566]
    (.letOp (n := 2570) (.exec 0x11eda8 (fun s => s.RIP = 0x11eda8) (movR64R64Effect 0x11eda8 12 0) (Reg.operands [.gpr 0] [])) #v[2566]
    (.letOp (n := 2571) (.out 0x11edab (movR64R64Effect 0x11edab 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2567]
    (.letOp (n := 2572) (.exec 0x11edab (fun s => s.RIP = 0x11edab) (movR64R64Effect 0x11edab 15 2) (Reg.operands [.gpr 2] [])) #v[2567]
    (.letOp (n := 2573) (.out 0x11edae (shldR64R64Effect 0x11edae 5 3 11 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[2526, 2523]
    (.letOp (n := 2574) (.exec 0x11edae (fun s => s.RIP = 0x11edae) (shldR64R64Effect 0x11edae 5 3 11 12) (Reg.operands [.gpr 3, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2526, 2523]
    (.letOp (n := 2575) (.out 0x11edb3 (shrR64Effect 0x11edb3 4 10 52) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2503]
    (.letOp (n := 2576) (.exec 0x11edb3 (fun s => s.RIP = 0x11edb3) (shrR64Effect 0x11edb3 4 10 52) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2503]
    (.letOp (n := 2577) (.out 0x11edb7 (movR64Imm64Effect 0x11edb7 0 0x1000003d10) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 2578) (.exec 0x11edb7 (fun s => s.RIP = 0x11edb7) (movR64Imm64Effect 0x11edb7 0 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2579) (.out 0x11edc1 (imulR64R64Effect 0x11edc1 4 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[2575, 2577]
    (.letOp (n := 2580) (.exec 0x11edc1 (fun s => s.RIP = 0x11edc1) (imulR64R64Effect 0x11edc1 4 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2575, 2577]
    (.letOp (n := 2581) (.out 0x11edc5 (movR64R64Effect 0x11edc5 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[2507]
    (.letOp (n := 2582) (.exec 0x11edc5 (fun s => s.RIP = 0x11edc5) (movR64R64Effect 0x11edc5 0 14) (Reg.operands [.gpr 14] [])) #v[2507]
    (.letOp (n := 2583) (.out 0x11edc8 (movR64Imm64Effect 0x11edc8 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2584) (.exec 0x11edc8 (fun s => s.RIP = 0x11edc8) (movR64Imm64Effect 0x11edc8 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2585) (.out 0x11edd2 (mulR64Effect 0x11edd2 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2583, 2581]
    (.letOp (n := 2586) (.out 0x11edd2 (mulR64Effect 0x11edd2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2583, 2581]
    (.letOp (n := 2587) (.exec 0x11edd2 (fun s => s.RIP = 0x11edd2) (mulR64Effect 0x11edd2 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2583, 2581]
    (b_l11d880_60)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_59 : List UInt8 :=
  [0x48, 0xF7, 0xE5, 0x48, 0x89, 0x54, 0x24, 0x78, 0x49, 0x89, 0xC1, 0x48, 0x8B, 0xBC, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0xD5, 0x49, 0x89, 0xC5, 0x48,
    0x89, 0xF0, 0x48, 0x8B, 0x74, 0x24, 0x60, 0x48, 0xF7, 0xE6, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD7,
    0x4C, 0x0F, 0xA4, 0xDB, 0x0C, 0x49, 0xC1, 0xEA, 0x34, 0x48, 0xB8, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xD0, 0x4C, 0x89, 0xF0, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1] ++ bytes_l11d880_60

theorem code_l11d880_59 : ∀ x ∈ codeRange 0x11ed7e bytes_l11d880_59, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ed7e 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_60

def b_l11d880_58 : Block Op Label signature Reg.count 2505 :=
  .letOp (n := 2505) (.out 0x11ed1f (movR64R64Effect 0x11ed1f 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2500]
    (.letOp (n := 2506) (.exec 0x11ed1f (fun s => s.RIP = 0x11ed1f) (movR64R64Effect 0x11ed1f 14 2) (Reg.operands [.gpr 2] [])) #v[2500]
    (.letOp (n := 2507) (.out 0x11ed22 (shldR64R64Effect 0x11ed22 5 14 0 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[2505, 2499]
    (.letOp (n := 2508) (.exec 0x11ed22 (fun s => s.RIP = 0x11ed22) (shldR64R64Effect 0x11ed22 5 14 0 12) (Reg.operands [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2505, 2499]
    (.letOp (n := 2509) (.out 0x11ed27 (movR64Imm64Effect 0x11ed27 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2510) (.exec 0x11ed27 (fun s => s.RIP = 0x11ed27) (movR64Imm64Effect 0x11ed27 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2511) (.out 0x11ed31 (andR64R64Effect 0x11ed31 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[2499, 2509]
    (.letOp (n := 2512) (.exec 0x11ed31 (fun s => s.RIP = 0x11ed31) (andR64R64Effect 0x11ed31 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[2499, 2509]
    (.letOp (n := 2513) (.out 0x11ed34 (movR64Imm64Effect 0x11ed34 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2514) (.exec 0x11ed34 (fun s => s.RIP = 0x11ed34) (movR64Imm64Effect 0x11ed34 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2515) (.out 0x11ed3e (mulR64Effect 0x11ed3e 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2513, 2511]
    (.letOp (n := 2516) (.out 0x11ed3e (mulR64Effect 0x11ed3e 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2513, 2511]
    (.letOp (n := 2517) (.exec 0x11ed3e (fun s => s.RIP = 0x11ed3e) (mulR64Effect 0x11ed3e 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2513, 2511]
    (.letOp (n := 2518) (.out 0x11ed41 (movR64R64Effect 0x11ed41 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2516]
    (.letOp (n := 2519) (.exec 0x11ed41 (fun s => s.RIP = 0x11ed41) (movR64R64Effect 0x11ed41 3 2) (Reg.operands [.gpr 2] [])) #v[2516]
    (.letOp (n := 2520) (.out 0x11ed44 (addR64R64Effect 0x11ed44 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[2515, 2487]
    (.letOp (n := 2521) (.out 0x11ed44 (addR64R64Effect 0x11ed44 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[2515, 2487]
    (.letOp (n := 2522) (.exec 0x11ed44 (fun s => s.RIP = 0x11ed44) (addR64R64Effect 0x11ed44 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[2515, 2487]
    (.letOp (n := 2523) (.out 0x11ed47 (movR64R64Effect 0x11ed47 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[2520]
    (.letOp (n := 2524) (.exec 0x11ed47 (fun s => s.RIP = 0x11ed47) (movR64R64Effect 0x11ed47 11 0) (Reg.operands [.gpr 0] [])) #v[2520]
    (.letOp (n := 2525) (.exec 0x11ed4a (StorePre 0x11ed4a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11ed4a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ed4a 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2520, 4]
    (.letOp (n := 2526) (.out 0x11ed52 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ed52 3 1)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[2518, 2490, 2521]
    (.letOp (n := 2527) (.exec 0x11ed52 (fun s => s.RIP = 0x11ed52) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ed52 3 1)) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2518, 2490, 2521]
    (.letOp (n := 2528) (.out 0x11ed55 (movR64R64Effect 0x11ed55 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[2411]
    (.letOp (n := 2529) (.exec 0x11ed55 (fun s => s.RIP = 0x11ed55) (movR64R64Effect 0x11ed55 0 12) (Reg.operands [.gpr 12] [])) #v[2411]
    (.letOp (n := 2530) (.out 0x11ed58 (mulR64Effect 0x11ed58 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2492, 2528]
    (.letOp (n := 2531) (.out 0x11ed58 (mulR64Effect 0x11ed58 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2492, 2528]
    (.letOp (n := 2532) (.exec 0x11ed58 (fun s => s.RIP = 0x11ed58) (mulR64Effect 0x11ed58 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2492, 2528]
    (.letOp (n := 2533) (.exec 0x11ed5b (StorePre 0x11ed5b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11ed5b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ed5b 2 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2531, 4]
    (.letOp (n := 2534) (.exec 0x11ed63 (StorePre 0x11ed63 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11ed63 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ed63 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2530, 4]
    (.letOp (n := 2535) (.out 0x11ed6b (movR64R64Effect 0x11ed6b 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[2439]
    (.letOp (n := 2536) (.exec 0x11ed6b (fun s => s.RIP = 0x11ed6b) (movR64R64Effect 0x11ed6b 0 13) (Reg.operands [.gpr 13] [])) #v[2439]
    (.letOp (n := 2537) (.out 0x11ed6e (mulM64Effect 0x11ed6e 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2535, 4]
    (.letOp (n := 2538) (.out 0x11ed6e (mulM64Effect 0x11ed6e 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2535, 4]
    (.letOp (n := 2539) (.exec 0x11ed6e (LoadPre 0x11ed6e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11ed6e + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11ed6e 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2535, 4]
    (.letOp (n := 2540) (.exec 0x11ed73 (StorePre 0x11ed73 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11ed73 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ed73 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2537, 4]
    (.letOp (n := 2541) (.out 0x11ed78 (movR64R64Effect 0x11ed78 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2538]
    (.letOp (n := 2542) (.exec 0x11ed78 (fun s => s.RIP = 0x11ed78) (movR64R64Effect 0x11ed78 8 2) (Reg.operands [.gpr 2] [])) #v[2538]
    (.letOp (n := 2543) (.out 0x11ed7b (movR64R64Effect 0x11ed7b 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2417]
    (.letOp (n := 2544) (.exec 0x11ed7b (fun s => s.RIP = 0x11ed7b) (movR64R64Effect 0x11ed7b 0 9) (Reg.operands [.gpr 9] [])) #v[2417]
    (b_l11d880_59))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_58 : List UInt8 :=
  [0x49, 0x89, 0xD6, 0x49, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE2, 0x48, 0x89, 0xD3, 0x4C, 0x01, 0xC0, 0x49, 0x89, 0xC3, 0x48, 0x89, 0x84, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x48, 0x11, 0xCB, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0x94, 0x24,
    0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE8, 0x48,
    0xF7, 0x64, 0x24, 0x30, 0x48, 0x89, 0x44, 0x24, 0x48, 0x49, 0x89, 0xD0, 0x4C, 0x89, 0xC8] ++ bytes_l11d880_59

theorem code_l11d880_58 : ∀ x ∈ codeRange 0x11ed1f bytes_l11d880_58, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ed1f 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_59

def b_l11d880_57 : Block Op Label signature Reg.count 2465 :=
  .letOp (n := 2465) (.exec 0x11ecd1 (StorePre 0x11ecd1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11ecd1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ecd1 15 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[2457, 4]
    (.letOp (n := 2466) (.out 0x11ecd6 (movR64R64Effect 0x11ecd6 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2463]
    (.letOp (n := 2467) (.exec 0x11ecd6 (fun s => s.RIP = 0x11ecd6) (movR64R64Effect 0x11ecd6 6 2) (Reg.operands [.gpr 2] [])) #v[2463]
    (.letOp (n := 2468) (.out 0x11ecd9 (movR64R64Effect 0x11ecd9 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2462]
    (.letOp (n := 2469) (.exec 0x11ecd9 (fun s => s.RIP = 0x11ecd9) (movR64R64Effect 0x11ecd9 10 0) (Reg.operands [.gpr 0] [])) #v[2462]
    (.letOp (n := 2470) (.out 0x11ecdc (addR64R64Effect 0x11ecdc 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[2468, 2452]
    (.letOp (n := 2471) (.out 0x11ecdc (addR64R64Effect 0x11ecdc 10 8) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 8] []) (.flag .CF)) #v[2468, 2452]
    (.letOp (n := 2472) (.exec 0x11ecdc (fun s => s.RIP = 0x11ecdc) (addR64R64Effect 0x11ecdc 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[2468, 2452]
    (.letOp (n := 2473) (.out 0x11ecdf (atFlags StatusFlags.CF (adcR64R64Effect 0x11ecdf 6 7)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[2466, 2455, 2471]
    (.letOp (n := 2474) (.exec 0x11ecdf (fun s => s.RIP = 0x11ecdf) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ecdf 6 7)) (Reg.operands [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2466, 2455, 2471]
    (.letOp (n := 2475) (.out 0x11ece2 (movR64M64Effect 0x11ece2 1 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 2476) (.exec 0x11ece2 (LoadPre 0x11ece2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x11ece2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ece2 1 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2477) (.exec 0x11ecea (StorePre 0x11ecea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11ecea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ecea 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2475, 4]
    (.letOp (n := 2478) (.out 0x11ecef (movR64R64Effect 0x11ecef 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2419]
    (.letOp (n := 2479) (.exec 0x11ecef (fun s => s.RIP = 0x11ecef) (movR64R64Effect 0x11ecef 0 11) (Reg.operands [.gpr 11] [])) #v[2419]
    (.letOp (n := 2480) (.out 0x11ecf2 (mulR64Effect 0x11ecf2 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2475, 2478]
    (.letOp (n := 2481) (.out 0x11ecf2 (mulR64Effect 0x11ecf2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2475, 2478]
    (.letOp (n := 2482) (.exec 0x11ecf2 (fun s => s.RIP = 0x11ecf2) (mulR64Effect 0x11ecf2 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2475, 2478]
    (.letOp (n := 2483) (.out 0x11ecf5 (movR64R64Effect 0x11ecf5 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2481]
    (.letOp (n := 2484) (.exec 0x11ecf5 (fun s => s.RIP = 0x11ecf5) (movR64R64Effect 0x11ecf5 1 2) (Reg.operands [.gpr 2] [])) #v[2481]
    (.letOp (n := 2485) (.out 0x11ecf8 (movR64R64Effect 0x11ecf8 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[2480]
    (.letOp (n := 2486) (.exec 0x11ecf8 (fun s => s.RIP = 0x11ecf8) (movR64R64Effect 0x11ecf8 8 0) (Reg.operands [.gpr 0] [])) #v[2480]
    (.letOp (n := 2487) (.out 0x11ecfb (addR64R64Effect 0x11ecfb 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[2485, 2470]
    (.letOp (n := 2488) (.out 0x11ecfb (addR64R64Effect 0x11ecfb 8 10) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 10] []) (.flag .CF)) #v[2485, 2470]
    (.letOp (n := 2489) (.exec 0x11ecfb (fun s => s.RIP = 0x11ecfb) (addR64R64Effect 0x11ecfb 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[2485, 2470]
    (.letOp (n := 2490) (.out 0x11ecfe (atFlags StatusFlags.CF (adcR64R64Effect 0x11ecfe 1 6)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[2483, 2473, 2488]
    (.letOp (n := 2491) (.exec 0x11ecfe (fun s => s.RIP = 0x11ecfe) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ecfe 1 6)) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2483, 2473, 2488]
    (.letOp (n := 2492) (.out 0x11ed01 (movR64M64Effect 0x11ed01 7 (.sib 4 none 0 (.d32 0x198))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 2493) (.exec 0x11ed01 (LoadPre 0x11ed01 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x11ed01 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ed01 7 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2494) (.out 0x11ed09 (movR64R64Effect 0x11ed09 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[2405]
    (.letOp (n := 2495) (.exec 0x11ed09 (fun s => s.RIP = 0x11ed09) (movR64R64Effect 0x11ed09 0 3) (Reg.operands [.gpr 3] [])) #v[2405]
    (.letOp (n := 2496) (.out 0x11ed0c (movR64R64Effect 0x11ed0c 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[2405]
    (.letOp (n := 2497) (.exec 0x11ed0c (fun s => s.RIP = 0x11ed0c) (movR64R64Effect 0x11ed0c 6 3) (Reg.operands [.gpr 3] [])) #v[2405]
    (.letOp (n := 2498) (.exec 0x11ed0f (StorePre 0x11ed0f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11ed0f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ed0f 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[2405, 4]
    (.letOp (n := 2499) (.out 0x11ed14 (mulR64Effect 0x11ed14 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2492, 2494]
    (.letOp (n := 2500) (.out 0x11ed14 (mulR64Effect 0x11ed14 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2492, 2494]
    (.letOp (n := 2501) (.exec 0x11ed14 (fun s => s.RIP = 0x11ed14) (mulR64Effect 0x11ed14 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2492, 2494]
    (.letOp (n := 2502) (.exec 0x11ed17 (StorePre 0x11ed17 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11ed17 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ed17 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[2492, 4]
    (.letOp (n := 2503) (.out 0x11ed1c (movR64R64Effect 0x11ed1c 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[2500]
    (.letOp (n := 2504) (.exec 0x11ed1c (fun s => s.RIP = 0x11ed1c) (movR64R64Effect 0x11ed1c 10 2) (Reg.operands [.gpr 2] [])) #v[2500]
    (b_l11d880_58))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_57 : List UInt8 :=
  [0x4C, 0x89, 0x7C, 0x24, 0x50, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC2, 0x4D, 0x01, 0xC2, 0x48, 0x11,
    0xFE, 0x48, 0x8B, 0x8C, 0x24, 0x78, 0x01, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x60, 0x4C, 0x89,
    0xD8, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC0, 0x4D, 0x01, 0xD0, 0x48, 0x11, 0xF1,
    0x48, 0x8B, 0xBC, 0x24, 0x98, 0x01, 0x00, 0x00, 0x48, 0x89, 0xD8, 0x48, 0x89, 0xDE, 0x48, 0x89,
    0x5C, 0x24, 0x10, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0x7C, 0x24, 0x40, 0x49, 0x89, 0xD2] ++ bytes_l11d880_58

theorem code_l11d880_57 : ∀ x ∈ codeRange 0x11ecd1 bytes_l11d880_57, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ecd1 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_58

def b_l11d880_56 : Block Op Label signature Reg.count 2425 :=
  .letOp (n := 2425) (.out 0x11ec80 (movR64R64Effect 0x11ec80 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[2411]
    (.letOp (n := 2426) (.exec 0x11ec80 (fun s => s.RIP = 0x11ec80) (movR64R64Effect 0x11ec80 0 12) (Reg.operands [.gpr 12] [])) #v[2411]
    (.letOp (n := 2427) (.exec 0x11ec83 (StorePre 0x11ec83 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11ec83 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ec83 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[2411, 4]
    (.letOp (n := 2428) (.out 0x11ec88 (mulR64Effect 0x11ec88 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2422, 2425]
    (.letOp (n := 2429) (.out 0x11ec88 (mulR64Effect 0x11ec88 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2422, 2425]
    (.letOp (n := 2430) (.exec 0x11ec88 (fun s => s.RIP = 0x11ec88) (mulR64Effect 0x11ec88 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2422, 2425]
    (.letOp (n := 2431) (.out 0x11ec8b (movR64R64Effect 0x11ec8b 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[2428]
    (.letOp (n := 2432) (.exec 0x11ec8b (fun s => s.RIP = 0x11ec8b) (movR64R64Effect 0x11ec8b 1 0) (Reg.operands [.gpr 0] [])) #v[2428]
    (.letOp (n := 2433) (.out 0x11ec8e (movR64R64Effect 0x11ec8e 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2429]
    (.letOp (n := 2434) (.exec 0x11ec8e (fun s => s.RIP = 0x11ec8e) (movR64R64Effect 0x11ec8e 6 2) (Reg.operands [.gpr 2] [])) #v[2429]
    (.letOp (n := 2435) (.out 0x11ec91 (movR64M64Effect 0x11ec91 7 (.sib 4 none 0 (.d32 0x188))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 2436) (.exec 0x11ec91 (LoadPre 0x11ec91 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x11ec91 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ec91 7 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2437) (.out 0x11ec99 (movR64R64Effect 0x11ec99 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[2413]
    (.letOp (n := 2438) (.exec 0x11ec99 (fun s => s.RIP = 0x11ec99) (movR64R64Effect 0x11ec99 0 5) (Reg.operands [.gpr 5] [])) #v[2413]
    (.letOp (n := 2439) (.out 0x11ec9c (movR64R64Effect 0x11ec9c 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 5] []) (.reg (.gpr 13))) #v[2413]
    (.letOp (n := 2440) (.exec 0x11ec9c (fun s => s.RIP = 0x11ec9c) (movR64R64Effect 0x11ec9c 13 5) (Reg.operands [.gpr 5] [])) #v[2413]
    (.letOp (n := 2441) (.exec 0x11ec9f (StorePre 0x11ec9f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11ec9f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ec9f 5 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[2413, 4]
    (.letOp (n := 2442) (.out 0x11eca7 (mulR64Effect 0x11eca7 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2435, 2437]
    (.letOp (n := 2443) (.out 0x11eca7 (mulR64Effect 0x11eca7 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2435, 2437]
    (.letOp (n := 2444) (.exec 0x11eca7 (fun s => s.RIP = 0x11eca7) (mulR64Effect 0x11eca7 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2435, 2437]
    (.letOp (n := 2445) (.out 0x11ecaa (movR64R64Effect 0x11ecaa 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 7] []) (.reg (.gpr 5))) #v[2435]
    (.letOp (n := 2446) (.exec 0x11ecaa (fun s => s.RIP = 0x11ecaa) (movR64R64Effect 0x11ecaa 5 7) (Reg.operands [.gpr 7] [])) #v[2435]
    (.letOp (n := 2447) (.exec 0x11ecad (StorePre 0x11ecad 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11ecad + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ecad 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[2435, 4]
    (.letOp (n := 2448) (.out 0x11ecb2 (movR64R64Effect 0x11ecb2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2443]
    (.letOp (n := 2449) (.exec 0x11ecb2 (fun s => s.RIP = 0x11ecb2) (movR64R64Effect 0x11ecb2 7 2) (Reg.operands [.gpr 2] [])) #v[2443]
    (.letOp (n := 2450) (.out 0x11ecb5 (movR64R64Effect 0x11ecb5 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[2442]
    (.letOp (n := 2451) (.exec 0x11ecb5 (fun s => s.RIP = 0x11ecb5) (movR64R64Effect 0x11ecb5 8 0) (Reg.operands [.gpr 0] [])) #v[2442]
    (.letOp (n := 2452) (.out 0x11ecb8 (addR64R64Effect 0x11ecb8 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[2450, 2431]
    (.letOp (n := 2453) (.out 0x11ecb8 (addR64R64Effect 0x11ecb8 8 1) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 1] []) (.flag .CF)) #v[2450, 2431]
    (.letOp (n := 2454) (.exec 0x11ecb8 (fun s => s.RIP = 0x11ecb8) (addR64R64Effect 0x11ecb8 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[2450, 2431]
    (.letOp (n := 2455) (.out 0x11ecbb (atFlags StatusFlags.CF (adcR64R64Effect 0x11ecbb 7 6)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[2448, 2433, 2453]
    (.letOp (n := 2456) (.exec 0x11ecbb (fun s => s.RIP = 0x11ecbb) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ecbb 7 6)) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2448, 2433, 2453]
    (.letOp (n := 2457) (.out 0x11ecbe (movR64M64Effect 0x11ecbe 15 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 2458) (.exec 0x11ecbe (LoadPre 0x11ecbe (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x11ecbe + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ecbe 15 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2459) (.out 0x11ecc6 (movR64R64Effect 0x11ecc6 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2417]
    (.letOp (n := 2460) (.exec 0x11ecc6 (fun s => s.RIP = 0x11ecc6) (movR64R64Effect 0x11ecc6 0 9) (Reg.operands [.gpr 9] [])) #v[2417]
    (.letOp (n := 2461) (.exec 0x11ecc9 (StorePre 0x11ecc9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11ecc9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ecc9 9 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[2417, 4]
    (.letOp (n := 2462) (.out 0x11ecce (mulR64Effect 0x11ecce 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[2457, 2459]
    (.letOp (n := 2463) (.out 0x11ecce (mulR64Effect 0x11ecce 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[2457, 2459]
    (.letOp (n := 2464) (.exec 0x11ecce (fun s => s.RIP = 0x11ecce) (mulR64Effect 0x11ecce 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[2457, 2459]
    (b_l11d880_57))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_56 : List UInt8 :=
  [0x4C, 0x89, 0xE0, 0x4C, 0x89, 0x64, 0x24, 0x18, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xC1, 0x48, 0x89,
    0xD6, 0x48, 0x8B, 0xBC, 0x24, 0x88, 0x01, 0x00, 0x00, 0x48, 0x89, 0xE8, 0x49, 0x89, 0xED, 0x48,
    0x89, 0xAC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xFD, 0x48, 0x89, 0x7C,
    0x24, 0x58, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0, 0x49, 0x01, 0xC8, 0x48, 0x11, 0xF7, 0x4C, 0x8B,
    0xBC, 0x24, 0x80, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xC8, 0x4C, 0x89, 0x4C, 0x24, 0x28, 0x49, 0xF7,
    0xE7] ++ bytes_l11d880_57

theorem code_l11d880_56 : ∀ x ∈ codeRange 0x11ec80 bytes_l11d880_56, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ec80 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_57

def b_l11d880_55 : Block Op Label signature Reg.count 2387 :=
  .letOp (n := 2387) (.out 0x11ec1b (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ec1b 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2374, 2385]
    (.letOp (n := 2388) (.exec 0x11ec1b (fun s => s.RIP = 0x11ec1b) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ec1b 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2374, 2385]
    (.letOp (n := 2389) (.out 0x11ec1f (movR64M64Effect 0x11ec1f 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2390) (.exec 0x11ec1f (LoadPre 0x11ec1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11ec1f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ec1f 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2391) (.exec 0x11ec24 (StorePre 0x11ec24 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x11ec24 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ec24 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2389, 4]
    (.letOp (n := 2392) (.out 0x11ec2c (addR64R64Effect 0x11ec2c 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[2384, 2367]
    (.letOp (n := 2393) (.out 0x11ec2c (addR64R64Effect 0x11ec2c 11 14) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 14] []) (.flag .CF)) #v[2384, 2367]
    (.letOp (n := 2394) (.exec 0x11ec2c (fun s => s.RIP = 0x11ec2c) (addR64R64Effect 0x11ec2c 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[2384, 2367]
    (.letOp (n := 2395) (.out 0x11ec2f (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ec2f 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2387, 2393]
    (.letOp (n := 2396) (.exec 0x11ec2f (fun s => s.RIP = 0x11ec2f) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ec2f 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2387, 2393]
    (.letOp (n := 2397) (.out 0x11ec33 (shldR64R64Effect 0x11ec33 5 2 11 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2395, 2392]
    (.letOp (n := 2398) (.exec 0x11ec33 (fun s => s.RIP = 0x11ec33) (shldR64R64Effect 0x11ec33 5 2 11 12) (Reg.operands [.gpr 2, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2395, 2392]
    (.letOp (n := 2399) (.out 0x11ec38 (movR64Imm64Effect 0x11ec38 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 2400) (.exec 0x11ec38 (fun s => s.RIP = 0x11ec38) (movR64Imm64Effect 0x11ec38 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2401) (.out 0x11ec42 (movR64M64Effect 0x11ec42 3 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 2402) (.exec 0x11ec42 (LoadPre 0x11ec42 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11ec42 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ec42 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2403) (.out 0x11ec47 (andR64R64Effect 0x11ec47 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[2401, 2399]
    (.letOp (n := 2404) (.exec 0x11ec47 (fun s => s.RIP = 0x11ec47) (andR64R64Effect 0x11ec47 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[2401, 2399]
    (.letOp (n := 2405) (.out 0x11ec4a (addR64R64Effect 0x11ec4a 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[2403, 2397]
    (.letOp (n := 2406) (.exec 0x11ec4a (fun s => s.RIP = 0x11ec4a) (addR64R64Effect 0x11ec4a 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[2403, 2397]
    (.letOp (n := 2407) (.out 0x11ec4d (movR64Imm64Effect 0x11ec4d 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 2408) (.exec 0x11ec4d (fun s => s.RIP = 0x11ec4d) (movR64Imm64Effect 0x11ec4d 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2409) (.out 0x11ec57 (movR64M64Effect 0x11ec57 12 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 2410) (.exec 0x11ec57 (LoadPre 0x11ec57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11ec57 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ec57 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2411) (.out 0x11ec5c (andR64R64Effect 0x11ec5c 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[2409, 2407]
    (.letOp (n := 2412) (.exec 0x11ec5c (fun s => s.RIP = 0x11ec5c) (andR64R64Effect 0x11ec5c 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[2409, 2407]
    (.letOp (n := 2413) (.out 0x11ec5f (andR64R64Effect 0x11ec5f 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[2262, 2407]
    (.letOp (n := 2414) (.exec 0x11ec5f (fun s => s.RIP = 0x11ec5f) (andR64R64Effect 0x11ec5f 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[2262, 2407]
    (.letOp (n := 2415) (.out 0x11ec62 (movR64R64Effect 0x11ec62 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[2351]
    (.letOp (n := 2416) (.exec 0x11ec62 (fun s => s.RIP = 0x11ec62) (movR64R64Effect 0x11ec62 9 8) (Reg.operands [.gpr 8] [])) #v[2351]
    (.letOp (n := 2417) (.out 0x11ec65 (andR64R64Effect 0x11ec65 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[2415, 2407]
    (.letOp (n := 2418) (.exec 0x11ec65 (fun s => s.RIP = 0x11ec65) (andR64R64Effect 0x11ec65 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2415, 2407]
    (.letOp (n := 2419) (.out 0x11ec68 (andR64R64Effect 0x11ec68 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[2392, 2407]
    (.letOp (n := 2420) (.exec 0x11ec68 (fun s => s.RIP = 0x11ec68) (andR64R64Effect 0x11ec68 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[2392, 2407]
    (.letOp (n := 2421) (.exec 0x11ec6b (StorePre 0x11ec6b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11ec6b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ec6b 11 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[2419, 4]
    (.letOp (n := 2422) (.out 0x11ec73 (movR64M64Effect 0x11ec73 2 (.sib 4 none 0 (.d32 0x190))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 2423) (.exec 0x11ec73 (LoadPre 0x11ec73 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x11ec73 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ec73 2 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2424) (.exec 0x11ec7b (StorePre 0x11ec7b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11ec7b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ec7b 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2422, 4]
    (b_l11d880_56))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_55 : List UInt8 :=
  [0x48, 0x83, 0xD2, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x78, 0x48, 0x89, 0x84, 0x24, 0x48, 0x01, 0x00,
    0x00, 0x4D, 0x01, 0xF3, 0x48, 0x83, 0xD2, 0x00, 0x4C, 0x0F, 0xA4, 0xDA, 0x0C, 0x48, 0xB8, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x8B, 0x5C, 0x24, 0x10, 0x48, 0x21, 0xC3, 0x48,
    0x01, 0xD3, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x8B, 0x64, 0x24,
    0x18, 0x49, 0x21, 0xC4, 0x48, 0x21, 0xC5, 0x4D, 0x89, 0xC1, 0x49, 0x21, 0xC1, 0x49, 0x21, 0xC3,
    0x4C, 0x89, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0x90, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x54, 0x24, 0x30] ++ bytes_l11d880_56

theorem code_l11d880_55 : ∀ x ∈ codeRange 0x11ec1b bytes_l11d880_55, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ec1b 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_56

def b_l11d880_54 : Block Op Label signature Reg.count 2348 :=
  .letOp (n := 2348) (.out 0x11eb9f (movR64M64Effect 0x11eb9f 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2349) (.exec 0x11eb9f (LoadPre 0x11eb9f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11eb9f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11eb9f 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2350) (.exec 0x11eba7 (StorePre 0x11eba7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x11eba7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11eba7 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2348, 4]
    (.letOp (n := 2351) (.out 0x11ebaf (addR64R64Effect 0x11ebaf 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[2343, 2292]
    (.letOp (n := 2352) (.out 0x11ebaf (addR64R64Effect 0x11ebaf 8 3) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 3] []) (.flag .CF)) #v[2343, 2292]
    (.letOp (n := 2353) (.exec 0x11ebaf (fun s => s.RIP = 0x11ebaf) (addR64R64Effect 0x11ebaf 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[2343, 2292]
    (.letOp (n := 2354) (.out 0x11ebb2 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ebb2 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2346, 2352]
    (.letOp (n := 2355) (.exec 0x11ebb2 (fun s => s.RIP = 0x11ebb2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ebb2 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2346, 2352]
    (.letOp (n := 2356) (.out 0x11ebb6 (movR64M64Effect 0x11ebb6 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2357) (.exec 0x11ebb6 (LoadPre 0x11ebb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11ebb6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ebb6 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2358) (.exec 0x11ebbe (StorePre 0x11ebbe 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x11ebbe + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ebbe 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2356, 4]
    (.letOp (n := 2359) (.out 0x11ebc6 (shldR64R64Effect 0x11ebc6 5 9 12 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2318, 2315]
    (.letOp (n := 2360) (.exec 0x11ebc6 (fun s => s.RIP = 0x11ebc6) (shldR64R64Effect 0x11ebc6 5 9 12 12) (Reg.operands [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2318, 2315]
    (.letOp (n := 2361) (.out 0x11ebcb (movR64M64Effect 0x11ebcb 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2362) (.exec 0x11ebcb (LoadPre 0x11ebcb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11ebcb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ebcb 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2363) (.exec 0x11ebd3 (StorePre 0x11ebd3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x11ebd3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ebd3 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2361, 4]
    (.letOp (n := 2364) (.out 0x11ebdb (movR64M64Effect 0x11ebdb 0 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2365) (.exec 0x11ebdb (LoadPre 0x11ebdb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x11ebdb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ebdb 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2366) (.exec 0x11ebe3 (StorePre 0x11ebe3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x11ebe3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ebe3 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2364, 4]
    (.letOp (n := 2367) (.out 0x11ebeb (shldR64R64Effect 0x11ebeb 5 14 8 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[2354, 2351]
    (.letOp (n := 2368) (.exec 0x11ebeb (fun s => s.RIP = 0x11ebeb) (shldR64R64Effect 0x11ebeb 5 14 8 12) (Reg.operands [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2354, 2351]
    (.letOp (n := 2369) (.out 0x11ebf0 (movR64R64Effect 0x11ebf0 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2359]
    (.letOp (n := 2370) (.exec 0x11ebf0 (fun s => s.RIP = 0x11ebf0) (movR64R64Effect 0x11ebf0 0 9) (Reg.operands [.gpr 9] [])) #v[2359]
    (.letOp (n := 2371) (.out 0x11ebf3 (movR64Imm64Effect 0x11ebf3 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2372) (.exec 0x11ebf3 (fun s => s.RIP = 0x11ebf3) (movR64Imm64Effect 0x11ebf3 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2373) (.out 0x11ebfd (mulR64Effect 0x11ebfd 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2371, 2369]
    (.letOp (n := 2374) (.out 0x11ebfd (mulR64Effect 0x11ebfd 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2371, 2369]
    (.letOp (n := 2375) (.exec 0x11ebfd (fun s => s.RIP = 0x11ebfd) (mulR64Effect 0x11ebfd 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2371, 2369]
    (.letOp (n := 2376) (.out 0x11ec00 (movR64R64Effect 0x11ec00 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[2373]
    (.letOp (n := 2377) (.exec 0x11ec00 (fun s => s.RIP = 0x11ec00) (movR64R64Effect 0x11ec00 11 0) (Reg.operands [.gpr 0] [])) #v[2373]
    (.letOp (n := 2378) (.out 0x11ec03 (movR64Imm64Effect 0x11ec03 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 2379) (.exec 0x11ec03 (fun s => s.RIP = 0x11ec03) (movR64Imm64Effect 0x11ec03 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2380) (.out 0x11ec0d (movR64M64Effect 0x11ec0d 1 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 2381) (.exec 0x11ec0d (LoadPre 0x11ec0d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11ec0d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ec0d 1 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2382) (.out 0x11ec15 (andR64R64Effect 0x11ec15 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2380, 2378]
    (.letOp (n := 2383) (.exec 0x11ec15 (fun s => s.RIP = 0x11ec15) (andR64R64Effect 0x11ec15 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2380, 2378]
    (.letOp (n := 2384) (.out 0x11ec18 (addR64R64Effect 0x11ec18 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[2376, 2382]
    (.letOp (n := 2385) (.out 0x11ec18 (addR64R64Effect 0x11ec18 11 1) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 1] []) (.flag .CF)) #v[2376, 2382]
    (.letOp (n := 2386) (.exec 0x11ec18 (fun s => s.RIP = 0x11ec18) (addR64R64Effect 0x11ec18 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[2376, 2382]
    (b_l11d880_55)))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_54 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00,
    0x49, 0x01, 0xD8, 0x49, 0x83, 0xD6, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x4D, 0x0F, 0xA4, 0xE1, 0x0C, 0x48, 0x8B, 0x84, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24,
    0xE0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x4D, 0x0F, 0xA4, 0xC6,
    0x0C, 0x4C, 0x89, 0xC8, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xE1, 0x49, 0x89, 0xC3, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x8B,
    0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x21, 0xC1, 0x49, 0x01, 0xCB] ++ bytes_l11d880_55

theorem code_l11d880_54 : ∀ x ∈ codeRange 0x11eb9f bytes_l11d880_54, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1eb9f 124 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_55

def b_l11d880_53 : Block Op Label signature Reg.count 2301 :=
  .letOp (n := 2301) (.out 0x11eb4d (movR64R64Effect 0x11eb4d 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2297]
    (.letOp (n := 2302) (.exec 0x11eb4d (fun s => s.RIP = 0x11eb4d) (movR64R64Effect 0x11eb4d 9 2) (Reg.operands [.gpr 2] [])) #v[2297]
    (.letOp (n := 2303) (.out 0x11eb50 (movR64M64Effect 0x11eb50 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2304) (.exec 0x11eb50 (LoadPre 0x11eb50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11eb50 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11eb50 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2305) (.out 0x11eb55 (mulR64Effect 0x11eb55 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[2218, 2303]
    (.letOp (n := 2306) (.out 0x11eb55 (mulR64Effect 0x11eb55 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[2218, 2303]
    (.letOp (n := 2307) (.exec 0x11eb55 (fun s => s.RIP = 0x11eb55) (mulR64Effect 0x11eb55 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2218, 2303]
    (.letOp (n := 2308) (.out 0x11eb58 (movR64R64Effect 0x11eb58 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[2305]
    (.letOp (n := 2309) (.exec 0x11eb58 (fun s => s.RIP = 0x11eb58) (movR64R64Effect 0x11eb58 12 0) (Reg.operands [.gpr 0] [])) #v[2305]
    (.letOp (n := 2310) (.out 0x11eb5b (addR64R64Effect 0x11eb5b 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[2308, 2299]
    (.letOp (n := 2311) (.out 0x11eb5b (addR64R64Effect 0x11eb5b 12 11) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 11] []) (.flag .CF)) #v[2308, 2299]
    (.letOp (n := 2312) (.exec 0x11eb5b (fun s => s.RIP = 0x11eb5b) (addR64R64Effect 0x11eb5b 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[2308, 2299]
    (.letOp (n := 2313) (.out 0x11eb5e (atFlags StatusFlags.CF (adcR64R64Effect 0x11eb5e 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[2301, 2306, 2311]
    (.letOp (n := 2314) (.exec 0x11eb5e (fun s => s.RIP = 0x11eb5e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11eb5e 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2301, 2306, 2311]
    (.letOp (n := 2315) (.out 0x11eb61 (addR64R64Effect 0x11eb61 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[2310, 2238]
    (.letOp (n := 2316) (.out 0x11eb61 (addR64R64Effect 0x11eb61 12 15) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 15] []) (.flag .CF)) #v[2310, 2238]
    (.letOp (n := 2317) (.exec 0x11eb61 (fun s => s.RIP = 0x11eb61) (addR64R64Effect 0x11eb61 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[2310, 2238]
    (.letOp (n := 2318) (.out 0x11eb64 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11eb64 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[2313, 2316]
    (.letOp (n := 2319) (.exec 0x11eb64 (fun s => s.RIP = 0x11eb64) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11eb64 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2313, 2316]
    (.letOp (n := 2320) (.out 0x11eb68 (movR64R64Effect 0x11eb68 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[2315]
    (.letOp (n := 2321) (.exec 0x11eb68 (fun s => s.RIP = 0x11eb68) (movR64R64Effect 0x11eb68 0 12) (Reg.operands [.gpr 12] [])) #v[2315]
    (.letOp (n := 2322) (.out 0x11eb6b (movR64Imm64Effect 0x11eb6b 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2323) (.exec 0x11eb6b (fun s => s.RIP = 0x11eb6b) (movR64Imm64Effect 0x11eb6b 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2324) (.out 0x11eb75 (andR64R64Effect 0x11eb75 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[2320, 2322]
    (.letOp (n := 2325) (.exec 0x11eb75 (fun s => s.RIP = 0x11eb75) (andR64R64Effect 0x11eb75 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[2320, 2322]
    (.letOp (n := 2326) (.out 0x11eb78 (movR64Imm64Effect 0x11eb78 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2327) (.exec 0x11eb78 (fun s => s.RIP = 0x11eb78) (movR64Imm64Effect 0x11eb78 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2328) (.out 0x11eb82 (mulR64Effect 0x11eb82 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2326, 2324]
    (.letOp (n := 2329) (.out 0x11eb82 (mulR64Effect 0x11eb82 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2326, 2324]
    (.letOp (n := 2330) (.exec 0x11eb82 (fun s => s.RIP = 0x11eb82) (mulR64Effect 0x11eb82 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2326, 2324]
    (.letOp (n := 2331) (.out 0x11eb85 (movR64R64Effect 0x11eb85 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[2328]
    (.letOp (n := 2332) (.exec 0x11eb85 (fun s => s.RIP = 0x11eb85) (movR64R64Effect 0x11eb85 8 0) (Reg.operands [.gpr 0] [])) #v[2328]
    (.letOp (n := 2333) (.out 0x11eb88 (addR64R64Effect 0x11eb88 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[2288, 2281]
    (.letOp (n := 2334) (.out 0x11eb88 (addR64R64Effect 0x11eb88 1 10) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 10] []) (.flag .CF)) #v[2288, 2281]
    (.letOp (n := 2335) (.exec 0x11eb88 (fun s => s.RIP = 0x11eb88) (addR64R64Effect 0x11eb88 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[2288, 2281]
    (.letOp (n := 2336) (.out 0x11eb8b (atFlags StatusFlags.CF (adcR64R64Effect 0x11eb8b 14 6)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2290, 2279, 2334]
    (.letOp (n := 2337) (.exec 0x11eb8b (fun s => s.RIP = 0x11eb8b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11eb8b 14 6)) (Reg.operands [.gpr 14, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2290, 2279, 2334]
    (.letOp (n := 2338) (.out 0x11eb8e (addR64R64Effect 0x11eb8e 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[2333, 2272]
    (.letOp (n := 2339) (.out 0x11eb8e (addR64R64Effect 0x11eb8e 1 7) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 7] []) (.flag .CF)) #v[2333, 2272]
    (.letOp (n := 2340) (.exec 0x11eb8e (fun s => s.RIP = 0x11eb8e) (addR64R64Effect 0x11eb8e 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[2333, 2272]
    (.letOp (n := 2341) (.out 0x11eb91 (atFlags StatusFlags.CF (adcR64M64Effect 0x11eb91 14 (.sib 4 none 0 (.d32 0x88)))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 14))) #v[2336, 4, 2339]
    (.letOp (n := 2342) (.exec 0x11eb91 (LoadPre 0x11eb91 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11eb91 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11eb91 14 (.sib 4 none 0 (.d32 0x88)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2336, 4, 2339]
    (.letOp (n := 2343) (.out 0x11eb99 (addR64R64Effect 0x11eb99 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[2331, 2338]
    (.letOp (n := 2344) (.out 0x11eb99 (addR64R64Effect 0x11eb99 8 1) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 1] []) (.flag .CF)) #v[2331, 2338]
    (.letOp (n := 2345) (.exec 0x11eb99 (fun s => s.RIP = 0x11eb99) (addR64R64Effect 0x11eb99 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[2331, 2338]
    (.letOp (n := 2346) (.out 0x11eb9c (atFlags StatusFlags.CF (adcR64R64Effect 0x11eb9c 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2341, 2329, 2344]
    (.letOp (n := 2347) (.exec 0x11eb9c (fun s => s.RIP = 0x11eb9c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11eb9c 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2341, 2329, 2344]
    (b_l11d880_54)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_53 : List UInt8 :=
  [0x49, 0x89, 0xD1, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xC4, 0x4D, 0x01,
    0xDC, 0x49, 0x11, 0xD1, 0x4D, 0x01, 0xFC, 0x49, 0x83, 0xD1, 0x00, 0x4C, 0x89, 0xE0, 0x48, 0xBA,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00,
    0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xC0, 0x4C, 0x01, 0xD1, 0x49, 0x11,
    0xF6, 0x48, 0x01, 0xF9, 0x4C, 0x13, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC8, 0x49,
    0x11, 0xD6] ++ bytes_l11d880_54

theorem code_l11d880_53 : ∀ x ∈ codeRange 0x11eb4d bytes_l11d880_53, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1eb4d 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_54

def b_l11d880_52 : Block Op Label signature Reg.count 2257 :=
  .letOp (n := 2257) (.out 0x11eafe (atFlags StatusFlags.CF (adcR64R64Effect 0x11eafe 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[2252, 2247, 2255]
    (.letOp (n := 2258) (.exec 0x11eafe (fun s => s.RIP = 0x11eafe) (atFlags StatusFlags.CF (adcR64R64Effect 0x11eafe 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2252, 2247, 2255]
    (.letOp (n := 2259) (.out 0x11eb01 (addR64R64Effect 0x11eb01 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[2254, 2203]
    (.letOp (n := 2260) (.out 0x11eb01 (addR64R64Effect 0x11eb01 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[2254, 2203]
    (.letOp (n := 2261) (.exec 0x11eb01 (fun s => s.RIP = 0x11eb01) (addR64R64Effect 0x11eb01 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[2254, 2203]
    (.letOp (n := 2262) (.out 0x11eb04 (movR64R64Effect 0x11eb04 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[2259]
    (.letOp (n := 2263) (.exec 0x11eb04 (fun s => s.RIP = 0x11eb04) (movR64R64Effect 0x11eb04 5 0) (Reg.operands [.gpr 0] [])) #v[2259]
    (.letOp (n := 2264) (.out 0x11eb07 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11eb07 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[2257, 2260]
    (.letOp (n := 2265) (.exec 0x11eb07 (fun s => s.RIP = 0x11eb07) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11eb07 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2257, 2260]
    (.letOp (n := 2266) (.out 0x11eb0b (movR64R64Effect 0x11eb0b 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2214]
    (.letOp (n := 2267) (.exec 0x11eb0b (fun s => s.RIP = 0x11eb0b) (movR64R64Effect 0x11eb0b 0 8) (Reg.operands [.gpr 8] [])) #v[2214]
    (.letOp (n := 2268) (.out 0x11eb0e (mulR64Effect 0x11eb0e 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[2174, 2266]
    (.letOp (n := 2269) (.out 0x11eb0e (mulR64Effect 0x11eb0e 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[2174, 2266]
    (.letOp (n := 2270) (.exec 0x11eb0e (fun s => s.RIP = 0x11eb0e) (mulR64Effect 0x11eb0e 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2174, 2266]
    (.letOp (n := 2271) (.exec 0x11eb11 (StorePre 0x11eb11 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11eb11 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11eb11 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2269, 4]
    (.letOp (n := 2272) (.out 0x11eb19 (movR64R64Effect 0x11eb19 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[2268]
    (.letOp (n := 2273) (.exec 0x11eb19 (fun s => s.RIP = 0x11eb19) (movR64R64Effect 0x11eb19 7 0) (Reg.operands [.gpr 0] [])) #v[2268]
    (.letOp (n := 2274) (.out 0x11eb1c (movR64M64Effect 0x11eb1c 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2275) (.exec 0x11eb1c (LoadPre 0x11eb1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11eb1c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11eb1c 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2276) (.out 0x11eb21 (mulR64Effect 0x11eb21 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[2183, 2274]
    (.letOp (n := 2277) (.out 0x11eb21 (mulR64Effect 0x11eb21 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[2183, 2274]
    (.letOp (n := 2278) (.exec 0x11eb21 (fun s => s.RIP = 0x11eb21) (mulR64Effect 0x11eb21 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[2183, 2274]
    (.letOp (n := 2279) (.out 0x11eb24 (movR64R64Effect 0x11eb24 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2277]
    (.letOp (n := 2280) (.exec 0x11eb24 (fun s => s.RIP = 0x11eb24) (movR64R64Effect 0x11eb24 6 2) (Reg.operands [.gpr 2] [])) #v[2277]
    (.letOp (n := 2281) (.out 0x11eb27 (movR64R64Effect 0x11eb27 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2276]
    (.letOp (n := 2282) (.exec 0x11eb27 (fun s => s.RIP = 0x11eb27) (movR64R64Effect 0x11eb27 10 0) (Reg.operands [.gpr 0] [])) #v[2276]
    (.letOp (n := 2283) (.out 0x11eb2a (movR64M64Effect 0x11eb2a 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2284) (.exec 0x11eb2a (LoadPre 0x11eb2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11eb2a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11eb2a 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2285) (.out 0x11eb2f (mulR64Effect 0x11eb2f 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[2194, 2283]
    (.letOp (n := 2286) (.out 0x11eb2f (mulR64Effect 0x11eb2f 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[2194, 2283]
    (.letOp (n := 2287) (.exec 0x11eb2f (fun s => s.RIP = 0x11eb2f) (mulR64Effect 0x11eb2f 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[2194, 2283]
    (.letOp (n := 2288) (.out 0x11eb32 (movR64R64Effect 0x11eb32 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[2285]
    (.letOp (n := 2289) (.exec 0x11eb32 (fun s => s.RIP = 0x11eb32) (movR64R64Effect 0x11eb32 1 0) (Reg.operands [.gpr 0] [])) #v[2285]
    (.letOp (n := 2290) (.out 0x11eb35 (movR64R64Effect 0x11eb35 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2286]
    (.letOp (n := 2291) (.exec 0x11eb35 (fun s => s.RIP = 0x11eb35) (movR64R64Effect 0x11eb35 14 2) (Reg.operands [.gpr 2] [])) #v[2286]
    (.letOp (n := 2292) (.out 0x11eb38 (shldR64R64Effect 0x11eb38 5 3 5 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[2264, 2262]
    (.letOp (n := 2293) (.exec 0x11eb38 (fun s => s.RIP = 0x11eb38) (shldR64R64Effect 0x11eb38 5 3 5 12) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2264, 2262]
    (.letOp (n := 2294) (.out 0x11eb3d (movR64M64Effect 0x11eb3d 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2295) (.exec 0x11eb3d (LoadPre 0x11eb3d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11eb3d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11eb3d 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2296) (.out 0x11eb45 (mulM64Effect 0x11eb45 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2294, 4]
    (.letOp (n := 2297) (.out 0x11eb45 (mulM64Effect 0x11eb45 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2294, 4]
    (.letOp (n := 2298) (.exec 0x11eb45 (LoadPre 0x11eb45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11eb45 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11eb45 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2294, 4]
    (.letOp (n := 2299) (.out 0x11eb4a (movR64R64Effect 0x11eb4a 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[2296]
    (.letOp (n := 2300) (.exec 0x11eb4a (fun s => s.RIP = 0x11eb4a) (movR64R64Effect 0x11eb4a 11 0) (Reg.operands [.gpr 0] [])) #v[2296]
    (b_l11d880_53))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_52 : List UInt8 :=
  [0x48, 0x11, 0xD3, 0x48, 0x01, 0xE8, 0x48, 0x89, 0xC5, 0x48, 0x83, 0xD3, 0x00, 0x4C, 0x89, 0xC0,
    0x49, 0xF7, 0xE1, 0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x48, 0x8B,
    0x44, 0x24, 0x60, 0x49, 0xF7, 0xE4, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC2, 0x48, 0x8B, 0x44, 0x24,
    0x28, 0x49, 0xF7, 0xE3, 0x48, 0x89, 0xC1, 0x49, 0x89, 0xD6, 0x48, 0x0F, 0xA4, 0xEB, 0x0C, 0x48,
    0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x30, 0x49, 0x89, 0xC3] ++ bytes_l11d880_53

theorem code_l11d880_52 : ∀ x ∈ codeRange 0x11eafe bytes_l11d880_52, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1eafe 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_53

def b_l11d880_51 : Block Op Label signature Reg.count 2210 :=
  .letOp (n := 2210) (.out 0x11eaa3 (movR64R64Effect 0x11eaa3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2207]
    (.letOp (n := 2211) (.exec 0x11eaa3 (fun s => s.RIP = 0x11eaa3) (movR64R64Effect 0x11eaa3 10 0) (Reg.operands [.gpr 0] [])) #v[2207]
    (.letOp (n := 2212) (.out 0x11eaa6 (movR64R64Effect 0x11eaa6 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2208]
    (.letOp (n := 2213) (.exec 0x11eaa6 (fun s => s.RIP = 0x11eaa6) (movR64R64Effect 0x11eaa6 15 2) (Reg.operands [.gpr 2] [])) #v[2208]
    (.letOp (n := 2214) (.out 0x11eaa9 (movR64M64Effect 0x11eaa9 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 2215) (.exec 0x11eaa9 (LoadPre 0x11eaa9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11eaa9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11eaa9 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2216) (.out 0x11eab1 (movR64R64Effect 0x11eab1 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2214]
    (.letOp (n := 2217) (.exec 0x11eab1 (fun s => s.RIP = 0x11eab1) (movR64R64Effect 0x11eab1 0 8) (Reg.operands [.gpr 8] [])) #v[2214]
    (.letOp (n := 2218) (.out 0x11eab4 (movR64M64Effect 0x11eab4 13 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 2219) (.exec 0x11eab4 (LoadPre 0x11eab4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11eab4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11eab4 13 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2220) (.out 0x11eab9 (mulR64Effect 0x11eab9 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[2218, 2216]
    (.letOp (n := 2221) (.out 0x11eab9 (mulR64Effect 0x11eab9 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[2218, 2216]
    (.letOp (n := 2222) (.exec 0x11eab9 (fun s => s.RIP = 0x11eab9) (mulR64Effect 0x11eab9 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2218, 2216]
    (.letOp (n := 2223) (.out 0x11eabc (addR64R64Effect 0x11eabc 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[2220, 2210]
    (.letOp (n := 2224) (.out 0x11eabc (addR64R64Effect 0x11eabc 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[2220, 2210]
    (.letOp (n := 2225) (.exec 0x11eabc (fun s => s.RIP = 0x11eabc) (addR64R64Effect 0x11eabc 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[2220, 2210]
    (.letOp (n := 2226) (.out 0x11eabf (atFlags StatusFlags.CF (adcR64R64Effect 0x11eabf 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[2212, 2221, 2224]
    (.letOp (n := 2227) (.exec 0x11eabf (fun s => s.RIP = 0x11eabf) (atFlags StatusFlags.CF (adcR64R64Effect 0x11eabf 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2212, 2221, 2224]
    (.letOp (n := 2228) (.out 0x11eac2 (addR64R64Effect 0x11eac2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2223, 2199]
    (.letOp (n := 2229) (.out 0x11eac2 (addR64R64Effect 0x11eac2 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[2223, 2199]
    (.letOp (n := 2230) (.exec 0x11eac2 (fun s => s.RIP = 0x11eac2) (addR64R64Effect 0x11eac2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2223, 2199]
    (.letOp (n := 2231) (.out 0x11eac5 (atFlags StatusFlags.CF (adcR64R64Effect 0x11eac5 15 6)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[2226, 2201, 2229]
    (.letOp (n := 2232) (.exec 0x11eac5 (fun s => s.RIP = 0x11eac5) (atFlags StatusFlags.CF (adcR64R64Effect 0x11eac5 15 6)) (Reg.operands [.gpr 15, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2226, 2201, 2229]
    (.letOp (n := 2233) (.out 0x11eac8 (addR64R64Effect 0x11eac8 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[2228, 2149]
    (.letOp (n := 2234) (.out 0x11eac8 (addR64R64Effect 0x11eac8 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[2228, 2149]
    (.letOp (n := 2235) (.exec 0x11eac8 (fun s => s.RIP = 0x11eac8) (addR64R64Effect 0x11eac8 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[2228, 2149]
    (.letOp (n := 2236) (.out 0x11eacb (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11eacb 15 0x0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[2231, 2234]
    (.letOp (n := 2237) (.exec 0x11eacb (fun s => s.RIP = 0x11eacb) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11eacb 15 0x0)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2231, 2234]
    (.letOp (n := 2238) (.out 0x11eacf (shldR64R64Effect 0x11eacf 5 15 0 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[2236, 2233]
    (.letOp (n := 2239) (.exec 0x11eacf (fun s => s.RIP = 0x11eacf) (shldR64R64Effect 0x11eacf 5 15 0 12) (Reg.operands [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2236, 2233]
    (.letOp (n := 2240) (.out 0x11ead4 (movR64Imm64Effect 0x11ead4 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2241) (.exec 0x11ead4 (fun s => s.RIP = 0x11ead4) (movR64Imm64Effect 0x11ead4 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2242) (.out 0x11eade (andR64R64Effect 0x11eade 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2233, 2240]
    (.letOp (n := 2243) (.exec 0x11eade (fun s => s.RIP = 0x11eade) (andR64R64Effect 0x11eade 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2233, 2240]
    (.letOp (n := 2244) (.out 0x11eae1 (movR64Imm64Effect 0x11eae1 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2245) (.exec 0x11eae1 (fun s => s.RIP = 0x11eae1) (movR64Imm64Effect 0x11eae1 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2246) (.out 0x11eaeb (mulR64Effect 0x11eaeb 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2244, 2242]
    (.letOp (n := 2247) (.out 0x11eaeb (mulR64Effect 0x11eaeb 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2244, 2242]
    (.letOp (n := 2248) (.exec 0x11eaeb (fun s => s.RIP = 0x11eaeb) (mulR64Effect 0x11eaeb 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2244, 2242]
    (.letOp (n := 2249) (.out 0x11eaee (addR64M64Effect 0x11eaee 7 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[2190, 4]
    (.letOp (n := 2250) (.out 0x11eaee (addR64M64Effect 0x11eaee 7 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[2190, 4]
    (.letOp (n := 2251) (.exec 0x11eaee (LoadPre 0x11eaee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11eaee + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11eaee 7 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[2190, 4]
    (.letOp (n := 2252) (.out 0x11eaf6 (atFlags StatusFlags.CF (adcR64M64Effect 0x11eaf6 3 (.sib 4 none 0 (.d8 0x20)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[2188, 4, 2250]
    (.letOp (n := 2253) (.exec 0x11eaf6 (LoadPre 0x11eaf6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11eaf6 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11eaf6 3 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2188, 4, 2250]
    (.letOp (n := 2254) (.out 0x11eafb (addR64R64Effect 0x11eafb 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[2246, 2249]
    (.letOp (n := 2255) (.out 0x11eafb (addR64R64Effect 0x11eafb 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[2246, 2249]
    (.letOp (n := 2256) (.exec 0x11eafb (fun s => s.RIP = 0x11eafb) (addR64R64Effect 0x11eafb 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[2246, 2249]
    (b_l11d880_52)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_51 : List UInt8 :=
  [0x49, 0x89, 0xC2, 0x49, 0x89, 0xD7, 0x4C, 0x8B, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xC0, 0x4C, 0x8B, 0x6C, 0x24, 0x40, 0x49, 0xF7, 0xE5, 0x4C, 0x01, 0xD0, 0x49, 0x11, 0xD7, 0x48,
    0x01, 0xC8, 0x49, 0x11, 0xF7, 0x4C, 0x01, 0xF0, 0x49, 0x83, 0xD7, 0x00, 0x49, 0x0F, 0xA4, 0xC7,
    0x0C, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8, 0x48, 0xB9,
    0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x03, 0xBC, 0x24, 0xC8,
    0x00, 0x00, 0x00, 0x48, 0x13, 0x5C, 0x24, 0x20, 0x48, 0x01, 0xF8] ++ bytes_l11d880_52

theorem code_l11d880_51 : ∀ x ∈ codeRange 0x11eaa3 bytes_l11d880_51, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1eaa3 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_52

def b_l11d880_50 : Block Op Label signature Reg.count 2169 :=
  .letOp (n := 2169) (.exec 0x11ea51 (StorePre 0x11ea51 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11ea51 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ea51 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2164, 4]
    (.letOp (n := 2170) (.out 0x11ea56 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ea56 5 2)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[2079, 2162, 2165]
    (.letOp (n := 2171) (.exec 0x11ea56 (fun s => s.RIP = 0x11ea56) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ea56 5 2)) (Reg.operands [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2079, 2162, 2165]
    (.letOp (n := 2172) (.out 0x11ea59 (movR64R64Effect 0x11ea59 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2122]
    (.letOp (n := 2173) (.exec 0x11ea59 (fun s => s.RIP = 0x11ea59) (movR64R64Effect 0x11ea59 0 6) (Reg.operands [.gpr 6] [])) #v[2122]
    (.letOp (n := 2174) (.out 0x11ea5c (movR64M64Effect 0x11ea5c 9 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 2175) (.exec 0x11ea5c (LoadPre 0x11ea5c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11ea5c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ea5c 9 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2176) (.out 0x11ea64 (mulR64Effect 0x11ea64 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[2174, 2172]
    (.letOp (n := 2177) (.out 0x11ea64 (mulR64Effect 0x11ea64 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[2174, 2172]
    (.letOp (n := 2178) (.exec 0x11ea64 (fun s => s.RIP = 0x11ea64) (mulR64Effect 0x11ea64 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2174, 2172]
    (.letOp (n := 2179) (.exec 0x11ea67 (StorePre 0x11ea67 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11ea67 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ea67 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2177, 4]
    (.letOp (n := 2180) (.exec 0x11ea6c (StorePre 0x11ea6c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11ea6c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ea6c 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2176, 4]
    (.letOp (n := 2181) (.out 0x11ea74 (movR64M64Effect 0x11ea74 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2182) (.exec 0x11ea74 (LoadPre 0x11ea74 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11ea74 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ea74 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2183) (.out 0x11ea79 (movR64M64Effect 0x11ea79 12 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 2184) (.exec 0x11ea79 (LoadPre 0x11ea79 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11ea79 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ea79 12 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2185) (.out 0x11ea7e (mulR64Effect 0x11ea7e 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[2183, 2181]
    (.letOp (n := 2186) (.out 0x11ea7e (mulR64Effect 0x11ea7e 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[2183, 2181]
    (.letOp (n := 2187) (.exec 0x11ea7e (fun s => s.RIP = 0x11ea7e) (mulR64Effect 0x11ea7e 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[2183, 2181]
    (.letOp (n := 2188) (.out 0x11ea81 (movR64R64Effect 0x11ea81 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2186]
    (.letOp (n := 2189) (.exec 0x11ea81 (fun s => s.RIP = 0x11ea81) (movR64R64Effect 0x11ea81 3 2) (Reg.operands [.gpr 2] [])) #v[2186]
    (.letOp (n := 2190) (.out 0x11ea84 (movR64R64Effect 0x11ea84 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[2185]
    (.letOp (n := 2191) (.exec 0x11ea84 (fun s => s.RIP = 0x11ea84) (movR64R64Effect 0x11ea84 7 0) (Reg.operands [.gpr 0] [])) #v[2185]
    (.letOp (n := 2192) (.out 0x11ea87 (movR64R64Effect 0x11ea87 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2081]
    (.letOp (n := 2193) (.exec 0x11ea87 (fun s => s.RIP = 0x11ea87) (movR64R64Effect 0x11ea87 0 11) (Reg.operands [.gpr 11] [])) #v[2081]
    (.letOp (n := 2194) (.out 0x11ea8a (movR64M64Effect 0x11ea8a 11 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 2195) (.exec 0x11ea8a (LoadPre 0x11ea8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11ea8a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ea8a 11 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2196) (.out 0x11ea8f (mulR64Effect 0x11ea8f 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[2194, 2192]
    (.letOp (n := 2197) (.out 0x11ea8f (mulR64Effect 0x11ea8f 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[2194, 2192]
    (.letOp (n := 2198) (.exec 0x11ea8f (fun s => s.RIP = 0x11ea8f) (mulR64Effect 0x11ea8f 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[2194, 2192]
    (.letOp (n := 2199) (.out 0x11ea92 (movR64R64Effect 0x11ea92 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[2196]
    (.letOp (n := 2200) (.exec 0x11ea92 (fun s => s.RIP = 0x11ea92) (movR64R64Effect 0x11ea92 1 0) (Reg.operands [.gpr 0] [])) #v[2196]
    (.letOp (n := 2201) (.out 0x11ea95 (movR64R64Effect 0x11ea95 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2197]
    (.letOp (n := 2202) (.exec 0x11ea95 (fun s => s.RIP = 0x11ea95) (movR64R64Effect 0x11ea95 6 2) (Reg.operands [.gpr 2] [])) #v[2197]
    (.letOp (n := 2203) (.out 0x11ea98 (shldR64R64Effect 0x11ea98 5 5 10 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[2170, 2167]
    (.letOp (n := 2204) (.exec 0x11ea98 (fun s => s.RIP = 0x11ea98) (shldR64R64Effect 0x11ea98 5 5 10 12) (Reg.operands [.gpr 5, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2170, 2167]
    (.letOp (n := 2205) (.out 0x11ea9d (movR64R64Effect 0x11ea9d 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[2096]
    (.letOp (n := 2206) (.exec 0x11ea9d (fun s => s.RIP = 0x11ea9d) (movR64R64Effect 0x11ea9d 0 13) (Reg.operands [.gpr 13] [])) #v[2096]
    (.letOp (n := 2207) (.out 0x11eaa0 (mulR64Effect 0x11eaa0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[2113, 2205]
    (.letOp (n := 2208) (.out 0x11eaa0 (mulR64Effect 0x11eaa0 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[2113, 2205]
    (.letOp (n := 2209) (.exec 0x11eaa0 (fun s => s.RIP = 0x11eaa0) (mulR64Effect 0x11eaa0 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[2113, 2205]
    (b_l11d880_51)))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_50 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x11, 0xD5, 0x48, 0x89, 0xF0, 0x4C, 0x8B, 0x8C, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x54, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0xC8,
    0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x4C, 0x8B, 0x64, 0x24, 0x48, 0x49, 0xF7, 0xE4,
    0x48, 0x89, 0xD3, 0x48, 0x89, 0xC7, 0x4C, 0x89, 0xD8, 0x4C, 0x8B, 0x5C, 0x24, 0x50, 0x49, 0xF7,
    0xE3, 0x48, 0x89, 0xC1, 0x48, 0x89, 0xD6, 0x4C, 0x0F, 0xA4, 0xD5, 0x0C, 0x4C, 0x89, 0xE8, 0x49,
    0xF7, 0xE0] ++ bytes_l11d880_51

theorem code_l11d880_50 : ∀ x ∈ codeRange 0x11ea51 bytes_l11d880_50, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ea51 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_51

def b_l11d880_49 : Block Op Label signature Reg.count 2122 :=
  .letOp (n := 2122) (.out 0x11e9fd (movR64M64Effect 0x11e9fd 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 2123) (.exec 0x11e9fd (LoadPre 0x11e9fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11e9fd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e9fd 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2124) (.out 0x11ea02 (movR64R64Effect 0x11ea02 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2122]
    (.letOp (n := 2125) (.exec 0x11ea02 (fun s => s.RIP = 0x11ea02) (movR64R64Effect 0x11ea02 0 6) (Reg.operands [.gpr 6] [])) #v[2122]
    (.letOp (n := 2126) (.out 0x11ea05 (mulM64Effect 0x11ea05 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2124, 4]
    (.letOp (n := 2127) (.out 0x11ea05 (mulM64Effect 0x11ea05 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2124, 4]
    (.letOp (n := 2128) (.exec 0x11ea05 (LoadPre 0x11ea05 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11ea05 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11ea05 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2124, 4]
    (.letOp (n := 2129) (.out 0x11ea0a (addR64R64Effect 0x11ea0a 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[2126, 2118]
    (.letOp (n := 2130) (.out 0x11ea0a (addR64R64Effect 0x11ea0a 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[2126, 2118]
    (.letOp (n := 2131) (.exec 0x11ea0a (fun s => s.RIP = 0x11ea0a) (addR64R64Effect 0x11ea0a 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[2126, 2118]
    (.letOp (n := 2132) (.out 0x11ea0d (atFlags StatusFlags.CF (adcR64R64Effect 0x11ea0d 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2120, 2127, 2130]
    (.letOp (n := 2133) (.exec 0x11ea0d (fun s => s.RIP = 0x11ea0d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ea0d 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2120, 2127, 2130]
    (.letOp (n := 2134) (.out 0x11ea10 (addR64R64Effect 0x11ea10 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[2129, 2103]
    (.letOp (n := 2135) (.out 0x11ea10 (addR64R64Effect 0x11ea10 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[2129, 2103]
    (.letOp (n := 2136) (.exec 0x11ea10 (fun s => s.RIP = 0x11ea10) (addR64R64Effect 0x11ea10 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[2129, 2103]
    (.letOp (n := 2137) (.out 0x11ea13 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ea13 14 9)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2132, 2105, 2135]
    (.letOp (n := 2138) (.exec 0x11ea13 (fun s => s.RIP = 0x11ea13) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ea13 14 9)) (Reg.operands [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2132, 2105, 2135]
    (.letOp (n := 2139) (.out 0x11ea16 (addR64R64Effect 0x11ea16 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2134, 2088]
    (.letOp (n := 2140) (.out 0x11ea16 (addR64R64Effect 0x11ea16 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[2134, 2088]
    (.letOp (n := 2141) (.exec 0x11ea16 (fun s => s.RIP = 0x11ea16) (addR64R64Effect 0x11ea16 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2134, 2088]
    (.letOp (n := 2142) (.out 0x11ea19 (atFlags StatusFlags.CF (adcR64R64Effect 0x11ea19 14 15)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2137, 2090, 2140]
    (.letOp (n := 2143) (.exec 0x11ea19 (fun s => s.RIP = 0x11ea19) (atFlags StatusFlags.CF (adcR64R64Effect 0x11ea19 14 15)) (Reg.operands [.gpr 14, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2137, 2090, 2140]
    (.letOp (n := 2144) (.out 0x11ea1c (addR64R64Effect 0x11ea1c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[2139, 2107]
    (.letOp (n := 2145) (.out 0x11ea1c (addR64R64Effect 0x11ea1c 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[2139, 2107]
    (.letOp (n := 2146) (.exec 0x11ea1c (fun s => s.RIP = 0x11ea1c) (addR64R64Effect 0x11ea1c 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[2139, 2107]
    (.letOp (n := 2147) (.out 0x11ea1f (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ea1f 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2142, 2145]
    (.letOp (n := 2148) (.exec 0x11ea1f (fun s => s.RIP = 0x11ea1f) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11ea1f 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2142, 2145]
    (.letOp (n := 2149) (.out 0x11ea23 (shldR64R64Effect 0x11ea23 5 14 0 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[2147, 2144]
    (.letOp (n := 2150) (.exec 0x11ea23 (fun s => s.RIP = 0x11ea23) (shldR64R64Effect 0x11ea23 5 14 0 12) (Reg.operands [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2147, 2144]
    (.letOp (n := 2151) (.out 0x11ea28 (shlR64Effect 0x11ea28 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2144]
    (.letOp (n := 2152) (.exec 0x11ea28 (fun s => s.RIP = 0x11ea28) (shlR64Effect 0x11ea28 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2144]
    (.letOp (n := 2153) (.out 0x11ea2c (movR64Imm64Effect 0x11ea2c 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2154) (.exec 0x11ea2c (fun s => s.RIP = 0x11ea2c) (movR64Imm64Effect 0x11ea2c 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 2155) (.out 0x11ea36 (andR64R64Effect 0x11ea36 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2151, 2153]
    (.letOp (n := 2156) (.exec 0x11ea36 (fun s => s.RIP = 0x11ea36) (andR64R64Effect 0x11ea36 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2151, 2153]
    (.letOp (n := 2157) (.out 0x11ea39 (orR64R64Effect 0x11ea39 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[2155, 2109]
    (.letOp (n := 2158) (.exec 0x11ea39 (fun s => s.RIP = 0x11ea39) (orR64R64Effect 0x11ea39 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[2155, 2109]
    (.letOp (n := 2159) (.out 0x11ea3c (movR64Imm64Effect 0x11ea3c 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2160) (.exec 0x11ea3c (fun s => s.RIP = 0x11ea3c) (movR64Imm64Effect 0x11ea3c 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 2161) (.out 0x11ea46 (mulR64Effect 0x11ea46 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2159, 2157]
    (.letOp (n := 2162) (.out 0x11ea46 (mulR64Effect 0x11ea46 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2159, 2157]
    (.letOp (n := 2163) (.exec 0x11ea46 (fun s => s.RIP = 0x11ea46) (mulR64Effect 0x11ea46 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2159, 2157]
    (.letOp (n := 2164) (.out 0x11ea49 (addR64M64Effect 0x11ea49 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2161, 4]
    (.letOp (n := 2165) (.out 0x11ea49 (addR64M64Effect 0x11ea49 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[2161, 4]
    (.letOp (n := 2166) (.exec 0x11ea49 (LoadPre 0x11ea49 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11ea49 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11ea49 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2161, 4]
    (.letOp (n := 2167) (.out 0x11ea4e (movR64R64Effect 0x11ea4e 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2164]
    (.letOp (n := 2168) (.exec 0x11ea4e (fun s => s.RIP = 0x11ea4e) (movR64R64Effect 0x11ea4e 10 0) (Reg.operands [.gpr 0] [])) #v[2164]
    (b_l11d880_50)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_49 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x60, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0x64, 0x24, 0x40, 0x4C, 0x01, 0xD0,
    0x49, 0x11, 0xD6, 0x48, 0x01, 0xF8, 0x4D, 0x11, 0xCE, 0x48, 0x01, 0xC8, 0x4D, 0x11, 0xFE, 0x48,
    0x01, 0xD8, 0x49, 0x83, 0xD6, 0x00, 0x49, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48,
    0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C, 0x09, 0xE0, 0x48,
    0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x03, 0x44, 0x24,
    0x18, 0x49, 0x89, 0xC2] ++ bytes_l11d880_50

theorem code_l11d880_49 : ∀ x ∈ codeRange 0x11e9fd bytes_l11d880_49, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e9fd 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_50

def b_l11d880_48 : Block Op Label signature Reg.count 2079 :=
  .letOp (n := 2079) (.out 0x11e9ad (movR64R64Effect 0x11e9ad 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2076]
    (.letOp (n := 2080) (.exec 0x11e9ad (fun s => s.RIP = 0x11e9ad) (movR64R64Effect 0x11e9ad 5 2) (Reg.operands [.gpr 2] [])) #v[2076]
    (.letOp (n := 2081) (.out 0x11e9b0 (movR64M64Effect 0x11e9b0 11 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 2082) (.exec 0x11e9b0 (LoadPre 0x11e9b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11e9b0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e9b0 11 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2083) (.out 0x11e9b8 (movR64R64Effect 0x11e9b8 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2081]
    (.letOp (n := 2084) (.exec 0x11e9b8 (fun s => s.RIP = 0x11e9b8) (movR64R64Effect 0x11e9b8 0 11) (Reg.operands [.gpr 11] [])) #v[2081]
    (.letOp (n := 2085) (.out 0x11e9bb (mulM64Effect 0x11e9bb 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2083, 4]
    (.letOp (n := 2086) (.out 0x11e9bb (mulM64Effect 0x11e9bb 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2083, 4]
    (.letOp (n := 2087) (.exec 0x11e9bb (LoadPre 0x11e9bb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11e9bb + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e9bb 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2083, 4]
    (.letOp (n := 2088) (.out 0x11e9c0 (movR64R64Effect 0x11e9c0 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[2085]
    (.letOp (n := 2089) (.exec 0x11e9c0 (fun s => s.RIP = 0x11e9c0) (movR64R64Effect 0x11e9c0 1 0) (Reg.operands [.gpr 0] [])) #v[2085]
    (.letOp (n := 2090) (.out 0x11e9c3 (movR64R64Effect 0x11e9c3 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2086]
    (.letOp (n := 2091) (.exec 0x11e9c3 (fun s => s.RIP = 0x11e9c3) (movR64R64Effect 0x11e9c3 15 2) (Reg.operands [.gpr 2] [])) #v[2086]
    (.letOp (n := 2092) (.out 0x11e9c6 (movR64R64Effect 0x11e9c6 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[2068]
    (.letOp (n := 2093) (.exec 0x11e9c6 (fun s => s.RIP = 0x11e9c6) (movR64R64Effect 0x11e9c6 12 6) (Reg.operands [.gpr 6] [])) #v[2068]
    (.letOp (n := 2094) (.out 0x11e9c9 (shrR64Effect 0x11e9c9 4 12 48) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[2092]
    (.letOp (n := 2095) (.exec 0x11e9c9 (fun s => s.RIP = 0x11e9c9) (shrR64Effect 0x11e9c9 4 12 48) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2092]
    (.letOp (n := 2096) (.out 0x11e9cd (movR64M64Effect 0x11e9cd 13 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 2097) (.exec 0x11e9cd (LoadPre 0x11e9cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11e9cd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e9cd 13 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2098) (.out 0x11e9d2 (movR64R64Effect 0x11e9d2 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[2096]
    (.letOp (n := 2099) (.exec 0x11e9d2 (fun s => s.RIP = 0x11e9d2) (movR64R64Effect 0x11e9d2 0 13) (Reg.operands [.gpr 13] [])) #v[2096]
    (.letOp (n := 2100) (.out 0x11e9d5 (mulR64Effect 0x11e9d5 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[2002, 2098]
    (.letOp (n := 2101) (.out 0x11e9d5 (mulR64Effect 0x11e9d5 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[2002, 2098]
    (.letOp (n := 2102) (.exec 0x11e9d5 (fun s => s.RIP = 0x11e9d5) (mulR64Effect 0x11e9d5 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2002, 2098]
    (.letOp (n := 2103) (.out 0x11e9d8 (movR64R64Effect 0x11e9d8 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[2100]
    (.letOp (n := 2104) (.exec 0x11e9d8 (fun s => s.RIP = 0x11e9d8) (movR64R64Effect 0x11e9d8 7 0) (Reg.operands [.gpr 0] [])) #v[2100]
    (.letOp (n := 2105) (.out 0x11e9db (movR64R64Effect 0x11e9db 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2101]
    (.letOp (n := 2106) (.exec 0x11e9db (fun s => s.RIP = 0x11e9db) (movR64R64Effect 0x11e9db 9 2) (Reg.operands [.gpr 2] [])) #v[2101]
    (.letOp (n := 2107) (.out 0x11e9de (shldR64R64Effect 0x11e9de 5 3 6 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[2071, 2068]
    (.letOp (n := 2108) (.exec 0x11e9de (fun s => s.RIP = 0x11e9de) (shldR64R64Effect 0x11e9de 5 3 6 12) (Reg.operands [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2071, 2068]
    (.letOp (n := 2109) (.out 0x11e9e3 (andR32Imm8Effect 0x11e9e3 4 12 0xf) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[2094]
    (.letOp (n := 2110) (.exec 0x11e9e3 (fun s => s.RIP = 0x11e9e3) (andR32Imm8Effect 0x11e9e3 4 12 0xf) (Reg.operands [.gpr 12] [])) #v[2094]
    (.letOp (n := 2111) (.out 0x11e9e7 (movR64M64Effect 0x11e9e7 0 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2112) (.exec 0x11e9e7 (LoadPre 0x11e9e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11e9e7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e9e7 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2113) (.out 0x11e9ef (movR64M64Effect 0x11e9ef 8 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 2114) (.exec 0x11e9ef (LoadPre 0x11e9ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11e9ef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e9ef 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2115) (.out 0x11e9f4 (mulR64Effect 0x11e9f4 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[2113, 2111]
    (.letOp (n := 2116) (.out 0x11e9f4 (mulR64Effect 0x11e9f4 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[2113, 2111]
    (.letOp (n := 2117) (.exec 0x11e9f4 (fun s => s.RIP = 0x11e9f4) (mulR64Effect 0x11e9f4 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[2113, 2111]
    (.letOp (n := 2118) (.out 0x11e9f7 (movR64R64Effect 0x11e9f7 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2115]
    (.letOp (n := 2119) (.exec 0x11e9f7 (fun s => s.RIP = 0x11e9f7) (movR64R64Effect 0x11e9f7 10 0) (Reg.operands [.gpr 0] [])) #v[2115]
    (.letOp (n := 2120) (.out 0x11e9fa (movR64R64Effect 0x11e9fa 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2116]
    (.letOp (n := 2121) (.exec 0x11e9fa (fun s => s.RIP = 0x11e9fa) (movR64R64Effect 0x11e9fa 14 2) (Reg.operands [.gpr 2] [])) #v[2116]
    (b_l11d880_49)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_48 : List UInt8 :=
  [0x48, 0x89, 0xD5, 0x4C, 0x8B, 0x9C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xD8, 0x48, 0xF7,
    0x64, 0x24, 0x48, 0x48, 0x89, 0xC1, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xF4, 0x49, 0xC1, 0xEC, 0x30,
    0x4C, 0x8B, 0x6C, 0x24, 0x58, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xC7, 0x49, 0x89,
    0xD1, 0x48, 0x0F, 0xA4, 0xF3, 0x0C, 0x41, 0x83, 0xE4, 0x0F, 0x48, 0x8B, 0x84, 0x24, 0xB8, 0x00,
    0x00, 0x00, 0x4C, 0x8B, 0x44, 0x24, 0x30, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xC2, 0x49, 0x89, 0xD6] ++ bytes_l11d880_49

theorem code_l11d880_48 : ∀ x ∈ codeRange 0x11e9ad bytes_l11d880_48, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e9ad 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_49

def b_l11d880_47 : Block Op Label signature Reg.count 2033 :=
  .letOp (n := 2033) (.out 0x11e95f (movR64R64Effect 0x11e95f 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1983]
    (.letOp (n := 2034) (.exec 0x11e95f (fun s => s.RIP = 0x11e95f) (movR64R64Effect 0x11e95f 0 5) (Reg.operands [.gpr 5] [])) #v[1983]
    (.letOp (n := 2035) (.out 0x11e962 (movR64Imm64Effect 0x11e962 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2036) (.exec 0x11e962 (fun s => s.RIP = 0x11e962) (movR64Imm64Effect 0x11e962 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2037) (.out 0x11e96c (mulR64Effect 0x11e96c 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2035, 2033]
    (.letOp (n := 2038) (.out 0x11e96c (mulR64Effect 0x11e96c 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2035, 2033]
    (.letOp (n := 2039) (.exec 0x11e96c (fun s => s.RIP = 0x11e96c) (mulR64Effect 0x11e96c 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2035, 2033]
    (.letOp (n := 2040) (.out 0x11e96f (addR64R64Effect 0x11e96f 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[2031, 2018]
    (.letOp (n := 2041) (.out 0x11e96f (addR64R64Effect 0x11e96f 7 12) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 12] []) (.flag .CF)) #v[2031, 2018]
    (.letOp (n := 2042) (.exec 0x11e96f (fun s => s.RIP = 0x11e96f) (addR64R64Effect 0x11e96f 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[2031, 2018]
    (.letOp (n := 2043) (.out 0x11e972 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e972 3 13)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[2029, 2020, 2041]
    (.letOp (n := 2044) (.exec 0x11e972 (fun s => s.RIP = 0x11e972) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e972 3 13)) (Reg.operands [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2029, 2020, 2041]
    (.letOp (n := 2045) (.out 0x11e975 (addR64R64Effect 0x11e975 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[2040, 2007]
    (.letOp (n := 2046) (.out 0x11e975 (addR64R64Effect 0x11e975 7 15) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 15] []) (.flag .CF)) #v[2040, 2007]
    (.letOp (n := 2047) (.exec 0x11e975 (fun s => s.RIP = 0x11e975) (addR64R64Effect 0x11e975 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[2040, 2007]
    (.letOp (n := 2048) (.out 0x11e978 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e978 3 6)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[2043, 2009, 2046]
    (.letOp (n := 2049) (.exec 0x11e978 (fun s => s.RIP = 0x11e978) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e978 3 6)) (Reg.operands [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2043, 2009, 2046]
    (.letOp (n := 2050) (.out 0x11e97b (addR64R64Effect 0x11e97b 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[2045, 1998]
    (.letOp (n := 2051) (.out 0x11e97b (addR64R64Effect 0x11e97b 7 1) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 1] []) (.flag .CF)) #v[2045, 1998]
    (.letOp (n := 2052) (.exec 0x11e97b (fun s => s.RIP = 0x11e97b) (addR64R64Effect 0x11e97b 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[2045, 1998]
    (.letOp (n := 2053) (.out 0x11e97e (atFlags StatusFlags.CF (adcR64M64Effect 0x11e97e 3 (.sib 4 none 0 (.d8 0x20)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[2048, 4, 2051]
    (.letOp (n := 2054) (.exec 0x11e97e (LoadPre 0x11e97e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e97e + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e97e 3 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2048, 4, 2051]
    (.letOp (n := 2055) (.out 0x11e983 (addR64M64Effect 0x11e983 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[2050, 4]
    (.letOp (n := 2056) (.out 0x11e983 (addR64M64Effect 0x11e983 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[2050, 4]
    (.letOp (n := 2057) (.exec 0x11e983 (LoadPre 0x11e983 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11e983 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11e983 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[2050, 4]
    (.letOp (n := 2058) (.out 0x11e988 (atFlags StatusFlags.CF (adcR64M64Effect 0x11e988 3 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[2053, 4, 2056]
    (.letOp (n := 2059) (.exec 0x11e988 (LoadPre 0x11e988 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11e988 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e988 3 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2053, 4, 2056]
    (.letOp (n := 2060) (.out 0x11e98d (addR64R64Effect 0x11e98d 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[2037, 2055]
    (.letOp (n := 2061) (.out 0x11e98d (addR64R64Effect 0x11e98d 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[2037, 2055]
    (.letOp (n := 2062) (.exec 0x11e98d (fun s => s.RIP = 0x11e98d) (addR64R64Effect 0x11e98d 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[2037, 2055]
    (.letOp (n := 2063) (.out 0x11e990 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e990 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[2058, 2038, 2061]
    (.letOp (n := 2064) (.exec 0x11e990 (fun s => s.RIP = 0x11e990) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e990 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2058, 2038, 2061]
    (.letOp (n := 2065) (.out 0x11e993 (addR64R64Effect 0x11e993 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[2060, 2011]
    (.letOp (n := 2066) (.out 0x11e993 (addR64R64Effect 0x11e993 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[2060, 2011]
    (.letOp (n := 2067) (.exec 0x11e993 (fun s => s.RIP = 0x11e993) (addR64R64Effect 0x11e993 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[2060, 2011]
    (.letOp (n := 2068) (.out 0x11e996 (movR64R64Effect 0x11e996 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2065]
    (.letOp (n := 2069) (.exec 0x11e996 (fun s => s.RIP = 0x11e996) (movR64R64Effect 0x11e996 6 0) (Reg.operands [.gpr 0] [])) #v[2065]
    (.letOp (n := 2070) (.exec 0x11e999 (StorePre 0x11e999 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11e999 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e999 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2065, 4]
    (.letOp (n := 2071) (.out 0x11e99e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e99e 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[2063, 2066]
    (.letOp (n := 2072) (.exec 0x11e99e (fun s => s.RIP = 0x11e99e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e99e 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2063, 2066]
    (.letOp (n := 2073) (.out 0x11e9a2 (movR64R64Effect 0x11e9a2 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2022]
    (.letOp (n := 2074) (.exec 0x11e9a2 (fun s => s.RIP = 0x11e9a2) (movR64R64Effect 0x11e9a2 0 8) (Reg.operands [.gpr 8] [])) #v[2022]
    (.letOp (n := 2075) (.out 0x11e9a5 (mulR64Effect 0x11e9a5 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[1884, 2073]
    (.letOp (n := 2076) (.out 0x11e9a5 (mulR64Effect 0x11e9a5 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[1884, 2073]
    (.letOp (n := 2077) (.exec 0x11e9a5 (fun s => s.RIP = 0x11e9a5) (mulR64Effect 0x11e9a5 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1884, 2073]
    (.letOp (n := 2078) (.exec 0x11e9a8 (StorePre 0x11e9a8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11e9a8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e9a8 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2075, 4]
    (b_l11d880_48))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_47 : List UInt8 :=
  [0x48, 0x89, 0xE8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x4C, 0x01, 0xE7, 0x4C, 0x11, 0xEB, 0x4C, 0x01, 0xFF, 0x48, 0x11, 0xF3, 0x48, 0x01, 0xCF, 0x48,
    0x13, 0x5C, 0x24, 0x20, 0x48, 0x03, 0x7C, 0x24, 0x18, 0x48, 0x13, 0x5C, 0x24, 0x10, 0x48, 0x01,
    0xF8, 0x48, 0x11, 0xD3, 0x4C, 0x01, 0xD8, 0x48, 0x89, 0xC6, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48,
    0x83, 0xD3, 0x00, 0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x44, 0x24, 0x18] ++ bytes_l11d880_48

theorem code_l11d880_47 : ∀ x ∈ codeRange 0x11e95f bytes_l11d880_47, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e95f 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_48

def b_l11d880_46 : Block Op Label signature Reg.count 1991 :=
  .letOp (n := 1991) (.exec 0x11e915 (StorePre 0x11e915 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11e915 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e915 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1987, 4]
    (.letOp (n := 1992) (.out 0x11e91a (movR64M64Effect 0x11e91a 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1993) (.exec 0x11e91a (LoadPre 0x11e91a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11e91a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e91a 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1994) (.out 0x11e91f (mulR64Effect 0x11e91f 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1895, 1992]
    (.letOp (n := 1995) (.out 0x11e91f (mulR64Effect 0x11e91f 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1895, 1992]
    (.letOp (n := 1996) (.exec 0x11e91f (fun s => s.RIP = 0x11e91f) (mulR64Effect 0x11e91f 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1895, 1992]
    (.letOp (n := 1997) (.exec 0x11e922 (StorePre 0x11e922 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e922 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e922 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1995, 4]
    (.letOp (n := 1998) (.out 0x11e927 (movR64R64Effect 0x11e927 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1994]
    (.letOp (n := 1999) (.exec 0x11e927 (fun s => s.RIP = 0x11e927) (movR64R64Effect 0x11e927 1 0) (Reg.operands [.gpr 0] [])) #v[1994]
    (.letOp (n := 2000) (.out 0x11e92a (movR64R64Effect 0x11e92a 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[1891]
    (.letOp (n := 2001) (.exec 0x11e92a (fun s => s.RIP = 0x11e92a) (movR64R64Effect 0x11e92a 0 12) (Reg.operands [.gpr 12] [])) #v[1891]
    (.letOp (n := 2002) (.out 0x11e92d (movR64M64Effect 0x11e92d 10 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 2003) (.exec 0x11e92d (LoadPre 0x11e92d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11e92d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e92d 10 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2004) (.out 0x11e932 (mulR64Effect 0x11e932 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[2002, 2000]
    (.letOp (n := 2005) (.out 0x11e932 (mulR64Effect 0x11e932 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[2002, 2000]
    (.letOp (n := 2006) (.exec 0x11e932 (fun s => s.RIP = 0x11e932) (mulR64Effect 0x11e932 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2002, 2000]
    (.letOp (n := 2007) (.out 0x11e935 (movR64R64Effect 0x11e935 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[2004]
    (.letOp (n := 2008) (.exec 0x11e935 (fun s => s.RIP = 0x11e935) (movR64R64Effect 0x11e935 15 0) (Reg.operands [.gpr 0] [])) #v[2004]
    (.letOp (n := 2009) (.out 0x11e938 (movR64R64Effect 0x11e938 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2005]
    (.letOp (n := 2010) (.exec 0x11e938 (fun s => s.RIP = 0x11e938) (movR64R64Effect 0x11e938 6 2) (Reg.operands [.gpr 2] [])) #v[2005]
    (.letOp (n := 2011) (.out 0x11e93b (shldR64R64Effect 0x11e93b 5 11 3 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1981, 1978]
    (.letOp (n := 2012) (.exec 0x11e93b (fun s => s.RIP = 0x11e93b) (shldR64R64Effect 0x11e93b 5 11 3 12) (Reg.operands [.gpr 11, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1981, 1978]
    (.letOp (n := 2013) (.out 0x11e940 (movR64R64Effect 0x11e940 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1902]
    (.letOp (n := 2014) (.exec 0x11e940 (fun s => s.RIP = 0x11e940) (movR64R64Effect 0x11e940 0 13) (Reg.operands [.gpr 13] [])) #v[1902]
    (.letOp (n := 2015) (.out 0x11e943 (mulM64Effect 0x11e943 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2013, 4]
    (.letOp (n := 2016) (.out 0x11e943 (mulM64Effect 0x11e943 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2013, 4]
    (.letOp (n := 2017) (.exec 0x11e943 (LoadPre 0x11e943 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11e943 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e943 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2013, 4]
    (.letOp (n := 2018) (.out 0x11e948 (movR64R64Effect 0x11e948 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[2015]
    (.letOp (n := 2019) (.exec 0x11e948 (fun s => s.RIP = 0x11e948) (movR64R64Effect 0x11e948 12 0) (Reg.operands [.gpr 0] [])) #v[2015]
    (.letOp (n := 2020) (.out 0x11e94b (movR64R64Effect 0x11e94b 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2016]
    (.letOp (n := 2021) (.exec 0x11e94b (fun s => s.RIP = 0x11e94b) (movR64R64Effect 0x11e94b 13 2) (Reg.operands [.gpr 2] [])) #v[2016]
    (.letOp (n := 2022) (.out 0x11e94e (movR64M64Effect 0x11e94e 8 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 2023) (.exec 0x11e94e (LoadPre 0x11e94e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11e94e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e94e 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2024) (.out 0x11e953 (movR64R64Effect 0x11e953 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2022]
    (.letOp (n := 2025) (.exec 0x11e953 (fun s => s.RIP = 0x11e953) (movR64R64Effect 0x11e953 0 8) (Reg.operands [.gpr 8] [])) #v[2022]
    (.letOp (n := 2026) (.out 0x11e956 (mulR64Effect 0x11e956 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[1930, 2024]
    (.letOp (n := 2027) (.out 0x11e956 (mulR64Effect 0x11e956 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[1930, 2024]
    (.letOp (n := 2028) (.exec 0x11e956 (fun s => s.RIP = 0x11e956) (mulR64Effect 0x11e956 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1930, 2024]
    (.letOp (n := 2029) (.out 0x11e959 (movR64R64Effect 0x11e959 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2027]
    (.letOp (n := 2030) (.exec 0x11e959 (fun s => s.RIP = 0x11e959) (movR64R64Effect 0x11e959 3 2) (Reg.operands [.gpr 2] [])) #v[2027]
    (.letOp (n := 2031) (.out 0x11e95c (movR64R64Effect 0x11e95c 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[2026]
    (.letOp (n := 2032) (.exec 0x11e95c (fun s => s.RIP = 0x11e95c) (movR64R64Effect 0x11e95c 7 0) (Reg.operands [.gpr 0] [])) #v[2026]
    (b_l11d880_47))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_46 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0x54,
    0x24, 0x20, 0x48, 0x89, 0xC1, 0x4C, 0x89, 0xE0, 0x4C, 0x8B, 0x54, 0x24, 0x50, 0x49, 0xF7, 0xE2,
    0x49, 0x89, 0xC7, 0x48, 0x89, 0xD6, 0x49, 0x0F, 0xA4, 0xDB, 0x0C, 0x4C, 0x89, 0xE8, 0x48, 0xF7,
    0x64, 0x24, 0x30, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD5, 0x4C, 0x8B, 0x44, 0x24, 0x28, 0x4C, 0x89,
    0xC0, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0xD3, 0x48, 0x89, 0xC7] ++ bytes_l11d880_47

theorem code_l11d880_46 : ∀ x ∈ codeRange 0x11e915 bytes_l11d880_46, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e915 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_47

def b_l11d880_45 : Block Op Label signature Reg.count 1948 :=
  .letOp (n := 1948) (.out 0x11e8a8 (movR64Imm64Effect 0x11e8a8 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1949) (.exec 0x11e8a8 (fun s => s.RIP = 0x11e8a8) (movR64Imm64Effect 0x11e8a8 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1950) (.out 0x11e8b2 (mulR64Effect 0x11e8b2 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1948, 1946]
    (.letOp (n := 1951) (.out 0x11e8b2 (mulR64Effect 0x11e8b2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1948, 1946]
    (.letOp (n := 1952) (.exec 0x11e8b2 (fun s => s.RIP = 0x11e8b2) (mulR64Effect 0x11e8b2 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1948, 1946]
    (.letOp (n := 1953) (.out 0x11e8b5 (movR64R64Effect 0x11e8b5 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1950]
    (.letOp (n := 1954) (.exec 0x11e8b5 (fun s => s.RIP = 0x11e8b5) (movR64R64Effect 0x11e8b5 1 0) (Reg.operands [.gpr 0] [])) #v[1950]
    (.letOp (n := 1955) (.out 0x11e8b8 (movR64Imm64Effect 0x11e8b8 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1956) (.exec 0x11e8b8 (fun s => s.RIP = 0x11e8b8) (movR64Imm64Effect 0x11e8b8 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1957) (.out 0x11e8c2 (andR64R64Effect 0x11e8c2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[1877, 1955]
    (.letOp (n := 1958) (.exec 0x11e8c2 (fun s => s.RIP = 0x11e8c2) (andR64R64Effect 0x11e8c2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[1877, 1955]
    (.letOp (n := 1959) (.exec 0x11e8c5 (StorePre 0x11e8c5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x11e8c5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e8c5 6 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1957, 4]
    (.letOp (n := 1960) (.out 0x11e8cd (addR64M64Effect 0x11e8cd 10 (.sib 4 none 0 (.d32 0x1a8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[1916, 4]
    (.letOp (n := 1961) (.out 0x11e8cd (addR64M64Effect 0x11e8cd 10 (.sib 4 none 0 (.d32 0x1a8))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[1916, 4]
    (.letOp (n := 1962) (.exec 0x11e8cd (LoadPre 0x11e8cd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x11e8cd + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11e8cd 10 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[1916, 4]
    (.letOp (n := 1963) (.out 0x11e8d5 (atFlags StatusFlags.CF (adcR64M64Effect 0x11e8d5 11 (.sib 4 none 0 (.d32 0xc8)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[1918, 4, 1961]
    (.letOp (n := 1964) (.exec 0x11e8d5 (LoadPre 0x11e8d5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11e8d5 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e8d5 11 (.sib 4 none 0 (.d32 0xc8)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1918, 4, 1961]
    (.letOp (n := 1965) (.out 0x11e8dd (addR64M64Effect 0x11e8dd 10 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[1960, 4]
    (.letOp (n := 1966) (.out 0x11e8dd (addR64M64Effect 0x11e8dd 10 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[1960, 4]
    (.letOp (n := 1967) (.exec 0x11e8dd (LoadPre 0x11e8dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e8dd + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11e8dd 10 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[1960, 4]
    (.letOp (n := 1968) (.out 0x11e8e2 (atFlags StatusFlags.CF (adcR64M64Effect 0x11e8e2 11 (.sib 4 none 0 (.d32 0xf8)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[1963, 4, 1966]
    (.letOp (n := 1969) (.exec 0x11e8e2 (LoadPre 0x11e8e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11e8e2 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e8e2 11 (.sib 4 none 0 (.d32 0xf8)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1963, 4, 1966]
    (.letOp (n := 1970) (.out 0x11e8ea (addR64M64Effect 0x11e8ea 10 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[1965, 4]
    (.letOp (n := 1971) (.out 0x11e8ea (addR64M64Effect 0x11e8ea 10 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[1965, 4]
    (.letOp (n := 1972) (.exec 0x11e8ea (LoadPre 0x11e8ea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11e8ea + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11e8ea 10 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[1965, 4]
    (.letOp (n := 1973) (.out 0x11e8ef (atFlags StatusFlags.CF (adcR64M64Effect 0x11e8ef 11 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[1968, 4, 1971]
    (.letOp (n := 1974) (.exec 0x11e8ef (LoadPre 0x11e8ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11e8ef + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e8ef 11 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1968, 4, 1971]
    (.letOp (n := 1975) (.out 0x11e8f4 (addR64R64Effect 0x11e8f4 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[1953, 1970]
    (.letOp (n := 1976) (.out 0x11e8f4 (addR64R64Effect 0x11e8f4 1 10) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 10] []) (.flag .CF)) #v[1953, 1970]
    (.letOp (n := 1977) (.exec 0x11e8f4 (fun s => s.RIP = 0x11e8f4) (addR64R64Effect 0x11e8f4 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[1953, 1970]
    (.letOp (n := 1978) (.out 0x11e8f7 (movR64R64Effect 0x11e8f7 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[1975]
    (.letOp (n := 1979) (.exec 0x11e8f7 (fun s => s.RIP = 0x11e8f7) (movR64R64Effect 0x11e8f7 3 1) (Reg.operands [.gpr 1] [])) #v[1975]
    (.letOp (n := 1980) (.exec 0x11e8fa (StorePre 0x11e8fa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11e8fa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e8fa 1 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1975, 4]
    (.letOp (n := 1981) (.out 0x11e902 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e902 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1973, 1951, 1976]
    (.letOp (n := 1982) (.exec 0x11e902 (fun s => s.RIP = 0x11e902) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e902 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1973, 1951, 1976]
    (.letOp (n := 1983) (.out 0x11e905 (shldR64R64Effect 0x11e905 5 5 15 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[1937, 1935]
    (.letOp (n := 1984) (.exec 0x11e905 (fun s => s.RIP = 0x11e905) (shldR64R64Effect 0x11e905 5 5 15 12) (Reg.operands [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1937, 1935]
    (.letOp (n := 1985) (.out 0x11e90a (movR64R64Effect 0x11e90a 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1926]
    (.letOp (n := 1986) (.exec 0x11e90a (fun s => s.RIP = 0x11e90a) (movR64R64Effect 0x11e90a 0 7) (Reg.operands [.gpr 7] [])) #v[1926]
    (.letOp (n := 1987) (.out 0x11e90d (mulR64Effect 0x11e90d 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[1884, 1985]
    (.letOp (n := 1988) (.out 0x11e90d (mulR64Effect 0x11e90d 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[1884, 1985]
    (.letOp (n := 1989) (.exec 0x11e90d (fun s => s.RIP = 0x11e90d) (mulR64Effect 0x11e90d 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1884, 1985]
    (.letOp (n := 1990) (.exec 0x11e910 (StorePre 0x11e910 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11e910 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e910 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1988, 4]
    (b_l11d880_46)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_45 : List UInt8 :=
  [0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xC1,
    0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC6, 0x48, 0x89, 0xB4,
    0x24, 0xE0, 0x00, 0x00, 0x00, 0x4C, 0x03, 0x94, 0x24, 0xA8, 0x01, 0x00, 0x00, 0x4C, 0x13, 0x9C,
    0x24, 0xC8, 0x00, 0x00, 0x00, 0x4C, 0x03, 0x54, 0x24, 0x20, 0x4C, 0x13, 0x9C, 0x24, 0xF8, 0x00,
    0x00, 0x00, 0x4C, 0x03, 0x54, 0x24, 0x18, 0x4C, 0x13, 0x5C, 0x24, 0x10, 0x4C, 0x01, 0xD1, 0x48,
    0x89, 0xCB, 0x48, 0x89, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x49, 0x11, 0xD3, 0x4C, 0x0F, 0xA4,
    0xFD, 0x0C, 0x48, 0x89, 0xF8, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x54, 0x24, 0x10] ++ bytes_l11d880_46

theorem code_l11d880_45 : ∀ x ∈ codeRange 0x11e8a8 bytes_l11d880_45, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e8a8 109 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_46

def b_l11d880_44 : Block Op Label signature Reg.count 1909 :=
  .letOp (n := 1909) (.exec 0x11e843 (StorePre 0x11e843 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11e843 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e843 2 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1907, 4]
    (.letOp (n := 1910) (.exec 0x11e84b (StorePre 0x11e84b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x11e84b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e84b 0 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1906, 4]
    (.letOp (n := 1911) (.out 0x11e853 (movR64M64Effect 0x11e853 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1912) (.exec 0x11e853 (LoadPre 0x11e853 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11e853 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e853 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1913) (.out 0x11e858 (mulM64Effect 0x11e858 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1911, 4]
    (.letOp (n := 1914) (.out 0x11e858 (mulM64Effect 0x11e858 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1911, 4]
    (.letOp (n := 1915) (.exec 0x11e858 (LoadPre 0x11e858 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11e858 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e858 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1911, 4]
    (.letOp (n := 1916) (.out 0x11e85d (movR64R64Effect 0x11e85d 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[1913]
    (.letOp (n := 1917) (.exec 0x11e85d (fun s => s.RIP = 0x11e85d) (movR64R64Effect 0x11e85d 10 0) (Reg.operands [.gpr 0] [])) #v[1913]
    (.letOp (n := 1918) (.out 0x11e860 (movR64R64Effect 0x11e860 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[1914]
    (.letOp (n := 1919) (.exec 0x11e860 (fun s => s.RIP = 0x11e860) (movR64R64Effect 0x11e860 11 2) (Reg.operands [.gpr 2] [])) #v[1914]
    (.letOp (n := 1920) (.out 0x11e863 (movR64Imm64Effect 0x11e863 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1921) (.exec 0x11e863 (fun s => s.RIP = 0x11e863) (movR64Imm64Effect 0x11e863 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1922) (.out 0x11e86d (movR64M64Effect 0x11e86d 1 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 1923) (.exec 0x11e86d (LoadPre 0x11e86d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11e86d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e86d 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1924) (.out 0x11e872 (andR64R64Effect 0x11e872 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1922, 1920]
    (.letOp (n := 1925) (.exec 0x11e872 (fun s => s.RIP = 0x11e872) (andR64R64Effect 0x11e872 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1922, 1920]
    (.letOp (n := 1926) (.out 0x11e875 (movR64M64Effect 0x11e875 7 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 1927) (.exec 0x11e875 (LoadPre 0x11e875 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11e875 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e875 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1928) (.out 0x11e87d (movR64R64Effect 0x11e87d 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1926]
    (.letOp (n := 1929) (.exec 0x11e87d (fun s => s.RIP = 0x11e87d) (movR64R64Effect 0x11e87d 0 7) (Reg.operands [.gpr 7] [])) #v[1926]
    (.letOp (n := 1930) (.out 0x11e880 (movR64M64Effect 0x11e880 14 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 1931) (.exec 0x11e880 (LoadPre 0x11e880 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11e880 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e880 14 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1932) (.out 0x11e885 (mulR64Effect 0x11e885 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[1930, 1928]
    (.letOp (n := 1933) (.out 0x11e885 (mulR64Effect 0x11e885 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[1930, 1928]
    (.letOp (n := 1934) (.exec 0x11e885 (fun s => s.RIP = 0x11e885) (mulR64Effect 0x11e885 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1930, 1928]
    (.letOp (n := 1935) (.out 0x11e888 (movR64R64Effect 0x11e888 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1932]
    (.letOp (n := 1936) (.exec 0x11e888 (fun s => s.RIP = 0x11e888) (movR64R64Effect 0x11e888 15 0) (Reg.operands [.gpr 0] [])) #v[1932]
    (.letOp (n := 1937) (.out 0x11e88b (movR64R64Effect 0x11e88b 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[1933]
    (.letOp (n := 1938) (.exec 0x11e88b (fun s => s.RIP = 0x11e88b) (movR64R64Effect 0x11e88b 5 2) (Reg.operands [.gpr 2] [])) #v[1933]
    (.letOp (n := 1939) (.out 0x11e88e (shldR64R64Effect 0x11e88e 5 3 6 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1880, 1877]
    (.letOp (n := 1940) (.exec 0x11e88e (fun s => s.RIP = 0x11e88e) (shldR64R64Effect 0x11e88e 5 3 6 12) (Reg.operands [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1880, 1877]
    (.letOp (n := 1941) (.out 0x11e893 (addR64R64Effect 0x11e893 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[1924, 1939]
    (.letOp (n := 1942) (.exec 0x11e893 (fun s => s.RIP = 0x11e893) (addR64R64Effect 0x11e893 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1924, 1939]
    (.letOp (n := 1943) (.exec 0x11e896 (StorePre 0x11e896 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11e896 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e896 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1941, 4]
    (.letOp (n := 1944) (.out 0x11e89b (movR64Imm64Effect 0x11e89b 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1945) (.exec 0x11e89b (fun s => s.RIP = 0x11e89b) (movR64Imm64Effect 0x11e89b 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1946) (.out 0x11e8a5 (andR64R64Effect 0x11e8a5 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1932, 1944]
    (.letOp (n := 1947) (.exec 0x11e8a5 (fun s => s.RIP = 0x11e8a5) (andR64R64Effect 0x11e8a5 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1932, 1944]
    (b_l11d880_45)))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_44 : List UInt8 :=
  [0x48, 0x89, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0xF7, 0x64, 0x24, 0x30, 0x49, 0x89, 0xC2, 0x49, 0x89, 0xD3,
    0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x78, 0x48,
    0x21, 0xC1, 0x48, 0x8B, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x4C, 0x8B, 0x74,
    0x24, 0x40, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xC7, 0x48, 0x89, 0xD5, 0x48, 0x0F, 0xA4, 0xF3, 0x0C,
    0x48, 0x01, 0xD9, 0x48, 0x89, 0x4C, 0x24, 0x78, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x0F, 0x00, 0x48, 0x21, 0xD0] ++ bytes_l11d880_45

theorem code_l11d880_44 : ∀ x ∈ codeRange 0x11e843 bytes_l11d880_44, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e843 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_45

def b_l11d880_43 : Block Op Label signature Reg.count 1868 :=
  .letOp (n := 1868) (.out 0x11e7e3 (movR64M64Effect 0x11e7e3 6 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 1869) (.exec 0x11e7e3 (LoadPre 0x11e7e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x11e7e3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e7e3 6 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1870) (.out 0x11e7eb (andR64R64Effect 0x11e7eb 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[1868, 1866]
    (.letOp (n := 1871) (.exec 0x11e7eb (fun s => s.RIP = 0x11e7eb) (andR64R64Effect 0x11e7eb 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[1868, 1866]
    (.letOp (n := 1872) (.out 0x11e7ee (addR64R64Effect 0x11e7ee 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[1870, 1861]
    (.letOp (n := 1873) (.out 0x11e7ee (addR64R64Effect 0x11e7ee 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[1870, 1861]
    (.letOp (n := 1874) (.exec 0x11e7ee (fun s => s.RIP = 0x11e7ee) (addR64R64Effect 0x11e7ee 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[1870, 1861]
    (.letOp (n := 1875) (.out 0x11e7f1 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e7f1 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1864, 1873]
    (.letOp (n := 1876) (.exec 0x11e7f1 (fun s => s.RIP = 0x11e7f1) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e7f1 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1864, 1873]
    (.letOp (n := 1877) (.out 0x11e7f5 (addR64R64Effect 0x11e7f5 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1872, 1850]
    (.letOp (n := 1878) (.out 0x11e7f5 (addR64R64Effect 0x11e7f5 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[1872, 1850]
    (.letOp (n := 1879) (.exec 0x11e7f5 (fun s => s.RIP = 0x11e7f5) (addR64R64Effect 0x11e7f5 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1872, 1850]
    (.letOp (n := 1880) (.out 0x11e7f8 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e7f8 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1875, 1878]
    (.letOp (n := 1881) (.exec 0x11e7f8 (fun s => s.RIP = 0x11e7f8) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e7f8 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1875, 1878]
    (.letOp (n := 1882) (.out 0x11e7fc (movR64M64Effect 0x11e7fc 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1883) (.exec 0x11e7fc (LoadPre 0x11e7fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11e7fc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e7fc 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1884) (.out 0x11e801 (movR64M64Effect 0x11e801 9 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 1885) (.exec 0x11e801 (LoadPre 0x11e801 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11e801 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e801 9 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1886) (.out 0x11e809 (mulR64Effect 0x11e809 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[1884, 1882]
    (.letOp (n := 1887) (.out 0x11e809 (mulR64Effect 0x11e809 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[1884, 1882]
    (.letOp (n := 1888) (.exec 0x11e809 (fun s => s.RIP = 0x11e809) (mulR64Effect 0x11e809 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1884, 1882]
    (.letOp (n := 1889) (.exec 0x11e80c (StorePre 0x11e80c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11e80c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e80c 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1887, 4]
    (.letOp (n := 1890) (.exec 0x11e811 (StorePre 0x11e811 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11e811 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e811 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1886, 4]
    (.letOp (n := 1891) (.out 0x11e816 (movR64M64Effect 0x11e816 12 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 1892) (.exec 0x11e816 (LoadPre 0x11e816 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11e816 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e816 12 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1893) (.out 0x11e81e (movR64R64Effect 0x11e81e 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[1891]
    (.letOp (n := 1894) (.exec 0x11e81e (fun s => s.RIP = 0x11e81e) (movR64R64Effect 0x11e81e 0 12) (Reg.operands [.gpr 12] [])) #v[1891]
    (.letOp (n := 1895) (.out 0x11e821 (movR64M64Effect 0x11e821 8 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 1896) (.exec 0x11e821 (LoadPre 0x11e821 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11e821 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e821 8 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1897) (.out 0x11e826 (mulR64Effect 0x11e826 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1895, 1893]
    (.letOp (n := 1898) (.out 0x11e826 (mulR64Effect 0x11e826 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1895, 1893]
    (.letOp (n := 1899) (.exec 0x11e826 (fun s => s.RIP = 0x11e826) (mulR64Effect 0x11e826 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1895, 1893]
    (.letOp (n := 1900) (.exec 0x11e829 (StorePre 0x11e829 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e829 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e829 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1897, 4]
    (.letOp (n := 1901) (.exec 0x11e82e (StorePre 0x11e82e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11e82e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e82e 2 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1898, 4]
    (.letOp (n := 1902) (.out 0x11e836 (movR64M64Effect 0x11e836 13 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 1903) (.exec 0x11e836 (LoadPre 0x11e836 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11e836 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e836 13 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1904) (.out 0x11e83b (movR64R64Effect 0x11e83b 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1902]
    (.letOp (n := 1905) (.exec 0x11e83b (fun s => s.RIP = 0x11e83b) (movR64R64Effect 0x11e83b 0 13) (Reg.operands [.gpr 13] [])) #v[1902]
    (.letOp (n := 1906) (.out 0x11e83e (mulM64Effect 0x11e83e 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1904, 4]
    (.letOp (n := 1907) (.out 0x11e83e (mulM64Effect 0x11e83e 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1904, 4]
    (.letOp (n := 1908) (.exec 0x11e83e (LoadPre 0x11e83e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11e83e + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e83e 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1904, 4]
    (b_l11d880_44)))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_43 : List UInt8 :=
  [0x48, 0x8B, 0xB4, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x21, 0xD6, 0x48, 0x01, 0xC6, 0x48, 0x83,
    0xD3, 0x00, 0x48, 0x01, 0xCE, 0x48, 0x83, 0xD3, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x4C, 0x8B,
    0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x89,
    0x44, 0x24, 0x18, 0x4C, 0x8B, 0xA4, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x4C, 0x8B,
    0x44, 0x24, 0x48, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0x94, 0x24, 0xF8,
    0x00, 0x00, 0x00, 0x4C, 0x8B, 0x6C, 0x24, 0x60, 0x4C, 0x89, 0xE8, 0x48, 0xF7, 0x64, 0x24, 0x50] ++ bytes_l11d880_44

theorem code_l11d880_43 : ∀ x ∈ codeRange 0x11e7e3 bytes_l11d880_43, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e7e3 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_44

def b_l11d880_42 : Block Op Label signature Reg.count 1823 :=
  .letOp (n := 1823) (.out 0x11e77a (movR64Imm64Effect 0x11e77a 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1824) (.exec 0x11e77a (fun s => s.RIP = 0x11e77a) (movR64Imm64Effect 0x11e77a 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1825) (.out 0x11e784 (mulR64Effect 0x11e784 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1823, 1821]
    (.letOp (n := 1826) (.out 0x11e784 (mulR64Effect 0x11e784 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1823, 1821]
    (.letOp (n := 1827) (.exec 0x11e784 (fun s => s.RIP = 0x11e784) (mulR64Effect 0x11e784 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1823, 1821]
    (.letOp (n := 1828) (.out 0x11e787 (addR64M64Effect 0x11e787 9 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[1773, 4]
    (.letOp (n := 1829) (.out 0x11e787 (addR64M64Effect 0x11e787 9 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 4] []) (.flag .CF)) #v[1773, 4]
    (.letOp (n := 1830) (.exec 0x11e787 (LoadPre 0x11e787 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11e787 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11e787 9 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[1773, 4]
    (.letOp (n := 1831) (.out 0x11e78f (atFlags StatusFlags.CF (adcR64M64Effect 0x11e78f 1 (.sib 4 none 0 (.d8 0x20)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[1771, 4, 1829]
    (.letOp (n := 1832) (.exec 0x11e78f (LoadPre 0x11e78f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e78f + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e78f 1 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1771, 4, 1829]
    (.letOp (n := 1833) (.out 0x11e794 (addR64R64Effect 0x11e794 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[1828, 1780]
    (.letOp (n := 1834) (.out 0x11e794 (addR64R64Effect 0x11e794 9 10) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 10] []) (.flag .CF)) #v[1828, 1780]
    (.letOp (n := 1835) (.exec 0x11e794 (fun s => s.RIP = 0x11e794) (addR64R64Effect 0x11e794 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[1828, 1780]
    (.letOp (n := 1836) (.out 0x11e797 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e797 1 3)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1831, 1782, 1834]
    (.letOp (n := 1837) (.exec 0x11e797 (fun s => s.RIP = 0x11e797) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e797 1 3)) (Reg.operands [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1831, 1782, 1834]
    (.letOp (n := 1838) (.out 0x11e79a (addR64R64Effect 0x11e79a 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[1833, 1825]
    (.letOp (n := 1839) (.out 0x11e79a (addR64R64Effect 0x11e79a 9 0) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 0] []) (.flag .CF)) #v[1833, 1825]
    (.letOp (n := 1840) (.exec 0x11e79a (fun s => s.RIP = 0x11e79a) (addR64R64Effect 0x11e79a 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1833, 1825]
    (.letOp (n := 1841) (.out 0x11e79d (atFlags StatusFlags.CF (adcR64R64Effect 0x11e79d 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1836, 1826, 1839]
    (.letOp (n := 1842) (.exec 0x11e79d (fun s => s.RIP = 0x11e79d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e79d 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1836, 1826, 1839]
    (.letOp (n := 1843) (.out 0x11e7a0 (addR64R64Effect 0x11e7a0 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[1838, 1784]
    (.letOp (n := 1844) (.out 0x11e7a0 (addR64R64Effect 0x11e7a0 9 11) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 11] []) (.flag .CF)) #v[1838, 1784]
    (.letOp (n := 1845) (.exec 0x11e7a0 (fun s => s.RIP = 0x11e7a0) (addR64R64Effect 0x11e7a0 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[1838, 1784]
    (.letOp (n := 1846) (.out 0x11e7a3 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e7a3 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1841, 1844]
    (.letOp (n := 1847) (.exec 0x11e7a3 (fun s => s.RIP = 0x11e7a3) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e7a3 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1841, 1844]
    (.letOp (n := 1848) (.out 0x11e7a7 (shldR64R64Effect 0x11e7a7 5 7 15 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1815, 1812]
    (.letOp (n := 1849) (.exec 0x11e7a7 (fun s => s.RIP = 0x11e7a7) (shldR64R64Effect 0x11e7a7 5 7 15 12) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1815, 1812]
    (.letOp (n := 1850) (.out 0x11e7ac (shldR64R64Effect 0x11e7ac 5 1 9 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1846, 1843]
    (.letOp (n := 1851) (.exec 0x11e7ac (fun s => s.RIP = 0x11e7ac) (shldR64R64Effect 0x11e7ac 5 1 9 12) (Reg.operands [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1846, 1843]
    (.letOp (n := 1852) (.out 0x11e7b1 (movR64Imm64Effect 0x11e7b1 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1853) (.exec 0x11e7b1 (fun s => s.RIP = 0x11e7b1) (movR64Imm64Effect 0x11e7b1 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1854) (.out 0x11e7bb (andR64R64Effect 0x11e7bb 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[1843, 1852]
    (.letOp (n := 1855) (.exec 0x11e7bb (fun s => s.RIP = 0x11e7bb) (andR64R64Effect 0x11e7bb 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1843, 1852]
    (.letOp (n := 1856) (.exec 0x11e7be (StorePre 0x11e7be 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11e7be + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e7be 9 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[1854, 4]
    (.letOp (n := 1857) (.out 0x11e7c6 (movR64R64Effect 0x11e7c6 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1848]
    (.letOp (n := 1858) (.exec 0x11e7c6 (fun s => s.RIP = 0x11e7c6) (movR64R64Effect 0x11e7c6 0 7) (Reg.operands [.gpr 7] [])) #v[1848]
    (.letOp (n := 1859) (.out 0x11e7c9 (movR64Imm64Effect 0x11e7c9 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1860) (.exec 0x11e7c9 (fun s => s.RIP = 0x11e7c9) (movR64Imm64Effect 0x11e7c9 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1861) (.out 0x11e7d3 (mulR64Effect 0x11e7d3 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1859, 1857]
    (.letOp (n := 1862) (.out 0x11e7d3 (mulR64Effect 0x11e7d3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1859, 1857]
    (.letOp (n := 1863) (.exec 0x11e7d3 (fun s => s.RIP = 0x11e7d3) (mulR64Effect 0x11e7d3 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1859, 1857]
    (.letOp (n := 1864) (.out 0x11e7d6 (movR64R64Effect 0x11e7d6 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[1862]
    (.letOp (n := 1865) (.exec 0x11e7d6 (fun s => s.RIP = 0x11e7d6) (movR64R64Effect 0x11e7d6 3 2) (Reg.operands [.gpr 2] [])) #v[1862]
    (.letOp (n := 1866) (.out 0x11e7d9 (movR64Imm64Effect 0x11e7d9 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1867) (.exec 0x11e7d9 (fun s => s.RIP = 0x11e7d9) (movR64Imm64Effect 0x11e7d9 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l11d880_43)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_42 : List UInt8 :=
  [0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x03, 0x8C,
    0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x13, 0x4C, 0x24, 0x20, 0x4D, 0x01, 0xD1, 0x48, 0x11, 0xD9,
    0x49, 0x01, 0xC1, 0x48, 0x11, 0xD1, 0x4D, 0x01, 0xD9, 0x48, 0x83, 0xD1, 0x00, 0x4C, 0x0F, 0xA4,
    0xFF, 0x0C, 0x4C, 0x0F, 0xA4, 0xC9, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F,
    0x00, 0x49, 0x21, 0xC1, 0x4C, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x48,
    0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD3, 0x48,
    0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] ++ bytes_l11d880_43

theorem code_l11d880_42 : ∀ x ∈ codeRange 0x11e77a bytes_l11d880_42, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e77a 105 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_43

def b_l11d880_41 : Block Op Label signature Reg.count 1780 :=
  .letOp (n := 1780) (.out 0x11e726 (movR64R64Effect 0x11e726 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[1777]
    (.letOp (n := 1781) (.exec 0x11e726 (fun s => s.RIP = 0x11e726) (movR64R64Effect 0x11e726 10 0) (Reg.operands [.gpr 0] [])) #v[1777]
    (.letOp (n := 1782) (.out 0x11e729 (movR64R64Effect 0x11e729 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[1778]
    (.letOp (n := 1783) (.exec 0x11e729 (fun s => s.RIP = 0x11e729) (movR64R64Effect 0x11e729 3 2) (Reg.operands [.gpr 2] [])) #v[1778]
    (.letOp (n := 1784) (.out 0x11e72c (shldR64R64Effect 0x11e72c 5 11 6 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1757, 1754]
    (.letOp (n := 1785) (.exec 0x11e72c (fun s => s.RIP = 0x11e72c) (shldR64R64Effect 0x11e72c 5 11 6 12) (Reg.operands [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1757, 1754]
    (.letOp (n := 1786) (.out 0x11e731 (movR64Imm64Effect 0x11e731 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1787) (.exec 0x11e731 (fun s => s.RIP = 0x11e731) (movR64Imm64Effect 0x11e731 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1788) (.out 0x11e73b (andR64R64Effect 0x11e73b 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[1754, 1786]
    (.letOp (n := 1789) (.exec 0x11e73b (fun s => s.RIP = 0x11e73b) (andR64R64Effect 0x11e73b 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[1754, 1786]
    (.letOp (n := 1790) (.exec 0x11e73e (StorePre 0x11e73e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11e73e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e73e 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1788, 4]
    (.letOp (n := 1791) (.out 0x11e746 (movR64R64Effect 0x11e746 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1594]
    (.letOp (n := 1792) (.exec 0x11e746 (fun s => s.RIP = 0x11e746) (movR64R64Effect 0x11e746 0 5) (Reg.operands [.gpr 5] [])) #v[1594]
    (.letOp (n := 1793) (.out 0x11e749 (mulM64Effect 0x11e749 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1791, 4]
    (.letOp (n := 1794) (.out 0x11e749 (mulM64Effect 0x11e749 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1791, 4]
    (.letOp (n := 1795) (.exec 0x11e749 (LoadPre 0x11e749 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11e749 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e749 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1791, 4]
    (.letOp (n := 1796) (.out 0x11e74e (movR64R64Effect 0x11e74e 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[1793]
    (.letOp (n := 1797) (.exec 0x11e74e (fun s => s.RIP = 0x11e74e) (movR64R64Effect 0x11e74e 12 0) (Reg.operands [.gpr 0] [])) #v[1793]
    (.letOp (n := 1798) (.out 0x11e751 (movR64R64Effect 0x11e751 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[1794]
    (.letOp (n := 1799) (.exec 0x11e751 (fun s => s.RIP = 0x11e751) (movR64R64Effect 0x11e751 7 2) (Reg.operands [.gpr 2] [])) #v[1794]
    (.letOp (n := 1800) (.out 0x11e754 (movR64R64Effect 0x11e754 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1709]
    (.letOp (n := 1801) (.exec 0x11e754 (fun s => s.RIP = 0x11e754) (movR64R64Effect 0x11e754 0 13) (Reg.operands [.gpr 13] [])) #v[1709]
    (.letOp (n := 1802) (.out 0x11e757 (mulR64Effect 0x11e757 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[1700, 1800]
    (.letOp (n := 1803) (.out 0x11e757 (mulR64Effect 0x11e757 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[1700, 1800]
    (.letOp (n := 1804) (.exec 0x11e757 (fun s => s.RIP = 0x11e757) (mulR64Effect 0x11e757 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[1700, 1800]
    (.letOp (n := 1805) (.out 0x11e75a (movR64R64Effect 0x11e75a 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1802]
    (.letOp (n := 1806) (.exec 0x11e75a (fun s => s.RIP = 0x11e75a) (movR64R64Effect 0x11e75a 15 0) (Reg.operands [.gpr 0] [])) #v[1802]
    (.letOp (n := 1807) (.out 0x11e75d (addR64R64Effect 0x11e75d 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[1805, 1796]
    (.letOp (n := 1808) (.out 0x11e75d (addR64R64Effect 0x11e75d 15 12) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 12] []) (.flag .CF)) #v[1805, 1796]
    (.letOp (n := 1809) (.exec 0x11e75d (fun s => s.RIP = 0x11e75d) (addR64R64Effect 0x11e75d 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[1805, 1796]
    (.letOp (n := 1810) (.out 0x11e760 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e760 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[1798, 1803, 1808]
    (.letOp (n := 1811) (.exec 0x11e760 (fun s => s.RIP = 0x11e760) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e760 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1798, 1803, 1808]
    (.letOp (n := 1812) (.out 0x11e763 (addR64R64Effect 0x11e763 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[1807, 1733]
    (.letOp (n := 1813) (.out 0x11e763 (addR64R64Effect 0x11e763 15 14) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 14] []) (.flag .CF)) #v[1807, 1733]
    (.letOp (n := 1814) (.exec 0x11e763 (fun s => s.RIP = 0x11e763) (addR64R64Effect 0x11e763 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[1807, 1733]
    (.letOp (n := 1815) (.out 0x11e766 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e766 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[1810, 1813]
    (.letOp (n := 1816) (.exec 0x11e766 (fun s => s.RIP = 0x11e766) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e766 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1810, 1813]
    (.letOp (n := 1817) (.out 0x11e76a (movR64R64Effect 0x11e76a 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[1812]
    (.letOp (n := 1818) (.exec 0x11e76a (fun s => s.RIP = 0x11e76a) (movR64R64Effect 0x11e76a 0 15) (Reg.operands [.gpr 15] [])) #v[1812]
    (.letOp (n := 1819) (.out 0x11e76d (movR64Imm64Effect 0x11e76d 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1820) (.exec 0x11e76d (fun s => s.RIP = 0x11e76d) (movR64Imm64Effect 0x11e76d 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1821) (.out 0x11e777 (andR64R64Effect 0x11e777 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1817, 1819]
    (.letOp (n := 1822) (.exec 0x11e777 (fun s => s.RIP = 0x11e777) (andR64R64Effect 0x11e777 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1817, 1819]
    (b_l11d880_42)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_41 : List UInt8 :=
  [0x49, 0x89, 0xC2, 0x48, 0x89, 0xD3, 0x49, 0x0F, 0xA4, 0xF3, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC6, 0x48, 0x89, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xE8, 0x48, 0xF7, 0x64, 0x24, 0x08, 0x49, 0x89, 0xC4, 0x48, 0x89, 0xD7, 0x4C, 0x89,
    0xE8, 0x49, 0xF7, 0xE7, 0x49, 0x89, 0xC7, 0x4D, 0x01, 0xE7, 0x48, 0x11, 0xD7, 0x4D, 0x01, 0xF7,
    0x48, 0x83, 0xD7, 0x00, 0x4C, 0x89, 0xF8, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F,
    0x00, 0x48, 0x21, 0xD0] ++ bytes_l11d880_42

theorem code_l11d880_41 : ∀ x ∈ codeRange 0x11e726 bytes_l11d880_41, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e726 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_42

def b_l11d880_40 : Block Op Label signature Reg.count 1735 :=
  .letOp (n := 1735) (.out 0x11e6bc (movR64Imm64Effect 0x11e6bc 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1736) (.exec 0x11e6bc (fun s => s.RIP = 0x11e6bc) (movR64Imm64Effect 0x11e6bc 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1737) (.out 0x11e6c6 (andR64R64Effect 0x11e6c6 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1728, 1735]
    (.letOp (n := 1738) (.exec 0x11e6c6 (fun s => s.RIP = 0x11e6c6) (andR64R64Effect 0x11e6c6 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1728, 1735]
    (.letOp (n := 1739) (.out 0x11e6c9 (movR64Imm64Effect 0x11e6c9 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1740) (.exec 0x11e6c9 (fun s => s.RIP = 0x11e6c9) (movR64Imm64Effect 0x11e6c9 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1741) (.out 0x11e6d3 (mulR64Effect 0x11e6d3 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1739, 1737]
    (.letOp (n := 1742) (.out 0x11e6d3 (mulR64Effect 0x11e6d3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1739, 1737]
    (.letOp (n := 1743) (.exec 0x11e6d3 (fun s => s.RIP = 0x11e6d3) (mulR64Effect 0x11e6d3 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1739, 1737]
    (.letOp (n := 1744) (.out 0x11e6d6 (addR64M64Effect 0x11e6d6 6 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[1680, 4]
    (.letOp (n := 1745) (.out 0x11e6d6 (addR64M64Effect 0x11e6d6 6 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[1680, 4]
    (.letOp (n := 1746) (.exec 0x11e6d6 (LoadPre 0x11e6d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11e6d6 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11e6d6 6 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1680, 4]
    (.letOp (n := 1747) (.out 0x11e6de (atFlags StatusFlags.CF (adcR64M64Effect 0x11e6de 11 (.sib 4 none 0 (.d8 0x20)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[1678, 4, 1745]
    (.letOp (n := 1748) (.exec 0x11e6de (LoadPre 0x11e6de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e6de + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e6de 11 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1678, 4, 1745]
    (.letOp (n := 1749) (.out 0x11e6e3 (addR64R64Effect 0x11e6e3 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[1744, 1741]
    (.letOp (n := 1750) (.out 0x11e6e3 (addR64R64Effect 0x11e6e3 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[1744, 1741]
    (.letOp (n := 1751) (.exec 0x11e6e3 (fun s => s.RIP = 0x11e6e3) (addR64R64Effect 0x11e6e3 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[1744, 1741]
    (.letOp (n := 1752) (.out 0x11e6e6 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e6e6 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1747, 1742, 1750]
    (.letOp (n := 1753) (.exec 0x11e6e6 (fun s => s.RIP = 0x11e6e6) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e6e6 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1747, 1742, 1750]
    (.letOp (n := 1754) (.out 0x11e6e9 (addR64R64Effect 0x11e6e9 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1749, 1691]
    (.letOp (n := 1755) (.out 0x11e6e9 (addR64R64Effect 0x11e6e9 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[1749, 1691]
    (.letOp (n := 1756) (.exec 0x11e6e9 (fun s => s.RIP = 0x11e6e9) (addR64R64Effect 0x11e6e9 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1749, 1691]
    (.letOp (n := 1757) (.out 0x11e6ec (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e6ec 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1752, 1755]
    (.letOp (n := 1758) (.exec 0x11e6ec (fun s => s.RIP = 0x11e6ec) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e6ec 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1752, 1755]
    (.letOp (n := 1759) (.out 0x11e6f0 (movR64M64Effect 0x11e6f0 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1760) (.exec 0x11e6f0 (LoadPre 0x11e6f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11e6f0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e6f0 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1761) (.out 0x11e6f8 (mulR64Effect 0x11e6f8 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[1713, 1759]
    (.letOp (n := 1762) (.out 0x11e6f8 (mulR64Effect 0x11e6f8 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[1713, 1759]
    (.letOp (n := 1763) (.exec 0x11e6f8 (fun s => s.RIP = 0x11e6f8) (mulR64Effect 0x11e6f8 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[1713, 1759]
    (.letOp (n := 1764) (.exec 0x11e6fb (StorePre 0x11e6fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e6fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e6fb 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1762, 4]
    (.letOp (n := 1765) (.exec 0x11e700 (StorePre 0x11e700 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11e700 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e700 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1761, 4]
    (.letOp (n := 1766) (.out 0x11e708 (movR64M64Effect 0x11e708 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1767) (.exec 0x11e708 (LoadPre 0x11e708 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11e708 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e708 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1768) (.out 0x11e70d (mulM64Effect 0x11e70d 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1766, 4]
    (.letOp (n := 1769) (.out 0x11e70d (mulM64Effect 0x11e70d 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1766, 4]
    (.letOp (n := 1770) (.exec 0x11e70d (LoadPre 0x11e70d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11e70d + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11e70d 8 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1766, 4]
    (.letOp (n := 1771) (.out 0x11e715 (movR64R64Effect 0x11e715 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1769]
    (.letOp (n := 1772) (.exec 0x11e715 (fun s => s.RIP = 0x11e715) (movR64R64Effect 0x11e715 1 2) (Reg.operands [.gpr 2] [])) #v[1769]
    (.letOp (n := 1773) (.out 0x11e718 (movR64R64Effect 0x11e718 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[1768]
    (.letOp (n := 1774) (.exec 0x11e718 (fun s => s.RIP = 0x11e718) (movR64R64Effect 0x11e718 9 0) (Reg.operands [.gpr 0] [])) #v[1768]
    (.letOp (n := 1775) (.out 0x11e71b (movR64M64Effect 0x11e71b 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1776) (.exec 0x11e71b (LoadPre 0x11e71b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11e71b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e71b 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1777) (.out 0x11e723 (mulR64Effect 0x11e723 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1673, 1775]
    (.letOp (n := 1778) (.out 0x11e723 (mulR64Effect 0x11e723 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1673, 1775]
    (.letOp (n := 1779) (.exec 0x11e723 (fun s => s.RIP = 0x11e723) (mulR64Effect 0x11e723 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1673, 1775]
    (b_l11d880_41)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_40 : List UInt8 :=
  [0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10,
    0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x03, 0xB4, 0x24, 0xC8, 0x00,
    0x00, 0x00, 0x4C, 0x13, 0x5C, 0x24, 0x20, 0x48, 0x01, 0xC6, 0x49, 0x11, 0xD3, 0x48, 0x01, 0xCE,
    0x49, 0x83, 0xD3, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE4, 0x48,
    0x89, 0x54, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24,
    0x18, 0x48, 0xF7, 0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC1, 0x48,
    0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE0] ++ bytes_l11d880_41

theorem code_l11d880_40 : ∀ x ∈ codeRange 0x11e6bc bytes_l11d880_40, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e6bc 106 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_41

def b_l11d880_39 : Block Op Label signature Reg.count 1691 :=
  .letOp (n := 1691) (.out 0x11e669 (shldR64R64Effect 0x11e669 5 1 14 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1662, 1659]
    (.letOp (n := 1692) (.exec 0x11e669 (fun s => s.RIP = 0x11e669) (shldR64R64Effect 0x11e669 5 1 14 12) (Reg.operands [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1662, 1659]
    (.letOp (n := 1693) (.out 0x11e66e (movR64Imm64Effect 0x11e66e 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1694) (.exec 0x11e66e (fun s => s.RIP = 0x11e66e) (movR64Imm64Effect 0x11e66e 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1695) (.out 0x11e678 (andR64R64Effect 0x11e678 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[1659, 1693]
    (.letOp (n := 1696) (.exec 0x11e678 (fun s => s.RIP = 0x11e678) (andR64R64Effect 0x11e678 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1659, 1693]
    (.letOp (n := 1697) (.exec 0x11e67b (StorePre 0x11e67b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11e67b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e67b 14 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[1695, 4]
    (.letOp (n := 1698) (.out 0x11e683 (movR64R64Effect 0x11e683 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1594]
    (.letOp (n := 1699) (.exec 0x11e683 (fun s => s.RIP = 0x11e683) (movR64R64Effect 0x11e683 0 5) (Reg.operands [.gpr 5] [])) #v[1594]
    (.letOp (n := 1700) (.out 0x11e686 (movR64M64Effect 0x11e686 15 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 1701) (.exec 0x11e686 (LoadPre 0x11e686 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11e686 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e686 15 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1702) (.out 0x11e68b (mulR64Effect 0x11e68b 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[1700, 1698]
    (.letOp (n := 1703) (.out 0x11e68b (mulR64Effect 0x11e68b 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[1700, 1698]
    (.letOp (n := 1704) (.exec 0x11e68b (fun s => s.RIP = 0x11e68b) (mulR64Effect 0x11e68b 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[1700, 1698]
    (.letOp (n := 1705) (.out 0x11e68e (movR64R64Effect 0x11e68e 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[1702]
    (.letOp (n := 1706) (.exec 0x11e68e (fun s => s.RIP = 0x11e68e) (movR64R64Effect 0x11e68e 10 0) (Reg.operands [.gpr 0] [])) #v[1702]
    (.letOp (n := 1707) (.out 0x11e691 (movR64R64Effect 0x11e691 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[1703]
    (.letOp (n := 1708) (.exec 0x11e691 (fun s => s.RIP = 0x11e691) (movR64R64Effect 0x11e691 14 2) (Reg.operands [.gpr 2] [])) #v[1703]
    (.letOp (n := 1709) (.out 0x11e694 (movR64M64Effect 0x11e694 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 1710) (.exec 0x11e694 (LoadPre 0x11e694 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11e694 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e694 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1711) (.out 0x11e699 (movR64R64Effect 0x11e699 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1709]
    (.letOp (n := 1712) (.exec 0x11e699 (fun s => s.RIP = 0x11e699) (movR64R64Effect 0x11e699 0 13) (Reg.operands [.gpr 13] [])) #v[1709]
    (.letOp (n := 1713) (.out 0x11e69c (movR64M64Effect 0x11e69c 12 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 1714) (.exec 0x11e69c (LoadPre 0x11e69c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11e69c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e69c 12 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1715) (.out 0x11e6a1 (mulR64Effect 0x11e6a1 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[1713, 1711]
    (.letOp (n := 1716) (.out 0x11e6a1 (mulR64Effect 0x11e6a1 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[1713, 1711]
    (.letOp (n := 1717) (.exec 0x11e6a1 (fun s => s.RIP = 0x11e6a1) (mulR64Effect 0x11e6a1 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[1713, 1711]
    (.letOp (n := 1718) (.out 0x11e6a4 (addR64R64Effect 0x11e6a4 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[1705, 1687]
    (.letOp (n := 1719) (.out 0x11e6a4 (addR64R64Effect 0x11e6a4 10 7) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 7] []) (.flag .CF)) #v[1705, 1687]
    (.letOp (n := 1720) (.exec 0x11e6a4 (fun s => s.RIP = 0x11e6a4) (addR64R64Effect 0x11e6a4 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[1705, 1687]
    (.letOp (n := 1721) (.out 0x11e6a7 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e6a7 14 9)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[1707, 1689, 1719]
    (.letOp (n := 1722) (.exec 0x11e6a7 (fun s => s.RIP = 0x11e6a7) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e6a7 14 9)) (Reg.operands [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1707, 1689, 1719]
    (.letOp (n := 1723) (.out 0x11e6aa (addR64R64Effect 0x11e6aa 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[1715, 1718]
    (.letOp (n := 1724) (.out 0x11e6aa (addR64R64Effect 0x11e6aa 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[1715, 1718]
    (.letOp (n := 1725) (.exec 0x11e6aa (fun s => s.RIP = 0x11e6aa) (addR64R64Effect 0x11e6aa 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[1715, 1718]
    (.letOp (n := 1726) (.out 0x11e6ad (atFlags StatusFlags.CF (adcR64R64Effect 0x11e6ad 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[1721, 1716, 1724]
    (.letOp (n := 1727) (.exec 0x11e6ad (fun s => s.RIP = 0x11e6ad) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e6ad 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1721, 1716, 1724]
    (.letOp (n := 1728) (.out 0x11e6b0 (addR64R64Effect 0x11e6b0 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[1723, 1640]
    (.letOp (n := 1729) (.out 0x11e6b0 (addR64R64Effect 0x11e6b0 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[1723, 1640]
    (.letOp (n := 1730) (.exec 0x11e6b0 (fun s => s.RIP = 0x11e6b0) (addR64R64Effect 0x11e6b0 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[1723, 1640]
    (.letOp (n := 1731) (.out 0x11e6b3 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e6b3 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[1726, 1729]
    (.letOp (n := 1732) (.exec 0x11e6b3 (fun s => s.RIP = 0x11e6b3) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e6b3 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1726, 1729]
    (.letOp (n := 1733) (.out 0x11e6b7 (shldR64R64Effect 0x11e6b7 5 14 0 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[1731, 1728]
    (.letOp (n := 1734) (.exec 0x11e6b7 (fun s => s.RIP = 0x11e6b7) (shldR64R64Effect 0x11e6b7 5 14 0 12) (Reg.operands [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1731, 1728]
    (b_l11d880_40))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_39 : List UInt8 :=
  [0x4C, 0x0F, 0xA4, 0xF1, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49,
    0x21, 0xC6, 0x4C, 0x89, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE8, 0x4C, 0x8B, 0x7C,
    0x24, 0x38, 0x49, 0xF7, 0xE7, 0x49, 0x89, 0xC2, 0x49, 0x89, 0xD6, 0x4C, 0x8B, 0x6C, 0x24, 0x10,
    0x4C, 0x89, 0xE8, 0x4C, 0x8B, 0x64, 0x24, 0x70, 0x49, 0xF7, 0xE4, 0x49, 0x01, 0xFA, 0x4D, 0x11,
    0xCE, 0x4C, 0x01, 0xD0, 0x49, 0x11, 0xD6, 0x48, 0x01, 0xD8, 0x49, 0x83, 0xD6, 0x00, 0x49, 0x0F,
    0xA4, 0xC6, 0x0C] ++ bytes_l11d880_40

theorem code_l11d880_39 : ∀ x ∈ codeRange 0x11e669 bytes_l11d880_39, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e669 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_40

def b_l11d880_38 : Block Op Label signature Reg.count 1648 :=
  .letOp (n := 1648) (.out 0x11e60f (orR64R64Effect 0x11e60f 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[1646, 1609]
    (.letOp (n := 1649) (.exec 0x11e60f (fun s => s.RIP = 0x11e60f) (orR64R64Effect 0x11e60f 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[1646, 1609]
    (.letOp (n := 1650) (.out 0x11e612 (movR64Imm64Effect 0x11e612 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1651) (.exec 0x11e612 (fun s => s.RIP = 0x11e612) (movR64Imm64Effect 0x11e612 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 1652) (.out 0x11e61c (mulR64Effect 0x11e61c 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1650, 1648]
    (.letOp (n := 1653) (.out 0x11e61c (mulR64Effect 0x11e61c 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1650, 1648]
    (.letOp (n := 1654) (.exec 0x11e61c (fun s => s.RIP = 0x11e61c) (mulR64Effect 0x11e61c 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1650, 1648]
    (.letOp (n := 1655) (.out 0x11e61f (movR64R64Effect 0x11e61f 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1653]
    (.letOp (n := 1656) (.exec 0x11e61f (fun s => s.RIP = 0x11e61f) (movR64R64Effect 0x11e61f 1 2) (Reg.operands [.gpr 2] [])) #v[1653]
    (.letOp (n := 1657) (.out 0x11e622 (movR64R64Effect 0x11e622 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[1652]
    (.letOp (n := 1658) (.exec 0x11e622 (fun s => s.RIP = 0x11e622) (movR64R64Effect 0x11e622 14 0) (Reg.operands [.gpr 0] [])) #v[1652]
    (.letOp (n := 1659) (.out 0x11e625 (addR64M64Effect 0x11e625 14 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[1657, 4]
    (.letOp (n := 1660) (.out 0x11e625 (addR64M64Effect 0x11e625 14 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 4] []) (.flag .CF)) #v[1657, 4]
    (.letOp (n := 1661) (.exec 0x11e625 (LoadPre 0x11e625 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e625 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11e625 14 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[1657, 4]
    (.letOp (n := 1662) (.out 0x11e62a (atFlags StatusFlags.CF (adcR64M64Effect 0x11e62a 1 (.sib 4 none 0 (.d32 0x90)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[1655, 4, 1660]
    (.letOp (n := 1663) (.exec 0x11e62a (LoadPre 0x11e62a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11e62a + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e62a 1 (.sib 4 none 0 (.d32 0x90)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1655, 4, 1660]
    (.letOp (n := 1664) (.out 0x11e632 (movR64R64Effect 0x11e632 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[1565]
    (.letOp (n := 1665) (.exec 0x11e632 (fun s => s.RIP = 0x11e632) (movR64R64Effect 0x11e632 0 10) (Reg.operands [.gpr 10] [])) #v[1565]
    (.letOp (n := 1666) (.out 0x11e635 (mulR64Effect 0x11e635 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[1613, 1664]
    (.letOp (n := 1667) (.out 0x11e635 (mulR64Effect 0x11e635 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[1613, 1664]
    (.letOp (n := 1668) (.exec 0x11e635 (fun s => s.RIP = 0x11e635) (mulR64Effect 0x11e635 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1613, 1664]
    (.letOp (n := 1669) (.exec 0x11e638 (StorePre 0x11e638 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e638 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e638 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1667, 4]
    (.letOp (n := 1670) (.exec 0x11e63d (StorePre 0x11e63d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11e63d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e63d 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1666, 4]
    (.letOp (n := 1671) (.out 0x11e645 (movR64R64Effect 0x11e645 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[1574]
    (.letOp (n := 1672) (.exec 0x11e645 (fun s => s.RIP = 0x11e645) (movR64R64Effect 0x11e645 0 6) (Reg.operands [.gpr 6] [])) #v[1574]
    (.letOp (n := 1673) (.out 0x11e648 (movR64M64Effect 0x11e648 8 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 1674) (.exec 0x11e648 (LoadPre 0x11e648 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11e648 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e648 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1675) (.out 0x11e64d (mulR64Effect 0x11e64d 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1673, 1671]
    (.letOp (n := 1676) (.out 0x11e64d (mulR64Effect 0x11e64d 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1673, 1671]
    (.letOp (n := 1677) (.exec 0x11e64d (fun s => s.RIP = 0x11e64d) (mulR64Effect 0x11e64d 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1673, 1671]
    (.letOp (n := 1678) (.out 0x11e650 (movR64R64Effect 0x11e650 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[1676]
    (.letOp (n := 1679) (.exec 0x11e650 (fun s => s.RIP = 0x11e650) (movR64R64Effect 0x11e650 11 2) (Reg.operands [.gpr 2] [])) #v[1676]
    (.letOp (n := 1680) (.out 0x11e653 (movR64R64Effect 0x11e653 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1675]
    (.letOp (n := 1681) (.exec 0x11e653 (fun s => s.RIP = 0x11e653) (movR64R64Effect 0x11e653 6 0) (Reg.operands [.gpr 0] [])) #v[1675]
    (.letOp (n := 1682) (.out 0x11e656 (movR64M64Effect 0x11e656 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1683) (.exec 0x11e656 (LoadPre 0x11e656 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11e656 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e656 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1684) (.out 0x11e65e (mulM64Effect 0x11e65e 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1682, 4]
    (.letOp (n := 1685) (.out 0x11e65e (mulM64Effect 0x11e65e 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1682, 4]
    (.letOp (n := 1686) (.exec 0x11e65e (LoadPre 0x11e65e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11e65e + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e65e 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1682, 4]
    (.letOp (n := 1687) (.out 0x11e663 (movR64R64Effect 0x11e663 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[1684]
    (.letOp (n := 1688) (.exec 0x11e663 (fun s => s.RIP = 0x11e663) (movR64R64Effect 0x11e663 7 0) (Reg.operands [.gpr 0] [])) #v[1684]
    (.letOp (n := 1689) (.out 0x11e666 (movR64R64Effect 0x11e666 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[1685]
    (.letOp (n := 1690) (.exec 0x11e666 (fun s => s.RIP = 0x11e666) (movR64R64Effect 0x11e666 9 2) (Reg.operands [.gpr 2] [])) #v[1685]
    (b_l11d880_39)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_38 : List UInt8 :=
  [0x4C, 0x09, 0xE0, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1,
    0x48, 0x89, 0xD1, 0x49, 0x89, 0xC6, 0x4C, 0x03, 0x74, 0x24, 0x20, 0x48, 0x13, 0x8C, 0x24, 0x90,
    0x00, 0x00, 0x00, 0x4C, 0x89, 0xD0, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0x54, 0x24, 0x20, 0x48, 0x89,
    0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF0, 0x4C, 0x8B, 0x44, 0x24, 0x68, 0x49, 0xF7,
    0xE0, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC6, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0x64, 0x24, 0x08, 0x48, 0x89, 0xC7, 0x49, 0x89, 0xD1] ++ bytes_l11d880_39

theorem code_l11d880_38 : ∀ x ∈ codeRange 0x11e60f bytes_l11d880_38, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e60f 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_39

def b_l11d880_37 : Block Op Label signature Reg.count 1603 :=
  .letOp (n := 1603) (.out 0x11e5bd (movR64R64Effect 0x11e5bd 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[1599]
    (.letOp (n := 1604) (.exec 0x11e5bd (fun s => s.RIP = 0x11e5bd) (movR64R64Effect 0x11e5bd 15 2) (Reg.operands [.gpr 2] [])) #v[1599]
    (.letOp (n := 1605) (.out 0x11e5c0 (movR64R64Effect 0x11e5c0 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 8] []) (.reg (.gpr 12))) #v[1560]
    (.letOp (n := 1606) (.exec 0x11e5c0 (fun s => s.RIP = 0x11e5c0) (movR64R64Effect 0x11e5c0 12 8) (Reg.operands [.gpr 8] [])) #v[1560]
    (.letOp (n := 1607) (.out 0x11e5c3 (shrR64Effect 0x11e5c3 4 12 48) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1605]
    (.letOp (n := 1608) (.exec 0x11e5c3 (fun s => s.RIP = 0x11e5c3) (shrR64Effect 0x11e5c3 4 12 48) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1605]
    (.letOp (n := 1609) (.out 0x11e5c7 (andR32Imm8Effect 0x11e5c7 4 12 0xf) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1607]
    (.letOp (n := 1610) (.exec 0x11e5c7 (fun s => s.RIP = 0x11e5c7) (andR32Imm8Effect 0x11e5c7 4 12 0xf) (Reg.operands [.gpr 12] [])) #v[1607]
    (.letOp (n := 1611) (.out 0x11e5cb (movR64M64Effect 0x11e5cb 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1612) (.exec 0x11e5cb (LoadPre 0x11e5cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11e5cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e5cb 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1613) (.out 0x11e5d0 (movR64M64Effect 0x11e5d0 13 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 1614) (.exec 0x11e5d0 (LoadPre 0x11e5d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11e5d0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e5d0 13 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1615) (.out 0x11e5d8 (mulR64Effect 0x11e5d8 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[1613, 1611]
    (.letOp (n := 1616) (.out 0x11e5d8 (mulR64Effect 0x11e5d8 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[1613, 1611]
    (.letOp (n := 1617) (.exec 0x11e5d8 (fun s => s.RIP = 0x11e5d8) (mulR64Effect 0x11e5d8 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1613, 1611]
    (.letOp (n := 1618) (.out 0x11e5db (shldR64R64Effect 0x11e5db 5 9 8 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[1563, 1560]
    (.letOp (n := 1619) (.exec 0x11e5db (fun s => s.RIP = 0x11e5db) (shldR64R64Effect 0x11e5db 5 9 8 12) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1563, 1560]
    (.letOp (n := 1620) (.out 0x11e5e0 (addR64R64Effect 0x11e5e0 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[1592, 1583]
    (.letOp (n := 1621) (.out 0x11e5e0 (addR64R64Effect 0x11e5e0 7 11) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 11] []) (.flag .CF)) #v[1592, 1583]
    (.letOp (n := 1622) (.exec 0x11e5e0 (fun s => s.RIP = 0x11e5e0) (addR64R64Effect 0x11e5e0 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[1592, 1583]
    (.letOp (n := 1623) (.out 0x11e5e3 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e5e3 3 1)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1590, 1581, 1621]
    (.letOp (n := 1624) (.exec 0x11e5e3 (fun s => s.RIP = 0x11e5e3) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e5e3 3 1)) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1590, 1581, 1621]
    (.letOp (n := 1625) (.out 0x11e5e6 (addR64R64Effect 0x11e5e6 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[1620, 1601]
    (.letOp (n := 1626) (.out 0x11e5e6 (addR64R64Effect 0x11e5e6 7 14) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 14] []) (.flag .CF)) #v[1620, 1601]
    (.letOp (n := 1627) (.exec 0x11e5e6 (fun s => s.RIP = 0x11e5e6) (addR64R64Effect 0x11e5e6 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[1620, 1601]
    (.letOp (n := 1628) (.out 0x11e5e9 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e5e9 3 15)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1623, 1603, 1626]
    (.letOp (n := 1629) (.exec 0x11e5e9 (fun s => s.RIP = 0x11e5e9) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e5e9 3 15)) (Reg.operands [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1623, 1603, 1626]
    (.letOp (n := 1630) (.out 0x11e5ec (addR64R64Effect 0x11e5ec 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[1615, 1625]
    (.letOp (n := 1631) (.out 0x11e5ec (addR64R64Effect 0x11e5ec 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[1615, 1625]
    (.letOp (n := 1632) (.exec 0x11e5ec (fun s => s.RIP = 0x11e5ec) (addR64R64Effect 0x11e5ec 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[1615, 1625]
    (.letOp (n := 1633) (.out 0x11e5ef (atFlags StatusFlags.CF (adcR64R64Effect 0x11e5ef 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1628, 1616, 1631]
    (.letOp (n := 1634) (.exec 0x11e5ef (fun s => s.RIP = 0x11e5ef) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e5ef 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1628, 1616, 1631]
    (.letOp (n := 1635) (.out 0x11e5f2 (addR64R64Effect 0x11e5f2 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[1630, 1618]
    (.letOp (n := 1636) (.out 0x11e5f2 (addR64R64Effect 0x11e5f2 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[1630, 1618]
    (.letOp (n := 1637) (.exec 0x11e5f2 (fun s => s.RIP = 0x11e5f2) (addR64R64Effect 0x11e5f2 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[1630, 1618]
    (.letOp (n := 1638) (.out 0x11e5f5 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e5f5 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1633, 1636]
    (.letOp (n := 1639) (.exec 0x11e5f5 (fun s => s.RIP = 0x11e5f5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e5f5 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1633, 1636]
    (.letOp (n := 1640) (.out 0x11e5f9 (shldR64R64Effect 0x11e5f9 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1638, 1635]
    (.letOp (n := 1641) (.exec 0x11e5f9 (fun s => s.RIP = 0x11e5f9) (shldR64R64Effect 0x11e5f9 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1638, 1635]
    (.letOp (n := 1642) (.out 0x11e5fe (shlR64Effect 0x11e5fe 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1635]
    (.letOp (n := 1643) (.exec 0x11e5fe (fun s => s.RIP = 0x11e5fe) (shlR64Effect 0x11e5fe 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1635]
    (.letOp (n := 1644) (.out 0x11e602 (movR64Imm64Effect 0x11e602 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1645) (.exec 0x11e602 (fun s => s.RIP = 0x11e602) (movR64Imm64Effect 0x11e602 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 1646) (.out 0x11e60c (andR64R64Effect 0x11e60c 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1642, 1644]
    (.letOp (n := 1647) (.exec 0x11e60c (fun s => s.RIP = 0x11e60c) (andR64R64Effect 0x11e60c 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1642, 1644]
    (b_l11d880_38)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_37 : List UInt8 :=
  [0x49, 0x89, 0xD7, 0x4D, 0x89, 0xC4, 0x49, 0xC1, 0xEC, 0x30, 0x41, 0x83, 0xE4, 0x0F, 0x48, 0x8B,
    0x44, 0x24, 0x10, 0x4C, 0x8B, 0xAC, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x4D, 0x0F,
    0xA4, 0xC1, 0x0C, 0x4C, 0x01, 0xDF, 0x48, 0x11, 0xCB, 0x4C, 0x01, 0xF7, 0x4C, 0x11, 0xFB, 0x48,
    0x01, 0xF8, 0x48, 0x11, 0xD3, 0x4C, 0x01, 0xC8, 0x48, 0x83, 0xD3, 0x00, 0x48, 0x0F, 0xA4, 0xC3,
    0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48,
    0x21, 0xC8] ++ bytes_l11d880_38

theorem code_l11d880_37 : ∀ x ∈ codeRange 0x11e5bd bytes_l11d880_37, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e5bd 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_38

def b_l11d880_36 : Block Op Label signature Reg.count 1562 :=
  .letOp (n := 1562) (.exec 0x11e562 (StorePre 0x11e562 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11e562 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e562 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1557, 4]
    (.letOp (n := 1563) (.out 0x11e567 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e567 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[1555, 1558]
    (.letOp (n := 1564) (.exec 0x11e567 (fun s => s.RIP = 0x11e567) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e567 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1555, 1558]
    (.letOp (n := 1565) (.out 0x11e56b (movR64M64Effect 0x11e56b 10 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 1566) (.exec 0x11e56b (LoadPre 0x11e56b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11e56b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e56b 10 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1567) (.out 0x11e573 (movR64R64Effect 0x11e573 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[1565]
    (.letOp (n := 1568) (.exec 0x11e573 (fun s => s.RIP = 0x11e573) (movR64R64Effect 0x11e573 0 10) (Reg.operands [.gpr 10] [])) #v[1565]
    (.letOp (n := 1569) (.out 0x11e576 (mulR64Effect 0x11e576 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[1423, 1567]
    (.letOp (n := 1570) (.out 0x11e576 (mulR64Effect 0x11e576 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[1423, 1567]
    (.letOp (n := 1571) (.exec 0x11e576 (fun s => s.RIP = 0x11e576) (mulR64Effect 0x11e576 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1423, 1567]
    (.letOp (n := 1572) (.exec 0x11e579 (StorePre 0x11e579 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e579 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e579 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1569, 4]
    (.letOp (n := 1573) (.exec 0x11e57e (StorePre 0x11e57e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11e57e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e57e 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1570, 4]
    (.letOp (n := 1574) (.out 0x11e586 (movR64M64Effect 0x11e586 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 1575) (.exec 0x11e586 (LoadPre 0x11e586 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11e586 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e586 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1576) (.out 0x11e58b (movR64R64Effect 0x11e58b 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[1574]
    (.letOp (n := 1577) (.exec 0x11e58b (fun s => s.RIP = 0x11e58b) (movR64R64Effect 0x11e58b 0 6) (Reg.operands [.gpr 6] [])) #v[1574]
    (.letOp (n := 1578) (.out 0x11e58e (mulM64Effect 0x11e58e 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1576, 4]
    (.letOp (n := 1579) (.out 0x11e58e (mulM64Effect 0x11e58e 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1576, 4]
    (.letOp (n := 1580) (.exec 0x11e58e (LoadPre 0x11e58e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11e58e + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e58e 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1576, 4]
    (.letOp (n := 1581) (.out 0x11e593 (movR64R64Effect 0x11e593 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1579]
    (.letOp (n := 1582) (.exec 0x11e593 (fun s => s.RIP = 0x11e593) (movR64R64Effect 0x11e593 1 2) (Reg.operands [.gpr 2] [])) #v[1579]
    (.letOp (n := 1583) (.out 0x11e596 (movR64R64Effect 0x11e596 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[1578]
    (.letOp (n := 1584) (.exec 0x11e596 (fun s => s.RIP = 0x11e596) (movR64R64Effect 0x11e596 11 0) (Reg.operands [.gpr 0] [])) #v[1578]
    (.letOp (n := 1585) (.out 0x11e599 (movR64M64Effect 0x11e599 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1586) (.exec 0x11e599 (LoadPre 0x11e599 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11e599 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e599 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1587) (.out 0x11e5a1 (mulM64Effect 0x11e5a1 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1585, 4]
    (.letOp (n := 1588) (.out 0x11e5a1 (mulM64Effect 0x11e5a1 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1585, 4]
    (.letOp (n := 1589) (.exec 0x11e5a1 (LoadPre 0x11e5a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11e5a1 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e5a1 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1585, 4]
    (.letOp (n := 1590) (.out 0x11e5a6 (movR64R64Effect 0x11e5a6 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[1588]
    (.letOp (n := 1591) (.exec 0x11e5a6 (fun s => s.RIP = 0x11e5a6) (movR64R64Effect 0x11e5a6 3 2) (Reg.operands [.gpr 2] [])) #v[1588]
    (.letOp (n := 1592) (.out 0x11e5a9 (movR64R64Effect 0x11e5a9 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[1587]
    (.letOp (n := 1593) (.exec 0x11e5a9 (fun s => s.RIP = 0x11e5a9) (movR64R64Effect 0x11e5a9 7 0) (Reg.operands [.gpr 0] [])) #v[1587]
    (.letOp (n := 1594) (.out 0x11e5ac (movR64M64Effect 0x11e5ac 5 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 1595) (.exec 0x11e5ac (LoadPre 0x11e5ac (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11e5ac + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e5ac 5 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1596) (.out 0x11e5b4 (movR64R64Effect 0x11e5b4 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1594]
    (.letOp (n := 1597) (.exec 0x11e5b4 (fun s => s.RIP = 0x11e5b4) (movR64R64Effect 0x11e5b4 0 5) (Reg.operands [.gpr 5] [])) #v[1594]
    (.letOp (n := 1598) (.out 0x11e5b7 (mulR64Effect 0x11e5b7 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[1489, 1596]
    (.letOp (n := 1599) (.out 0x11e5b7 (mulR64Effect 0x11e5b7 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[1489, 1596]
    (.letOp (n := 1600) (.exec 0x11e5b7 (fun s => s.RIP = 0x11e5b7) (mulR64Effect 0x11e5b7 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1489, 1596]
    (.letOp (n := 1601) (.out 0x11e5ba (movR64R64Effect 0x11e5ba 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[1598]
    (.letOp (n := 1602) (.exec 0x11e5ba (fun s => s.RIP = 0x11e5ba) (movR64R64Effect 0x11e5ba 14 0) (Reg.operands [.gpr 0] [])) #v[1598]
    (b_l11d880_37)))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_36 : List UInt8 :=
  [0x48, 0x89, 0x7C, 0x24, 0x78, 0x49, 0x83, 0xD1, 0x00, 0x4C, 0x8B, 0x94, 0x24, 0xA0, 0x00, 0x00,
    0x00, 0x4C, 0x89, 0xD0, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0x94, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0x64, 0x24,
    0x08, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC3, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0x64, 0x24, 0x38, 0x48, 0x89, 0xD3, 0x48, 0x89, 0xC7, 0x48, 0x8B, 0xAC, 0x24, 0xF8, 0x00,
    0x00, 0x00, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xC6] ++ bytes_l11d880_37

theorem code_l11d880_36 : ∀ x ∈ codeRange 0x11e562 bytes_l11d880_36, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e562 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_37

def b_l11d880_35 : Block Op Label signature Reg.count 1515 :=
  .letOp (n := 1515) (.out 0x11e50b (shldR64R64Effect 0x11e50b 5 6 8 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1469, 1466]
    (.letOp (n := 1516) (.exec 0x11e50b (fun s => s.RIP = 0x11e50b) (shldR64R64Effect 0x11e50b 5 6 8 12) (Reg.operands [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1469, 1466]
    (.letOp (n := 1517) (.out 0x11e510 (shrR64Effect 0x11e510 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1446]
    (.letOp (n := 1518) (.exec 0x11e510 (fun s => s.RIP = 0x11e510) (shrR64Effect 0x11e510 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1446]
    (.letOp (n := 1519) (.out 0x11e514 (movR64Imm64Effect 0x11e514 0 0x1000003d10) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1520) (.exec 0x11e514 (fun s => s.RIP = 0x11e514) (movR64Imm64Effect 0x11e514 0 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1521) (.out 0x11e51e (imulR64R64Effect 0x11e51e 4 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1517, 1519]
    (.letOp (n := 1522) (.exec 0x11e51e (fun s => s.RIP = 0x11e51e) (imulR64R64Effect 0x11e51e 4 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1517, 1519]
    (.letOp (n := 1523) (.out 0x11e522 (movR64R64Effect 0x11e522 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[1450]
    (.letOp (n := 1524) (.exec 0x11e522 (fun s => s.RIP = 0x11e522) (movR64R64Effect 0x11e522 0 10) (Reg.operands [.gpr 10] [])) #v[1450]
    (.letOp (n := 1525) (.out 0x11e525 (movR64Imm64Effect 0x11e525 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1526) (.exec 0x11e525 (fun s => s.RIP = 0x11e525) (movR64Imm64Effect 0x11e525 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1527) (.out 0x11e52f (mulR64Effect 0x11e52f 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1525, 1523]
    (.letOp (n := 1528) (.out 0x11e52f (mulR64Effect 0x11e52f 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1525, 1523]
    (.letOp (n := 1529) (.exec 0x11e52f (fun s => s.RIP = 0x11e52f) (mulR64Effect 0x11e52f 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1525, 1523]
    (.letOp (n := 1530) (.out 0x11e532 (addR64R64Effect 0x11e532 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[1521, 1528]
    (.letOp (n := 1531) (.exec 0x11e532 (fun s => s.RIP = 0x11e532) (addR64R64Effect 0x11e532 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1521, 1528]
    (.letOp (n := 1532) (.out 0x11e535 (addR64M64Effect 0x11e535 7 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[1483, 4]
    (.letOp (n := 1533) (.out 0x11e535 (addR64M64Effect 0x11e535 7 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[1483, 4]
    (.letOp (n := 1534) (.exec 0x11e535 (LoadPre 0x11e535 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11e535 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11e535 7 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1483, 4]
    (.letOp (n := 1535) (.out 0x11e53d (atFlags StatusFlags.CF (adcR64M64Effect 0x11e53d 9 (.sib 4 none 0 (.d8 0x78)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[1485, 4, 1533]
    (.letOp (n := 1536) (.exec 0x11e53d (LoadPre 0x11e53d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11e53d + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e53d 9 (.sib 4 none 0 (.d8 0x78)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1485, 4, 1533]
    (.letOp (n := 1537) (.out 0x11e542 (addR64R64Effect 0x11e542 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[1532, 1495]
    (.letOp (n := 1538) (.out 0x11e542 (addR64R64Effect 0x11e542 7 15) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 15] []) (.flag .CF)) #v[1532, 1495]
    (.letOp (n := 1539) (.exec 0x11e542 (fun s => s.RIP = 0x11e542) (addR64R64Effect 0x11e542 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[1532, 1495]
    (.letOp (n := 1540) (.out 0x11e545 (atFlags StatusFlags.CF (adcR64M64Effect 0x11e545 9 (.sib 4 none 0 (.d8 0x20)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[1535, 4, 1538]
    (.letOp (n := 1541) (.exec 0x11e545 (LoadPre 0x11e545 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e545 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e545 9 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1535, 4, 1538]
    (.letOp (n := 1542) (.out 0x11e54a (addR64R64Effect 0x11e54a 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[1537, 1504]
    (.letOp (n := 1543) (.out 0x11e54a (addR64R64Effect 0x11e54a 7 12) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 12] []) (.flag .CF)) #v[1537, 1504]
    (.letOp (n := 1544) (.exec 0x11e54a (fun s => s.RIP = 0x11e54a) (addR64R64Effect 0x11e54a 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[1537, 1504]
    (.letOp (n := 1545) (.out 0x11e54d (atFlags StatusFlags.CF (adcR64R64Effect 0x11e54d 9 3)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[1540, 1502, 1543]
    (.letOp (n := 1546) (.exec 0x11e54d (fun s => s.RIP = 0x11e54d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e54d 9 3)) (Reg.operands [.gpr 9, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1540, 1502, 1543]
    (.letOp (n := 1547) (.out 0x11e550 (addR64R64Effect 0x11e550 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[1542, 1511]
    (.letOp (n := 1548) (.out 0x11e550 (addR64R64Effect 0x11e550 7 5) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 5] []) (.flag .CF)) #v[1542, 1511]
    (.letOp (n := 1549) (.exec 0x11e550 (fun s => s.RIP = 0x11e550) (addR64R64Effect 0x11e550 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[1542, 1511]
    (.letOp (n := 1550) (.out 0x11e553 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e553 9 11)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[1545, 1513, 1548]
    (.letOp (n := 1551) (.exec 0x11e553 (fun s => s.RIP = 0x11e553) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e553 9 11)) (Reg.operands [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1545, 1513, 1548]
    (.letOp (n := 1552) (.out 0x11e556 (addR64R64Effect 0x11e556 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[1547, 1527]
    (.letOp (n := 1553) (.out 0x11e556 (addR64R64Effect 0x11e556 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[1547, 1527]
    (.letOp (n := 1554) (.exec 0x11e556 (fun s => s.RIP = 0x11e556) (addR64R64Effect 0x11e556 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1547, 1527]
    (.letOp (n := 1555) (.out 0x11e559 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e559 9 1)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[1550, 1530, 1553]
    (.letOp (n := 1556) (.exec 0x11e559 (fun s => s.RIP = 0x11e559) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e559 9 1)) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1550, 1530, 1553]
    (.letOp (n := 1557) (.out 0x11e55c (addR64R64Effect 0x11e55c 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[1552, 1515]
    (.letOp (n := 1558) (.out 0x11e55c (addR64R64Effect 0x11e55c 7 6) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 6] []) (.flag .CF)) #v[1552, 1515]
    (.letOp (n := 1559) (.exec 0x11e55c (fun s => s.RIP = 0x11e55c) (addR64R64Effect 0x11e55c 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[1552, 1515]
    (.letOp (n := 1560) (.out 0x11e55f (movR64R64Effect 0x11e55f 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[1557]
    (.letOp (n := 1561) (.exec 0x11e55f (fun s => s.RIP = 0x11e55f) (movR64R64Effect 0x11e55f 8 7) (Reg.operands [.gpr 7] [])) #v[1557]
    (b_l11d880_36)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_35 : List UInt8 :=
  [0x4C, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0xC1, 0xE9, 0x34, 0x48, 0xB8, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xC8, 0x4C, 0x89, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x01, 0xD1, 0x48, 0x03, 0xBC, 0x24, 0x90, 0x00,
    0x00, 0x00, 0x4C, 0x13, 0x4C, 0x24, 0x78, 0x4C, 0x01, 0xFF, 0x4C, 0x13, 0x4C, 0x24, 0x20, 0x4C,
    0x01, 0xE7, 0x49, 0x11, 0xD9, 0x48, 0x01, 0xEF, 0x4D, 0x11, 0xD9, 0x48, 0x01, 0xC7, 0x49, 0x11,
    0xC9, 0x48, 0x01, 0xF7, 0x49, 0x89, 0xF8] ++ bytes_l11d880_36

theorem code_l11d880_35 : ∀ x ∈ codeRange 0x11e50b bytes_l11d880_35, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e50b 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_36

def b_l11d880_34 : Block Op Label signature Reg.count 1473 :=
  .letOp (n := 1473) (.out 0x11e4c2 (mulR64Effect 0x11e4c2 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[1441, 1471]
    (.letOp (n := 1474) (.out 0x11e4c2 (mulR64Effect 0x11e4c2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[1441, 1471]
    (.letOp (n := 1475) (.exec 0x11e4c2 (fun s => s.RIP = 0x11e4c2) (mulR64Effect 0x11e4c2 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1441, 1471]
    (.letOp (n := 1476) (.exec 0x11e4c5 (StorePre 0x11e4c5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11e4c5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e4c5 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1474, 4]
    (.letOp (n := 1477) (.exec 0x11e4ca (StorePre 0x11e4ca 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11e4ca + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e4ca 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1473, 4]
    (.letOp (n := 1478) (.out 0x11e4d2 (movR64R64Effect 0x11e4d2 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[1385]
    (.letOp (n := 1479) (.exec 0x11e4d2 (fun s => s.RIP = 0x11e4d2) (movR64R64Effect 0x11e4d2 0 15) (Reg.operands [.gpr 15] [])) #v[1385]
    (.letOp (n := 1480) (.out 0x11e4d5 (mulM64Effect 0x11e4d5 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1478, 4]
    (.letOp (n := 1481) (.out 0x11e4d5 (mulM64Effect 0x11e4d5 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1478, 4]
    (.letOp (n := 1482) (.exec 0x11e4d5 (LoadPre 0x11e4d5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11e4d5 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e4d5 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1478, 4]
    (.letOp (n := 1483) (.out 0x11e4da (movR64R64Effect 0x11e4da 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[1480]
    (.letOp (n := 1484) (.exec 0x11e4da (fun s => s.RIP = 0x11e4da) (movR64R64Effect 0x11e4da 7 0) (Reg.operands [.gpr 0] [])) #v[1480]
    (.letOp (n := 1485) (.out 0x11e4dd (movR64R64Effect 0x11e4dd 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[1481]
    (.letOp (n := 1486) (.exec 0x11e4dd (fun s => s.RIP = 0x11e4dd) (movR64R64Effect 0x11e4dd 9 2) (Reg.operands [.gpr 2] [])) #v[1481]
    (.letOp (n := 1487) (.out 0x11e4e0 (movR64R64Effect 0x11e4e0 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[1401]
    (.letOp (n := 1488) (.exec 0x11e4e0 (fun s => s.RIP = 0x11e4e0) (movR64R64Effect 0x11e4e0 0 14) (Reg.operands [.gpr 14] [])) #v[1401]
    (.letOp (n := 1489) (.out 0x11e4e3 (movR64M64Effect 0x11e4e3 14 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 1490) (.exec 0x11e4e3 (LoadPre 0x11e4e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11e4e3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e4e3 14 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1491) (.out 0x11e4e8 (mulR64Effect 0x11e4e8 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[1489, 1487]
    (.letOp (n := 1492) (.out 0x11e4e8 (mulR64Effect 0x11e4e8 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[1489, 1487]
    (.letOp (n := 1493) (.exec 0x11e4e8 (fun s => s.RIP = 0x11e4e8) (mulR64Effect 0x11e4e8 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1489, 1487]
    (.letOp (n := 1494) (.exec 0x11e4eb (StorePre 0x11e4eb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e4eb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e4eb 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1492, 4]
    (.letOp (n := 1495) (.out 0x11e4f0 (movR64R64Effect 0x11e4f0 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1491]
    (.letOp (n := 1496) (.exec 0x11e4f0 (fun s => s.RIP = 0x11e4f0) (movR64R64Effect 0x11e4f0 15 0) (Reg.operands [.gpr 0] [])) #v[1491]
    (.letOp (n := 1497) (.out 0x11e4f3 (movR64R64Effect 0x11e4f3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[1419]
    (.letOp (n := 1498) (.exec 0x11e4f3 (fun s => s.RIP = 0x11e4f3) (movR64R64Effect 0x11e4f3 0 12) (Reg.operands [.gpr 12] [])) #v[1419]
    (.letOp (n := 1499) (.out 0x11e4f6 (mulR64Effect 0x11e4f6 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[1405, 1497]
    (.letOp (n := 1500) (.out 0x11e4f6 (mulR64Effect 0x11e4f6 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[1405, 1497]
    (.letOp (n := 1501) (.exec 0x11e4f6 (fun s => s.RIP = 0x11e4f6) (mulR64Effect 0x11e4f6 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1405, 1497]
    (.letOp (n := 1502) (.out 0x11e4f9 (movR64R64Effect 0x11e4f9 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[1500]
    (.letOp (n := 1503) (.exec 0x11e4f9 (fun s => s.RIP = 0x11e4f9) (movR64R64Effect 0x11e4f9 3 2) (Reg.operands [.gpr 2] [])) #v[1500]
    (.letOp (n := 1504) (.out 0x11e4fc (movR64R64Effect 0x11e4fc 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[1499]
    (.letOp (n := 1505) (.exec 0x11e4fc (fun s => s.RIP = 0x11e4fc) (movR64R64Effect 0x11e4fc 12 0) (Reg.operands [.gpr 0] [])) #v[1499]
    (.letOp (n := 1506) (.out 0x11e4ff (movR64R64Effect 0x11e4ff 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1437]
    (.letOp (n := 1507) (.exec 0x11e4ff (fun s => s.RIP = 0x11e4ff) (movR64R64Effect 0x11e4ff 0 5) (Reg.operands [.gpr 5] [])) #v[1437]
    (.letOp (n := 1508) (.out 0x11e502 (mulR64Effect 0x11e502 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[1423, 1506]
    (.letOp (n := 1509) (.out 0x11e502 (mulR64Effect 0x11e502 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[1423, 1506]
    (.letOp (n := 1510) (.exec 0x11e502 (fun s => s.RIP = 0x11e502) (mulR64Effect 0x11e502 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1423, 1506]
    (.letOp (n := 1511) (.out 0x11e505 (movR64R64Effect 0x11e505 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[1508]
    (.letOp (n := 1512) (.exec 0x11e505 (fun s => s.RIP = 0x11e505) (movR64R64Effect 0x11e505 5 0) (Reg.operands [.gpr 0] [])) #v[1508]
    (.letOp (n := 1513) (.out 0x11e508 (movR64R64Effect 0x11e508 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[1509]
    (.letOp (n := 1514) (.exec 0x11e508 (fun s => s.RIP = 0x11e508) (movR64R64Effect 0x11e508 11 2) (Reg.operands [.gpr 2] [])) #v[1509]
    (b_l11d880_35))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_34 : List UInt8 :=
  [0x49, 0xF7, 0xE1, 0x48, 0x89, 0x54, 0x24, 0x78, 0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x4C, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x38, 0x48, 0x89, 0xC7, 0x49, 0x89, 0xD1, 0x4C, 0x89,
    0xF0, 0x4C, 0x8B, 0x74, 0x24, 0x70, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0x54, 0x24, 0x20, 0x49, 0x89,
    0xC7, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC4, 0x48, 0x89, 0xE8,
    0x49, 0xF7, 0xE5, 0x48, 0x89, 0xC5, 0x49, 0x89, 0xD3] ++ bytes_l11d880_35

theorem code_l11d880_34 : ∀ x ∈ codeRange 0x11e4c2 bytes_l11d880_34, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e4c2 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_35

def b_l11d880_33 : Block Op Label signature Reg.count 1430 :=
  .letOp (n := 1430) (.out 0x11e46d (movR64R64Effect 0x11e46d 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[1425]
    (.letOp (n := 1431) (.exec 0x11e46d (fun s => s.RIP = 0x11e46d) (movR64R64Effect 0x11e46d 8 0) (Reg.operands [.gpr 0] [])) #v[1425]
    (.letOp (n := 1432) (.out 0x11e470 (addR64R64Effect 0x11e470 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[1430, 1414]
    (.letOp (n := 1433) (.out 0x11e470 (addR64R64Effect 0x11e470 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[1430, 1414]
    (.letOp (n := 1434) (.exec 0x11e470 (fun s => s.RIP = 0x11e470) (addR64R64Effect 0x11e470 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[1430, 1414]
    (.letOp (n := 1435) (.out 0x11e473 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e473 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[1428, 1417, 1433]
    (.letOp (n := 1436) (.exec 0x11e473 (fun s => s.RIP = 0x11e473) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e473 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1428, 1417, 1433]
    (.letOp (n := 1437) (.out 0x11e476 (movR64M64Effect 0x11e476 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 1438) (.exec 0x11e476 (LoadPre 0x11e476 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11e476 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e476 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1439) (.out 0x11e47b (movR64R64Effect 0x11e47b 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1437]
    (.letOp (n := 1440) (.exec 0x11e47b (fun s => s.RIP = 0x11e47b) (movR64R64Effect 0x11e47b 0 5) (Reg.operands [.gpr 5] [])) #v[1437]
    (.letOp (n := 1441) (.out 0x11e47e (movR64M64Effect 0x11e47e 9 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 1442) (.exec 0x11e47e (LoadPre 0x11e47e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11e47e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e47e 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1443) (.out 0x11e483 (mulR64Effect 0x11e483 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[1441, 1439]
    (.letOp (n := 1444) (.out 0x11e483 (mulR64Effect 0x11e483 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[1441, 1439]
    (.letOp (n := 1445) (.exec 0x11e483 (fun s => s.RIP = 0x11e483) (mulR64Effect 0x11e483 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1441, 1439]
    (.letOp (n := 1446) (.out 0x11e486 (movR64R64Effect 0x11e486 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1444]
    (.letOp (n := 1447) (.exec 0x11e486 (fun s => s.RIP = 0x11e486) (movR64R64Effect 0x11e486 1 2) (Reg.operands [.gpr 2] [])) #v[1444]
    (.letOp (n := 1448) (.out 0x11e489 (movR64R64Effect 0x11e489 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[1444]
    (.letOp (n := 1449) (.exec 0x11e489 (fun s => s.RIP = 0x11e489) (movR64R64Effect 0x11e489 10 2) (Reg.operands [.gpr 2] [])) #v[1444]
    (.letOp (n := 1450) (.out 0x11e48c (shldR64R64Effect 0x11e48c 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[1448, 1443]
    (.letOp (n := 1451) (.exec 0x11e48c (fun s => s.RIP = 0x11e48c) (shldR64R64Effect 0x11e48c 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1448, 1443]
    (.letOp (n := 1452) (.out 0x11e491 (movR64Imm64Effect 0x11e491 2 0xffffffffffffe) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1453) (.exec 0x11e491 (fun s => s.RIP = 0x11e491) (movR64Imm64Effect 0x11e491 2 0xffffffffffffe) (Reg.operands [] [])) #v[]
    (.letOp (n := 1454) (.out 0x11e49b (andR64R64Effect 0x11e49b 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1443, 1452]
    (.letOp (n := 1455) (.exec 0x11e49b (fun s => s.RIP = 0x11e49b) (andR64R64Effect 0x11e49b 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1443, 1452]
    (.letOp (n := 1456) (.out 0x11e49e (movR64Imm64Effect 0x11e49e 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1457) (.exec 0x11e49e (fun s => s.RIP = 0x11e49e) (movR64Imm64Effect 0x11e49e 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1458) (.out 0x11e4a8 (mulR64Effect 0x11e4a8 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1456, 1454]
    (.letOp (n := 1459) (.out 0x11e4a8 (mulR64Effect 0x11e4a8 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1456, 1454]
    (.letOp (n := 1460) (.exec 0x11e4a8 (fun s => s.RIP = 0x11e4a8) (mulR64Effect 0x11e4a8 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1456, 1454]
    (.letOp (n := 1461) (.out 0x11e4ab (movR64R64Effect 0x11e4ab 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1459]
    (.letOp (n := 1462) (.exec 0x11e4ab (fun s => s.RIP = 0x11e4ab) (movR64R64Effect 0x11e4ab 6 2) (Reg.operands [.gpr 2] [])) #v[1459]
    (.letOp (n := 1463) (.out 0x11e4ae (addR64R64Effect 0x11e4ae 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[1458, 1432]
    (.letOp (n := 1464) (.out 0x11e4ae (addR64R64Effect 0x11e4ae 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[1458, 1432]
    (.letOp (n := 1465) (.exec 0x11e4ae (fun s => s.RIP = 0x11e4ae) (addR64R64Effect 0x11e4ae 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[1458, 1432]
    (.letOp (n := 1466) (.out 0x11e4b1 (movR64R64Effect 0x11e4b1 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[1463]
    (.letOp (n := 1467) (.exec 0x11e4b1 (fun s => s.RIP = 0x11e4b1) (movR64R64Effect 0x11e4b1 8 0) (Reg.operands [.gpr 0] [])) #v[1463]
    (.letOp (n := 1468) (.exec 0x11e4b4 (StorePre 0x11e4b4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x11e4b4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e4b4 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1463, 4]
    (.letOp (n := 1469) (.out 0x11e4bc (atFlags StatusFlags.CF (adcR64R64Effect 0x11e4bc 6 7)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[1461, 1435, 1464]
    (.letOp (n := 1470) (.exec 0x11e4bc (fun s => s.RIP = 0x11e4bc) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e4bc 6 7)) (Reg.operands [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1461, 1435, 1464]
    (.letOp (n := 1471) (.out 0x11e4bf (movR64R64Effect 0x11e4bf 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[1366]
    (.letOp (n := 1472) (.exec 0x11e4bf (fun s => s.RIP = 0x11e4bf) (movR64R64Effect 0x11e4bf 0 11) (Reg.operands [.gpr 11] [])) #v[1366]
    (b_l11d880_34)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_33 : List UInt8 :=
  [0x49, 0x89, 0xC0, 0x49, 0x01, 0xF0, 0x48, 0x11, 0xCF, 0x48, 0x8B, 0x6C, 0x24, 0x10, 0x48, 0x89,
    0xE8, 0x4C, 0x8B, 0x4C, 0x24, 0x08, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xD2, 0x49,
    0x0F, 0xA4, 0xC2, 0x0C, 0x48, 0xBA, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21,
    0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x89,
    0xD6, 0x4C, 0x01, 0xC0, 0x49, 0x89, 0xC0, 0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48,
    0x11, 0xFE, 0x4C, 0x89, 0xD8] ++ bytes_l11d880_34

theorem code_l11d880_33 : ∀ x ∈ codeRange 0x11e46d bytes_l11d880_33, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e46d 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_34

def b_l11d880_32 : Block Op Label signature Reg.count 1385 :=
  .letOp (n := 1385) (.out 0x11e41c (movR64M64Effect 0x11e41c 15 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 1386) (.exec 0x11e41c (LoadPre 0x11e41c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11e41c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e41c 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1387) (.out 0x11e421 (movR64R64Effect 0x11e421 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[1385]
    (.letOp (n := 1388) (.exec 0x11e421 (fun s => s.RIP = 0x11e421) (movR64R64Effect 0x11e421 0 15) (Reg.operands [.gpr 15] [])) #v[1385]
    (.letOp (n := 1389) (.out 0x11e424 (mulM64Effect 0x11e424 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1387, 4]
    (.letOp (n := 1390) (.out 0x11e424 (mulM64Effect 0x11e424 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1387, 4]
    (.letOp (n := 1391) (.exec 0x11e424 (LoadPre 0x11e424 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11e424 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e424 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1387, 4]
    (.letOp (n := 1392) (.out 0x11e429 (movR64R64Effect 0x11e429 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[1390]
    (.letOp (n := 1393) (.exec 0x11e429 (fun s => s.RIP = 0x11e429) (movR64R64Effect 0x11e429 7 2) (Reg.operands [.gpr 2] [])) #v[1390]
    (.letOp (n := 1394) (.out 0x11e42c (movR64R64Effect 0x11e42c 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[1389]
    (.letOp (n := 1395) (.exec 0x11e42c (fun s => s.RIP = 0x11e42c) (movR64R64Effect 0x11e42c 8 0) (Reg.operands [.gpr 0] [])) #v[1389]
    (.letOp (n := 1396) (.out 0x11e42f (addR64R64Effect 0x11e42f 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[1394, 1373]
    (.letOp (n := 1397) (.out 0x11e42f (addR64R64Effect 0x11e42f 8 1) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 1] []) (.flag .CF)) #v[1394, 1373]
    (.letOp (n := 1398) (.exec 0x11e42f (fun s => s.RIP = 0x11e42f) (addR64R64Effect 0x11e42f 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[1394, 1373]
    (.letOp (n := 1399) (.out 0x11e432 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e432 7 6)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[1392, 1375, 1397]
    (.letOp (n := 1400) (.exec 0x11e432 (fun s => s.RIP = 0x11e432) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e432 7 6)) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1392, 1375, 1397]
    (.letOp (n := 1401) (.out 0x11e435 (movR64M64Effect 0x11e435 14 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 1402) (.exec 0x11e435 (LoadPre 0x11e435 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11e435 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e435 14 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1403) (.out 0x11e43d (movR64R64Effect 0x11e43d 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[1401]
    (.letOp (n := 1404) (.exec 0x11e43d (fun s => s.RIP = 0x11e43d) (movR64R64Effect 0x11e43d 0 14) (Reg.operands [.gpr 14] [])) #v[1401]
    (.letOp (n := 1405) (.out 0x11e440 (movR64M64Effect 0x11e440 3 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1406) (.exec 0x11e440 (LoadPre 0x11e440 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11e440 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e440 3 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1407) (.out 0x11e448 (mulR64Effect 0x11e448 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[1405, 1403]
    (.letOp (n := 1408) (.out 0x11e448 (mulR64Effect 0x11e448 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[1405, 1403]
    (.letOp (n := 1409) (.exec 0x11e448 (fun s => s.RIP = 0x11e448) (mulR64Effect 0x11e448 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1405, 1403]
    (.letOp (n := 1410) (.out 0x11e44b (movR64R64Effect 0x11e44b 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1408]
    (.letOp (n := 1411) (.exec 0x11e44b (fun s => s.RIP = 0x11e44b) (movR64R64Effect 0x11e44b 1 2) (Reg.operands [.gpr 2] [])) #v[1408]
    (.letOp (n := 1412) (.out 0x11e44e (movR64R64Effect 0x11e44e 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1407]
    (.letOp (n := 1413) (.exec 0x11e44e (fun s => s.RIP = 0x11e44e) (movR64R64Effect 0x11e44e 6 0) (Reg.operands [.gpr 0] [])) #v[1407]
    (.letOp (n := 1414) (.out 0x11e451 (addR64R64Effect 0x11e451 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[1412, 1396]
    (.letOp (n := 1415) (.out 0x11e451 (addR64R64Effect 0x11e451 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[1412, 1396]
    (.letOp (n := 1416) (.exec 0x11e451 (fun s => s.RIP = 0x11e451) (addR64R64Effect 0x11e451 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[1412, 1396]
    (.letOp (n := 1417) (.out 0x11e454 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e454 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1410, 1399, 1415]
    (.letOp (n := 1418) (.exec 0x11e454 (fun s => s.RIP = 0x11e454) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e454 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1410, 1399, 1415]
    (.letOp (n := 1419) (.out 0x11e457 (movR64M64Effect 0x11e457 12 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 1420) (.exec 0x11e457 (LoadPre 0x11e457 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11e457 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e457 12 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1421) (.out 0x11e45f (movR64R64Effect 0x11e45f 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[1419]
    (.letOp (n := 1422) (.exec 0x11e45f (fun s => s.RIP = 0x11e45f) (movR64R64Effect 0x11e45f 0 12) (Reg.operands [.gpr 12] [])) #v[1419]
    (.letOp (n := 1423) (.out 0x11e462 (movR64M64Effect 0x11e462 13 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 1424) (.exec 0x11e462 (LoadPre 0x11e462 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11e462 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e462 13 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1425) (.out 0x11e467 (mulR64Effect 0x11e467 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[1423, 1421]
    (.letOp (n := 1426) (.out 0x11e467 (mulR64Effect 0x11e467 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[1423, 1421]
    (.letOp (n := 1427) (.exec 0x11e467 (fun s => s.RIP = 0x11e467) (mulR64Effect 0x11e467 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1423, 1421]
    (.letOp (n := 1428) (.out 0x11e46a (movR64R64Effect 0x11e46a 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[1426]
    (.letOp (n := 1429) (.exec 0x11e46a (fun s => s.RIP = 0x11e46a) (movR64R64Effect 0x11e46a 7 2) (Reg.operands [.gpr 2] [])) #v[1426]
    (b_l11d880_33)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_32 : List UInt8 :=
  [0x4C, 0x8B, 0x7C, 0x24, 0x18, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x70, 0x48, 0x89, 0xD7,
    0x49, 0x89, 0xC0, 0x49, 0x01, 0xC8, 0x48, 0x11, 0xF7, 0x4C, 0x8B, 0xB4, 0x24, 0x80, 0x00, 0x00,
    0x00, 0x4C, 0x89, 0xF0, 0x48, 0x8B, 0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE3, 0x48,
    0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x01, 0xC6, 0x48, 0x11, 0xF9, 0x4C, 0x8B, 0xA4, 0x24, 0xF8,
    0x00, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x4C, 0x8B, 0x6C, 0x24, 0x68, 0x49, 0xF7, 0xE5, 0x48, 0x89,
    0xD7] ++ bytes_l11d880_33

theorem code_l11d880_32 : ∀ x ∈ codeRange 0x11e41c bytes_l11d880_32, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e41c 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_33

def b_l11d880_31 : Block Op Label signature Reg.count 1349 :=
  .letOp (n := 1349) (.out 0x11e3b1 (movR64R64Effect 0x11e3b1 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1345]
    (.letOp (n := 1350) (.exec 0x11e3b1 (fun s => s.RIP = 0x11e3b1) (movR64R64Effect 0x11e3b1 2 1) (Reg.operands [.gpr 1] [])) #v[1345]
    (.letOp (n := 1351) (.out 0x11e3b4 (movR64R64Effect 0x11e3b4 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1345]
    (.letOp (n := 1352) (.exec 0x11e3b4 (fun s => s.RIP = 0x11e3b4) (movR64R64Effect 0x11e3b4 7 1) (Reg.operands [.gpr 1] [])) #v[1345]
    (.letOp (n := 1353) (.out 0x11e3b7 (shrR64Effect 0x11e3b7 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1349]
    (.letOp (n := 1354) (.exec 0x11e3b7 (fun s => s.RIP = 0x11e3b7) (shrR64Effect 0x11e3b7 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1349]
    (.letOp (n := 1355) (.out 0x11e3bb (addR64R64Effect 0x11e3bb 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1353, 1347]
    (.letOp (n := 1356) (.exec 0x11e3bb (fun s => s.RIP = 0x11e3bb) (addR64R64Effect 0x11e3bb 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1353, 1347]
    (.letOp (n := 1357) (.exec 0x11e3be (StorePre 0x11e3be 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x11e3be + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e3be 2 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1355, 4]
    (.letOp (n := 1358) (.out 0x11e3c6 (movR64Imm64Effect 0x11e3c6 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1359) (.exec 0x11e3c6 (fun s => s.RIP = 0x11e3c6) (movR64Imm64Effect 0x11e3c6 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1360) (.out 0x11e3d0 (andR64R64Effect 0x11e3d0 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[1317, 1358]
    (.letOp (n := 1361) (.exec 0x11e3d0 (fun s => s.RIP = 0x11e3d0) (andR64R64Effect 0x11e3d0 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1317, 1358]
    (.letOp (n := 1362) (.exec 0x11e3d3 (StorePre 0x11e3d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11e3d3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e3d3 8 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1360, 4]
    (.letOp (n := 1363) (.out 0x11e3db (andR64R64Effect 0x11e3db 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[1327, 1358]
    (.letOp (n := 1364) (.exec 0x11e3db (fun s => s.RIP = 0x11e3db) (andR64R64Effect 0x11e3db 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1327, 1358]
    (.letOp (n := 1365) (.exec 0x11e3de (StorePre 0x11e3de 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x11e3de + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e3de 9 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[1363, 4]
    (.letOp (n := 1366) (.out 0x11e3e6 (movR64M64Effect 0x11e3e6 11 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 1367) (.exec 0x11e3e6 (LoadPre 0x11e3e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11e3e6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e3e6 11 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1368) (.out 0x11e3ee (movR64R64Effect 0x11e3ee 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[1366]
    (.letOp (n := 1369) (.exec 0x11e3ee (fun s => s.RIP = 0x11e3ee) (movR64R64Effect 0x11e3ee 0 11) (Reg.operands [.gpr 11] [])) #v[1366]
    (.letOp (n := 1370) (.out 0x11e3f1 (mulM64Effect 0x11e3f1 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1368, 4]
    (.letOp (n := 1371) (.out 0x11e3f1 (mulM64Effect 0x11e3f1 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1368, 4]
    (.letOp (n := 1372) (.exec 0x11e3f1 (LoadPre 0x11e3f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11e3f1 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e3f1 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1368, 4]
    (.letOp (n := 1373) (.out 0x11e3f6 (movR64R64Effect 0x11e3f6 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1370]
    (.letOp (n := 1374) (.exec 0x11e3f6 (fun s => s.RIP = 0x11e3f6) (movR64R64Effect 0x11e3f6 1 0) (Reg.operands [.gpr 0] [])) #v[1370]
    (.letOp (n := 1375) (.out 0x11e3f9 (movR64R64Effect 0x11e3f9 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1371]
    (.letOp (n := 1376) (.exec 0x11e3f9 (fun s => s.RIP = 0x11e3f9) (movR64R64Effect 0x11e3f9 6 2) (Reg.operands [.gpr 2] [])) #v[1371]
    (.letOp (n := 1377) (.out 0x11e3fc (movR64Imm64Effect 0x11e3fc 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1378) (.exec 0x11e3fc (fun s => s.RIP = 0x11e3fc) (movR64Imm64Effect 0x11e3fc 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1379) (.out 0x11e406 (andR64R64Effect 0x11e406 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[1341, 1377]
    (.letOp (n := 1380) (.exec 0x11e406 (fun s => s.RIP = 0x11e406) (andR64R64Effect 0x11e406 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[1341, 1377]
    (.letOp (n := 1381) (.exec 0x11e409 (StorePre 0x11e409 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11e409 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e409 10 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[1379, 4]
    (.letOp (n := 1382) (.out 0x11e411 (andR64R64Effect 0x11e411 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[1351, 1377]
    (.letOp (n := 1383) (.exec 0x11e411 (fun s => s.RIP = 0x11e411) (andR64R64Effect 0x11e411 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1351, 1377]
    (.letOp (n := 1384) (.exec 0x11e414 (StorePre 0x11e414 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11e414 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e414 7 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1382, 4]
    (b_l11d880_32))))))))))))))))))))))))))))))))))))

def bytes_l11d880_31 : List UInt8 :=
  [0x48, 0x89, 0xCA, 0x48, 0x89, 0xCF, 0x48, 0xC1, 0xEA, 0x34, 0x48, 0x01, 0xC2, 0x48, 0x89, 0x94,
    0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49,
    0x21, 0xC0, 0x4C, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x49, 0x21, 0xC1, 0x4C, 0x89, 0x8C,
    0x24, 0x08, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xD8,
    0x48, 0xF7, 0x64, 0x24, 0x38, 0x48, 0x89, 0xC1, 0x48, 0x89, 0xD6, 0x48, 0xB8, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xC2, 0x4C, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00,
    0x48, 0x21, 0xC7, 0x48, 0x89, 0xBC, 0x24, 0xE8, 0x00, 0x00, 0x00] ++ bytes_l11d880_32

theorem code_l11d880_31 : ∀ x ∈ codeRange 0x11e3b1 bytes_l11d880_31, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e3b1 107 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_32

def b_l11d880_30 : Block Op Label signature Reg.count 1309 :=
  .letOp (n := 1309) (.out 0x11e35e (leaR64Effect 0x11e35e 2 (.sib 2 (some 2) 1 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[1307, 1307]
    (.letOp (n := 1310) (.exec 0x11e35e (fun s => s.RIP = 0x11e35e) (leaR64Effect 0x11e35e 2 (.sib 2 (some 2) 1 .none)) (Reg.operands [.gpr 2, .gpr 2] [])) #v[1307, 1307]
    (.letOp (n := 1311) (.out 0x11e362 (leaR64Effect 0x11e362 6 (.sib 1 (some 2) 3 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1, .gpr 2] []) (.reg (.gpr 6))) #v[1305, 1309]
    (.letOp (n := 1312) (.exec 0x11e362 (fun s => s.RIP = 0x11e362) (leaR64Effect 0x11e362 6 (.sib 1 (some 2) 3 .none)) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1305, 1309]
    (.letOp (n := 1313) (.out 0x11e366 (leaR64Effect 0x11e366 1 (.sib 12 (some 12) 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12, .gpr 12] []) (.reg (.gpr 1))) #v[1203, 1203]
    (.letOp (n := 1314) (.exec 0x11e366 (fun s => s.RIP = 0x11e366) (leaR64Effect 0x11e366 1 (.sib 12 (some 12) 1 .none)) (Reg.operands [.gpr 12, .gpr 12] [])) #v[1203, 1203]
    (.letOp (n := 1315) (.out 0x11e36a (movR64R64Effect 0x11e36a 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[1311]
    (.letOp (n := 1316) (.exec 0x11e36a (fun s => s.RIP = 0x11e36a) (movR64R64Effect 0x11e36a 2 6) (Reg.operands [.gpr 6] [])) #v[1311]
    (.letOp (n := 1317) (.out 0x11e36d (movR64R64Effect 0x11e36d 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[1311]
    (.letOp (n := 1318) (.exec 0x11e36d (fun s => s.RIP = 0x11e36d) (movR64R64Effect 0x11e36d 8 6) (Reg.operands [.gpr 6] [])) #v[1311]
    (.letOp (n := 1319) (.out 0x11e370 (shrR64Effect 0x11e370 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1315]
    (.letOp (n := 1320) (.exec 0x11e370 (fun s => s.RIP = 0x11e370) (shrR64Effect 0x11e370 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1315]
    (.letOp (n := 1321) (.out 0x11e374 (leaR64Effect 0x11e374 6 (.sib 2 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2, .gpr 1] []) (.reg (.gpr 6))) #v[1319, 1313]
    (.letOp (n := 1322) (.exec 0x11e374 (fun s => s.RIP = 0x11e374) (leaR64Effect 0x11e374 6 (.sib 2 (some 1) 3 .none)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[1319, 1313]
    (.letOp (n := 1323) (.out 0x11e378 (leaR64Effect 0x11e378 1 (.sib 7 (some 7) 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7, .gpr 7] []) (.reg (.gpr 1))) #v[1273, 1273]
    (.letOp (n := 1324) (.exec 0x11e378 (fun s => s.RIP = 0x11e378) (leaR64Effect 0x11e378 1 (.sib 7 (some 7) 1 .none)) (Reg.operands [.gpr 7, .gpr 7] [])) #v[1273, 1273]
    (.letOp (n := 1325) (.out 0x11e37c (movR64R64Effect 0x11e37c 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[1321]
    (.letOp (n := 1326) (.exec 0x11e37c (fun s => s.RIP = 0x11e37c) (movR64R64Effect 0x11e37c 2 6) (Reg.operands [.gpr 6] [])) #v[1321]
    (.letOp (n := 1327) (.out 0x11e37f (movR64R64Effect 0x11e37f 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[1321]
    (.letOp (n := 1328) (.exec 0x11e37f (fun s => s.RIP = 0x11e37f) (movR64R64Effect 0x11e37f 9 6) (Reg.operands [.gpr 6] [])) #v[1321]
    (.letOp (n := 1329) (.out 0x11e382 (shrR64Effect 0x11e382 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1325]
    (.letOp (n := 1330) (.exec 0x11e382 (fun s => s.RIP = 0x11e382) (shrR64Effect 0x11e382 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1325]
    (.letOp (n := 1331) (.out 0x11e386 (leaR64Effect 0x11e386 6 (.sib 2 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2, .gpr 1] []) (.reg (.gpr 6))) #v[1329, 1323]
    (.letOp (n := 1332) (.exec 0x11e386 (fun s => s.RIP = 0x11e386) (leaR64Effect 0x11e386 6 (.sib 2 (some 1) 3 .none)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[1329, 1323]
    (.letOp (n := 1333) (.out 0x11e38a (movR64Imm64Effect 0x11e38a 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1334) (.exec 0x11e38a (fun s => s.RIP = 0x11e38a) (movR64Imm64Effect 0x11e38a 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1335) (.out 0x11e394 (andR64R64Effect 0x11e394 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[1282, 1333]
    (.letOp (n := 1336) (.exec 0x11e394 (fun s => s.RIP = 0x11e394) (andR64R64Effect 0x11e394 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[1282, 1333]
    (.letOp (n := 1337) (.out 0x11e397 (leaR64Effect 0x11e397 1 (.sib 15 (some 15) 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15, .gpr 15] []) (.reg (.gpr 1))) #v[1335, 1335]
    (.letOp (n := 1338) (.exec 0x11e397 (fun s => s.RIP = 0x11e397) (leaR64Effect 0x11e397 1 (.sib 15 (some 15) 1 .none)) (Reg.operands [.gpr 15, .gpr 15] [])) #v[1335, 1335]
    (.letOp (n := 1339) (.out 0x11e39b (movR64R64Effect 0x11e39b 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[1331]
    (.letOp (n := 1340) (.exec 0x11e39b (fun s => s.RIP = 0x11e39b) (movR64R64Effect 0x11e39b 2 6) (Reg.operands [.gpr 6] [])) #v[1331]
    (.letOp (n := 1341) (.out 0x11e39e (movR64R64Effect 0x11e39e 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[1331]
    (.letOp (n := 1342) (.exec 0x11e39e (fun s => s.RIP = 0x11e39e) (movR64R64Effect 0x11e39e 10 6) (Reg.operands [.gpr 6] [])) #v[1331]
    (.letOp (n := 1343) (.out 0x11e3a1 (shrR64Effect 0x11e3a1 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1339]
    (.letOp (n := 1344) (.exec 0x11e3a1 (fun s => s.RIP = 0x11e3a1) (shrR64Effect 0x11e3a1 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1339]
    (.letOp (n := 1345) (.out 0x11e3a5 (leaR64Effect 0x11e3a5 1 (.sib 2 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 1] []) (.reg (.gpr 1))) #v[1343, 1337]
    (.letOp (n := 1346) (.exec 0x11e3a5 (fun s => s.RIP = 0x11e3a5) (leaR64Effect 0x11e3a5 1 (.sib 2 (some 1) 3 .none)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[1343, 1337]
    (.letOp (n := 1347) (.out 0x11e3a9 (andR64M64Effect 0x11e3a9 0 (.sib 4 none 0 (.d32 0x1c8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1297, 4]
    (.letOp (n := 1348) (.exec 0x11e3a9 (LoadPre 0x11e3a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x11e3a9 + BitVec.ofNat 64 8)) 8) (andR64M64Effect 0x11e3a9 0 (.sib 4 none 0 (.d32 0x1c8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1297, 4]
    (b_l11d880_31))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_30 : List UInt8 :=
  [0x48, 0x8D, 0x14, 0x52, 0x48, 0x8D, 0x34, 0xD1, 0x4B, 0x8D, 0x0C, 0x64, 0x48, 0x89, 0xF2, 0x49,
    0x89, 0xF0, 0x48, 0xC1, 0xEA, 0x34, 0x48, 0x8D, 0x34, 0xCA, 0x48, 0x8D, 0x0C, 0x7F, 0x48, 0x89,
    0xF2, 0x49, 0x89, 0xF1, 0x48, 0xC1, 0xEA, 0x34, 0x48, 0x8D, 0x34, 0xCA, 0x48, 0xB9, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xCF, 0x4B, 0x8D, 0x0C, 0x7F, 0x48, 0x89, 0xF2,
    0x49, 0x89, 0xF2, 0x48, 0xC1, 0xEA, 0x34, 0x48, 0x8D, 0x0C, 0xCA, 0x48, 0x23, 0x84, 0x24, 0xC8,
    0x01, 0x00, 0x00] ++ bytes_l11d880_31

theorem code_l11d880_30 : ∀ x ∈ codeRange 0x11e35e bytes_l11d880_30, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e35e 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_31

def b_l11d880_29 : Block Op Label signature Reg.count 1266 :=
  .letOp (n := 1266) (.out 0x11e2fe (mulR64Effect 0x11e2fe 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1237, 1264]
    (.letOp (n := 1267) (.out 0x11e2fe (mulR64Effect 0x11e2fe 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1237, 1264]
    (.letOp (n := 1268) (.exec 0x11e2fe (fun s => s.RIP = 0x11e2fe) (mulR64Effect 0x11e2fe 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1237, 1264]
    (.letOp (n := 1269) (.out 0x11e301 (shldR64R64Effect 0x11e301 5 6 7 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1260, 1257]
    (.letOp (n := 1270) (.exec 0x11e301 (fun s => s.RIP = 0x11e301) (shldR64R64Effect 0x11e301 5 6 7 12) (Reg.operands [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1260, 1257]
    (.letOp (n := 1271) (.out 0x11e306 (movR64Imm64Effect 0x11e306 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1272) (.exec 0x11e306 (fun s => s.RIP = 0x11e306) (movR64Imm64Effect 0x11e306 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1273) (.out 0x11e310 (andR64R64Effect 0x11e310 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[1257, 1271]
    (.letOp (n := 1274) (.exec 0x11e310 (fun s => s.RIP = 0x11e310) (andR64R64Effect 0x11e310 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[1257, 1271]
    (.letOp (n := 1275) (.out 0x11e313 (andR64R64Effect 0x11e313 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[892, 1271]
    (.letOp (n := 1276) (.exec 0x11e313 (fun s => s.RIP = 0x11e313) (andR64R64Effect 0x11e313 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[892, 1271]
    (.letOp (n := 1277) (.out 0x11e316 (addR64R64Effect 0x11e316 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[1275, 1266]
    (.letOp (n := 1278) (.out 0x11e316 (addR64R64Effect 0x11e316 15 0) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 0] []) (.flag .CF)) #v[1275, 1266]
    (.letOp (n := 1279) (.exec 0x11e316 (fun s => s.RIP = 0x11e316) (addR64R64Effect 0x11e316 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[1275, 1266]
    (.letOp (n := 1280) (.out 0x11e319 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e319 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[1267, 1278]
    (.letOp (n := 1281) (.exec 0x11e319 (fun s => s.RIP = 0x11e319) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e319 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1267, 1278]
    (.letOp (n := 1282) (.out 0x11e31d (addR64R64Effect 0x11e31d 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[1277, 1269]
    (.letOp (n := 1283) (.out 0x11e31d (addR64R64Effect 0x11e31d 15 6) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 6] []) (.flag .CF)) #v[1277, 1269]
    (.letOp (n := 1284) (.exec 0x11e31d (fun s => s.RIP = 0x11e31d) (addR64R64Effect 0x11e31d 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[1277, 1269]
    (.letOp (n := 1285) (.out 0x11e320 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e320 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[1280, 1283]
    (.letOp (n := 1286) (.exec 0x11e320 (fun s => s.RIP = 0x11e320) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e320 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1280, 1283]
    (.letOp (n := 1287) (.out 0x11e324 (shldR64R64Effect 0x11e324 5 2 15 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1285, 1282]
    (.letOp (n := 1288) (.exec 0x11e324 (fun s => s.RIP = 0x11e324) (shldR64R64Effect 0x11e324 5 2 15 12) (Reg.operands [.gpr 2, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1285, 1282]
    (.letOp (n := 1289) (.out 0x11e329 (movR64Imm64Effect 0x11e329 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1290) (.exec 0x11e329 (fun s => s.RIP = 0x11e329) (movR64Imm64Effect 0x11e329 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1291) (.out 0x11e333 (andR64R64Effect 0x11e333 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[978, 1289]
    (.letOp (n := 1292) (.exec 0x11e333 (fun s => s.RIP = 0x11e333) (andR64R64Effect 0x11e333 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[978, 1289]
    (.letOp (n := 1293) (.out 0x11e336 (addR64R64Effect 0x11e336 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[1291, 1287]
    (.letOp (n := 1294) (.exec 0x11e336 (fun s => s.RIP = 0x11e336) (addR64R64Effect 0x11e336 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[1291, 1287]
    (.letOp (n := 1295) (.out 0x11e339 (shlR64Effect 0x11e339 4 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1293]
    (.letOp (n := 1296) (.exec 0x11e339 (fun s => s.RIP = 0x11e339) (shlR64Effect 0x11e339 4 3 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1293]
    (.letOp (n := 1297) (.out 0x11e33d (leaR64Effect 0x11e33d 0 (.sib 3 (some 3) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 3] []) (.reg (.gpr 0))) #v[1295, 1295]
    (.letOp (n := 1298) (.exec 0x11e33d (fun s => s.RIP = 0x11e33d) (leaR64Effect 0x11e33d 0 (.sib 3 (some 3) 1 .none)) (Reg.operands [.gpr 3, .gpr 3] [])) #v[1295, 1295]
    (.letOp (n := 1299) (.out 0x11e341 (movR64R64Effect 0x11e341 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1297]
    (.letOp (n := 1300) (.exec 0x11e341 (fun s => s.RIP = 0x11e341) (movR64R64Effect 0x11e341 1 0) (Reg.operands [.gpr 0] [])) #v[1297]
    (.letOp (n := 1301) (.out 0x11e344 (shrR64Effect 0x11e344 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1299]
    (.letOp (n := 1302) (.exec 0x11e344 (fun s => s.RIP = 0x11e344) (shrR64Effect 0x11e344 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1299]
    (.letOp (n := 1303) (.out 0x11e348 (movR64Imm64Effect 0x11e348 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1304) (.exec 0x11e348 (fun s => s.RIP = 0x11e348) (movR64Imm64Effect 0x11e348 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 1305) (.out 0x11e352 (imulR64R64Effect 0x11e352 4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[1301, 1303]
    (.letOp (n := 1306) (.exec 0x11e352 (fun s => s.RIP = 0x11e352) (imulR64R64Effect 0x11e352 4 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1301, 1303]
    (.letOp (n := 1307) (.out 0x11e356 (movR64M64Effect 0x11e356 2 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 1308) (.exec 0x11e356 (LoadPre 0x11e356 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11e356 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e356 2 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11d880_30)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_29 : List UInt8 :=
  [0x48, 0xF7, 0xE1, 0x48, 0x0F, 0xA4, 0xFE, 0x0C, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x0F, 0x00, 0x48, 0x21, 0xCF, 0x49, 0x21, 0xCF, 0x49, 0x01, 0xC7, 0x48, 0x83, 0xD2, 0x00, 0x49,
    0x01, 0xF7, 0x48, 0x83, 0xD2, 0x00, 0x4C, 0x0F, 0xA4, 0xFA, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x21, 0xC3, 0x48, 0x01, 0xD3, 0x48, 0xC1, 0xE3, 0x03, 0x48,
    0x8D, 0x04, 0x5B, 0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x30, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xCA, 0x48, 0x8B, 0x94, 0x24, 0xD0, 0x00, 0x00, 0x00] ++ bytes_l11d880_30

theorem code_l11d880_29 : ∀ x ∈ codeRange 0x11e2fe bytes_l11d880_29, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e2fe 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_30

def b_l11d880_28 : Block Op Label signature Reg.count 1219 :=
  .letOp (n := 1219) (.out 0x11e2a6 (movR64R64Effect 0x11e2a6 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[1216]
    (.letOp (n := 1220) (.exec 0x11e2a6 (fun s => s.RIP = 0x11e2a6) (movR64R64Effect 0x11e2a6 11 0) (Reg.operands [.gpr 0] [])) #v[1216]
    (.letOp (n := 1221) (.out 0x11e2a9 (addR64R64Effect 0x11e2a9 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[1219, 1210]
    (.letOp (n := 1222) (.out 0x11e2a9 (addR64R64Effect 0x11e2a9 11 8) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 8] []) (.flag .CF)) #v[1219, 1210]
    (.letOp (n := 1223) (.exec 0x11e2a9 (fun s => s.RIP = 0x11e2a9) (addR64R64Effect 0x11e2a9 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[1219, 1210]
    (.letOp (n := 1224) (.out 0x11e2ac (atFlags StatusFlags.CF (adcR64R64Effect 0x11e2ac 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1212, 1217, 1222]
    (.letOp (n := 1225) (.exec 0x11e2ac (fun s => s.RIP = 0x11e2ac) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e2ac 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1212, 1217, 1222]
    (.letOp (n := 1226) (.out 0x11e2af (addR64R64Effect 0x11e2af 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[1221, 1148]
    (.letOp (n := 1227) (.out 0x11e2af (addR64R64Effect 0x11e2af 11 1) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 1] []) (.flag .CF)) #v[1221, 1148]
    (.letOp (n := 1228) (.exec 0x11e2af (fun s => s.RIP = 0x11e2af) (addR64R64Effect 0x11e2af 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[1221, 1148]
    (.letOp (n := 1229) (.out 0x11e2b2 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e2b2 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1224, 1227]
    (.letOp (n := 1230) (.exec 0x11e2b2 (fun s => s.RIP = 0x11e2b2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e2b2 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1224, 1227]
    (.letOp (n := 1231) (.out 0x11e2b6 (movR64R64Effect 0x11e2b6 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[1226]
    (.letOp (n := 1232) (.exec 0x11e2b6 (fun s => s.RIP = 0x11e2b6) (movR64R64Effect 0x11e2b6 0 11) (Reg.operands [.gpr 11] [])) #v[1226]
    (.letOp (n := 1233) (.out 0x11e2b9 (movR64Imm64Effect 0x11e2b9 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1234) (.exec 0x11e2b9 (fun s => s.RIP = 0x11e2b9) (movR64Imm64Effect 0x11e2b9 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1235) (.out 0x11e2c3 (andR64R64Effect 0x11e2c3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1231, 1233]
    (.letOp (n := 1236) (.exec 0x11e2c3 (fun s => s.RIP = 0x11e2c3) (andR64R64Effect 0x11e2c3 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1231, 1233]
    (.letOp (n := 1237) (.out 0x11e2c6 (movR64Imm64Effect 0x11e2c6 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1238) (.exec 0x11e2c6 (fun s => s.RIP = 0x11e2c6) (movR64Imm64Effect 0x11e2c6 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1239) (.out 0x11e2d0 (mulR64Effect 0x11e2d0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1237, 1235]
    (.letOp (n := 1240) (.out 0x11e2d0 (mulR64Effect 0x11e2d0 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1237, 1235]
    (.letOp (n := 1241) (.exec 0x11e2d0 (fun s => s.RIP = 0x11e2d0) (mulR64Effect 0x11e2d0 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1237, 1235]
    (.letOp (n := 1242) (.out 0x11e2d3 (addR64R64Effect 0x11e2d3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[1195, 1188]
    (.letOp (n := 1243) (.out 0x11e2d3 (addR64R64Effect 0x11e2d3 7 9) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 9] []) (.flag .CF)) #v[1195, 1188]
    (.letOp (n := 1244) (.exec 0x11e2d3 (fun s => s.RIP = 0x11e2d3) (addR64R64Effect 0x11e2d3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[1195, 1188]
    (.letOp (n := 1245) (.out 0x11e2d6 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e2d6 6 13)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[1197, 1186, 1243]
    (.letOp (n := 1246) (.exec 0x11e2d6 (fun s => s.RIP = 0x11e2d6) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e2d6 6 13)) (Reg.operands [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1197, 1186, 1243]
    (.letOp (n := 1247) (.out 0x11e2d9 (addR64M64Effect 0x11e2d9 7 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[1242, 4]
    (.letOp (n := 1248) (.out 0x11e2d9 (addR64M64Effect 0x11e2d9 7 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[1242, 4]
    (.letOp (n := 1249) (.exec 0x11e2d9 (LoadPre 0x11e2d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11e2d9 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11e2d9 7 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1242, 4]
    (.letOp (n := 1250) (.out 0x11e2e1 (atFlags StatusFlags.CF (adcR64M64Effect 0x11e2e1 6 (.sib 4 none 0 (.d32 0xe8)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[1245, 4, 1248]
    (.letOp (n := 1251) (.exec 0x11e2e1 (LoadPre 0x11e2e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11e2e1 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e2e1 6 (.sib 4 none 0 (.d32 0xe8)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1245, 4, 1248]
    (.letOp (n := 1252) (.out 0x11e2e9 (addR64R64Effect 0x11e2e9 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[1247, 1239]
    (.letOp (n := 1253) (.out 0x11e2e9 (addR64R64Effect 0x11e2e9 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[1247, 1239]
    (.letOp (n := 1254) (.exec 0x11e2e9 (fun s => s.RIP = 0x11e2e9) (addR64R64Effect 0x11e2e9 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1247, 1239]
    (.letOp (n := 1255) (.out 0x11e2ec (atFlags StatusFlags.CF (adcR64R64Effect 0x11e2ec 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[1250, 1240, 1253]
    (.letOp (n := 1256) (.exec 0x11e2ec (fun s => s.RIP = 0x11e2ec) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e2ec 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1250, 1240, 1253]
    (.letOp (n := 1257) (.out 0x11e2ef (addR64R64Effect 0x11e2ef 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[1252, 1199]
    (.letOp (n := 1258) (.out 0x11e2ef (addR64R64Effect 0x11e2ef 7 5) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 5] []) (.flag .CF)) #v[1252, 1199]
    (.letOp (n := 1259) (.exec 0x11e2ef (fun s => s.RIP = 0x11e2ef) (addR64R64Effect 0x11e2ef 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[1252, 1199]
    (.letOp (n := 1260) (.out 0x11e2f2 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e2f2 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[1255, 1258]
    (.letOp (n := 1261) (.exec 0x11e2f2 (fun s => s.RIP = 0x11e2f2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e2f2 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1255, 1258]
    (.letOp (n := 1262) (.out 0x11e2f6 (shldR64R64Effect 0x11e2f6 5 10 11 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[1229, 1226]
    (.letOp (n := 1263) (.exec 0x11e2f6 (fun s => s.RIP = 0x11e2f6) (shldR64R64Effect 0x11e2f6 5 10 11 12) (Reg.operands [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1229, 1226]
    (.letOp (n := 1264) (.out 0x11e2fb (movR64R64Effect 0x11e2fb 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[1262]
    (.letOp (n := 1265) (.exec 0x11e2fb (fun s => s.RIP = 0x11e2fb) (movR64R64Effect 0x11e2fb 0 10) (Reg.operands [.gpr 10] [])) #v[1262]
    (b_l11d880_29)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_28 : List UInt8 :=
  [0x49, 0x89, 0xC3, 0x4D, 0x01, 0xC3, 0x49, 0x11, 0xD2, 0x49, 0x01, 0xCB, 0x49, 0x83, 0xD2, 0x00,
    0x4C, 0x89, 0xD8, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8,
    0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x4C, 0x01, 0xCF,
    0x4C, 0x11, 0xEE, 0x48, 0x03, 0xBC, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x13, 0xB4, 0x24, 0xE8,
    0x00, 0x00, 0x00, 0x48, 0x01, 0xC7, 0x48, 0x11, 0xD6, 0x48, 0x01, 0xEF, 0x48, 0x83, 0xD6, 0x00,
    0x4D, 0x0F, 0xA4, 0xDA, 0x0C, 0x4C, 0x89, 0xD0] ++ bytes_l11d880_29

theorem code_l11d880_28 : ∀ x ∈ codeRange 0x11e2a6 bytes_l11d880_28, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e2a6 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_29

def b_l11d880_27 : Block Op Label signature Reg.count 1176 :=
  .letOp (n := 1176) (.out 0x11e23f (mulM64Effect 0x11e23f 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1174, 4]
    (.letOp (n := 1177) (.out 0x11e23f (mulM64Effect 0x11e23f 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1174, 4]
    (.letOp (n := 1178) (.exec 0x11e23f (LoadPre 0x11e23f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11e23f + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11e23f 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1174, 4]
    (.letOp (n := 1179) (.exec 0x11e247 (StorePre 0x11e247 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11e247 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e247 2 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1177, 4]
    (.letOp (n := 1180) (.exec 0x11e24f (StorePre 0x11e24f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11e24f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e24f 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1176, 4]
    (.letOp (n := 1181) (.out 0x11e257 (movR64M64Effect 0x11e257 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1182) (.exec 0x11e257 (LoadPre 0x11e257 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x11e257 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e257 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1183) (.out 0x11e25f (mulM64Effect 0x11e25f 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1181, 4]
    (.letOp (n := 1184) (.out 0x11e25f (mulM64Effect 0x11e25f 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1181, 4]
    (.letOp (n := 1185) (.exec 0x11e25f (LoadPre 0x11e25f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11e25f + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e25f 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1181, 4]
    (.letOp (n := 1186) (.out 0x11e264 (movR64R64Effect 0x11e264 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[1184]
    (.letOp (n := 1187) (.exec 0x11e264 (fun s => s.RIP = 0x11e264) (movR64R64Effect 0x11e264 13 2) (Reg.operands [.gpr 2] [])) #v[1184]
    (.letOp (n := 1188) (.out 0x11e267 (movR64R64Effect 0x11e267 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[1183]
    (.letOp (n := 1189) (.exec 0x11e267 (fun s => s.RIP = 0x11e267) (movR64R64Effect 0x11e267 9 0) (Reg.operands [.gpr 0] [])) #v[1183]
    (.letOp (n := 1190) (.out 0x11e26a (movR64M64Effect 0x11e26a 0 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1191) (.exec 0x11e26a (LoadPre 0x11e26a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x11e26a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e26a 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1192) (.out 0x11e272 (mulR64Effect 0x11e272 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[1098, 1190]
    (.letOp (n := 1193) (.out 0x11e272 (mulR64Effect 0x11e272 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[1098, 1190]
    (.letOp (n := 1194) (.exec 0x11e272 (fun s => s.RIP = 0x11e272) (mulR64Effect 0x11e272 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[1098, 1190]
    (.letOp (n := 1195) (.out 0x11e275 (movR64R64Effect 0x11e275 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[1192]
    (.letOp (n := 1196) (.exec 0x11e275 (fun s => s.RIP = 0x11e275) (movR64R64Effect 0x11e275 7 0) (Reg.operands [.gpr 0] [])) #v[1192]
    (.letOp (n := 1197) (.out 0x11e278 (movR64R64Effect 0x11e278 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1193]
    (.letOp (n := 1198) (.exec 0x11e278 (fun s => s.RIP = 0x11e278) (movR64R64Effect 0x11e278 6 2) (Reg.operands [.gpr 2] [])) #v[1193]
    (.letOp (n := 1199) (.out 0x11e27b (shldR64R64Effect 0x11e27b 5 5 12 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[1172, 1169]
    (.letOp (n := 1200) (.exec 0x11e27b (fun s => s.RIP = 0x11e27b) (shldR64R64Effect 0x11e27b 5 5 12 12) (Reg.operands [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1172, 1169]
    (.letOp (n := 1201) (.out 0x11e280 (movR64Imm64Effect 0x11e280 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1202) (.exec 0x11e280 (fun s => s.RIP = 0x11e280) (movR64Imm64Effect 0x11e280 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1203) (.out 0x11e28a (andR64R64Effect 0x11e28a 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[1169, 1201]
    (.letOp (n := 1204) (.exec 0x11e28a (fun s => s.RIP = 0x11e28a) (andR64R64Effect 0x11e28a 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[1169, 1201]
    (.letOp (n := 1205) (.out 0x11e28d (movR64M64Effect 0x11e28d 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1206) (.exec 0x11e28d (LoadPre 0x11e28d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11e28d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e28d 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1207) (.out 0x11e292 (mulR64Effect 0x11e292 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1115, 1205]
    (.letOp (n := 1208) (.out 0x11e292 (mulR64Effect 0x11e292 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1115, 1205]
    (.letOp (n := 1209) (.exec 0x11e292 (fun s => s.RIP = 0x11e292) (mulR64Effect 0x11e292 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1115, 1205]
    (.letOp (n := 1210) (.out 0x11e295 (movR64R64Effect 0x11e295 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[1207]
    (.letOp (n := 1211) (.exec 0x11e295 (fun s => s.RIP = 0x11e295) (movR64R64Effect 0x11e295 8 0) (Reg.operands [.gpr 0] [])) #v[1207]
    (.letOp (n := 1212) (.out 0x11e298 (movR64R64Effect 0x11e298 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[1208]
    (.letOp (n := 1213) (.exec 0x11e298 (fun s => s.RIP = 0x11e298) (movR64R64Effect 0x11e298 10 2) (Reg.operands [.gpr 2] [])) #v[1208]
    (.letOp (n := 1214) (.out 0x11e29b (movR64M64Effect 0x11e29b 0 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1215) (.exec 0x11e29b (LoadPre 0x11e29b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x11e29b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e29b 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1216) (.out 0x11e2a3 (mulR64Effect 0x11e2a3 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[1128, 1214]
    (.letOp (n := 1217) (.out 0x11e2a3 (mulR64Effect 0x11e2a3 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[1128, 1214]
    (.letOp (n := 1218) (.exec 0x11e2a3 (fun s => s.RIP = 0x11e2a3) (mulR64Effect 0x11e2a3 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1128, 1214]
    (b_l11d880_28)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_27 : List UInt8 :=
  [0x48, 0xF7, 0xA4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xE8, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00,
    0x48, 0xF7, 0x64, 0x24, 0x48, 0x49, 0x89, 0xD5, 0x49, 0x89, 0xC1, 0x48, 0x8B, 0x84, 0x24, 0xE0,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xC7, 0x48, 0x89, 0xD6, 0x4C, 0x0F, 0xA4, 0xE5,
    0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xC4, 0x48, 0x8B,
    0x44, 0x24, 0x78, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xC0, 0x49, 0x89, 0xD2, 0x48, 0x8B, 0x84, 0x24,
    0x10, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE6] ++ bytes_l11d880_28

theorem code_l11d880_27 : ∀ x ∈ codeRange 0x11e23f bytes_l11d880_27, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e23f 103 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_28

def b_l11d880_26 : Block Op Label signature Reg.count 1128 :=
  .letOp (n := 1128) (.out 0x11e1e3 (movR64M64Effect 0x11e1e3 14 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 1129) (.exec 0x11e1e3 (LoadPre 0x11e1e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11e1e3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e1e3 14 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1130) (.out 0x11e1e8 (mulR64Effect 0x11e1e8 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[1128, 1126]
    (.letOp (n := 1131) (.out 0x11e1e8 (mulR64Effect 0x11e1e8 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[1128, 1126]
    (.letOp (n := 1132) (.exec 0x11e1e8 (fun s => s.RIP = 0x11e1e8) (mulR64Effect 0x11e1e8 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1128, 1126]
    (.letOp (n := 1133) (.out 0x11e1eb (addR64R64Effect 0x11e1eb 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[1130, 1120]
    (.letOp (n := 1134) (.out 0x11e1eb (addR64R64Effect 0x11e1eb 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[1130, 1120]
    (.letOp (n := 1135) (.exec 0x11e1eb (fun s => s.RIP = 0x11e1eb) (addR64R64Effect 0x11e1eb 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[1130, 1120]
    (.letOp (n := 1136) (.out 0x11e1ee (atFlags StatusFlags.CF (adcR64R64Effect 0x11e1ee 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1122, 1131, 1134]
    (.letOp (n := 1137) (.exec 0x11e1ee (fun s => s.RIP = 0x11e1ee) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e1ee 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1122, 1131, 1134]
    (.letOp (n := 1138) (.out 0x11e1f1 (addR64R64Effect 0x11e1f1 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[1133, 1103]
    (.letOp (n := 1139) (.out 0x11e1f1 (addR64R64Effect 0x11e1f1 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[1133, 1103]
    (.letOp (n := 1140) (.exec 0x11e1f1 (fun s => s.RIP = 0x11e1f1) (addR64R64Effect 0x11e1f1 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[1133, 1103]
    (.letOp (n := 1141) (.out 0x11e1f4 (atFlags StatusFlags.CF (adcR64M64Effect 0x11e1f4 1 (.sib 4 none 0 (.d8 0x20)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[1136, 4, 1139]
    (.letOp (n := 1142) (.exec 0x11e1f4 (LoadPre 0x11e1f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e1f4 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e1f4 1 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1136, 4, 1139]
    (.letOp (n := 1143) (.out 0x11e1f9 (addR64R64Effect 0x11e1f9 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[1138, 1056]
    (.letOp (n := 1144) (.out 0x11e1f9 (addR64R64Effect 0x11e1f9 0 13) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 13] []) (.flag .CF)) #v[1138, 1056]
    (.letOp (n := 1145) (.exec 0x11e1f9 (fun s => s.RIP = 0x11e1f9) (addR64R64Effect 0x11e1f9 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[1138, 1056]
    (.letOp (n := 1146) (.out 0x11e1fc (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e1fc 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1141, 1144]
    (.letOp (n := 1147) (.exec 0x11e1fc (fun s => s.RIP = 0x11e1fc) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e1fc 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1141, 1144]
    (.letOp (n := 1148) (.out 0x11e200 (shldR64R64Effect 0x11e200 5 1 0 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1146, 1143]
    (.letOp (n := 1149) (.exec 0x11e200 (fun s => s.RIP = 0x11e200) (shldR64R64Effect 0x11e200 5 1 0 12) (Reg.operands [.gpr 1, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1146, 1143]
    (.letOp (n := 1150) (.out 0x11e205 (movR64Imm64Effect 0x11e205 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1151) (.exec 0x11e205 (fun s => s.RIP = 0x11e205) (movR64Imm64Effect 0x11e205 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1152) (.out 0x11e20f (andR64R64Effect 0x11e20f 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1143, 1150]
    (.letOp (n := 1153) (.exec 0x11e20f (fun s => s.RIP = 0x11e20f) (andR64R64Effect 0x11e20f 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1143, 1150]
    (.letOp (n := 1154) (.out 0x11e212 (movR64Imm64Effect 0x11e212 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1155) (.exec 0x11e212 (fun s => s.RIP = 0x11e212) (movR64Imm64Effect 0x11e212 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1156) (.out 0x11e21c (mulR64Effect 0x11e21c 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1154, 1152]
    (.letOp (n := 1157) (.out 0x11e21c (mulR64Effect 0x11e21c 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1154, 1152]
    (.letOp (n := 1158) (.exec 0x11e21c (fun s => s.RIP = 0x11e21c) (mulR64Effect 0x11e21c 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1154, 1152]
    (.letOp (n := 1159) (.out 0x11e21f (addR64M64Effect 0x11e21f 12 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[1094, 4]
    (.letOp (n := 1160) (.out 0x11e21f (addR64M64Effect 0x11e21f 12 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 4] []) (.flag .CF)) #v[1094, 4]
    (.letOp (n := 1161) (.exec 0x11e21f (LoadPre 0x11e21f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11e21f + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11e21f 12 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[1094, 4]
    (.letOp (n := 1162) (.out 0x11e227 (atFlags StatusFlags.CF (adcR64M64Effect 0x11e227 5 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 5))) #v[1092, 4, 1160]
    (.letOp (n := 1163) (.exec 0x11e227 (LoadPre 0x11e227 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11e227 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e227 5 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1092, 4, 1160]
    (.letOp (n := 1164) (.out 0x11e22f (addR64R64Effect 0x11e22f 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[1159, 1156]
    (.letOp (n := 1165) (.out 0x11e22f (addR64R64Effect 0x11e22f 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[1159, 1156]
    (.letOp (n := 1166) (.exec 0x11e22f (fun s => s.RIP = 0x11e22f) (addR64R64Effect 0x11e22f 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[1159, 1156]
    (.letOp (n := 1167) (.out 0x11e232 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e232 5 2)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[1162, 1157, 1165]
    (.letOp (n := 1168) (.exec 0x11e232 (fun s => s.RIP = 0x11e232) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e232 5 2)) (Reg.operands [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1162, 1157, 1165]
    (.letOp (n := 1169) (.out 0x11e235 (addR64R64Effect 0x11e235 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[1164, 1106]
    (.letOp (n := 1170) (.out 0x11e235 (addR64R64Effect 0x11e235 12 6) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 6] []) (.flag .CF)) #v[1164, 1106]
    (.letOp (n := 1171) (.exec 0x11e235 (fun s => s.RIP = 0x11e235) (addR64R64Effect 0x11e235 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[1164, 1106]
    (.letOp (n := 1172) (.out 0x11e238 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e238 5 0x0)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[1167, 1170]
    (.letOp (n := 1173) (.exec 0x11e238 (fun s => s.RIP = 0x11e238) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e238 5 0x0)) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1167, 1170]
    (.letOp (n := 1174) (.out 0x11e23c (movR64R64Effect 0x11e23c 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1124]
    (.letOp (n := 1175) (.exec 0x11e23c (fun s => s.RIP = 0x11e23c) (movR64R64Effect 0x11e23c 0 7) (Reg.operands [.gpr 7] [])) #v[1124]
    (b_l11d880_27))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_26 : List UInt8 :=
  [0x4C, 0x8B, 0x74, 0x24, 0x40, 0x49, 0xF7, 0xE6, 0x4C, 0x01, 0xD8, 0x48, 0x11, 0xD1, 0x4C, 0x01,
    0xC8, 0x48, 0x13, 0x4C, 0x24, 0x20, 0x4C, 0x01, 0xE8, 0x48, 0x83, 0xD1, 0x00, 0x48, 0x0F, 0xA4,
    0xC1, 0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48,
    0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x03, 0xA4, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x48, 0x13, 0xAC, 0x24, 0x98, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC4, 0x48,
    0x11, 0xD5, 0x49, 0x01, 0xF4, 0x48, 0x83, 0xD5, 0x00, 0x48, 0x89, 0xF8] ++ bytes_l11d880_27

theorem code_l11d880_26 : ∀ x ∈ codeRange 0x11e1e3 bytes_l11d880_26, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e1e3 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_27

def b_l11d880_25 : Block Op Label signature Reg.count 1087 :=
  .letOp (n := 1087) (.out 0x11e182 (movR64M64Effect 0x11e182 0 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1088) (.exec 0x11e182 (LoadPre 0x11e182 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x11e182 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e182 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1089) (.out 0x11e18a (mulR64Effect 0x11e18a 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[994, 1087]
    (.letOp (n := 1090) (.out 0x11e18a (mulR64Effect 0x11e18a 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[994, 1087]
    (.letOp (n := 1091) (.exec 0x11e18a (fun s => s.RIP = 0x11e18a) (mulR64Effect 0x11e18a 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[994, 1087]
    (.letOp (n := 1092) (.out 0x11e18d (movR64R64Effect 0x11e18d 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[1090]
    (.letOp (n := 1093) (.exec 0x11e18d (fun s => s.RIP = 0x11e18d) (movR64R64Effect 0x11e18d 5 2) (Reg.operands [.gpr 2] [])) #v[1090]
    (.letOp (n := 1094) (.out 0x11e190 (movR64R64Effect 0x11e190 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[1089]
    (.letOp (n := 1095) (.exec 0x11e190 (fun s => s.RIP = 0x11e190) (movR64R64Effect 0x11e190 12 0) (Reg.operands [.gpr 0] [])) #v[1089]
    (.letOp (n := 1096) (.out 0x11e193 (movR64M64Effect 0x11e193 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1097) (.exec 0x11e193 (LoadPre 0x11e193 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11e193 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e193 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1098) (.out 0x11e198 (movR64M64Effect 0x11e198 10 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 1099) (.exec 0x11e198 (LoadPre 0x11e198 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11e198 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e198 10 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1100) (.out 0x11e19d (mulR64Effect 0x11e19d 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[1098, 1096]
    (.letOp (n := 1101) (.out 0x11e19d (mulR64Effect 0x11e19d 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[1098, 1096]
    (.letOp (n := 1102) (.exec 0x11e19d (fun s => s.RIP = 0x11e19d) (mulR64Effect 0x11e19d 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[1098, 1096]
    (.letOp (n := 1103) (.out 0x11e1a0 (movR64R64Effect 0x11e1a0 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[1100]
    (.letOp (n := 1104) (.exec 0x11e1a0 (fun s => s.RIP = 0x11e1a0) (movR64R64Effect 0x11e1a0 9 0) (Reg.operands [.gpr 0] [])) #v[1100]
    (.letOp (n := 1105) (.exec 0x11e1a3 (StorePre 0x11e1a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e1a3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e1a3 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1101, 4]
    (.letOp (n := 1106) (.out 0x11e1a8 (shldR64R64Effect 0x11e1a8 5 6 8 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1078, 1075]
    (.letOp (n := 1107) (.exec 0x11e1a8 (fun s => s.RIP = 0x11e1a8) (shldR64R64Effect 0x11e1a8 5 6 8 12) (Reg.operands [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1078, 1075]
    (.letOp (n := 1108) (.out 0x11e1ad (movR64Imm64Effect 0x11e1ad 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1109) (.exec 0x11e1ad (fun s => s.RIP = 0x11e1ad) (movR64Imm64Effect 0x11e1ad 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1110) (.out 0x11e1b7 (andR64R64Effect 0x11e1b7 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[1075, 1108]
    (.letOp (n := 1111) (.exec 0x11e1b7 (fun s => s.RIP = 0x11e1b7) (andR64R64Effect 0x11e1b7 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1075, 1108]
    (.letOp (n := 1112) (.exec 0x11e1ba (StorePre 0x11e1ba 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11e1ba + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e1ba 8 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1110, 4]
    (.letOp (n := 1113) (.out 0x11e1c2 (movR64M64Effect 0x11e1c2 0 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1114) (.exec 0x11e1c2 (LoadPre 0x11e1c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x11e1c2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e1c2 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1115) (.out 0x11e1ca (movR64M64Effect 0x11e1ca 8 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 1116) (.exec 0x11e1ca (LoadPre 0x11e1ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11e1ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e1ca 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1117) (.out 0x11e1cf (mulR64Effect 0x11e1cf 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1115, 1113]
    (.letOp (n := 1118) (.out 0x11e1cf (mulR64Effect 0x11e1cf 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1115, 1113]
    (.letOp (n := 1119) (.exec 0x11e1cf (fun s => s.RIP = 0x11e1cf) (mulR64Effect 0x11e1cf 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1115, 1113]
    (.letOp (n := 1120) (.out 0x11e1d2 (movR64R64Effect 0x11e1d2 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[1117]
    (.letOp (n := 1121) (.exec 0x11e1d2 (fun s => s.RIP = 0x11e1d2) (movR64R64Effect 0x11e1d2 11 0) (Reg.operands [.gpr 0] [])) #v[1117]
    (.letOp (n := 1122) (.out 0x11e1d5 (movR64R64Effect 0x11e1d5 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1118]
    (.letOp (n := 1123) (.exec 0x11e1d5 (fun s => s.RIP = 0x11e1d5) (movR64R64Effect 0x11e1d5 1 2) (Reg.operands [.gpr 2] [])) #v[1118]
    (.letOp (n := 1124) (.out 0x11e1d8 (movR64M64Effect 0x11e1d8 7 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 1125) (.exec 0x11e1d8 (LoadPre 0x11e1d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11e1d8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e1d8 7 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1126) (.out 0x11e1e0 (movR64R64Effect 0x11e1e0 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1124]
    (.letOp (n := 1127) (.exec 0x11e1e0 (fun s => s.RIP = 0x11e1e0) (movR64R64Effect 0x11e1e0 0 7) (Reg.operands [.gpr 7] [])) #v[1124]
    (b_l11d880_26)))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_25 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD5, 0x49, 0x89,
    0xC4, 0x48, 0x8B, 0x44, 0x24, 0x78, 0x4C, 0x8B, 0x54, 0x24, 0x50, 0x49, 0xF7, 0xE2, 0x49, 0x89,
    0xC1, 0x48, 0x89, 0x54, 0x24, 0x20, 0x4C, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xC0, 0x4C, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x44, 0x24, 0x30, 0x49, 0xF7, 0xE0,
    0x49, 0x89, 0xC3, 0x48, 0x89, 0xD1, 0x48, 0x8B, 0xBC, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x89,
    0xF8] ++ bytes_l11d880_26

theorem code_l11d880_25 : ∀ x ∈ codeRange 0x11e182 bytes_l11d880_25, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e182 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_26

def b_l11d880_24 : Block Op Label signature Reg.count 1044 :=
  .letOp (n := 1044) (.out 0x11e120 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e120 13 9)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[1039, 1014, 1042]
    (.letOp (n := 1045) (.exec 0x11e120 (fun s => s.RIP = 0x11e120) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e120 13 9)) (Reg.operands [.gpr 13, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1039, 1014, 1042]
    (.letOp (n := 1046) (.out 0x11e123 (addR64R64Effect 0x11e123 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1041, 999]
    (.letOp (n := 1047) (.out 0x11e123 (addR64R64Effect 0x11e123 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[1041, 999]
    (.letOp (n := 1048) (.exec 0x11e123 (fun s => s.RIP = 0x11e123) (addR64R64Effect 0x11e123 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1041, 999]
    (.letOp (n := 1049) (.out 0x11e126 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e126 13 5)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[1044, 1001, 1047]
    (.letOp (n := 1050) (.exec 0x11e126 (fun s => s.RIP = 0x11e126) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e126 13 5)) (Reg.operands [.gpr 13, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1044, 1001, 1047]
    (.letOp (n := 1051) (.out 0x11e129 (addR64R64Effect 0x11e129 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[1046, 1016]
    (.letOp (n := 1052) (.out 0x11e129 (addR64R64Effect 0x11e129 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[1046, 1016]
    (.letOp (n := 1053) (.exec 0x11e129 (fun s => s.RIP = 0x11e129) (addR64R64Effect 0x11e129 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[1046, 1016]
    (.letOp (n := 1054) (.out 0x11e12c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e12c 13 0x0)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[1049, 1052]
    (.letOp (n := 1055) (.exec 0x11e12c (fun s => s.RIP = 0x11e12c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e12c 13 0x0)) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1049, 1052]
    (.letOp (n := 1056) (.out 0x11e130 (shldR64R64Effect 0x11e130 5 13 0 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1054, 1051]
    (.letOp (n := 1057) (.exec 0x11e130 (fun s => s.RIP = 0x11e130) (shldR64R64Effect 0x11e130 5 13 0 12) (Reg.operands [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1054, 1051]
    (.letOp (n := 1058) (.out 0x11e135 (shlR64Effect 0x11e135 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1051]
    (.letOp (n := 1059) (.exec 0x11e135 (fun s => s.RIP = 0x11e135) (shlR64Effect 0x11e135 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1051]
    (.letOp (n := 1060) (.out 0x11e139 (movR64Imm64Effect 0x11e139 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1061) (.exec 0x11e139 (fun s => s.RIP = 0x11e139) (movR64Imm64Effect 0x11e139 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 1062) (.out 0x11e143 (andR64R64Effect 0x11e143 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1058, 1060]
    (.letOp (n := 1063) (.exec 0x11e143 (fun s => s.RIP = 0x11e143) (andR64R64Effect 0x11e143 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1058, 1060]
    (.letOp (n := 1064) (.out 0x11e146 (orR64R64Effect 0x11e146 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[1062, 1018]
    (.letOp (n := 1065) (.exec 0x11e146 (fun s => s.RIP = 0x11e146) (orR64R64Effect 0x11e146 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[1062, 1018]
    (.letOp (n := 1066) (.out 0x11e149 (movR64Imm64Effect 0x11e149 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1067) (.exec 0x11e149 (fun s => s.RIP = 0x11e149) (movR64Imm64Effect 0x11e149 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 1068) (.out 0x11e153 (mulR64Effect 0x11e153 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1066, 1064]
    (.letOp (n := 1069) (.out 0x11e153 (mulR64Effect 0x11e153 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1066, 1064]
    (.letOp (n := 1070) (.exec 0x11e153 (fun s => s.RIP = 0x11e153) (mulR64Effect 0x11e153 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1066, 1064]
    (.letOp (n := 1071) (.out 0x11e156 (movR64R64Effect 0x11e156 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1069]
    (.letOp (n := 1072) (.exec 0x11e156 (fun s => s.RIP = 0x11e156) (movR64R64Effect 0x11e156 6 2) (Reg.operands [.gpr 2] [])) #v[1069]
    (.letOp (n := 1073) (.out 0x11e159 (movR64R64Effect 0x11e159 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[1068]
    (.letOp (n := 1074) (.exec 0x11e159 (fun s => s.RIP = 0x11e159) (movR64R64Effect 0x11e159 8 0) (Reg.operands [.gpr 0] [])) #v[1068]
    (.letOp (n := 1075) (.out 0x11e15c (addR64M64Effect 0x11e15c 8 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[1073, 4]
    (.letOp (n := 1076) (.out 0x11e15c (addR64M64Effect 0x11e15c 8 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[1073, 4]
    (.letOp (n := 1077) (.exec 0x11e15c (LoadPre 0x11e15c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11e15c + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11e15c 8 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1073, 4]
    (.letOp (n := 1078) (.out 0x11e164 (atFlags StatusFlags.CF (adcR64M64Effect 0x11e164 6 (.sib 4 none 0 (.d32 0xd0)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[1071, 4, 1076]
    (.letOp (n := 1079) (.exec 0x11e164 (LoadPre 0x11e164 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11e164 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e164 6 (.sib 4 none 0 (.d32 0xd0)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1071, 4, 1076]
    (.letOp (n := 1080) (.out 0x11e16c (movR64R64Effect 0x11e16c 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1029]
    (.letOp (n := 1081) (.exec 0x11e16c (fun s => s.RIP = 0x11e16c) (movR64R64Effect 0x11e16c 0 1) (Reg.operands [.gpr 1] [])) #v[1029]
    (.letOp (n := 1082) (.out 0x11e16f (mulR64Effect 0x11e16f 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[985, 1080]
    (.letOp (n := 1083) (.out 0x11e16f (mulR64Effect 0x11e16f 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[985, 1080]
    (.letOp (n := 1084) (.exec 0x11e16f (fun s => s.RIP = 0x11e16f) (mulR64Effect 0x11e16f 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[985, 1080]
    (.letOp (n := 1085) (.exec 0x11e172 (StorePre 0x11e172 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11e172 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e172 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1083, 4]
    (.letOp (n := 1086) (.exec 0x11e17a (StorePre 0x11e17a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11e17a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e17a 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1082, 4]
    (b_l11d880_25)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_24 : List UInt8 :=
  [0x4D, 0x11, 0xCD, 0x48, 0x01, 0xF0, 0x49, 0x11, 0xED, 0x4C, 0x01, 0xE0, 0x49, 0x83, 0xD5, 0x00,
    0x49, 0x0F, 0xA4, 0xC5, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x4C, 0x09, 0xD8, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC0, 0x4C, 0x03, 0x84, 0x24,
    0x98, 0x00, 0x00, 0x00, 0x48, 0x13, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x49,
    0xF7, 0xE6, 0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x90, 0x00,
    0x00, 0x00] ++ bytes_l11d880_25

theorem code_l11d880_24 : ∀ x ∈ codeRange 0x11e120 bytes_l11d880_24, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e120 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_25

def b_l11d880_23 : Block Op Label signature Reg.count 999 :=
  .letOp (n := 999) (.out 0x11e0d0 (movR64R64Effect 0x11e0d0 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[996]
    (.letOp (n := 1000) (.exec 0x11e0d0 (fun s => s.RIP = 0x11e0d0) (movR64R64Effect 0x11e0d0 6 0) (Reg.operands [.gpr 0] [])) #v[996]
    (.letOp (n := 1001) (.out 0x11e0d3 (movR64R64Effect 0x11e0d3 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[997]
    (.letOp (n := 1002) (.exec 0x11e0d3 (fun s => s.RIP = 0x11e0d3) (movR64R64Effect 0x11e0d3 5 2) (Reg.operands [.gpr 2] [])) #v[997]
    (.letOp (n := 1003) (.out 0x11e0d6 (movR64R64Effect 0x11e0d6 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[978]
    (.letOp (n := 1004) (.exec 0x11e0d6 (fun s => s.RIP = 0x11e0d6) (movR64R64Effect 0x11e0d6 11 3) (Reg.operands [.gpr 3] [])) #v[978]
    (.letOp (n := 1005) (.out 0x11e0d9 (shrR64Effect 0x11e0d9 4 11 48) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1003]
    (.letOp (n := 1006) (.exec 0x11e0d9 (fun s => s.RIP = 0x11e0d9) (shrR64Effect 0x11e0d9 4 11 48) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1003]
    (.letOp (n := 1007) (.out 0x11e0dd (movR64R64Effect 0x11e0dd 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[906]
    (.letOp (n := 1008) (.exec 0x11e0dd (fun s => s.RIP = 0x11e0dd) (movR64R64Effect 0x11e0dd 0 13) (Reg.operands [.gpr 13] [])) #v[906]
    (.letOp (n := 1009) (.out 0x11e0e0 (mulM64Effect 0x11e0e0 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1007, 4]
    (.letOp (n := 1010) (.out 0x11e0e0 (mulM64Effect 0x11e0e0 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1007, 4]
    (.letOp (n := 1011) (.exec 0x11e0e0 (LoadPre 0x11e0e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11e0e0 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e0e0 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1007, 4]
    (.letOp (n := 1012) (.out 0x11e0e5 (movR64R64Effect 0x11e0e5 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[1009]
    (.letOp (n := 1013) (.exec 0x11e0e5 (fun s => s.RIP = 0x11e0e5) (movR64R64Effect 0x11e0e5 8 0) (Reg.operands [.gpr 0] [])) #v[1009]
    (.letOp (n := 1014) (.out 0x11e0e8 (movR64R64Effect 0x11e0e8 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[1010]
    (.letOp (n := 1015) (.exec 0x11e0e8 (fun s => s.RIP = 0x11e0e8) (movR64R64Effect 0x11e0e8 9 2) (Reg.operands [.gpr 2] [])) #v[1010]
    (.letOp (n := 1016) (.out 0x11e0eb (shldR64R64Effect 0x11e0eb 5 12 3 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[981, 978]
    (.letOp (n := 1017) (.exec 0x11e0eb (fun s => s.RIP = 0x11e0eb) (shldR64R64Effect 0x11e0eb 5 12 3 12) (Reg.operands [.gpr 12, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[981, 978]
    (.letOp (n := 1018) (.out 0x11e0f0 (andR32Imm8Effect 0x11e0f0 4 11 0xf) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[1005]
    (.letOp (n := 1019) (.exec 0x11e0f0 (fun s => s.RIP = 0x11e0f0) (andR32Imm8Effect 0x11e0f0 4 11 0xf) (Reg.operands [.gpr 11] [])) #v[1005]
    (.letOp (n := 1020) (.out 0x11e0f4 (movR64M64Effect 0x11e0f4 0 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1021) (.exec 0x11e0f4 (LoadPre 0x11e0f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11e0f4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e0f4 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1022) (.out 0x11e0fc (mulM64Effect 0x11e0fc 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1020, 4]
    (.letOp (n := 1023) (.out 0x11e0fc (mulM64Effect 0x11e0fc 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1020, 4]
    (.letOp (n := 1024) (.exec 0x11e0fc (LoadPre 0x11e0fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11e0fc + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e0fc 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1020, 4]
    (.letOp (n := 1025) (.out 0x11e101 (movR64R64Effect 0x11e101 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[1022]
    (.letOp (n := 1026) (.exec 0x11e101 (fun s => s.RIP = 0x11e101) (movR64R64Effect 0x11e101 10 0) (Reg.operands [.gpr 0] [])) #v[1022]
    (.letOp (n := 1027) (.out 0x11e104 (movR64R64Effect 0x11e104 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[1023]
    (.letOp (n := 1028) (.exec 0x11e104 (fun s => s.RIP = 0x11e104) (movR64R64Effect 0x11e104 13 2) (Reg.operands [.gpr 2] [])) #v[1023]
    (.letOp (n := 1029) (.out 0x11e107 (movR64M64Effect 0x11e107 1 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 1030) (.exec 0x11e107 (LoadPre 0x11e107 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x11e107 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e107 1 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1031) (.out 0x11e10f (movR64R64Effect 0x11e10f 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1029]
    (.letOp (n := 1032) (.exec 0x11e10f (fun s => s.RIP = 0x11e10f) (movR64R64Effect 0x11e10f 0 1) (Reg.operands [.gpr 1] [])) #v[1029]
    (.letOp (n := 1033) (.out 0x11e112 (mulM64Effect 0x11e112 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1031, 4]
    (.letOp (n := 1034) (.out 0x11e112 (mulM64Effect 0x11e112 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1031, 4]
    (.letOp (n := 1035) (.exec 0x11e112 (LoadPre 0x11e112 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11e112 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e112 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1031, 4]
    (.letOp (n := 1036) (.out 0x11e117 (addR64R64Effect 0x11e117 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[1033, 1025]
    (.letOp (n := 1037) (.out 0x11e117 (addR64R64Effect 0x11e117 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[1033, 1025]
    (.letOp (n := 1038) (.exec 0x11e117 (fun s => s.RIP = 0x11e117) (addR64R64Effect 0x11e117 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[1033, 1025]
    (.letOp (n := 1039) (.out 0x11e11a (atFlags StatusFlags.CF (adcR64R64Effect 0x11e11a 13 2)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[1027, 1034, 1037]
    (.letOp (n := 1040) (.exec 0x11e11a (fun s => s.RIP = 0x11e11a) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e11a 13 2)) (Reg.operands [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1027, 1034, 1037]
    (.letOp (n := 1041) (.out 0x11e11d (addR64R64Effect 0x11e11d 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[1036, 1012]
    (.letOp (n := 1042) (.out 0x11e11d (addR64R64Effect 0x11e11d 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[1036, 1012]
    (.letOp (n := 1043) (.exec 0x11e11d (fun s => s.RIP = 0x11e11d) (addR64R64Effect 0x11e11d 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[1036, 1012]
    (b_l11d880_24)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_23 : List UInt8 :=
  [0x48, 0x89, 0xC6, 0x48, 0x89, 0xD5, 0x49, 0x89, 0xDB, 0x49, 0xC1, 0xEB, 0x30, 0x4C, 0x89, 0xE8,
    0x48, 0xF7, 0x64, 0x24, 0x50, 0x49, 0x89, 0xC0, 0x49, 0x89, 0xD1, 0x49, 0x0F, 0xA4, 0xDC, 0x0C,
    0x41, 0x83, 0xE3, 0x0F, 0x48, 0x8B, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64, 0x24,
    0x30, 0x49, 0x89, 0xC2, 0x49, 0x89, 0xD5, 0x48, 0x8B, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48,
    0x89, 0xC8, 0x48, 0xF7, 0x64, 0x24, 0x40, 0x4C, 0x01, 0xD0, 0x49, 0x11, 0xD5, 0x4C, 0x01, 0xC0] ++ bytes_l11d880_24

theorem code_l11d880_23 : ∀ x ∈ codeRange 0x11e0d0 bytes_l11d880_23, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e0d0 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_24

def b_l11d880_22 : Block Op Label signature Reg.count 953 :=
  .letOp (n := 953) (.out 0x11e06f (addR64R64Effect 0x11e06f 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[944, 931]
    (.letOp (n := 954) (.out 0x11e06f (addR64R64Effect 0x11e06f 3 7) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 7] []) (.flag .CF)) #v[944, 931]
    (.letOp (n := 955) (.exec 0x11e06f (fun s => s.RIP = 0x11e06f) (addR64R64Effect 0x11e06f 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[944, 931]
    (.letOp (n := 956) (.out 0x11e072 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e072 12 10)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[942, 933, 954]
    (.letOp (n := 957) (.exec 0x11e072 (fun s => s.RIP = 0x11e072) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e072 12 10)) (Reg.operands [.gpr 12, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[942, 933, 954]
    (.letOp (n := 958) (.out 0x11e075 (addR64R64Effect 0x11e075 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[953, 920]
    (.letOp (n := 959) (.out 0x11e075 (addR64R64Effect 0x11e075 3 5) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 5] []) (.flag .CF)) #v[953, 920]
    (.letOp (n := 960) (.exec 0x11e075 (fun s => s.RIP = 0x11e075) (addR64R64Effect 0x11e075 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[953, 920]
    (.letOp (n := 961) (.out 0x11e078 (atFlags StatusFlags.CF (adcR64R64Effect 0x11e078 12 11)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[956, 922, 959]
    (.letOp (n := 962) (.exec 0x11e078 (fun s => s.RIP = 0x11e078) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e078 12 11)) (Reg.operands [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[956, 922, 959]
    (.letOp (n := 963) (.out 0x11e07b (addR64M64Effect 0x11e07b 3 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[958, 4]
    (.letOp (n := 964) (.out 0x11e07b (addR64M64Effect 0x11e07b 3 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[958, 4]
    (.letOp (n := 965) (.exec 0x11e07b (LoadPre 0x11e07b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e07b + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11e07b 3 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[958, 4]
    (.letOp (n := 966) (.out 0x11e080 (atFlags StatusFlags.CF (adcR64M64Effect 0x11e080 12 (.sib 4 none 0 (.d32 0x90)))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 12))) #v[961, 4, 964]
    (.letOp (n := 967) (.exec 0x11e080 (LoadPre 0x11e080 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11e080 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e080 12 (.sib 4 none 0 (.d32 0x90)))) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[961, 4, 964]
    (.letOp (n := 968) (.out 0x11e088 (addR64M64Effect 0x11e088 3 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[963, 4]
    (.letOp (n := 969) (.out 0x11e088 (addR64M64Effect 0x11e088 3 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[963, 4]
    (.letOp (n := 970) (.exec 0x11e088 (LoadPre 0x11e088 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11e088 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11e088 3 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[963, 4]
    (.letOp (n := 971) (.out 0x11e090 (atFlags StatusFlags.CF (adcR64M64Effect 0x11e090 12 (.sib 4 none 0 (.d32 0xd0)))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 12))) #v[966, 4, 969]
    (.letOp (n := 972) (.exec 0x11e090 (LoadPre 0x11e090 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11e090 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11e090 12 (.sib 4 none 0 (.d32 0xd0)))) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[966, 4, 969]
    (.letOp (n := 973) (.out 0x11e098 (addR64R64Effect 0x11e098 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[968, 950]
    (.letOp (n := 974) (.out 0x11e098 (addR64R64Effect 0x11e098 3 0) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 0] []) (.flag .CF)) #v[968, 950]
    (.letOp (n := 975) (.exec 0x11e098 (fun s => s.RIP = 0x11e098) (addR64R64Effect 0x11e098 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[968, 950]
    (.letOp (n := 976) (.out 0x11e09b (atFlags StatusFlags.CF (adcR64R64Effect 0x11e09b 12 2)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[971, 951, 974]
    (.letOp (n := 977) (.exec 0x11e09b (fun s => s.RIP = 0x11e09b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11e09b 12 2)) (Reg.operands [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[971, 951, 974]
    (.letOp (n := 978) (.out 0x11e09e (addR64R64Effect 0x11e09e 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[973, 924]
    (.letOp (n := 979) (.out 0x11e09e (addR64R64Effect 0x11e09e 3 14) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 14] []) (.flag .CF)) #v[973, 924]
    (.letOp (n := 980) (.exec 0x11e09e (fun s => s.RIP = 0x11e09e) (addR64R64Effect 0x11e09e 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[973, 924]
    (.letOp (n := 981) (.out 0x11e0a1 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e0a1 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[976, 979]
    (.letOp (n := 982) (.exec 0x11e0a1 (fun s => s.RIP = 0x11e0a1) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11e0a1 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[976, 979]
    (.letOp (n := 983) (.out 0x11e0a5 (movR64R64Effect 0x11e0a5 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[935]
    (.letOp (n := 984) (.exec 0x11e0a5 (fun s => s.RIP = 0x11e0a5) (movR64R64Effect 0x11e0a5 0 6) (Reg.operands [.gpr 6] [])) #v[935]
    (.letOp (n := 985) (.out 0x11e0a8 (movR64M64Effect 0x11e0a8 14 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 986) (.exec 0x11e0a8 (LoadPre 0x11e0a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11e0a8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e0a8 14 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 987) (.out 0x11e0b0 (mulR64Effect 0x11e0b0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[985, 983]
    (.letOp (n := 988) (.out 0x11e0b0 (mulR64Effect 0x11e0b0 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[985, 983]
    (.letOp (n := 989) (.exec 0x11e0b0 (fun s => s.RIP = 0x11e0b0) (mulR64Effect 0x11e0b0 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[985, 983]
    (.letOp (n := 990) (.exec 0x11e0b3 (StorePre 0x11e0b3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11e0b3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e0b3 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[987, 4]
    (.letOp (n := 991) (.exec 0x11e0bb (StorePre 0x11e0bb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11e0bb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e0bb 2 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[988, 4]
    (.letOp (n := 992) (.out 0x11e0c3 (movR64M64Effect 0x11e0c3 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 993) (.exec 0x11e0c3 (LoadPre 0x11e0c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11e0c3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e0c3 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 994) (.out 0x11e0c8 (movR64M64Effect 0x11e0c8 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 995) (.exec 0x11e0c8 (LoadPre 0x11e0c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11e0c8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11e0c8 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 996) (.out 0x11e0cd (mulR64Effect 0x11e0cd 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[994, 992]
    (.letOp (n := 997) (.out 0x11e0cd (mulR64Effect 0x11e0cd 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[994, 992]
    (.letOp (n := 998) (.exec 0x11e0cd (fun s => s.RIP = 0x11e0cd) (mulR64Effect 0x11e0cd 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[994, 992]
    (b_l11d880_23))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_22 : List UInt8 :=
  [0x48, 0x01, 0xFB, 0x4D, 0x11, 0xD4, 0x48, 0x01, 0xEB, 0x4D, 0x11, 0xDC, 0x48, 0x03, 0x5C, 0x24,
    0x20, 0x4C, 0x13, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x03, 0x9C, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x4C, 0x13, 0xA4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x01, 0xC3, 0x49, 0x11, 0xD4, 0x4C,
    0x01, 0xF3, 0x49, 0x83, 0xD4, 0x00, 0x48, 0x89, 0xF0, 0x4C, 0x8B, 0xB4, 0x24, 0x88, 0x00, 0x00,
    0x00, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24,
    0xD0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x78, 0x48, 0x8B, 0x7C, 0x24, 0x48, 0x48, 0xF7,
    0xE7] ++ bytes_l11d880_23

theorem code_l11d880_22 : ∀ x ∈ codeRange 0x11e06f bytes_l11d880_22, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e06f 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_23

def b_l11d880_21 : Block Op Label signature Reg.count 910 :=
  .letOp (n := 910) (.out 0x11e01c (mulM64Effect 0x11e01c 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[908, 4]
    (.letOp (n := 911) (.out 0x11e01c (mulM64Effect 0x11e01c 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[908, 4]
    (.letOp (n := 912) (.exec 0x11e01c (LoadPre 0x11e01c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11e01c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11e01c 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[908, 4]
    (.letOp (n := 913) (.exec 0x11e021 (StorePre 0x11e021 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11e021 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e021 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[911, 4]
    (.letOp (n := 914) (.exec 0x11e029 (StorePre 0x11e029 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11e029 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11e029 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[910, 4]
    (.letOp (n := 915) (.out 0x11e02e (movR64R64Effect 0x11e02e 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[811]
    (.letOp (n := 916) (.exec 0x11e02e (fun s => s.RIP = 0x11e02e) (movR64R64Effect 0x11e02e 0 3) (Reg.operands [.gpr 3] [])) #v[811]
    (.letOp (n := 917) (.out 0x11e031 (mulR64Effect 0x11e031 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[860, 915]
    (.letOp (n := 918) (.out 0x11e031 (mulR64Effect 0x11e031 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[860, 915]
    (.letOp (n := 919) (.exec 0x11e031 (fun s => s.RIP = 0x11e031) (mulR64Effect 0x11e031 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[860, 915]
    (.letOp (n := 920) (.out 0x11e034 (movR64R64Effect 0x11e034 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[917]
    (.letOp (n := 921) (.exec 0x11e034 (fun s => s.RIP = 0x11e034) (movR64R64Effect 0x11e034 5 0) (Reg.operands [.gpr 0] [])) #v[917]
    (.letOp (n := 922) (.out 0x11e037 (movR64R64Effect 0x11e037 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[918]
    (.letOp (n := 923) (.exec 0x11e037 (fun s => s.RIP = 0x11e037) (movR64R64Effect 0x11e037 11 2) (Reg.operands [.gpr 2] [])) #v[918]
    (.letOp (n := 924) (.out 0x11e03a (shldR64R64Effect 0x11e03a 5 14 15 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[895, 892]
    (.letOp (n := 925) (.exec 0x11e03a (fun s => s.RIP = 0x11e03a) (shldR64R64Effect 0x11e03a 5 14 15 12) (Reg.operands [.gpr 14, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[895, 892]
    (.letOp (n := 926) (.out 0x11e03f (movR64R64Effect 0x11e03f 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[820]
    (.letOp (n := 927) (.exec 0x11e03f (fun s => s.RIP = 0x11e03f) (movR64R64Effect 0x11e03f 0 12) (Reg.operands [.gpr 12] [])) #v[820]
    (.letOp (n := 928) (.out 0x11e042 (mulR64Effect 0x11e042 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[755, 926]
    (.letOp (n := 929) (.out 0x11e042 (mulR64Effect 0x11e042 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[755, 926]
    (.letOp (n := 930) (.exec 0x11e042 (fun s => s.RIP = 0x11e042) (mulR64Effect 0x11e042 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[755, 926]
    (.letOp (n := 931) (.out 0x11e045 (movR64R64Effect 0x11e045 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[928]
    (.letOp (n := 932) (.exec 0x11e045 (fun s => s.RIP = 0x11e045) (movR64R64Effect 0x11e045 7 0) (Reg.operands [.gpr 0] [])) #v[928]
    (.letOp (n := 933) (.out 0x11e048 (movR64R64Effect 0x11e048 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[929]
    (.letOp (n := 934) (.exec 0x11e048 (fun s => s.RIP = 0x11e048) (movR64R64Effect 0x11e048 10 2) (Reg.operands [.gpr 2] [])) #v[929]
    (.letOp (n := 935) (.out 0x11e04b (movR64M64Effect 0x11e04b 6 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 936) (.exec 0x11e04b (LoadPre 0x11e04b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x11e04b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e04b 6 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 937) (.out 0x11e053 (movR64R64Effect 0x11e053 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[935]
    (.letOp (n := 938) (.exec 0x11e053 (fun s => s.RIP = 0x11e053) (movR64R64Effect 0x11e053 0 6) (Reg.operands [.gpr 6] [])) #v[935]
    (.letOp (n := 939) (.out 0x11e056 (mulR64Effect 0x11e056 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[875, 937]
    (.letOp (n := 940) (.out 0x11e056 (mulR64Effect 0x11e056 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[875, 937]
    (.letOp (n := 941) (.exec 0x11e056 (fun s => s.RIP = 0x11e056) (mulR64Effect 0x11e056 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[875, 937]
    (.letOp (n := 942) (.out 0x11e059 (movR64R64Effect 0x11e059 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[940]
    (.letOp (n := 943) (.exec 0x11e059 (fun s => s.RIP = 0x11e059) (movR64R64Effect 0x11e059 12 2) (Reg.operands [.gpr 2] [])) #v[940]
    (.letOp (n := 944) (.out 0x11e05c (movR64R64Effect 0x11e05c 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[939]
    (.letOp (n := 945) (.exec 0x11e05c (fun s => s.RIP = 0x11e05c) (movR64R64Effect 0x11e05c 3 0) (Reg.operands [.gpr 0] [])) #v[939]
    (.letOp (n := 946) (.out 0x11e05f (movR64R64Effect 0x11e05f 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[897]
    (.letOp (n := 947) (.exec 0x11e05f (fun s => s.RIP = 0x11e05f) (movR64R64Effect 0x11e05f 0 8) (Reg.operands [.gpr 8] [])) #v[897]
    (.letOp (n := 948) (.out 0x11e062 (movR64Imm64Effect 0x11e062 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 949) (.exec 0x11e062 (fun s => s.RIP = 0x11e062) (movR64Imm64Effect 0x11e062 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 950) (.out 0x11e06c (mulR64Effect 0x11e06c 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[948, 946]
    (.letOp (n := 951) (.out 0x11e06c (mulR64Effect 0x11e06c 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[948, 946]
    (.letOp (n := 952) (.exec 0x11e06c (fun s => s.RIP = 0x11e06c) (mulR64Effect 0x11e06c 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[948, 946]
    (b_l11d880_22)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_21 : List UInt8 :=
  [0x48, 0xF7, 0x64, 0x24, 0x48, 0x48, 0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44,
    0x24, 0x20, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE3, 0x48, 0x89, 0xC5, 0x49, 0x89, 0xD3, 0x4D, 0x0F,
    0xA4, 0xFE, 0x0C, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0xC7, 0x49, 0x89, 0xD2, 0x48,
    0x8B, 0xB4, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD4,
    0x48, 0x89, 0xC3, 0x4C, 0x89, 0xC0, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE1] ++ bytes_l11d880_22

theorem code_l11d880_21 : ∀ x ∈ codeRange 0x11e01c bytes_l11d880_21, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e01c 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_22

def b_l11d880_20 : Block Op Label signature Reg.count 868 :=
  .letOp (n := 868) (.exec 0x11dfa3 (StorePre 0x11dfa3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11dfa3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11dfa3 5 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[866, 4]
    (.letOp (n := 869) (.out 0x11dfab (movR64Imm64Effect 0x11dfab 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 870) (.exec 0x11dfab (fun s => s.RIP = 0x11dfab) (movR64Imm64Effect 0x11dfab 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 871) (.out 0x11dfb5 (mulR64Effect 0x11dfb5 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[869, 864]
    (.letOp (n := 872) (.out 0x11dfb5 (mulR64Effect 0x11dfb5 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[869, 864]
    (.letOp (n := 873) (.exec 0x11dfb5 (fun s => s.RIP = 0x11dfb5) (mulR64Effect 0x11dfb5 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[869, 864]
    (.letOp (n := 874) (.exec 0x11dfb8 (StorePre 0x11dfb8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11dfb8 + BitVec.ofNat 64 8)) 8) (addMREffect 0x11dfb8 8 64 10 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[848, 4]
    (.letOp (n := 875) (.out 0x11dfc0 (movR64R64Effect 0x11dfc0 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[848]
    (.letOp (n := 876) (.exec 0x11dfc0 (fun s => s.RIP = 0x11dfc0) (movR64R64Effect 0x11dfc0 1 10) (Reg.operands [.gpr 10] [])) #v[848]
    (.letOp (n := 877) (.out 0x11dfc3 (addR64M64Effect 0x11dfc3 15 (.sib 4 none 0 (.d32 0x1a8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[840, 4]
    (.letOp (n := 878) (.out 0x11dfc3 (addR64M64Effect 0x11dfc3 15 (.sib 4 none 0 (.d32 0x1a8))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[840, 4]
    (.letOp (n := 879) (.exec 0x11dfc3 (LoadPre 0x11dfc3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x11dfc3 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11dfc3 15 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[840, 4]
    (.letOp (n := 880) (.out 0x11dfcb (atFlags StatusFlags.CF (adcR64M64Effect 0x11dfcb 14 (.sib 4 none 0 (.d32 0xc8)))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 14))) #v[842, 4, 878]
    (.letOp (n := 881) (.exec 0x11dfcb (LoadPre 0x11dfcb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11dfcb + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11dfcb 14 (.sib 4 none 0 (.d32 0xc8)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[842, 4, 878]
    (.letOp (n := 882) (.out 0x11dfd3 (addR64M64Effect 0x11dfd3 15 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[877, 4]
    (.letOp (n := 883) (.out 0x11dfd3 (addR64M64Effect 0x11dfd3 15 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[877, 4]
    (.letOp (n := 884) (.exec 0x11dfd3 (LoadPre 0x11dfd3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11dfd3 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11dfd3 15 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[877, 4]
    (.letOp (n := 885) (.out 0x11dfd8 (atFlags StatusFlags.CF (adcR64M64Effect 0x11dfd8 14 (.sib 4 none 0 (.d32 0x90)))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 14))) #v[880, 4, 883]
    (.letOp (n := 886) (.exec 0x11dfd8 (LoadPre 0x11dfd8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11dfd8 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11dfd8 14 (.sib 4 none 0 (.d32 0x90)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[880, 4, 883]
    (.letOp (n := 887) (.out 0x11dfe0 (addR64M64Effect 0x11dfe0 15 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[882, 4]
    (.letOp (n := 888) (.out 0x11dfe0 (addR64M64Effect 0x11dfe0 15 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[882, 4]
    (.letOp (n := 889) (.exec 0x11dfe0 (LoadPre 0x11dfe0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11dfe0 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11dfe0 15 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[882, 4]
    (.letOp (n := 890) (.out 0x11dfe8 (atFlags StatusFlags.CF (adcR64M64Effect 0x11dfe8 14 (.sib 4 none 0 (.d32 0xd0)))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 14))) #v[885, 4, 888]
    (.letOp (n := 891) (.exec 0x11dfe8 (LoadPre 0x11dfe8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11dfe8 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11dfe8 14 (.sib 4 none 0 (.d32 0xd0)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[885, 4, 888]
    (.letOp (n := 892) (.out 0x11dff0 (addR64R64Effect 0x11dff0 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[887, 871]
    (.letOp (n := 893) (.out 0x11dff0 (addR64R64Effect 0x11dff0 15 0) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 0] []) (.flag .CF)) #v[887, 871]
    (.letOp (n := 894) (.exec 0x11dff0 (fun s => s.RIP = 0x11dff0) (addR64R64Effect 0x11dff0 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[887, 871]
    (.letOp (n := 895) (.out 0x11dff3 (atFlags StatusFlags.CF (adcR64R64Effect 0x11dff3 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[890, 872, 893]
    (.letOp (n := 896) (.exec 0x11dff3 (fun s => s.RIP = 0x11dff3) (atFlags StatusFlags.CF (adcR64R64Effect 0x11dff3 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[890, 872, 893]
    (.letOp (n := 897) (.out 0x11dff6 (shldR64R64Effect 0x11dff6 5 8 6 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[855, 853]
    (.letOp (n := 898) (.exec 0x11dff6 (fun s => s.RIP = 0x11dff6) (shldR64R64Effect 0x11dff6 5 8 6 12) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[855, 853]
    (.letOp (n := 899) (.out 0x11dffb (movR64R64Effect 0x11dffb 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[844]
    (.letOp (n := 900) (.exec 0x11dffb (fun s => s.RIP = 0x11dffb) (movR64R64Effect 0x11dffb 0 7) (Reg.operands [.gpr 7] [])) #v[844]
    (.letOp (n := 901) (.out 0x11dffe (mulR64Effect 0x11dffe 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[796, 899]
    (.letOp (n := 902) (.out 0x11dffe (mulR64Effect 0x11dffe 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[796, 899]
    (.letOp (n := 903) (.exec 0x11dffe (fun s => s.RIP = 0x11dffe) (mulR64Effect 0x11dffe 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[796, 899]
    (.letOp (n := 904) (.exec 0x11e001 (StorePre 0x11e001 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11e001 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e001 2 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[902, 4]
    (.letOp (n := 905) (.exec 0x11e009 (StorePre 0x11e009 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11e009 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11e009 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[901, 4]
    (.letOp (n := 906) (.out 0x11e011 (movR64M64Effect 0x11e011 13 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 907) (.exec 0x11e011 (LoadPre 0x11e011 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x11e011 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11e011 13 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 908) (.out 0x11e019 (movR64R64Effect 0x11e019 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[906]
    (.letOp (n := 909) (.exec 0x11e019 (fun s => s.RIP = 0x11e019) (movR64R64Effect 0x11e019 0 13) (Reg.operands [.gpr 13] [])) #v[906]
    (b_l11d880_21))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_20 : List UInt8 :=
  [0x48, 0x89, 0xAC, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x01, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xD1,
    0x4C, 0x03, 0xBC, 0x24, 0xA8, 0x01, 0x00, 0x00, 0x4C, 0x13, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00,
    0x4C, 0x03, 0x7C, 0x24, 0x20, 0x4C, 0x13, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x03, 0xBC,
    0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x13, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC7,
    0x49, 0x11, 0xD6, 0x49, 0x0F, 0xA4, 0xF0, 0x0C, 0x48, 0x89, 0xF8, 0x49, 0xF7, 0xE5, 0x48, 0x89,
    0x94, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x8B,
    0xAC, 0x24, 0x10, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE8] ++ bytes_l11d880_21

theorem code_l11d880_20 : ∀ x ∈ codeRange 0x11dfa3 bytes_l11d880_20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1dfa3 121 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_21

def b_l11d880_19 : Block Op Label signature Reg.count 830 :=
  .letOp (n := 830) (.exec 0x11df43 (StorePre 0x11df43 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11df43 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11df43 2 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[827, 4]
    (.letOp (n := 831) (.exec 0x11df4b (StorePre 0x11df4b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x11df4b + BitVec.ofNat 64 8)) 8) (addMREffect 0x11df4b 8 64 15 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[674, 4]
    (.letOp (n := 832) (.out 0x11df53 (addR64R64Effect 0x11df53 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[683, 699]
    (.letOp (n := 833) (.exec 0x11df53 (fun s => s.RIP = 0x11df53) (addR64R64Effect 0x11df53 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[683, 699]
    (.letOp (n := 834) (.exec 0x11df56 (StorePre 0x11df56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x11df56 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11df56 10 (.sib 4 none 0 (.d32 0x1b0))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[832, 4]
    (.letOp (n := 835) (.out 0x11df5e (movR64M64Effect 0x11df5e 0 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 836) (.exec 0x11df5e (LoadPre 0x11df5e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x11df5e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11df5e 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 837) (.out 0x11df66 (mulR64Effect 0x11df66 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[755, 835]
    (.letOp (n := 838) (.out 0x11df66 (mulR64Effect 0x11df66 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[755, 835]
    (.letOp (n := 839) (.exec 0x11df66 (fun s => s.RIP = 0x11df66) (mulR64Effect 0x11df66 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[755, 835]
    (.letOp (n := 840) (.out 0x11df69 (movR64R64Effect 0x11df69 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[837]
    (.letOp (n := 841) (.exec 0x11df69 (fun s => s.RIP = 0x11df69) (movR64R64Effect 0x11df69 15 0) (Reg.operands [.gpr 0] [])) #v[837]
    (.letOp (n := 842) (.out 0x11df6c (movR64R64Effect 0x11df6c 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[838]
    (.letOp (n := 843) (.exec 0x11df6c (fun s => s.RIP = 0x11df6c) (movR64R64Effect 0x11df6c 14 2) (Reg.operands [.gpr 2] [])) #v[838]
    (.letOp (n := 844) (.out 0x11df6f (movR64M64Effect 0x11df6f 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 845) (.exec 0x11df6f (LoadPre 0x11df6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11df6f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11df6f 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 846) (.out 0x11df74 (movR64R64Effect 0x11df74 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[844]
    (.letOp (n := 847) (.exec 0x11df74 (fun s => s.RIP = 0x11df74) (movR64R64Effect 0x11df74 0 7) (Reg.operands [.gpr 7] [])) #v[844]
    (.letOp (n := 848) (.out 0x11df77 (movR64M64Effect 0x11df77 10 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 849) (.exec 0x11df77 (LoadPre 0x11df77 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11df77 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11df77 10 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 850) (.out 0x11df7c (mulR64Effect 0x11df7c 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[848, 846]
    (.letOp (n := 851) (.out 0x11df7c (mulR64Effect 0x11df7c 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[848, 846]
    (.letOp (n := 852) (.exec 0x11df7c (fun s => s.RIP = 0x11df7c) (mulR64Effect 0x11df7c 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[848, 846]
    (.letOp (n := 853) (.out 0x11df7f (movR64R64Effect 0x11df7f 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[850]
    (.letOp (n := 854) (.exec 0x11df7f (fun s => s.RIP = 0x11df7f) (movR64R64Effect 0x11df7f 6 0) (Reg.operands [.gpr 0] [])) #v[850]
    (.letOp (n := 855) (.out 0x11df82 (movR64R64Effect 0x11df82 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[851]
    (.letOp (n := 856) (.exec 0x11df82 (fun s => s.RIP = 0x11df82) (movR64R64Effect 0x11df82 8 2) (Reg.operands [.gpr 2] [])) #v[851]
    (.letOp (n := 857) (.out 0x11df85 (addR64R64Effect 0x11df85 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[708, 824]
    (.letOp (n := 858) (.exec 0x11df85 (fun s => s.RIP = 0x11df85) (addR64R64Effect 0x11df85 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[708, 824]
    (.letOp (n := 859) (.exec 0x11df88 (StorePre 0x11df88 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x11df88 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11df88 11 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[857, 4]
    (.letOp (n := 860) (.out 0x11df90 (movR64R64Effect 0x11df90 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[824]
    (.letOp (n := 861) (.exec 0x11df90 (fun s => s.RIP = 0x11df90) (movR64R64Effect 0x11df90 11 1) (Reg.operands [.gpr 1] [])) #v[824]
    (.letOp (n := 862) (.out 0x11df93 (movR64Imm64Effect 0x11df93 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 863) (.exec 0x11df93 (fun s => s.RIP = 0x11df93) (movR64Imm64Effect 0x11df93 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 864) (.out 0x11df9d (andR64R64Effect 0x11df9d 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[850, 862]
    (.letOp (n := 865) (.exec 0x11df9d (fun s => s.RIP = 0x11df9d) (andR64R64Effect 0x11df9d 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[850, 862]
    (.letOp (n := 866) (.out 0x11dfa0 (addR64R64Effect 0x11dfa0 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[737, 755]
    (.letOp (n := 867) (.exec 0x11dfa0 (fun s => s.RIP = 0x11dfa0) (addR64R64Effect 0x11dfa0 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[737, 755]
    (b_l11d880_20))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_19 : List UInt8 :=
  [0x48, 0x89, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xBC, 0x24, 0x20, 0x01, 0x00, 0x00,
    0x4D, 0x01, 0xF2, 0x4C, 0x89, 0x94, 0x24, 0xB0, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xE0,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE1, 0x49, 0x89, 0xC7, 0x49, 0x89, 0xD6, 0x48, 0x8B, 0x7C, 0x24,
    0x78, 0x48, 0x89, 0xF8, 0x4C, 0x8B, 0x54, 0x24, 0x40, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xC6, 0x49,
    0x89, 0xD0, 0x49, 0x01, 0xCB, 0x4C, 0x89, 0x9C, 0x24, 0x18, 0x01, 0x00, 0x00, 0x49, 0x89, 0xCB,
    0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0, 0x4C, 0x01, 0xCD] ++ bytes_l11d880_20

theorem code_l11d880_19 : ∀ x ∈ codeRange 0x11df43 bytes_l11d880_19, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1df43 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_20

def b_l11d880_18 : Block Op Label signature Reg.count 794 :=
  .letOp (n := 794) (.out 0x11dede (movR64R64Effect 0x11dede 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[623]
    (.letOp (n := 795) (.exec 0x11dede (fun s => s.RIP = 0x11dede) (movR64R64Effect 0x11dede 0 12) (Reg.operands [.gpr 12] [])) #v[623]
    (.letOp (n := 796) (.out 0x11dee1 (movR64R64Effect 0x11dee1 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[674]
    (.letOp (n := 797) (.exec 0x11dee1 (fun s => s.RIP = 0x11dee1) (movR64R64Effect 0x11dee1 13 15) (Reg.operands [.gpr 15] [])) #v[674]
    (.letOp (n := 798) (.out 0x11dee4 (mulR64Effect 0x11dee4 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[674, 794]
    (.letOp (n := 799) (.out 0x11dee4 (mulR64Effect 0x11dee4 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[674, 794]
    (.letOp (n := 800) (.exec 0x11dee4 (fun s => s.RIP = 0x11dee4) (mulR64Effect 0x11dee4 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[674, 794]
    (.letOp (n := 801) (.exec 0x11dee7 (StorePre 0x11dee7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11dee7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11dee7 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[798, 4]
    (.letOp (n := 802) (.exec 0x11deef (StorePre 0x11deef 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11deef + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11deef 2 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[799, 4]
    (.letOp (n := 803) (.out 0x11def7 (andR64R64Effect 0x11def7 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[792, 779]
    (.letOp (n := 804) (.exec 0x11def7 (fun s => s.RIP = 0x11def7) (andR64R64Effect 0x11def7 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[792, 779]
    (.letOp (n := 805) (.exec 0x11defa (StorePre 0x11defa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11defa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11defa 3 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[803, 4]
    (.letOp (n := 806) (.out 0x11df02 (movR64M64Effect 0x11df02 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 807) (.exec 0x11df02 (LoadPre 0x11df02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11df02 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11df02 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 808) (.out 0x11df07 (addR64R64Effect 0x11df07 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[806, 806]
    (.letOp (n := 809) (.exec 0x11df07 (fun s => s.RIP = 0x11df07) (addR64R64Effect 0x11df07 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[806, 806]
    (.letOp (n := 810) (.exec 0x11df0a (StorePre 0x11df0a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11df0a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11df0a 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[808, 4]
    (.letOp (n := 811) (.out 0x11df0f (movR64M64Effect 0x11df0f 3 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 812) (.exec 0x11df0f (LoadPre 0x11df0f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11df0f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11df0f 3 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 813) (.out 0x11df17 (movR64R64Effect 0x11df17 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[811]
    (.letOp (n := 814) (.exec 0x11df17 (fun s => s.RIP = 0x11df17) (movR64R64Effect 0x11df17 0 3) (Reg.operands [.gpr 3] [])) #v[811]
    (.letOp (n := 815) (.out 0x11df1a (mulR64Effect 0x11df1a 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[699, 813]
    (.letOp (n := 816) (.out 0x11df1a (mulR64Effect 0x11df1a 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[699, 813]
    (.letOp (n := 817) (.exec 0x11df1a (fun s => s.RIP = 0x11df1a) (mulR64Effect 0x11df1a 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[699, 813]
    (.letOp (n := 818) (.exec 0x11df1d (StorePre 0x11df1d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11df1d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11df1d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[815, 4]
    (.letOp (n := 819) (.exec 0x11df22 (StorePre 0x11df22 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11df22 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11df22 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[816, 4]
    (.letOp (n := 820) (.out 0x11df2a (movR64M64Effect 0x11df2a 12 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 821) (.exec 0x11df2a (LoadPre 0x11df2a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x11df2a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11df2a 12 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 822) (.out 0x11df32 (movR64R64Effect 0x11df32 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[820]
    (.letOp (n := 823) (.exec 0x11df32 (fun s => s.RIP = 0x11df32) (movR64R64Effect 0x11df32 0 12) (Reg.operands [.gpr 12] [])) #v[820]
    (.letOp (n := 824) (.out 0x11df35 (movR64R64Effect 0x11df35 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[722]
    (.letOp (n := 825) (.exec 0x11df35 (fun s => s.RIP = 0x11df35) (movR64R64Effect 0x11df35 1 8) (Reg.operands [.gpr 8] [])) #v[722]
    (.letOp (n := 826) (.out 0x11df38 (mulR64Effect 0x11df38 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[722, 822]
    (.letOp (n := 827) (.out 0x11df38 (mulR64Effect 0x11df38 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[722, 822]
    (.letOp (n := 828) (.exec 0x11df38 (fun s => s.RIP = 0x11df38) (mulR64Effect 0x11df38 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[722, 822]
    (.letOp (n := 829) (.exec 0x11df3b (StorePre 0x11df3b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x11df3b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11df3b 0 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[826, 4]
    (b_l11d880_19))))))))))))))))))))))))))))))))))))

def bytes_l11d880_18 : List UInt8 :=
  [0x4C, 0x89, 0xE0, 0x4D, 0x89, 0xFD, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x94, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x21, 0xCB, 0x48, 0x89, 0x9C, 0x24,
    0xF8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x01, 0xC0, 0x48, 0x89, 0x44, 0x24,
    0x10, 0x48, 0x8B, 0x9C, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE6, 0x48,
    0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0xA4, 0x24,
    0x08, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x4C, 0x89, 0xC1, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0x84,
    0x24, 0xA8, 0x01, 0x00, 0x00] ++ bytes_l11d880_19

theorem code_l11d880_18 : ∀ x ∈ codeRange 0x11dede bytes_l11d880_18, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1dede 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_19

def b_l11d880_17 : Block Op Label signature Reg.count 759 :=
  .letOp (n := 759) (.out 0x11de7b (subR64R64Effect 0x11de7b 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[757, 753]
    (.letOp (n := 760) (.exec 0x11de7b (fun s => s.RIP = 0x11de7b) (subR64R64Effect 0x11de7b 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[757, 753]
    (.letOp (n := 761) (.exec 0x11de7e (StorePre 0x11de7e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11de7e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11de7e 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[759, 4]
    (.letOp (n := 762) (.out 0x11de83 (movR64Imm64Effect 0x11de83 0 0x3fffffffffffc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 763) (.exec 0x11de83 (fun s => s.RIP = 0x11de83) (movR64Imm64Effect 0x11de83 0 0x3fffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 764) (.out 0x11de8d (movR64M64Effect 0x11de8d 2 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 765) (.exec 0x11de8d (LoadPre 0x11de8d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11de8d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11de8d 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 766) (.out 0x11de92 (addR64R64Effect 0x11de92 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[762, 764]
    (.letOp (n := 767) (.exec 0x11de92 (fun s => s.RIP = 0x11de92) (addR64R64Effect 0x11de92 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[762, 764]
    (.letOp (n := 768) (.out 0x11de95 (subR64R64Effect 0x11de95 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[766, 749]
    (.letOp (n := 769) (.exec 0x11de95 (fun s => s.RIP = 0x11de95) (subR64R64Effect 0x11de95 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[766, 749]
    (.letOp (n := 770) (.exec 0x11de98 (StorePre 0x11de98 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11de98 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11de98 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[768, 4]
    (.letOp (n := 771) (.out 0x11de9d (movR64M64Effect 0x11de9d 2 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 772) (.exec 0x11de9d (LoadPre 0x11de9d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11de9d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11de9d 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 773) (.out 0x11dea5 (addR64R64Effect 0x11dea5 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[771, 771]
    (.letOp (n := 774) (.exec 0x11dea5 (fun s => s.RIP = 0x11dea5) (addR64R64Effect 0x11dea5 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[771, 771]
    (.letOp (n := 775) (.out 0x11dea8 (movR64M64Effect 0x11dea8 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 776) (.exec 0x11dea8 (LoadPre 0x11dea8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11dea8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11dea8 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 777) (.out 0x11dead (addR64R64Effect 0x11dead 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[775, 775]
    (.letOp (n := 778) (.exec 0x11dead (fun s => s.RIP = 0x11dead) (addR64R64Effect 0x11dead 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[775, 775]
    (.letOp (n := 779) (.out 0x11deb0 (movR64Imm64Effect 0x11deb0 1 0x1ffffffffffffe) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 780) (.exec 0x11deb0 (fun s => s.RIP = 0x11deb0) (movR64Imm64Effect 0x11deb0 1 0x1ffffffffffffe) (Reg.operands [] [])) #v[]
    (.letOp (n := 781) (.out 0x11deba (andR64R64Effect 0x11deba 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[773, 779]
    (.letOp (n := 782) (.exec 0x11deba (fun s => s.RIP = 0x11deba) (andR64R64Effect 0x11deba 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[773, 779]
    (.letOp (n := 783) (.exec 0x11debd (StorePre 0x11debd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11debd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11debd 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[781, 4]
    (.letOp (n := 784) (.out 0x11dec5 (andR64R64Effect 0x11dec5 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[777, 779]
    (.letOp (n := 785) (.exec 0x11dec5 (fun s => s.RIP = 0x11dec5) (andR64R64Effect 0x11dec5 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[777, 779]
    (.letOp (n := 786) (.exec 0x11dec8 (StorePre 0x11dec8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11dec8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11dec8 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[784, 4]
    (.letOp (n := 787) (.out 0x11decd (addR64R64Effect 0x11decd 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[522, 522]
    (.letOp (n := 788) (.exec 0x11decd (fun s => s.RIP = 0x11decd) (addR64R64Effect 0x11decd 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[522, 522]
    (.letOp (n := 789) (.out 0x11ded0 (andR64R64Effect 0x11ded0 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[787, 779]
    (.letOp (n := 790) (.exec 0x11ded0 (fun s => s.RIP = 0x11ded0) (andR64R64Effect 0x11ded0 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[787, 779]
    (.letOp (n := 791) (.exec 0x11ded3 (StorePre 0x11ded3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11ded3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ded3 13 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[789, 4]
    (.letOp (n := 792) (.out 0x11dedb (addR64R64Effect 0x11dedb 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[554, 554]
    (.letOp (n := 793) (.exec 0x11dedb (fun s => s.RIP = 0x11dedb) (addR64R64Effect 0x11dedb 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[554, 554]
    (b_l11d880_18)))))))))))))))))))))))))))))))))))

def bytes_l11d880_17 : List UInt8 :=
  [0x48, 0x29, 0xD0, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x03, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x40, 0x48, 0x01, 0xD0, 0x48, 0x29, 0xC8, 0x48, 0x89, 0x44,
    0x24, 0x08, 0x48, 0x8B, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x01, 0xD2, 0x48, 0x8B, 0x74,
    0x24, 0x18, 0x48, 0x01, 0xF6, 0x48, 0xB9, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x1F, 0x00, 0x48,
    0x21, 0xCA, 0x48, 0x89, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x21, 0xCE, 0x48, 0x89, 0x74,
    0x24, 0x18, 0x4D, 0x01, 0xED, 0x49, 0x21, 0xCD, 0x4C, 0x89, 0xAC, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x48, 0x01, 0xDB] ++ bytes_l11d880_18

theorem code_l11d880_17 : ∀ x ∈ codeRange 0x11de7b bytes_l11d880_17, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1de7b 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_18

def b_l11d880_16 : Block Op Label signature Reg.count 720 :=
  .letOp (n := 720) (.out 0x11de1f (andR64R64Effect 0x11de1f 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[714, 718]
    (.letOp (n := 721) (.exec 0x11de1f (fun s => s.RIP = 0x11de1f) (andR64R64Effect 0x11de1f 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[714, 718]
    (.letOp (n := 722) (.out 0x11de22 (movR64M64Effect 0x11de22 8 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 723) (.exec 0x11de22 (LoadPre 0x11de22 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11de22 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11de22 8 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 724) (.out 0x11de27 (leaR64Effect 0x11de27 6 (.sib 8 (some 7) 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8, .gpr 7] []) (.reg (.gpr 6))) #v[722, 697]
    (.letOp (n := 725) (.exec 0x11de27 (fun s => s.RIP = 0x11de27) (leaR64Effect 0x11de27 6 (.sib 8 (some 7) 0 .none)) (Reg.operands [.gpr 8, .gpr 7] [])) #v[722, 697]
    (.letOp (n := 726) (.out 0x11de2b (subR64R64Effect 0x11de2b 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[724, 720]
    (.letOp (n := 727) (.exec 0x11de2b (fun s => s.RIP = 0x11de2b) (subR64R64Effect 0x11de2b 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[724, 720]
    (.letOp (n := 728) (.exec 0x11de2e (StorePre 0x11de2e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11de2e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11de2e 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[726, 4]
    (.letOp (n := 729) (.out 0x11de33 (movR64Imm64Effect 0x11de33 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 730) (.exec 0x11de33 (fun s => s.RIP = 0x11de33) (movR64Imm64Effect 0x11de33 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 731) (.out 0x11de3d (andR64R64Effect 0x11de3d 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[642, 729]
    (.letOp (n := 732) (.exec 0x11de3d (fun s => s.RIP = 0x11de3d) (andR64R64Effect 0x11de3d 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[642, 729]
    (.letOp (n := 733) (.out 0x11de40 (shrR64Effect 0x11de40 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[716]
    (.letOp (n := 734) (.exec 0x11de40 (fun s => s.RIP = 0x11de40) (shrR64Effect 0x11de40 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[716]
    (.letOp (n := 735) (.out 0x11de44 (leaR64Effect 0x11de44 1 (.sib 9 (some 9) 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9, .gpr 9] []) (.reg (.gpr 1))) #v[731, 731]
    (.letOp (n := 736) (.exec 0x11de44 (fun s => s.RIP = 0x11de44) (leaR64Effect 0x11de44 1 (.sib 9 (some 9) 1 .none)) (Reg.operands [.gpr 9, .gpr 9] [])) #v[731, 731]
    (.letOp (n := 737) (.out 0x11de48 (movR64R64Effect 0x11de48 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[731]
    (.letOp (n := 738) (.exec 0x11de48 (fun s => s.RIP = 0x11de48) (movR64R64Effect 0x11de48 5 9) (Reg.operands [.gpr 9] [])) #v[731]
    (.letOp (n := 739) (.out 0x11de4b (addR64R64Effect 0x11de4b 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[733, 735]
    (.letOp (n := 740) (.exec 0x11de4b (fun s => s.RIP = 0x11de4b) (addR64R64Effect 0x11de4b 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[733, 735]
    (.letOp (n := 741) (.out 0x11de4e (movR64Imm64Effect 0x11de4e 1 0xffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 742) (.exec 0x11de4e (fun s => s.RIP = 0x11de4e) (movR64Imm64Effect 0x11de4e 1 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 743) (.out 0x11de58 (andR64R64Effect 0x11de58 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[654, 741]
    (.letOp (n := 744) (.exec 0x11de58 (fun s => s.RIP = 0x11de58) (andR64R64Effect 0x11de58 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[654, 741]
    (.letOp (n := 745) (.out 0x11de5b (movR64R64Effect 0x11de5b 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[739]
    (.letOp (n := 746) (.exec 0x11de5b (fun s => s.RIP = 0x11de5b) (movR64R64Effect 0x11de5b 1 2) (Reg.operands [.gpr 2] [])) #v[739]
    (.letOp (n := 747) (.out 0x11de5e (shrR64Effect 0x11de5e 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[745]
    (.letOp (n := 748) (.exec 0x11de5e (fun s => s.RIP = 0x11de5e) (shrR64Effect 0x11de5e 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[745]
    (.letOp (n := 749) (.out 0x11de62 (addR64R64Effect 0x11de62 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[747, 743]
    (.letOp (n := 750) (.exec 0x11de62 (fun s => s.RIP = 0x11de62) (addR64R64Effect 0x11de62 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[747, 743]
    (.letOp (n := 751) (.out 0x11de65 (movR64Imm64Effect 0x11de65 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 752) (.exec 0x11de65 (fun s => s.RIP = 0x11de65) (movR64Imm64Effect 0x11de65 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 753) (.out 0x11de6f (andR64R64Effect 0x11de6f 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[739, 751]
    (.letOp (n := 754) (.exec 0x11de6f (fun s => s.RIP = 0x11de6f) (andR64R64Effect 0x11de6f 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[739, 751]
    (.letOp (n := 755) (.out 0x11de72 (movR64M64Effect 0x11de72 9 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 756) (.exec 0x11de72 (LoadPre 0x11de72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11de72 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11de72 9 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 757) (.out 0x11de77 (leaR64Effect 0x11de77 0 (.sib 9 (some 7) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 7] []) (.reg (.gpr 0))) #v[755, 697]
    (.letOp (n := 758) (.exec 0x11de77 (fun s => s.RIP = 0x11de77) (leaR64Effect 0x11de77 0 (.sib 9 (some 7) 0 .none)) (Reg.operands [.gpr 9, .gpr 7] [])) #v[755, 697]
    (b_l11d880_17)))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_16 : List UInt8 :=
  [0x48, 0x21, 0xF1, 0x4C, 0x8B, 0x44, 0x24, 0x50, 0x49, 0x8D, 0x34, 0x38, 0x48, 0x29, 0xCE, 0x48,
    0x89, 0x74, 0x24, 0x70, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21,
    0xC9, 0x48, 0xC1, 0xEA, 0x34, 0x4B, 0x8D, 0x0C, 0x49, 0x4C, 0x89, 0xCD, 0x48, 0x01, 0xCA, 0x48,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x21, 0xC8, 0x48, 0x89, 0xD1, 0x48,
    0xC1, 0xE9, 0x34, 0x48, 0x01, 0xC1, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x48, 0x21, 0xC2, 0x4C, 0x8B, 0x4C, 0x24, 0x30, 0x49, 0x8D, 0x04, 0x39] ++ bytes_l11d880_17

theorem code_l11d880_16 : ∀ x ∈ codeRange 0x11de1f bytes_l11d880_16, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1de1f 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_17

def b_l11d880_15 : Block Op Label signature Reg.count 681 :=
  .letOp (n := 681) (.out 0x11ddb4 (movR64Imm64Effect 0x11ddb4 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 682) (.exec 0x11ddb4 (fun s => s.RIP = 0x11ddb4) (movR64Imm64Effect 0x11ddb4 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 683) (.out 0x11ddbe (andR64R64Effect 0x11ddbe 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[617, 681]
    (.letOp (n := 684) (.exec 0x11ddbe (fun s => s.RIP = 0x11ddbe) (andR64R64Effect 0x11ddbe 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[617, 681]
    (.letOp (n := 685) (.out 0x11ddc1 (shrR64Effect 0x11ddc1 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[666]
    (.letOp (n := 686) (.exec 0x11ddc1 (fun s => s.RIP = 0x11ddc1) (shrR64Effect 0x11ddc1 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[666]
    (.letOp (n := 687) (.out 0x11ddc5 (leaR64Effect 0x11ddc5 1 (.sib 10 (some 10) 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10, .gpr 10] []) (.reg (.gpr 1))) #v[683, 683]
    (.letOp (n := 688) (.exec 0x11ddc5 (fun s => s.RIP = 0x11ddc5) (leaR64Effect 0x11ddc5 1 (.sib 10 (some 10) 1 .none)) (Reg.operands [.gpr 10, .gpr 10] [])) #v[683, 683]
    (.letOp (n := 689) (.out 0x11ddc9 (addR64R64Effect 0x11ddc9 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[685, 687]
    (.letOp (n := 690) (.exec 0x11ddc9 (fun s => s.RIP = 0x11ddc9) (addR64R64Effect 0x11ddc9 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[685, 687]
    (.letOp (n := 691) (.out 0x11ddcc (movR64R64Effect 0x11ddcc 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[689]
    (.letOp (n := 692) (.exec 0x11ddcc (fun s => s.RIP = 0x11ddcc) (movR64R64Effect 0x11ddcc 1 2) (Reg.operands [.gpr 2] [])) #v[689]
    (.letOp (n := 693) (.out 0x11ddcf (movR64Imm64Effect 0x11ddcf 6 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 694) (.exec 0x11ddcf (fun s => s.RIP = 0x11ddcf) (movR64Imm64Effect 0x11ddcf 6 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 695) (.out 0x11ddd9 (andR64R64Effect 0x11ddd9 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[689, 693]
    (.letOp (n := 696) (.exec 0x11ddd9 (fun s => s.RIP = 0x11ddd9) (andR64R64Effect 0x11ddd9 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[689, 693]
    (.letOp (n := 697) (.out 0x11dddc (movR64Imm64Effect 0x11dddc 7 0x3ffffffffffffc) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 698) (.exec 0x11dddc (fun s => s.RIP = 0x11dddc) (movR64Imm64Effect 0x11dddc 7 0x3ffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 699) (.out 0x11dde6 (movR64M64Effect 0x11dde6 14 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 700) (.exec 0x11dde6 (LoadPre 0x11dde6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11dde6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11dde6 14 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 701) (.out 0x11ddeb (leaR64Effect 0x11ddeb 6 (.sib 14 (some 7) 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14, .gpr 7] []) (.reg (.gpr 6))) #v[699, 697]
    (.letOp (n := 702) (.exec 0x11ddeb (fun s => s.RIP = 0x11ddeb) (leaR64Effect 0x11ddeb 6 (.sib 14 (some 7) 0 .none)) (Reg.operands [.gpr 14, .gpr 7] [])) #v[699, 697]
    (.letOp (n := 703) (.out 0x11ddef (subR64R64Effect 0x11ddef 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[701, 695]
    (.letOp (n := 704) (.exec 0x11ddef (fun s => s.RIP = 0x11ddef) (subR64R64Effect 0x11ddef 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[701, 695]
    (.letOp (n := 705) (.exec 0x11ddf2 (StorePre 0x11ddf2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11ddf2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ddf2 6 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[703, 4]
    (.letOp (n := 706) (.out 0x11ddfa (movR64Imm64Effect 0x11ddfa 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 707) (.exec 0x11ddfa (fun s => s.RIP = 0x11ddfa) (movR64Imm64Effect 0x11ddfa 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 708) (.out 0x11de04 (andR64R64Effect 0x11de04 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[632, 706]
    (.letOp (n := 709) (.exec 0x11de04 (fun s => s.RIP = 0x11de04) (andR64R64Effect 0x11de04 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[632, 706]
    (.letOp (n := 710) (.out 0x11de07 (shrR64Effect 0x11de07 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[691]
    (.letOp (n := 711) (.exec 0x11de07 (fun s => s.RIP = 0x11de07) (shrR64Effect 0x11de07 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[691]
    (.letOp (n := 712) (.out 0x11de0b (leaR64Effect 0x11de0b 2 (.sib 11 (some 11) 1 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 11] []) (.reg (.gpr 2))) #v[708, 708]
    (.letOp (n := 713) (.exec 0x11de0b (fun s => s.RIP = 0x11de0b) (leaR64Effect 0x11de0b 2 (.sib 11 (some 11) 1 .none)) (Reg.operands [.gpr 11, .gpr 11] [])) #v[708, 708]
    (.letOp (n := 714) (.out 0x11de0f (addR64R64Effect 0x11de0f 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[710, 712]
    (.letOp (n := 715) (.exec 0x11de0f (fun s => s.RIP = 0x11de0f) (addR64R64Effect 0x11de0f 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[710, 712]
    (.letOp (n := 716) (.out 0x11de12 (movR64R64Effect 0x11de12 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[714]
    (.letOp (n := 717) (.exec 0x11de12 (fun s => s.RIP = 0x11de12) (movR64R64Effect 0x11de12 2 1) (Reg.operands [.gpr 1] [])) #v[714]
    (.letOp (n := 718) (.out 0x11de15 (movR64Imm64Effect 0x11de15 6 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 719) (.exec 0x11de15 (fun s => s.RIP = 0x11de15) (movR64Imm64Effect 0x11de15 6 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l11d880_16)))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_15 : List UInt8 :=
  [0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xCA, 0x48, 0xC1, 0xEA,
    0x34, 0x4B, 0x8D, 0x0C, 0x52, 0x48, 0x01, 0xCA, 0x48, 0x89, 0xD1, 0x48, 0xBE, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xF2, 0x48, 0xBF, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x3F, 0x00, 0x4C, 0x8B, 0x74, 0x24, 0x48, 0x49, 0x8D, 0x34, 0x3E, 0x48, 0x29, 0xD6, 0x48, 0x89,
    0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x49, 0x21, 0xD3, 0x48, 0xC1, 0xE9, 0x34, 0x4B, 0x8D, 0x14, 0x5B, 0x48, 0x01, 0xD1, 0x48, 0x89,
    0xCA, 0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] ++ bytes_l11d880_16

theorem code_l11d880_15 : ∀ x ∈ codeRange 0x11ddb4 bytes_l11d880_15, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ddb4 107 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_16

def b_l11d880_14 : Block Op Label signature Reg.count 644 :=
  .letOp (n := 644) (.out 0x11dd4d (shrR64Effect 0x11dd4d 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[640]
    (.letOp (n := 645) (.exec 0x11dd4d (fun s => s.RIP = 0x11dd4d) (shrR64Effect 0x11dd4d 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[640]
    (.letOp (n := 646) (.out 0x11dd51 (addR64R64Effect 0x11dd51 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[644, 638]
    (.letOp (n := 647) (.exec 0x11dd51 (fun s => s.RIP = 0x11dd51) (addR64R64Effect 0x11dd51 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[644, 638]
    (.letOp (n := 648) (.exec 0x11dd54 (StorePre 0x11dd54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11dd54 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11dd54 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[646, 4]
    (.letOp (n := 649) (.out 0x11dd5c (movR64Imm64Effect 0x11dd5c 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 650) (.exec 0x11dd5c (fun s => s.RIP = 0x11dd5c) (movR64Imm64Effect 0x11dd5c 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 651) (.out 0x11dd66 (andR64R64Effect 0x11dd66 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[602, 649]
    (.letOp (n := 652) (.exec 0x11dd66 (fun s => s.RIP = 0x11dd66) (andR64R64Effect 0x11dd66 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[602, 649]
    (.letOp (n := 653) (.exec 0x11dd69 (StorePre 0x11dd69 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x11dd69 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11dd69 7 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[651, 4]
    (.letOp (n := 654) (.out 0x11dd71 (leaR64Effect 0x11dd71 0 (.sib 1 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 1] []) (.reg (.gpr 0))) #v[646, 646]
    (.letOp (n := 655) (.exec 0x11dd71 (fun s => s.RIP = 0x11dd71) (leaR64Effect 0x11dd71 0 (.sib 1 (some 1) 1 .none)) (Reg.operands [.gpr 1, .gpr 1] [])) #v[646, 646]
    (.letOp (n := 656) (.out 0x11dd75 (movR64R64Effect 0x11dd75 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[654]
    (.letOp (n := 657) (.exec 0x11dd75 (fun s => s.RIP = 0x11dd75) (movR64R64Effect 0x11dd75 1 0) (Reg.operands [.gpr 0] [])) #v[654]
    (.letOp (n := 658) (.out 0x11dd78 (shrR64Effect 0x11dd78 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[656]
    (.letOp (n := 659) (.exec 0x11dd78 (fun s => s.RIP = 0x11dd78) (shrR64Effect 0x11dd78 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[656]
    (.letOp (n := 660) (.out 0x11dd7c (imulR64R64Effect 0x11dd7c 4 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[658, 587]
    (.letOp (n := 661) (.exec 0x11dd7c (fun s => s.RIP = 0x11dd7c) (imulR64R64Effect 0x11dd7c 4 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[658, 587]
    (.letOp (n := 662) (.out 0x11dd80 (leaR64Effect 0x11dd80 2 (.sib 7 (some 7) 1 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 7] []) (.reg (.gpr 2))) #v[651, 651]
    (.letOp (n := 663) (.exec 0x11dd80 (fun s => s.RIP = 0x11dd80) (leaR64Effect 0x11dd80 2 (.sib 7 (some 7) 1 .none)) (Reg.operands [.gpr 7, .gpr 7] [])) #v[651, 651]
    (.letOp (n := 664) (.out 0x11dd84 (addR64R64Effect 0x11dd84 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[660, 662]
    (.letOp (n := 665) (.exec 0x11dd84 (fun s => s.RIP = 0x11dd84) (addR64R64Effect 0x11dd84 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[660, 662]
    (.letOp (n := 666) (.out 0x11dd87 (movR64R64Effect 0x11dd87 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[664]
    (.letOp (n := 667) (.exec 0x11dd87 (fun s => s.RIP = 0x11dd87) (movR64R64Effect 0x11dd87 2 1) (Reg.operands [.gpr 1] [])) #v[664]
    (.letOp (n := 668) (.out 0x11dd8a (movR64Imm64Effect 0x11dd8a 6 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 669) (.exec 0x11dd8a (fun s => s.RIP = 0x11dd8a) (movR64Imm64Effect 0x11dd8a 6 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 670) (.out 0x11dd94 (andR64R64Effect 0x11dd94 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[664, 668]
    (.letOp (n := 671) (.exec 0x11dd94 (fun s => s.RIP = 0x11dd94) (andR64R64Effect 0x11dd94 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[664, 668]
    (.letOp (n := 672) (.out 0x11dd97 (movR64Imm64Effect 0x11dd97 6 0x3ffffbfffff0bc) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 673) (.exec 0x11dd97 (fun s => s.RIP = 0x11dd97) (movR64Imm64Effect 0x11dd97 6 0x3ffffbfffff0bc) (Reg.operands [] [])) #v[]
    (.letOp (n := 674) (.out 0x11dda1 (movR64M64Effect 0x11dda1 15 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 675) (.exec 0x11dda1 (LoadPre 0x11dda1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11dda1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11dda1 15 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 676) (.out 0x11dda9 (addR64R64Effect 0x11dda9 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[672, 674]
    (.letOp (n := 677) (.exec 0x11dda9 (fun s => s.RIP = 0x11dda9) (addR64R64Effect 0x11dda9 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[672, 674]
    (.letOp (n := 678) (.out 0x11ddac (subR64R64Effect 0x11ddac 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[676, 670]
    (.letOp (n := 679) (.exec 0x11ddac (fun s => s.RIP = 0x11ddac) (subR64R64Effect 0x11ddac 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[676, 670]
    (.letOp (n := 680) (.exec 0x11ddaf (StorePre 0x11ddaf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11ddaf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ddaf 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[678, 4]
    (b_l11d880_15)))))))))))))))))))))))))))))))))))))

def bytes_l11d880_14 : List UInt8 :=
  [0x48, 0xC1, 0xE9, 0x34, 0x48, 0x01, 0xC1, 0x48, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC7, 0x48, 0x89, 0xBC, 0x24,
    0x20, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x04, 0x49, 0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x30, 0x48,
    0x0F, 0xAF, 0xCD, 0x48, 0x8D, 0x14, 0x7F, 0x48, 0x01, 0xD1, 0x48, 0x89, 0xCA, 0x48, 0xBE, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xF1, 0x48, 0xBE, 0xBC, 0xF0, 0xFF, 0xFF,
    0xFB, 0xFF, 0x3F, 0x00, 0x4C, 0x8B, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xFE, 0x48,
    0x29, 0xCE, 0x48, 0x89, 0x74, 0x24, 0x68] ++ bytes_l11d880_15

theorem code_l11d880_14 : ∀ x ∈ codeRange 0x11dd4d bytes_l11d880_14, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1dd4d 103 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_15

def b_l11d880_13 : Block Op Label signature Reg.count 606 :=
  .letOp (n := 606) (.out 0x11dcf7 (addR64R64Effect 0x11dcf7 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[604, 598]
    (.letOp (n := 607) (.exec 0x11dcf7 (fun s => s.RIP = 0x11dcf7) (addR64R64Effect 0x11dcf7 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[604, 598]
    (.letOp (n := 608) (.out 0x11dcfa (movR64M64Effect 0x11dcfa 2 (.sib 4 none 0 (.d32 0x4a0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 609) (.exec 0x11dcfa (LoadPre 0x11dcfa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x4a0)) s (0x11dcfa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11dcfa 2 (.sib 4 none 0 (.d32 0x4a0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 610) (.exec 0x11dd02 (StorePre 0x11dd02 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11dd02 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11dd02 2 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[608, 4]
    (.letOp (n := 611) (.out 0x11dd0a (leaR64Effect 0x11dd0a 1 (.sib 2 (some 2) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 2] []) (.reg (.gpr 1))) #v[608, 608]
    (.letOp (n := 612) (.exec 0x11dd0a (fun s => s.RIP = 0x11dd0a) (leaR64Effect 0x11dd0a 1 (.sib 2 (some 2) 2 .none)) (Reg.operands [.gpr 2, .gpr 2] [])) #v[608, 608]
    (.letOp (n := 613) (.out 0x11dd0e (leaR64Effect 0x11dd0e 1 (.sib 2 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 1] []) (.reg (.gpr 1))) #v[608, 611]
    (.letOp (n := 614) (.exec 0x11dd0e (fun s => s.RIP = 0x11dd0e) (leaR64Effect 0x11dd0e 1 (.sib 2 (some 1) 2 .none)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[608, 611]
    (.letOp (n := 615) (.out 0x11dd12 (movR64R64Effect 0x11dd12 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[606]
    (.letOp (n := 616) (.exec 0x11dd12 (fun s => s.RIP = 0x11dd12) (movR64R64Effect 0x11dd12 9 8) (Reg.operands [.gpr 8] [])) #v[606]
    (.letOp (n := 617) (.out 0x11dd15 (movR64R64Effect 0x11dd15 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[606]
    (.letOp (n := 618) (.exec 0x11dd15 (fun s => s.RIP = 0x11dd15) (movR64R64Effect 0x11dd15 10 8) (Reg.operands [.gpr 8] [])) #v[606]
    (.letOp (n := 619) (.out 0x11dd18 (shrR64Effect 0x11dd18 4 9 52) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[615]
    (.letOp (n := 620) (.exec 0x11dd18 (fun s => s.RIP = 0x11dd18) (shrR64Effect 0x11dd18 4 9 52) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[615]
    (.letOp (n := 621) (.out 0x11dd1c (addR64R64Effect 0x11dd1c 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[619, 613]
    (.letOp (n := 622) (.exec 0x11dd1c (fun s => s.RIP = 0x11dd1c) (addR64R64Effect 0x11dd1c 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[619, 613]
    (.letOp (n := 623) (.out 0x11dd1f (movR64M64Effect 0x11dd1f 12 (.sib 4 none 0 (.d32 0x4a8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 624) (.exec 0x11dd1f (LoadPre 0x11dd1f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x4a8)) s (0x11dd1f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11dd1f 12 (.sib 4 none 0 (.d32 0x4a8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 625) (.out 0x11dd27 (leaR64Effect 0x11dd27 1 (.sib 12 (some 12) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12, .gpr 12] []) (.reg (.gpr 1))) #v[623, 623]
    (.letOp (n := 626) (.exec 0x11dd27 (fun s => s.RIP = 0x11dd27) (leaR64Effect 0x11dd27 1 (.sib 12 (some 12) 2 .none)) (Reg.operands [.gpr 12, .gpr 12] [])) #v[623, 623]
    (.letOp (n := 627) (.out 0x11dd2b (leaR64Effect 0x11dd2b 1 (.sib 12 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12, .gpr 1] []) (.reg (.gpr 1))) #v[623, 625]
    (.letOp (n := 628) (.exec 0x11dd2b (fun s => s.RIP = 0x11dd2b) (leaR64Effect 0x11dd2b 1 (.sib 12 (some 1) 2 .none)) (Reg.operands [.gpr 12, .gpr 1] [])) #v[623, 625]
    (.letOp (n := 629) (.exec 0x11dd2f (StorePre 0x11dd2f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x11dd2f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11dd2f 12 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[623, 4]
    (.letOp (n := 630) (.out 0x11dd37 (movR64R64Effect 0x11dd37 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[621]
    (.letOp (n := 631) (.exec 0x11dd37 (fun s => s.RIP = 0x11dd37) (movR64R64Effect 0x11dd37 2 9) (Reg.operands [.gpr 9] [])) #v[621]
    (.letOp (n := 632) (.out 0x11dd3a (movR64R64Effect 0x11dd3a 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[621]
    (.letOp (n := 633) (.exec 0x11dd3a (fun s => s.RIP = 0x11dd3a) (movR64R64Effect 0x11dd3a 11 9) (Reg.operands [.gpr 9] [])) #v[621]
    (.letOp (n := 634) (.out 0x11dd3d (shrR64Effect 0x11dd3d 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[630]
    (.letOp (n := 635) (.exec 0x11dd3d (fun s => s.RIP = 0x11dd3d) (shrR64Effect 0x11dd3d 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[630]
    (.letOp (n := 636) (.out 0x11dd41 (addR64R64Effect 0x11dd41 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[634, 627]
    (.letOp (n := 637) (.exec 0x11dd41 (fun s => s.RIP = 0x11dd41) (addR64R64Effect 0x11dd41 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[634, 627]
    (.letOp (n := 638) (.out 0x11dd44 (andR64R64Effect 0x11dd44 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[581, 558]
    (.letOp (n := 639) (.exec 0x11dd44 (fun s => s.RIP = 0x11dd44) (andR64R64Effect 0x11dd44 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[581, 558]
    (.letOp (n := 640) (.out 0x11dd47 (movR64R64Effect 0x11dd47 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[636]
    (.letOp (n := 641) (.exec 0x11dd47 (fun s => s.RIP = 0x11dd47) (movR64R64Effect 0x11dd47 1 2) (Reg.operands [.gpr 2] [])) #v[636]
    (.letOp (n := 642) (.out 0x11dd4a (movR64R64Effect 0x11dd4a 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[636]
    (.letOp (n := 643) (.exec 0x11dd4a (fun s => s.RIP = 0x11dd4a) (movR64R64Effect 0x11dd4a 9 2) (Reg.operands [.gpr 2] [])) #v[636]
    (b_l11d880_14))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_13 : List UInt8 :=
  [0x49, 0x01, 0xC8, 0x48, 0x8B, 0x94, 0x24, 0xA0, 0x04, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xE8,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x0C, 0x92, 0x48, 0x8D, 0x0C, 0x8A, 0x4D, 0x89, 0xC1, 0x4D, 0x89,
    0xC2, 0x49, 0xC1, 0xE9, 0x34, 0x49, 0x01, 0xC9, 0x4C, 0x8B, 0xA4, 0x24, 0xA8, 0x04, 0x00, 0x00,
    0x4B, 0x8D, 0x0C, 0xA4, 0x49, 0x8D, 0x0C, 0x8C, 0x4C, 0x89, 0xA4, 0x24, 0x10, 0x01, 0x00, 0x00,
    0x4C, 0x89, 0xCA, 0x4D, 0x89, 0xCB, 0x48, 0xC1, 0xEA, 0x34, 0x48, 0x01, 0xCA, 0x48, 0x21, 0xF0,
    0x48, 0x89, 0xD1, 0x49, 0x89, 0xD1] ++ bytes_l11d880_14

theorem code_l11d880_13 : ∀ x ∈ codeRange 0x11dcf7 bytes_l11d880_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1dcf7 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_14

def b_l11d880_12 : Block Op Label signature Reg.count 569 :=
  .letOp (n := 569) (.out 0x11dc90 (movR64M64Effect 0x11dc90 1 (.sib 4 none 0 (.d32 0x490))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 570) (.exec 0x11dc90 (LoadPre 0x11dc90 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x490)) s (0x11dc90 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11dc90 1 (.sib 4 none 0 (.d32 0x490))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 571) (.exec 0x11dc98 (StorePre 0x11dc98 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x11dc98 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11dc98 1 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[569, 4]
    (.letOp (n := 572) (.out 0x11dca0 (leaR64Effect 0x11dca0 0 (.sib 1 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 1] []) (.reg (.gpr 0))) #v[569, 569]
    (.letOp (n := 573) (.exec 0x11dca0 (fun s => s.RIP = 0x11dca0) (leaR64Effect 0x11dca0 0 (.sib 1 (some 1) 2 .none)) (Reg.operands [.gpr 1, .gpr 1] [])) #v[569, 569]
    (.letOp (n := 574) (.out 0x11dca4 (leaR64Effect 0x11dca4 1 (.sib 1 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[569, 572]
    (.letOp (n := 575) (.exec 0x11dca4 (fun s => s.RIP = 0x11dca4) (leaR64Effect 0x11dca4 1 (.sib 1 (some 0) 2 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[569, 572]
    (.letOp (n := 576) (.out 0x11dca8 (movR64M64Effect 0x11dca8 2 (.sib 4 none 0 (.d32 0x4b0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 577) (.exec 0x11dca8 (LoadPre 0x11dca8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x4b0)) s (0x11dca8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11dca8 2 (.sib 4 none 0 (.d32 0x4b0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 578) (.exec 0x11dcb0 (StorePre 0x11dcb0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11dcb0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11dcb0 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[576, 4]
    (.letOp (n := 579) (.out 0x11dcb5 (leaR64Effect 0x11dcb5 0 (.sib 2 (some 2) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 2] []) (.reg (.gpr 0))) #v[576, 576]
    (.letOp (n := 580) (.exec 0x11dcb5 (fun s => s.RIP = 0x11dcb5) (leaR64Effect 0x11dcb5 0 (.sib 2 (some 2) 2 .none)) (Reg.operands [.gpr 2, .gpr 2] [])) #v[576, 576]
    (.letOp (n := 581) (.out 0x11dcb9 (leaR64Effect 0x11dcb9 0 (.sib 2 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[576, 579]
    (.letOp (n := 582) (.exec 0x11dcb9 (fun s => s.RIP = 0x11dcb9) (leaR64Effect 0x11dcb9 0 (.sib 2 (some 0) 2 .none)) (Reg.operands [.gpr 2, .gpr 0] [])) #v[576, 579]
    (.letOp (n := 583) (.out 0x11dcbd (movR64R64Effect 0x11dcbd 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[581]
    (.letOp (n := 584) (.exec 0x11dcbd (fun s => s.RIP = 0x11dcbd) (movR64R64Effect 0x11dcbd 2 0) (Reg.operands [.gpr 0] [])) #v[581]
    (.letOp (n := 585) (.out 0x11dcc0 (shrR64Effect 0x11dcc0 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[583]
    (.letOp (n := 586) (.exec 0x11dcc0 (fun s => s.RIP = 0x11dcc0) (shrR64Effect 0x11dcc0 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[583]
    (.letOp (n := 587) (.out 0x11dcc4 (movR64Imm64Effect 0x11dcc4 5 0x1000003d1) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 588) (.exec 0x11dcc4 (fun s => s.RIP = 0x11dcc4) (movR64Imm64Effect 0x11dcc4 5 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 589) (.out 0x11dcce (imulR64R64Effect 0x11dcce 4 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[585, 587]
    (.letOp (n := 590) (.exec 0x11dcce (fun s => s.RIP = 0x11dcce) (imulR64R64Effect 0x11dcce 4 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[585, 587]
    (.letOp (n := 591) (.out 0x11dcd2 (addR64R64Effect 0x11dcd2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[589, 574]
    (.letOp (n := 592) (.exec 0x11dcd2 (fun s => s.RIP = 0x11dcd2) (addR64R64Effect 0x11dcd2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[589, 574]
    (.letOp (n := 593) (.out 0x11dcd5 (movR64M64Effect 0x11dcd5 7 (.sib 4 none 0 (.d32 0x498))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 594) (.exec 0x11dcd5 (LoadPre 0x11dcd5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x498)) s (0x11dcd5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11dcd5 7 (.sib 4 none 0 (.d32 0x498))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 595) (.exec 0x11dcdd (StorePre 0x11dcdd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x11dcdd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11dcdd 7 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[593, 4]
    (.letOp (n := 596) (.out 0x11dce5 (leaR64Effect 0x11dce5 1 (.sib 7 (some 7) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7, .gpr 7] []) (.reg (.gpr 1))) #v[593, 593]
    (.letOp (n := 597) (.exec 0x11dce5 (fun s => s.RIP = 0x11dce5) (leaR64Effect 0x11dce5 1 (.sib 7 (some 7) 2 .none)) (Reg.operands [.gpr 7, .gpr 7] [])) #v[593, 593]
    (.letOp (n := 598) (.out 0x11dce9 (leaR64Effect 0x11dce9 1 (.sib 7 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7, .gpr 1] []) (.reg (.gpr 1))) #v[593, 596]
    (.letOp (n := 599) (.exec 0x11dce9 (fun s => s.RIP = 0x11dce9) (leaR64Effect 0x11dce9 1 (.sib 7 (some 1) 2 .none)) (Reg.operands [.gpr 7, .gpr 1] [])) #v[593, 596]
    (.letOp (n := 600) (.out 0x11dced (movR64R64Effect 0x11dced 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[591]
    (.letOp (n := 601) (.exec 0x11dced (fun s => s.RIP = 0x11dced) (movR64R64Effect 0x11dced 8 2) (Reg.operands [.gpr 2] [])) #v[591]
    (.letOp (n := 602) (.out 0x11dcf0 (movR64R64Effect 0x11dcf0 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[591]
    (.letOp (n := 603) (.exec 0x11dcf0 (fun s => s.RIP = 0x11dcf0) (movR64R64Effect 0x11dcf0 7 2) (Reg.operands [.gpr 2] [])) #v[591]
    (.letOp (n := 604) (.out 0x11dcf3 (shrR64Effect 0x11dcf3 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[600]
    (.letOp (n := 605) (.exec 0x11dcf3 (fun s => s.RIP = 0x11dcf3) (shrR64Effect 0x11dcf3 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[600]
    (b_l11d880_13)))))))))))))))))))))))))))))))))))))

def bytes_l11d880_12 : List UInt8 :=
  [0x48, 0x8B, 0x8C, 0x24, 0x90, 0x04, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0x04, 0x89, 0x48, 0x8D, 0x0C, 0x81, 0x48, 0x8B, 0x94, 0x24, 0xB0, 0x04, 0x00, 0x00,
    0x48, 0x89, 0x54, 0x24, 0x78, 0x48, 0x8D, 0x04, 0x92, 0x48, 0x8D, 0x04, 0x82, 0x48, 0x89, 0xC2,
    0x48, 0xC1, 0xEA, 0x30, 0x48, 0xBD, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0x0F,
    0xAF, 0xD5, 0x48, 0x01, 0xCA, 0x48, 0x8B, 0xBC, 0x24, 0x98, 0x04, 0x00, 0x00, 0x48, 0x89, 0xBC,
    0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x0C, 0xBF, 0x48, 0x8D, 0x0C, 0x8F, 0x49, 0x89, 0xD0,
    0x48, 0x89, 0xD7, 0x49, 0xC1, 0xE8, 0x34] ++ bytes_l11d880_13

theorem code_l11d880_12 : ∀ x ∈ codeRange 0x11dc90 bytes_l11d880_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1dc90 103 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_13

def b_l11d880_11 : Block Op Label signature Reg.count 527 :=
  .letOp (n := 527) (.out 0x11dc2e (shldR64R64Effect 0x11dc2e 5 11 12 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[492, 489]
    (.letOp (n := 528) (.exec 0x11dc2e (fun s => s.RIP = 0x11dc2e) (shldR64R64Effect 0x11dc2e 5 11 12 12) (Reg.operands [.gpr 11, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[492, 489]
    (.letOp (n := 529) (.out 0x11dc33 (shldR64R64Effect 0x11dc33 5 1 13 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[525, 522]
    (.letOp (n := 530) (.exec 0x11dc33 (fun s => s.RIP = 0x11dc33) (shldR64R64Effect 0x11dc33 5 1 13 12) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[525, 522]
    (.letOp (n := 531) (.out 0x11dc38 (movR64R64Effect 0x11dc38 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[527]
    (.letOp (n := 532) (.exec 0x11dc38 (fun s => s.RIP = 0x11dc38) (movR64R64Effect 0x11dc38 0 11) (Reg.operands [.gpr 11] [])) #v[527]
    (.letOp (n := 533) (.out 0x11dc3b (movR64Imm64Effect 0x11dc3b 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 534) (.exec 0x11dc3b (fun s => s.RIP = 0x11dc3b) (movR64Imm64Effect 0x11dc3b 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 535) (.out 0x11dc45 (mulR64Effect 0x11dc45 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[533, 531]
    (.letOp (n := 536) (.out 0x11dc45 (mulR64Effect 0x11dc45 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[533, 531]
    (.letOp (n := 537) (.exec 0x11dc45 (fun s => s.RIP = 0x11dc45) (mulR64Effect 0x11dc45 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[533, 531]
    (.letOp (n := 538) (.out 0x11dc48 (movR64R64Effect 0x11dc48 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[535]
    (.letOp (n := 539) (.exec 0x11dc48 (fun s => s.RIP = 0x11dc48) (movR64R64Effect 0x11dc48 6 0) (Reg.operands [.gpr 0] [])) #v[535]
    (.letOp (n := 540) (.out 0x11dc4b (movR64Imm64Effect 0x11dc4b 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 541) (.exec 0x11dc4b (fun s => s.RIP = 0x11dc4b) (movR64Imm64Effect 0x11dc4b 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 542) (.out 0x11dc55 (movR64M64Effect 0x11dc55 7 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 543) (.exec 0x11dc55 (LoadPre 0x11dc55 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11dc55 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11dc55 7 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 544) (.out 0x11dc5d (andR64R64Effect 0x11dc5d 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[542, 540]
    (.letOp (n := 545) (.exec 0x11dc5d (fun s => s.RIP = 0x11dc5d) (andR64R64Effect 0x11dc5d 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[542, 540]
    (.letOp (n := 546) (.out 0x11dc60 (addR64R64Effect 0x11dc60 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[538, 544]
    (.letOp (n := 547) (.out 0x11dc60 (addR64R64Effect 0x11dc60 6 7) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 7] []) (.flag .CF)) #v[538, 544]
    (.letOp (n := 548) (.exec 0x11dc60 (fun s => s.RIP = 0x11dc60) (addR64R64Effect 0x11dc60 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[538, 544]
    (.letOp (n := 549) (.out 0x11dc63 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11dc63 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[536, 547]
    (.letOp (n := 550) (.exec 0x11dc63 (fun s => s.RIP = 0x11dc63) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11dc63 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[536, 547]
    (.letOp (n := 551) (.out 0x11dc67 (addR64R64Effect 0x11dc67 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[546, 529]
    (.letOp (n := 552) (.out 0x11dc67 (addR64R64Effect 0x11dc67 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[546, 529]
    (.letOp (n := 553) (.exec 0x11dc67 (fun s => s.RIP = 0x11dc67) (addR64R64Effect 0x11dc67 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[546, 529]
    (.letOp (n := 554) (.out 0x11dc6a (movR64R64Effect 0x11dc6a 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[551]
    (.letOp (n := 555) (.exec 0x11dc6a (fun s => s.RIP = 0x11dc6a) (movR64R64Effect 0x11dc6a 3 6) (Reg.operands [.gpr 6] [])) #v[551]
    (.letOp (n := 556) (.out 0x11dc6d (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11dc6d 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[549, 552]
    (.letOp (n := 557) (.exec 0x11dc6d (fun s => s.RIP = 0x11dc6d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11dc6d 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[549, 552]
    (.letOp (n := 558) (.out 0x11dc71 (movR64Imm64Effect 0x11dc71 6 0xffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 559) (.exec 0x11dc71 (fun s => s.RIP = 0x11dc71) (movR64Imm64Effect 0x11dc71 6 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 560) (.out 0x11dc7b (movR64M64Effect 0x11dc7b 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 561) (.exec 0x11dc7b (LoadPre 0x11dc7b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11dc7b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11dc7b 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 562) (.out 0x11dc80 (andR64R64Effect 0x11dc80 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[560, 558]
    (.letOp (n := 563) (.exec 0x11dc80 (fun s => s.RIP = 0x11dc80) (andR64R64Effect 0x11dc80 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[560, 558]
    (.letOp (n := 564) (.out 0x11dc83 (shldR64R64Effect 0x11dc83 5 2 3 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[556, 554]
    (.letOp (n := 565) (.exec 0x11dc83 (fun s => s.RIP = 0x11dc83) (shldR64R64Effect 0x11dc83 5 2 3 12) (Reg.operands [.gpr 2, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[556, 554]
    (.letOp (n := 566) (.out 0x11dc88 (addR64R64Effect 0x11dc88 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[562, 564]
    (.letOp (n := 567) (.exec 0x11dc88 (fun s => s.RIP = 0x11dc88) (addR64R64Effect 0x11dc88 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[562, 564]
    (.letOp (n := 568) (.exec 0x11dc8b (StorePre 0x11dc8b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11dc8b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11dc8b 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[566, 4]
    (b_l11d880_12))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_11 : List UInt8 :=
  [0x4D, 0x0F, 0xA4, 0xE3, 0x0C, 0x4C, 0x0F, 0xA4, 0xE9, 0x0C, 0x4C, 0x89, 0xD8, 0x48, 0xBA, 0x10,
    0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xC6, 0x48, 0xB8, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x8B, 0xBC, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48,
    0x21, 0xC7, 0x48, 0x01, 0xFE, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x01, 0xCE, 0x48, 0x89, 0xF3, 0x48,
    0x83, 0xD2, 0x00, 0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x8B, 0x4C,
    0x24, 0x10, 0x48, 0x21, 0xF1, 0x48, 0x0F, 0xA4, 0xDA, 0x0C, 0x48, 0x01, 0xD1, 0x48, 0x89, 0x4C,
    0x24, 0x10] ++ bytes_l11d880_12

theorem code_l11d880_11 : ∀ x ∈ codeRange 0x11dc2e bytes_l11d880_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1dc2e 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_12

def b_l11d880_10 : Block Op Label signature Reg.count 479 :=
  .letOp (n := 479) (.out 0x11dbe2 (mulR64Effect 0x11dbe2 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[300, 477]
    (.letOp (n := 480) (.out 0x11dbe2 (mulR64Effect 0x11dbe2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[300, 477]
    (.letOp (n := 481) (.exec 0x11dbe2 (fun s => s.RIP = 0x11dbe2) (mulR64Effect 0x11dbe2 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[300, 477]
    (.letOp (n := 482) (.out 0x11dbe5 (movR64R64Effect 0x11dbe5 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[479]
    (.letOp (n := 483) (.exec 0x11dbe5 (fun s => s.RIP = 0x11dbe5) (movR64R64Effect 0x11dbe5 12 0) (Reg.operands [.gpr 0] [])) #v[479]
    (.letOp (n := 484) (.out 0x11dbe8 (addR64R64Effect 0x11dbe8 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[482, 473]
    (.letOp (n := 485) (.out 0x11dbe8 (addR64R64Effect 0x11dbe8 12 13) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 13] []) (.flag .CF)) #v[482, 473]
    (.letOp (n := 486) (.exec 0x11dbe8 (fun s => s.RIP = 0x11dbe8) (addR64R64Effect 0x11dbe8 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[482, 473]
    (.letOp (n := 487) (.out 0x11dbeb (atFlags StatusFlags.CF (adcR64R64Effect 0x11dbeb 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[475, 480, 485]
    (.letOp (n := 488) (.exec 0x11dbeb (fun s => s.RIP = 0x11dbeb) (atFlags StatusFlags.CF (adcR64R64Effect 0x11dbeb 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[475, 480, 485]
    (.letOp (n := 489) (.out 0x11dbee (addR64R64Effect 0x11dbee 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 9] []) (.reg (.gpr 12))) #v[484, 410]
    (.letOp (n := 490) (.out 0x11dbee (addR64R64Effect 0x11dbee 12 9) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 9] []) (.flag .CF)) #v[484, 410]
    (.letOp (n := 491) (.exec 0x11dbee (fun s => s.RIP = 0x11dbee) (addR64R64Effect 0x11dbee 12 9) (Reg.operands [.gpr 12, .gpr 9] [])) #v[484, 410]
    (.letOp (n := 492) (.out 0x11dbf1 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11dbf1 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[487, 490]
    (.letOp (n := 493) (.exec 0x11dbf1 (fun s => s.RIP = 0x11dbf1) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11dbf1 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[487, 490]
    (.letOp (n := 494) (.out 0x11dbf5 (movR64R64Effect 0x11dbf5 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[489]
    (.letOp (n := 495) (.exec 0x11dbf5 (fun s => s.RIP = 0x11dbf5) (movR64R64Effect 0x11dbf5 0 12) (Reg.operands [.gpr 12] [])) #v[489]
    (.letOp (n := 496) (.out 0x11dbf8 (movR64Imm64Effect 0x11dbf8 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 497) (.exec 0x11dbf8 (fun s => s.RIP = 0x11dbf8) (movR64Imm64Effect 0x11dbf8 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 498) (.out 0x11dc02 (andR64R64Effect 0x11dc02 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[494, 496]
    (.letOp (n := 499) (.exec 0x11dc02 (fun s => s.RIP = 0x11dc02) (andR64R64Effect 0x11dc02 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[494, 496]
    (.letOp (n := 500) (.out 0x11dc05 (movR64Imm64Effect 0x11dc05 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 501) (.exec 0x11dc05 (fun s => s.RIP = 0x11dc05) (movR64Imm64Effect 0x11dc05 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 502) (.out 0x11dc0f (mulR64Effect 0x11dc0f 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[500, 498]
    (.letOp (n := 503) (.out 0x11dc0f (mulR64Effect 0x11dc0f 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[500, 498]
    (.letOp (n := 504) (.exec 0x11dc0f (fun s => s.RIP = 0x11dc0f) (mulR64Effect 0x11dc0f 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[500, 498]
    (.letOp (n := 505) (.out 0x11dc12 (movR64R64Effect 0x11dc12 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[502]
    (.letOp (n := 506) (.exec 0x11dc12 (fun s => s.RIP = 0x11dc12) (movR64R64Effect 0x11dc12 13 0) (Reg.operands [.gpr 0] [])) #v[502]
    (.letOp (n := 507) (.out 0x11dc15 (addR64R64Effect 0x11dc15 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[462, 455]
    (.letOp (n := 508) (.out 0x11dc15 (addR64R64Effect 0x11dc15 14 15) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 15] []) (.flag .CF)) #v[462, 455]
    (.letOp (n := 509) (.exec 0x11dc15 (fun s => s.RIP = 0x11dc15) (addR64R64Effect 0x11dc15 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[462, 455]
    (.letOp (n := 510) (.out 0x11dc18 (atFlags StatusFlags.CF (adcR64R64Effect 0x11dc18 1 3)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[464, 453, 508]
    (.letOp (n := 511) (.exec 0x11dc18 (fun s => s.RIP = 0x11dc18) (atFlags StatusFlags.CF (adcR64R64Effect 0x11dc18 1 3)) (Reg.operands [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[464, 453, 508]
    (.letOp (n := 512) (.out 0x11dc1b (addR64R64Effect 0x11dc1b 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[507, 446]
    (.letOp (n := 513) (.out 0x11dc1b (addR64R64Effect 0x11dc1b 14 8) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 8] []) (.flag .CF)) #v[507, 446]
    (.letOp (n := 514) (.exec 0x11dc1b (fun s => s.RIP = 0x11dc1b) (addR64R64Effect 0x11dc1b 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[507, 446]
    (.letOp (n := 515) (.out 0x11dc1e (atFlags StatusFlags.CF (adcR64R64Effect 0x11dc1e 1 5)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[510, 444, 513]
    (.letOp (n := 516) (.exec 0x11dc1e (fun s => s.RIP = 0x11dc1e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11dc1e 1 5)) (Reg.operands [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[510, 444, 513]
    (.letOp (n := 517) (.out 0x11dc21 (addR64R64Effect 0x11dc21 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[505, 512]
    (.letOp (n := 518) (.out 0x11dc21 (addR64R64Effect 0x11dc21 13 14) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 14] []) (.flag .CF)) #v[505, 512]
    (.letOp (n := 519) (.exec 0x11dc21 (fun s => s.RIP = 0x11dc21) (addR64R64Effect 0x11dc21 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[505, 512]
    (.letOp (n := 520) (.out 0x11dc24 (atFlags StatusFlags.CF (adcR64R64Effect 0x11dc24 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[515, 503, 518]
    (.letOp (n := 521) (.exec 0x11dc24 (fun s => s.RIP = 0x11dc24) (atFlags StatusFlags.CF (adcR64R64Effect 0x11dc24 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[515, 503, 518]
    (.letOp (n := 522) (.out 0x11dc27 (addR64R64Effect 0x11dc27 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 6] []) (.reg (.gpr 13))) #v[517, 466]
    (.letOp (n := 523) (.out 0x11dc27 (addR64R64Effect 0x11dc27 13 6) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 6] []) (.flag .CF)) #v[517, 466]
    (.letOp (n := 524) (.exec 0x11dc27 (fun s => s.RIP = 0x11dc27) (addR64R64Effect 0x11dc27 13 6) (Reg.operands [.gpr 13, .gpr 6] [])) #v[517, 466]
    (.letOp (n := 525) (.out 0x11dc2a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11dc2a 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[520, 523]
    (.letOp (n := 526) (.exec 0x11dc2a (fun s => s.RIP = 0x11dc2a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11dc2a 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[520, 523]
    (b_l11d880_11))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_10 : List UInt8 :=
  [0x48, 0xF7, 0xE7, 0x49, 0x89, 0xC4, 0x4D, 0x01, 0xEC, 0x49, 0x11, 0xD3, 0x4D, 0x01, 0xCC, 0x49,
    0x83, 0xD3, 0x00, 0x4C, 0x89, 0xE0, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x49, 0x89, 0xC5, 0x4D, 0x01, 0xFE, 0x48, 0x11, 0xD9, 0x4D, 0x01, 0xC6, 0x48, 0x11, 0xE9, 0x4D,
    0x01, 0xF5, 0x48, 0x11, 0xD1, 0x49, 0x01, 0xF5, 0x48, 0x83, 0xD1, 0x00] ++ bytes_l11d880_11

theorem code_l11d880_10 : ∀ x ∈ codeRange 0x11dbe2 bytes_l11d880_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1dbe2 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_11

def b_l11d880_9 : Block Op Label signature Reg.count 436 :=
  .letOp (n := 436) (.exec 0x11db97 (StorePre 0x11db97 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11db97 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11db97 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[431, 4]
    (.letOp (n := 437) (.out 0x11db9c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11db9c 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[429, 432]
    (.letOp (n := 438) (.exec 0x11db9c (fun s => s.RIP = 0x11db9c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11db9c 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[429, 432]
    (.letOp (n := 439) (.out 0x11dba0 (movR64R64Effect 0x11dba0 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[388]
    (.letOp (n := 440) (.exec 0x11dba0 (fun s => s.RIP = 0x11dba0) (movR64R64Effect 0x11dba0 0 1) (Reg.operands [.gpr 1] [])) #v[388]
    (.letOp (n := 441) (.out 0x11dba3 (mulM64Effect 0x11dba3 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[439, 4]
    (.letOp (n := 442) (.out 0x11dba3 (mulM64Effect 0x11dba3 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[439, 4]
    (.letOp (n := 443) (.exec 0x11dba3 (LoadPre 0x11dba3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11dba3 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11dba3 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[439, 4]
    (.letOp (n := 444) (.out 0x11dba8 (movR64R64Effect 0x11dba8 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[442]
    (.letOp (n := 445) (.exec 0x11dba8 (fun s => s.RIP = 0x11dba8) (movR64R64Effect 0x11dba8 5 2) (Reg.operands [.gpr 2] [])) #v[442]
    (.letOp (n := 446) (.out 0x11dbab (movR64R64Effect 0x11dbab 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[441]
    (.letOp (n := 447) (.exec 0x11dbab (fun s => s.RIP = 0x11dbab) (movR64R64Effect 0x11dbab 8 0) (Reg.operands [.gpr 0] [])) #v[441]
    (.letOp (n := 448) (.out 0x11dbae (movR64M64Effect 0x11dbae 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 449) (.exec 0x11dbae (LoadPre 0x11dbae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11dbae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11dbae 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 450) (.out 0x11dbb3 (mulM64Effect 0x11dbb3 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[448, 4]
    (.letOp (n := 451) (.out 0x11dbb3 (mulM64Effect 0x11dbb3 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[448, 4]
    (.letOp (n := 452) (.exec 0x11dbb3 (LoadPre 0x11dbb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11dbb3 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11dbb3 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[448, 4]
    (.letOp (n := 453) (.out 0x11dbb8 (movR64R64Effect 0x11dbb8 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[451]
    (.letOp (n := 454) (.exec 0x11dbb8 (fun s => s.RIP = 0x11dbb8) (movR64R64Effect 0x11dbb8 3 2) (Reg.operands [.gpr 2] [])) #v[451]
    (.letOp (n := 455) (.out 0x11dbbb (movR64R64Effect 0x11dbbb 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[450]
    (.letOp (n := 456) (.exec 0x11dbbb (fun s => s.RIP = 0x11dbbb) (movR64R64Effect 0x11dbbb 15 0) (Reg.operands [.gpr 0] [])) #v[450]
    (.letOp (n := 457) (.out 0x11dbbe (movR64M64Effect 0x11dbbe 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 458) (.exec 0x11dbbe (LoadPre 0x11dbbe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11dbbe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11dbbe 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 459) (.out 0x11dbc3 (mulR64Effect 0x11dbc3 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[368, 457]
    (.letOp (n := 460) (.out 0x11dbc3 (mulR64Effect 0x11dbc3 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[368, 457]
    (.letOp (n := 461) (.exec 0x11dbc3 (fun s => s.RIP = 0x11dbc3) (mulR64Effect 0x11dbc3 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[368, 457]
    (.letOp (n := 462) (.out 0x11dbc6 (movR64R64Effect 0x11dbc6 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[459]
    (.letOp (n := 463) (.exec 0x11dbc6 (fun s => s.RIP = 0x11dbc6) (movR64R64Effect 0x11dbc6 14 0) (Reg.operands [.gpr 0] [])) #v[459]
    (.letOp (n := 464) (.out 0x11dbc9 (movR64R64Effect 0x11dbc9 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[460]
    (.letOp (n := 465) (.exec 0x11dbc9 (fun s => s.RIP = 0x11dbc9) (movR64R64Effect 0x11dbc9 1 2) (Reg.operands [.gpr 2] [])) #v[460]
    (.letOp (n := 466) (.out 0x11dbcc (shldR64R64Effect 0x11dbcc 5 6 12 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[437, 434]
    (.letOp (n := 467) (.exec 0x11dbcc (fun s => s.RIP = 0x11dbcc) (shldR64R64Effect 0x11dbcc 5 6 12 12) (Reg.operands [.gpr 6, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[437, 434]
    (.letOp (n := 468) (.out 0x11dbd1 (movR64R64Effect 0x11dbd1 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[364]
    (.letOp (n := 469) (.exec 0x11dbd1 (fun s => s.RIP = 0x11dbd1) (movR64R64Effect 0x11dbd1 0 11) (Reg.operands [.gpr 11] [])) #v[364]
    (.letOp (n := 470) (.out 0x11dbd4 (mulM64Effect 0x11dbd4 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[468, 4]
    (.letOp (n := 471) (.out 0x11dbd4 (mulM64Effect 0x11dbd4 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[468, 4]
    (.letOp (n := 472) (.exec 0x11dbd4 (LoadPre 0x11dbd4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11dbd4 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11dbd4 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[468, 4]
    (.letOp (n := 473) (.out 0x11dbd9 (movR64R64Effect 0x11dbd9 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[470]
    (.letOp (n := 474) (.exec 0x11dbd9 (fun s => s.RIP = 0x11dbd9) (movR64R64Effect 0x11dbd9 13 0) (Reg.operands [.gpr 0] [])) #v[470]
    (.letOp (n := 475) (.out 0x11dbdc (movR64R64Effect 0x11dbdc 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[471]
    (.letOp (n := 476) (.exec 0x11dbdc (fun s => s.RIP = 0x11dbdc) (movR64R64Effect 0x11dbdc 11 2) (Reg.operands [.gpr 2] [])) #v[471]
    (.letOp (n := 477) (.out 0x11dbdf (movR64R64Effect 0x11dbdf 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[270]
    (.letOp (n := 478) (.exec 0x11dbdf (fun s => s.RIP = 0x11dbdf) (movR64R64Effect 0x11dbdf 0 10) (Reg.operands [.gpr 10] [])) #v[270]
    (b_l11d880_10)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_9 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x83, 0xD6, 0x00, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0x64, 0x24,
    0x08, 0x48, 0x89, 0xD5, 0x49, 0x89, 0xC0, 0x48, 0x8B, 0x44, 0x24, 0x60, 0x48, 0xF7, 0x64, 0x24,
    0x38, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x49, 0xF7, 0xE5, 0x49,
    0x89, 0xC6, 0x48, 0x89, 0xD1, 0x4C, 0x0F, 0xA4, 0xE6, 0x0C, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0x64,
    0x24, 0x70, 0x49, 0x89, 0xC5, 0x49, 0x89, 0xD3, 0x4C, 0x89, 0xD0] ++ bytes_l11d880_10

theorem code_l11d880_9 : ∀ x ∈ codeRange 0x11db97 bytes_l11d880_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1db97 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_10

def b_l11d880_8 : Block Op Label signature Reg.count 388 :=
  .letOp (n := 388) (.out 0x11db41 (movR64M64Effect 0x11db41 1 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 389) (.exec 0x11db41 (LoadPre 0x11db41 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11db41 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11db41 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 390) (.out 0x11db49 (movR64R64Effect 0x11db49 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[388]
    (.letOp (n := 391) (.exec 0x11db49 (fun s => s.RIP = 0x11db49) (movR64R64Effect 0x11db49 0 1) (Reg.operands [.gpr 1] [])) #v[388]
    (.letOp (n := 392) (.out 0x11db4c (mulR64Effect 0x11db4c 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[300, 390]
    (.letOp (n := 393) (.out 0x11db4c (mulR64Effect 0x11db4c 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[300, 390]
    (.letOp (n := 394) (.exec 0x11db4c (fun s => s.RIP = 0x11db4c) (mulR64Effect 0x11db4c 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[300, 390]
    (.letOp (n := 395) (.out 0x11db4f (addR64R64Effect 0x11db4f 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[392, 384]
    (.letOp (n := 396) (.out 0x11db4f (addR64R64Effect 0x11db4f 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[392, 384]
    (.letOp (n := 397) (.exec 0x11db4f (fun s => s.RIP = 0x11db4f) (addR64R64Effect 0x11db4f 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[392, 384]
    (.letOp (n := 398) (.out 0x11db52 (atFlags StatusFlags.CF (adcR64R64Effect 0x11db52 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[386, 393, 396]
    (.letOp (n := 399) (.exec 0x11db52 (fun s => s.RIP = 0x11db52) (atFlags StatusFlags.CF (adcR64R64Effect 0x11db52 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[386, 393, 396]
    (.letOp (n := 400) (.out 0x11db55 (addR64R64Effect 0x11db55 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[395, 373]
    (.letOp (n := 401) (.out 0x11db55 (addR64R64Effect 0x11db55 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[395, 373]
    (.letOp (n := 402) (.exec 0x11db55 (fun s => s.RIP = 0x11db55) (addR64R64Effect 0x11db55 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[395, 373]
    (.letOp (n := 403) (.out 0x11db58 (atFlags StatusFlags.CF (adcR64R64Effect 0x11db58 9 15)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[398, 375, 401]
    (.letOp (n := 404) (.exec 0x11db58 (fun s => s.RIP = 0x11db58) (atFlags StatusFlags.CF (adcR64R64Effect 0x11db58 9 15)) (Reg.operands [.gpr 9, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[398, 375, 401]
    (.letOp (n := 405) (.out 0x11db5b (addR64R64Effect 0x11db5b 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[400, 325]
    (.letOp (n := 406) (.out 0x11db5b (addR64R64Effect 0x11db5b 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[400, 325]
    (.letOp (n := 407) (.exec 0x11db5b (fun s => s.RIP = 0x11db5b) (addR64R64Effect 0x11db5b 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[400, 325]
    (.letOp (n := 408) (.out 0x11db5e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11db5e 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[403, 406]
    (.letOp (n := 409) (.exec 0x11db5e (fun s => s.RIP = 0x11db5e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11db5e 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[403, 406]
    (.letOp (n := 410) (.out 0x11db62 (shldR64R64Effect 0x11db62 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[408, 405]
    (.letOp (n := 411) (.exec 0x11db62 (fun s => s.RIP = 0x11db62) (shldR64R64Effect 0x11db62 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[408, 405]
    (.letOp (n := 412) (.out 0x11db67 (movR64Imm64Effect 0x11db67 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 413) (.exec 0x11db67 (fun s => s.RIP = 0x11db67) (movR64Imm64Effect 0x11db67 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 414) (.out 0x11db71 (andR64R64Effect 0x11db71 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[405, 412]
    (.letOp (n := 415) (.exec 0x11db71 (fun s => s.RIP = 0x11db71) (andR64R64Effect 0x11db71 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[405, 412]
    (.letOp (n := 416) (.out 0x11db74 (movR64Imm64Effect 0x11db74 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 417) (.exec 0x11db74 (fun s => s.RIP = 0x11db74) (movR64Imm64Effect 0x11db74 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 418) (.out 0x11db7e (mulR64Effect 0x11db7e 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[416, 414]
    (.letOp (n := 419) (.out 0x11db7e (mulR64Effect 0x11db7e 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[416, 414]
    (.letOp (n := 420) (.exec 0x11db7e (fun s => s.RIP = 0x11db7e) (mulR64Effect 0x11db7e 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[416, 414]
    (.letOp (n := 421) (.out 0x11db81 (addR64M64Effect 0x11db81 3 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[362, 4]
    (.letOp (n := 422) (.out 0x11db81 (addR64M64Effect 0x11db81 3 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[362, 4]
    (.letOp (n := 423) (.exec 0x11db81 (LoadPre 0x11db81 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11db81 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11db81 3 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[362, 4]
    (.letOp (n := 424) (.out 0x11db86 (atFlags StatusFlags.CF (adcR64M64Effect 0x11db86 6 (.sib 4 none 0 (.d8 0x68)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[360, 4, 422]
    (.letOp (n := 425) (.exec 0x11db86 (LoadPre 0x11db86 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11db86 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11db86 6 (.sib 4 none 0 (.d8 0x68)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[360, 4, 422]
    (.letOp (n := 426) (.out 0x11db8b (addR64R64Effect 0x11db8b 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[418, 421]
    (.letOp (n := 427) (.out 0x11db8b (addR64R64Effect 0x11db8b 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[418, 421]
    (.letOp (n := 428) (.exec 0x11db8b (fun s => s.RIP = 0x11db8b) (addR64R64Effect 0x11db8b 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[418, 421]
    (.letOp (n := 429) (.out 0x11db8e (atFlags StatusFlags.CF (adcR64R64Effect 0x11db8e 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[424, 419, 427]
    (.letOp (n := 430) (.exec 0x11db8e (fun s => s.RIP = 0x11db8e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11db8e 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[424, 419, 427]
    (.letOp (n := 431) (.out 0x11db91 (addR64R64Effect 0x11db91 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[426, 377]
    (.letOp (n := 432) (.out 0x11db91 (addR64R64Effect 0x11db91 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[426, 377]
    (.letOp (n := 433) (.exec 0x11db91 (fun s => s.RIP = 0x11db91) (addR64R64Effect 0x11db91 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[426, 377]
    (.letOp (n := 434) (.out 0x11db94 (movR64R64Effect 0x11db94 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[431]
    (.letOp (n := 435) (.exec 0x11db94 (fun s => s.RIP = 0x11db94) (movR64R64Effect 0x11db94 12 0) (Reg.operands [.gpr 0] [])) #v[431]
    (b_l11d880_9))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_8 : List UInt8 :=
  [0x48, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0xE7, 0x4C, 0x01,
    0xE0, 0x49, 0x11, 0xD1, 0x4C, 0x01, 0xF0, 0x4D, 0x11, 0xF9, 0x4C, 0x01, 0xC0, 0x49, 0x83, 0xD1,
    0x00, 0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x48, 0x03, 0x5C, 0x24, 0x18, 0x48, 0x13, 0x74, 0x24, 0x68, 0x48, 0x01, 0xD8, 0x48, 0x11, 0xD6,
    0x48, 0x01, 0xE8, 0x49, 0x89, 0xC4] ++ bytes_l11d880_9

theorem code_l11d880_8 : ∀ x ∈ codeRange 0x11db41 bytes_l11d880_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1db41 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_9

def b_l11d880_7 : Block Op Label signature Reg.count 346 :=
  .letOp (n := 346) (.out 0x11daf1 (atFlags StatusFlags.CF (adcR64R64Effect 0x11daf1 5 2)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[255, 338, 341]
    (.letOp (n := 347) (.exec 0x11daf1 (fun s => s.RIP = 0x11daf1) (atFlags StatusFlags.CF (adcR64R64Effect 0x11daf1 5 2)) (Reg.operands [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[255, 338, 341]
    (.letOp (n := 348) (.out 0x11daf4 (movR64R64Effect 0x11daf4 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[296]
    (.letOp (n := 349) (.exec 0x11daf4 (fun s => s.RIP = 0x11daf4) (movR64R64Effect 0x11daf4 0 13) (Reg.operands [.gpr 13] [])) #v[296]
    (.letOp (n := 350) (.out 0x11daf7 (mulM64Effect 0x11daf7 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[348, 4]
    (.letOp (n := 351) (.out 0x11daf7 (mulM64Effect 0x11daf7 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[348, 4]
    (.letOp (n := 352) (.exec 0x11daf7 (LoadPre 0x11daf7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11daf7 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11daf7 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[348, 4]
    (.letOp (n := 353) (.exec 0x11dafc (StorePre 0x11dafc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11dafc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11dafc 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[351, 4]
    (.letOp (n := 354) (.exec 0x11db01 (StorePre 0x11db01 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11db01 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11db01 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[350, 4]
    (.letOp (n := 355) (.out 0x11db06 (movR64R64Effect 0x11db06 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[199]
    (.letOp (n := 356) (.exec 0x11db06 (fun s => s.RIP = 0x11db06) (movR64R64Effect 0x11db06 0 11) (Reg.operands [.gpr 11] [])) #v[199]
    (.letOp (n := 357) (.out 0x11db09 (mulM64Effect 0x11db09 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[355, 4]
    (.letOp (n := 358) (.out 0x11db09 (mulM64Effect 0x11db09 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[355, 4]
    (.letOp (n := 359) (.exec 0x11db09 (LoadPre 0x11db09 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11db09 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11db09 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[355, 4]
    (.letOp (n := 360) (.out 0x11db0e (movR64R64Effect 0x11db0e 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[358]
    (.letOp (n := 361) (.exec 0x11db0e (fun s => s.RIP = 0x11db0e) (movR64R64Effect 0x11db0e 6 2) (Reg.operands [.gpr 2] [])) #v[358]
    (.letOp (n := 362) (.out 0x11db11 (movR64R64Effect 0x11db11 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[357]
    (.letOp (n := 363) (.exec 0x11db11 (fun s => s.RIP = 0x11db11) (movR64R64Effect 0x11db11 3 0) (Reg.operands [.gpr 0] [])) #v[357]
    (.letOp (n := 364) (.out 0x11db14 (movR64M64Effect 0x11db14 11 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 365) (.exec 0x11db14 (LoadPre 0x11db14 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11db14 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11db14 11 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 366) (.out 0x11db1c (movR64R64Effect 0x11db1c 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[364]
    (.letOp (n := 367) (.exec 0x11db1c (fun s => s.RIP = 0x11db1c) (movR64R64Effect 0x11db1c 0 11) (Reg.operands [.gpr 11] [])) #v[364]
    (.letOp (n := 368) (.out 0x11db1f (movR64M64Effect 0x11db1f 13 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 369) (.exec 0x11db1f (LoadPre 0x11db1f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11db1f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11db1f 13 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 370) (.out 0x11db27 (mulR64Effect 0x11db27 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[368, 366]
    (.letOp (n := 371) (.out 0x11db27 (mulR64Effect 0x11db27 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[368, 366]
    (.letOp (n := 372) (.exec 0x11db27 (fun s => s.RIP = 0x11db27) (mulR64Effect 0x11db27 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[368, 366]
    (.letOp (n := 373) (.out 0x11db2a (movR64R64Effect 0x11db2a 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[370]
    (.letOp (n := 374) (.exec 0x11db2a (fun s => s.RIP = 0x11db2a) (movR64R64Effect 0x11db2a 14 0) (Reg.operands [.gpr 0] [])) #v[370]
    (.letOp (n := 375) (.out 0x11db2d (movR64R64Effect 0x11db2d 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[371]
    (.letOp (n := 376) (.exec 0x11db2d (fun s => s.RIP = 0x11db2d) (movR64R64Effect 0x11db2d 15 2) (Reg.operands [.gpr 2] [])) #v[371]
    (.letOp (n := 377) (.out 0x11db30 (shldR64R64Effect 0x11db30 5 5 9 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[346, 343]
    (.letOp (n := 378) (.exec 0x11db30 (fun s => s.RIP = 0x11db30) (shldR64R64Effect 0x11db30 5 5 9 12) (Reg.operands [.gpr 5, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[346, 343]
    (.letOp (n := 379) (.out 0x11db35 (movR64R64Effect 0x11db35 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[270]
    (.letOp (n := 380) (.exec 0x11db35 (fun s => s.RIP = 0x11db35) (movR64R64Effect 0x11db35 0 10) (Reg.operands [.gpr 10] [])) #v[270]
    (.letOp (n := 381) (.out 0x11db38 (mulR64Effect 0x11db38 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[287, 379]
    (.letOp (n := 382) (.out 0x11db38 (mulR64Effect 0x11db38 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[287, 379]
    (.letOp (n := 383) (.exec 0x11db38 (fun s => s.RIP = 0x11db38) (mulR64Effect 0x11db38 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[287, 379]
    (.letOp (n := 384) (.out 0x11db3b (movR64R64Effect 0x11db3b 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[381]
    (.letOp (n := 385) (.exec 0x11db3b (fun s => s.RIP = 0x11db3b) (movR64R64Effect 0x11db3b 12 0) (Reg.operands [.gpr 0] [])) #v[381]
    (.letOp (n := 386) (.out 0x11db3e (movR64R64Effect 0x11db3e 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[382]
    (.letOp (n := 387) (.exec 0x11db3e (fun s => s.RIP = 0x11db3e) (movR64R64Effect 0x11db3e 9 2) (Reg.operands [.gpr 2] [])) #v[382]
    (b_l11d880_8))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_7 : List UInt8 :=
  [0x48, 0x11, 0xD5, 0x4C, 0x89, 0xE8, 0x48, 0xF7, 0x64, 0x24, 0x08, 0x48, 0x89, 0x54, 0x24, 0x68,
    0x48, 0x89, 0x44, 0x24, 0x18, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0x64, 0x24, 0x38, 0x48, 0x89, 0xD6,
    0x48, 0x89, 0xC3, 0x4C, 0x8B, 0x9C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xD8, 0x4C, 0x8B,
    0xAC, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xC6, 0x49, 0x89, 0xD7, 0x4C,
    0x0F, 0xA4, 0xCD, 0x0C, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD1] ++ bytes_l11d880_8

theorem code_l11d880_7 : ∀ x ∈ codeRange 0x11daf1 bytes_l11d880_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1daf1 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_8

def b_l11d880_6 : Block Op Label signature Reg.count 300 :=
  .letOp (n := 300) (.out 0x11da95 (movR64M64Effect 0x11da95 7 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 301) (.exec 0x11da95 (LoadPre 0x11da95 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11da95 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11da95 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 302) (.out 0x11da9d (mulR64Effect 0x11da9d 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[300, 298]
    (.letOp (n := 303) (.out 0x11da9d (mulR64Effect 0x11da9d 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[300, 298]
    (.letOp (n := 304) (.exec 0x11da9d (fun s => s.RIP = 0x11da9d) (mulR64Effect 0x11da9d 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[300, 298]
    (.letOp (n := 305) (.out 0x11daa0 (addR64R64Effect 0x11daa0 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[302, 292]
    (.letOp (n := 306) (.out 0x11daa0 (addR64R64Effect 0x11daa0 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[302, 292]
    (.letOp (n := 307) (.exec 0x11daa0 (fun s => s.RIP = 0x11daa0) (addR64R64Effect 0x11daa0 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[302, 292]
    (.letOp (n := 308) (.out 0x11daa3 (atFlags StatusFlags.CF (adcR64R64Effect 0x11daa3 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[294, 303, 306]
    (.letOp (n := 309) (.exec 0x11daa3 (fun s => s.RIP = 0x11daa3) (atFlags StatusFlags.CF (adcR64R64Effect 0x11daa3 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[294, 303, 306]
    (.letOp (n := 310) (.out 0x11daa6 (addR64R64Effect 0x11daa6 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[305, 277]
    (.letOp (n := 311) (.out 0x11daa6 (addR64R64Effect 0x11daa6 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[305, 277]
    (.letOp (n := 312) (.exec 0x11daa6 (fun s => s.RIP = 0x11daa6) (addR64R64Effect 0x11daa6 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[305, 277]
    (.letOp (n := 313) (.out 0x11daa9 (atFlags StatusFlags.CF (adcR64R64Effect 0x11daa9 8 14)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[308, 279, 311]
    (.letOp (n := 314) (.exec 0x11daa9 (fun s => s.RIP = 0x11daa9) (atFlags StatusFlags.CF (adcR64R64Effect 0x11daa9 8 14)) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[308, 279, 311]
    (.letOp (n := 315) (.out 0x11daac (addR64R64Effect 0x11daac 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[310, 262]
    (.letOp (n := 316) (.out 0x11daac (addR64R64Effect 0x11daac 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[310, 262]
    (.letOp (n := 317) (.exec 0x11daac (fun s => s.RIP = 0x11daac) (addR64R64Effect 0x11daac 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[310, 262]
    (.letOp (n := 318) (.out 0x11daaf (atFlags StatusFlags.CF (adcR64M64Effect 0x11daaf 8 (.sib 4 none 0 (.d8 0x18)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[313, 4, 316]
    (.letOp (n := 319) (.exec 0x11daaf (LoadPre 0x11daaf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11daaf + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11daaf 8 (.sib 4 none 0 (.d8 0x18)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[313, 4, 316]
    (.letOp (n := 320) (.out 0x11dab4 (addR64R64Effect 0x11dab4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[315, 281]
    (.letOp (n := 321) (.out 0x11dab4 (addR64R64Effect 0x11dab4 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[315, 281]
    (.letOp (n := 322) (.exec 0x11dab4 (fun s => s.RIP = 0x11dab4) (addR64R64Effect 0x11dab4 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[315, 281]
    (.letOp (n := 323) (.out 0x11dab7 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11dab7 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[318, 321]
    (.letOp (n := 324) (.exec 0x11dab7 (fun s => s.RIP = 0x11dab7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11dab7 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[318, 321]
    (.letOp (n := 325) (.out 0x11dabb (shldR64R64Effect 0x11dabb 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[323, 320]
    (.letOp (n := 326) (.exec 0x11dabb (fun s => s.RIP = 0x11dabb) (shldR64R64Effect 0x11dabb 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[323, 320]
    (.letOp (n := 327) (.out 0x11dac0 (shlR64Effect 0x11dac0 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[320]
    (.letOp (n := 328) (.exec 0x11dac0 (fun s => s.RIP = 0x11dac0) (shlR64Effect 0x11dac0 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[320]
    (.letOp (n := 329) (.out 0x11dac4 (movR64Imm64Effect 0x11dac4 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 330) (.exec 0x11dac4 (fun s => s.RIP = 0x11dac4) (movR64Imm64Effect 0x11dac4 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 331) (.out 0x11dace (andR64R64Effect 0x11dace 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[327, 329]
    (.letOp (n := 332) (.exec 0x11dace (fun s => s.RIP = 0x11dace) (andR64R64Effect 0x11dace 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[327, 329]
    (.letOp (n := 333) (.out 0x11dad1 (orR64R64Effect 0x11dad1 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[331, 283]
    (.letOp (n := 334) (.exec 0x11dad1 (fun s => s.RIP = 0x11dad1) (orR64R64Effect 0x11dad1 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[331, 283]
    (.letOp (n := 335) (.out 0x11dad4 (movR64Imm64Effect 0x11dad4 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 336) (.exec 0x11dad4 (fun s => s.RIP = 0x11dad4) (movR64Imm64Effect 0x11dad4 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 337) (.out 0x11dade (mulR64Effect 0x11dade 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[335, 333]
    (.letOp (n := 338) (.out 0x11dade (mulR64Effect 0x11dade 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[335, 333]
    (.letOp (n := 339) (.exec 0x11dade (fun s => s.RIP = 0x11dade) (mulR64Effect 0x11dade 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[335, 333]
    (.letOp (n := 340) (.out 0x11dae1 (addR64M64Effect 0x11dae1 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[337, 4]
    (.letOp (n := 341) (.out 0x11dae1 (addR64M64Effect 0x11dae1 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[337, 4]
    (.letOp (n := 342) (.exec 0x11dae1 (LoadPre 0x11dae1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11dae1 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11dae1 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[337, 4]
    (.letOp (n := 343) (.out 0x11dae6 (movR64R64Effect 0x11dae6 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[340]
    (.letOp (n := 344) (.exec 0x11dae6 (fun s => s.RIP = 0x11dae6) (movR64R64Effect 0x11dae6 9 0) (Reg.operands [.gpr 0] [])) #v[340]
    (.letOp (n := 345) (.exec 0x11dae9 (StorePre 0x11dae9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11dae9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11dae9 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[340, 4]
    (b_l11d880_7))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_6 : List UInt8 :=
  [0x48, 0x8B, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x4C, 0x01, 0xF8, 0x49, 0x11,
    0xD0, 0x48, 0x01, 0xD8, 0x4D, 0x11, 0xF0, 0x4C, 0x01, 0xC8, 0x4C, 0x13, 0x44, 0x24, 0x18, 0x48,
    0x01, 0xF0, 0x49, 0x83, 0xD0, 0x00, 0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48,
    0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x4C, 0x09, 0xE0, 0x48,
    0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x03, 0x44, 0x24,
    0x68, 0x49, 0x89, 0xC1, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] ++ bytes_l11d880_7

theorem code_l11d880_6 : ∀ x ∈ codeRange 0x11da95 bytes_l11d880_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1da95 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_7

def b_l11d880_5 : Block Op Label signature Reg.count 259 :=
  .letOp (n := 259) (.out 0x11da4b (mulR64Effect 0x11da4b 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[167, 257]
    (.letOp (n := 260) (.out 0x11da4b (mulR64Effect 0x11da4b 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[167, 257]
    (.letOp (n := 261) (.exec 0x11da4b (fun s => s.RIP = 0x11da4b) (mulR64Effect 0x11da4b 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[167, 257]
    (.letOp (n := 262) (.out 0x11da4e (movR64R64Effect 0x11da4e 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[259]
    (.letOp (n := 263) (.exec 0x11da4e (fun s => s.RIP = 0x11da4e) (movR64R64Effect 0x11da4e 9 0) (Reg.operands [.gpr 0] [])) #v[259]
    (.letOp (n := 264) (.exec 0x11da51 (StorePre 0x11da51 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11da51 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11da51 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[260, 4]
    (.letOp (n := 265) (.exec 0x11da56 (StorePre 0x11da56 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11da56 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11da56 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[244, 4]
    (.letOp (n := 266) (.out 0x11da5b (movR64R64Effect 0x11da5b 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 8] []) (.reg (.gpr 12))) #v[244]
    (.letOp (n := 267) (.exec 0x11da5b (fun s => s.RIP = 0x11da5b) (movR64R64Effect 0x11da5b 12 8) (Reg.operands [.gpr 8] [])) #v[244]
    (.letOp (n := 268) (.out 0x11da5e (shrR64Effect 0x11da5e 4 12 48) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[266]
    (.letOp (n := 269) (.exec 0x11da5e (fun s => s.RIP = 0x11da5e) (shrR64Effect 0x11da5e 4 12 48) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[266]
    (.letOp (n := 270) (.out 0x11da62 (movR64M64Effect 0x11da62 10 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 271) (.exec 0x11da62 (LoadPre 0x11da62 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11da62 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11da62 10 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 272) (.out 0x11da67 (movR64R64Effect 0x11da67 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[270]
    (.letOp (n := 273) (.exec 0x11da67 (fun s => s.RIP = 0x11da67) (movR64R64Effect 0x11da67 0 10) (Reg.operands [.gpr 10] [])) #v[270]
    (.letOp (n := 274) (.out 0x11da6a (mulR64Effect 0x11da6a 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[179, 272]
    (.letOp (n := 275) (.out 0x11da6a (mulR64Effect 0x11da6a 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[179, 272]
    (.letOp (n := 276) (.exec 0x11da6a (fun s => s.RIP = 0x11da6a) (mulR64Effect 0x11da6a 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[179, 272]
    (.letOp (n := 277) (.out 0x11da6d (movR64R64Effect 0x11da6d 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[274]
    (.letOp (n := 278) (.exec 0x11da6d (fun s => s.RIP = 0x11da6d) (movR64R64Effect 0x11da6d 3 0) (Reg.operands [.gpr 0] [])) #v[274]
    (.letOp (n := 279) (.out 0x11da70 (movR64R64Effect 0x11da70 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[275]
    (.letOp (n := 280) (.exec 0x11da70 (fun s => s.RIP = 0x11da70) (movR64R64Effect 0x11da70 14 2) (Reg.operands [.gpr 2] [])) #v[275]
    (.letOp (n := 281) (.out 0x11da73 (shldR64R64Effect 0x11da73 5 6 8 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[247, 244]
    (.letOp (n := 282) (.exec 0x11da73 (fun s => s.RIP = 0x11da73) (shldR64R64Effect 0x11da73 5 6 8 12) (Reg.operands [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[247, 244]
    (.letOp (n := 283) (.out 0x11da78 (andR32Imm8Effect 0x11da78 4 12 0xf) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[268]
    (.letOp (n := 284) (.exec 0x11da78 (fun s => s.RIP = 0x11da78) (andR32Imm8Effect 0x11da78 4 12 0xf) (Reg.operands [.gpr 12] [])) #v[268]
    (.letOp (n := 285) (.out 0x11da7c (movR64R64Effect 0x11da7c 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[174]
    (.letOp (n := 286) (.exec 0x11da7c (fun s => s.RIP = 0x11da7c) (movR64R64Effect 0x11da7c 0 7) (Reg.operands [.gpr 7] [])) #v[174]
    (.letOp (n := 287) (.out 0x11da7f (movR64M64Effect 0x11da7f 1 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 288) (.exec 0x11da7f (LoadPre 0x11da7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11da7f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11da7f 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 289) (.out 0x11da84 (mulR64Effect 0x11da84 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[287, 285]
    (.letOp (n := 290) (.out 0x11da84 (mulR64Effect 0x11da84 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[287, 285]
    (.letOp (n := 291) (.exec 0x11da84 (fun s => s.RIP = 0x11da84) (mulR64Effect 0x11da84 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[287, 285]
    (.letOp (n := 292) (.out 0x11da87 (movR64R64Effect 0x11da87 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[289]
    (.letOp (n := 293) (.exec 0x11da87 (fun s => s.RIP = 0x11da87) (movR64R64Effect 0x11da87 15 0) (Reg.operands [.gpr 0] [])) #v[289]
    (.letOp (n := 294) (.out 0x11da8a (movR64R64Effect 0x11da8a 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[290]
    (.letOp (n := 295) (.exec 0x11da8a (fun s => s.RIP = 0x11da8a) (movR64R64Effect 0x11da8a 8 2) (Reg.operands [.gpr 2] [])) #v[290]
    (.letOp (n := 296) (.out 0x11da8d (movR64M64Effect 0x11da8d 13 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 297) (.exec 0x11da8d (LoadPre 0x11da8d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11da8d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11da8d 13 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 298) (.out 0x11da92 (movR64R64Effect 0x11da92 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[296]
    (.letOp (n := 299) (.exec 0x11da92 (fun s => s.RIP = 0x11da92) (movR64R64Effect 0x11da92 0 13) (Reg.operands [.gpr 13] [])) #v[296]
    (b_l11d880_6)))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_5 : List UInt8 :=
  [0x49, 0xF7, 0xE2, 0x49, 0x89, 0xC1, 0x48, 0x89, 0x54, 0x24, 0x18, 0x4C, 0x89, 0x44, 0x24, 0x10,
    0x4D, 0x89, 0xC4, 0x49, 0xC1, 0xEC, 0x30, 0x4C, 0x8B, 0x54, 0x24, 0x58, 0x4C, 0x89, 0xD0, 0x48,
    0xF7, 0xE3, 0x48, 0x89, 0xC3, 0x49, 0x89, 0xD6, 0x4C, 0x0F, 0xA4, 0xC6, 0x0C, 0x41, 0x83, 0xE4,
    0x0F, 0x48, 0x89, 0xF8, 0x48, 0x8B, 0x4C, 0x24, 0x70, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xC7, 0x49,
    0x89, 0xD0, 0x4C, 0x8B, 0x6C, 0x24, 0x60, 0x4C, 0x89, 0xE8] ++ bytes_l11d880_6

theorem code_l11d880_5 : ∀ x ∈ codeRange 0x11da4b bytes_l11d880_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1da4b 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_6

def b_l11d880_4 : Block Op Label signature Reg.count 212 :=
  .letOp (n := 212) (.out 0x11d9f5 (movR64Imm64Effect 0x11d9f5 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 213) (.exec 0x11d9f5 (fun s => s.RIP = 0x11d9f5) (movR64Imm64Effect 0x11d9f5 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 214) (.out 0x11d9ff (mulR64Effect 0x11d9ff 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[212, 210]
    (.letOp (n := 215) (.out 0x11d9ff (mulR64Effect 0x11d9ff 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[212, 210]
    (.letOp (n := 216) (.exec 0x11d9ff (fun s => s.RIP = 0x11d9ff) (mulR64Effect 0x11d9ff 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[212, 210]
    (.letOp (n := 217) (.out 0x11da02 (movR64R64Effect 0x11da02 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[214]
    (.letOp (n := 218) (.exec 0x11da02 (fun s => s.RIP = 0x11da02) (movR64R64Effect 0x11da02 8 0) (Reg.operands [.gpr 0] [])) #v[214]
    (.letOp (n := 219) (.out 0x11da05 (addR64R64Effect 0x11da05 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[208, 195]
    (.letOp (n := 220) (.out 0x11da05 (addR64R64Effect 0x11da05 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[208, 195]
    (.letOp (n := 221) (.exec 0x11da05 (fun s => s.RIP = 0x11da05) (addR64R64Effect 0x11da05 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[208, 195]
    (.letOp (n := 222) (.out 0x11da08 (atFlags StatusFlags.CF (adcR64R64Effect 0x11da08 6 13)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[206, 197, 220]
    (.letOp (n := 223) (.exec 0x11da08 (fun s => s.RIP = 0x11da08) (atFlags StatusFlags.CF (adcR64R64Effect 0x11da08 6 13)) (Reg.operands [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[206, 197, 220]
    (.letOp (n := 224) (.out 0x11da0b (addR64R64Effect 0x11da0b 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[219, 184]
    (.letOp (n := 225) (.out 0x11da0b (addR64R64Effect 0x11da0b 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[219, 184]
    (.letOp (n := 226) (.exec 0x11da0b (fun s => s.RIP = 0x11da0b) (addR64R64Effect 0x11da0b 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[219, 184]
    (.letOp (n := 227) (.out 0x11da0e (atFlags StatusFlags.CF (adcR64R64Effect 0x11da0e 6 14)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[222, 186, 225]
    (.letOp (n := 228) (.exec 0x11da0e (fun s => s.RIP = 0x11da0e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11da0e 6 14)) (Reg.operands [.gpr 6, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[222, 186, 225]
    (.letOp (n := 229) (.out 0x11da11 (addR64M64Effect 0x11da11 5 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[224, 4]
    (.letOp (n := 230) (.out 0x11da11 (addR64M64Effect 0x11da11 5 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[224, 4]
    (.letOp (n := 231) (.exec 0x11da11 (LoadPre 0x11da11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11da11 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11da11 5 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[224, 4]
    (.letOp (n := 232) (.out 0x11da19 (atFlags StatusFlags.CF (adcR64M64Effect 0x11da19 6 (.sib 4 none 0 (.d8 0x18)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[227, 4, 230]
    (.letOp (n := 233) (.exec 0x11da19 (LoadPre 0x11da19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11da19 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11da19 6 (.sib 4 none 0 (.d8 0x18)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[227, 4, 230]
    (.letOp (n := 234) (.out 0x11da1e (addR64M64Effect 0x11da1e 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[229, 4]
    (.letOp (n := 235) (.out 0x11da1e (addR64M64Effect 0x11da1e 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[229, 4]
    (.letOp (n := 236) (.exec 0x11da1e (LoadPre 0x11da1e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11da1e + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11da1e 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[229, 4]
    (.letOp (n := 237) (.out 0x11da23 (atFlags StatusFlags.CF (adcR64M64Effect 0x11da23 6 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[232, 4, 235]
    (.letOp (n := 238) (.exec 0x11da23 (LoadPre 0x11da23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11da23 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11da23 6 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[232, 4, 235]
    (.letOp (n := 239) (.out 0x11da28 (addR64R64Effect 0x11da28 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[217, 234]
    (.letOp (n := 240) (.out 0x11da28 (addR64R64Effect 0x11da28 8 5) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 5] []) (.flag .CF)) #v[217, 234]
    (.letOp (n := 241) (.exec 0x11da28 (fun s => s.RIP = 0x11da28) (addR64R64Effect 0x11da28 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[217, 234]
    (.letOp (n := 242) (.out 0x11da2b (atFlags StatusFlags.CF (adcR64R64Effect 0x11da2b 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[237, 215, 240]
    (.letOp (n := 243) (.exec 0x11da2b (fun s => s.RIP = 0x11da2b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11da2b 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[237, 215, 240]
    (.letOp (n := 244) (.out 0x11da2e (addR64R64Effect 0x11da2e 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[239, 188]
    (.letOp (n := 245) (.out 0x11da2e (addR64R64Effect 0x11da2e 8 1) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 1] []) (.flag .CF)) #v[239, 188]
    (.letOp (n := 246) (.exec 0x11da2e (fun s => s.RIP = 0x11da2e) (addR64R64Effect 0x11da2e 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[239, 188]
    (.letOp (n := 247) (.out 0x11da31 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11da31 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[242, 245]
    (.letOp (n := 248) (.exec 0x11da31 (fun s => s.RIP = 0x11da31) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11da31 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[242, 245]
    (.letOp (n := 249) (.out 0x11da35 (movR64R64Effect 0x11da35 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[199]
    (.letOp (n := 250) (.exec 0x11da35 (fun s => s.RIP = 0x11da35) (movR64R64Effect 0x11da35 0 11) (Reg.operands [.gpr 11] [])) #v[199]
    (.letOp (n := 251) (.out 0x11da38 (mulR64Effect 0x11da38 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[158, 249]
    (.letOp (n := 252) (.out 0x11da38 (mulR64Effect 0x11da38 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[158, 249]
    (.letOp (n := 253) (.exec 0x11da38 (fun s => s.RIP = 0x11da38) (mulR64Effect 0x11da38 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[158, 249]
    (.letOp (n := 254) (.exec 0x11da3b (StorePre 0x11da3b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11da3b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11da3b 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[251, 4]
    (.letOp (n := 255) (.out 0x11da40 (movR64R64Effect 0x11da40 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[252]
    (.letOp (n := 256) (.exec 0x11da40 (fun s => s.RIP = 0x11da40) (movR64R64Effect 0x11da40 5 2) (Reg.operands [.gpr 2] [])) #v[252]
    (.letOp (n := 257) (.out 0x11da43 (movR64M64Effect 0x11da43 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 258) (.exec 0x11da43 (LoadPre 0x11da43 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11da43 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11da43 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11d880_5)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_4 : List UInt8 :=
  [0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xC0,
    0x4C, 0x01, 0xE5, 0x4C, 0x11, 0xEE, 0x4C, 0x01, 0xFD, 0x4C, 0x11, 0xF6, 0x48, 0x03, 0xAC, 0x24,
    0xA0, 0x00, 0x00, 0x00, 0x48, 0x13, 0x74, 0x24, 0x18, 0x48, 0x03, 0x6C, 0x24, 0x68, 0x48, 0x13,
    0x74, 0x24, 0x10, 0x49, 0x01, 0xE8, 0x48, 0x11, 0xD6, 0x49, 0x01, 0xC8, 0x48, 0x83, 0xD6, 0x00,
    0x4C, 0x89, 0xD8, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x89, 0xD5, 0x48, 0x8B,
    0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] ++ bytes_l11d880_5

theorem code_l11d880_4 : ∀ x ∈ codeRange 0x11d9f5 bytes_l11d880_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1d9f5 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_5

def b_l11d880_3 : Block Op Label signature Reg.count 172 :=
  .letOp (n := 172) (.exec 0x11d99d (StorePre 0x11d99d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11d99d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d99d 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[170, 4]
    (.letOp (n := 173) (.exec 0x11d9a2 (StorePre 0x11d9a2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11d9a2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d9a2 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[169, 4]
    (.letOp (n := 174) (.out 0x11d9aa (movR64R64Effect 0x11d9aa 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[78]
    (.letOp (n := 175) (.exec 0x11d9aa (fun s => s.RIP = 0x11d9aa) (movR64R64Effect 0x11d9aa 7 13) (Reg.operands [.gpr 13] [])) #v[78]
    (.letOp (n := 176) (.exec 0x11d9ad (StorePre 0x11d9ad 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11d9ad + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d9ad 13 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[78, 4]
    (.letOp (n := 177) (.out 0x11d9b5 (movR64R64Effect 0x11d9b5 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[78]
    (.letOp (n := 178) (.exec 0x11d9b5 (fun s => s.RIP = 0x11d9b5) (movR64R64Effect 0x11d9b5 0 13) (Reg.operands [.gpr 13] [])) #v[78]
    (.letOp (n := 179) (.out 0x11d9b8 (movR64M64Effect 0x11d9b8 3 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 180) (.exec 0x11d9b8 (LoadPre 0x11d9b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11d9b8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d9b8 3 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 181) (.out 0x11d9c0 (mulR64Effect 0x11d9c0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[179, 177]
    (.letOp (n := 182) (.out 0x11d9c0 (mulR64Effect 0x11d9c0 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[179, 177]
    (.letOp (n := 183) (.exec 0x11d9c0 (fun s => s.RIP = 0x11d9c0) (mulR64Effect 0x11d9c0 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[179, 177]
    (.letOp (n := 184) (.out 0x11d9c3 (movR64R64Effect 0x11d9c3 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[181]
    (.letOp (n := 185) (.exec 0x11d9c3 (fun s => s.RIP = 0x11d9c3) (movR64R64Effect 0x11d9c3 15 0) (Reg.operands [.gpr 0] [])) #v[181]
    (.letOp (n := 186) (.out 0x11d9c6 (movR64R64Effect 0x11d9c6 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[182]
    (.letOp (n := 187) (.exec 0x11d9c6 (fun s => s.RIP = 0x11d9c6) (movR64R64Effect 0x11d9c6 14 2) (Reg.operands [.gpr 2] [])) #v[182]
    (.letOp (n := 188) (.out 0x11d9c9 (shldR64R64Effect 0x11d9c9 5 1 6 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[152, 149]
    (.letOp (n := 189) (.exec 0x11d9c9 (fun s => s.RIP = 0x11d9c9) (shldR64R64Effect 0x11d9c9 5 1 6 12) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[152, 149]
    (.letOp (n := 190) (.out 0x11d9ce (movR64M64Effect 0x11d9ce 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 191) (.exec 0x11d9ce (LoadPre 0x11d9ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11d9ce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11d9ce 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 192) (.out 0x11d9d3 (mulR64Effect 0x11d9d3 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[96, 190]
    (.letOp (n := 193) (.out 0x11d9d3 (mulR64Effect 0x11d9d3 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[96, 190]
    (.letOp (n := 194) (.exec 0x11d9d3 (fun s => s.RIP = 0x11d9d3) (mulR64Effect 0x11d9d3 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[96, 190]
    (.letOp (n := 195) (.out 0x11d9d6 (movR64R64Effect 0x11d9d6 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[192]
    (.letOp (n := 196) (.exec 0x11d9d6 (fun s => s.RIP = 0x11d9d6) (movR64R64Effect 0x11d9d6 12 0) (Reg.operands [.gpr 0] [])) #v[192]
    (.letOp (n := 197) (.out 0x11d9d9 (movR64R64Effect 0x11d9d9 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[193]
    (.letOp (n := 198) (.exec 0x11d9d9 (fun s => s.RIP = 0x11d9d9) (movR64R64Effect 0x11d9d9 13 2) (Reg.operands [.gpr 2] [])) #v[193]
    (.letOp (n := 199) (.out 0x11d9dc (movR64M64Effect 0x11d9dc 11 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 200) (.exec 0x11d9dc (LoadPre 0x11d9dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11d9dc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11d9dc 11 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 201) (.out 0x11d9e1 (movR64R64Effect 0x11d9e1 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[199]
    (.letOp (n := 202) (.exec 0x11d9e1 (fun s => s.RIP = 0x11d9e1) (movR64R64Effect 0x11d9e1 0 11) (Reg.operands [.gpr 11] [])) #v[199]
    (.letOp (n := 203) (.out 0x11d9e4 (mulM64Effect 0x11d9e4 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[201, 4]
    (.letOp (n := 204) (.out 0x11d9e4 (mulM64Effect 0x11d9e4 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[201, 4]
    (.letOp (n := 205) (.exec 0x11d9e4 (LoadPre 0x11d9e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11d9e4 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11d9e4 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[201, 4]
    (.letOp (n := 206) (.out 0x11d9ec (movR64R64Effect 0x11d9ec 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[204]
    (.letOp (n := 207) (.exec 0x11d9ec (fun s => s.RIP = 0x11d9ec) (movR64R64Effect 0x11d9ec 6 2) (Reg.operands [.gpr 2] [])) #v[204]
    (.letOp (n := 208) (.out 0x11d9ef (movR64R64Effect 0x11d9ef 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[203]
    (.letOp (n := 209) (.exec 0x11d9ef (fun s => s.RIP = 0x11d9ef) (movR64R64Effect 0x11d9ef 5 0) (Reg.operands [.gpr 0] [])) #v[203]
    (.letOp (n := 210) (.out 0x11d9f2 (movR64R64Effect 0x11d9f2 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[154]
    (.letOp (n := 211) (.exec 0x11d9f2 (fun s => s.RIP = 0x11d9f2) (movR64R64Effect 0x11d9f2 0 8) (Reg.operands [.gpr 8] [])) #v[154]
    (b_l11d880_4))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_3 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xEF,
    0x4C, 0x89, 0xAC, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE8, 0x48, 0x8B, 0x9C, 0x24, 0xA8,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xC7, 0x49, 0x89, 0xD6, 0x48, 0x0F, 0xA4, 0xF1,
    0x0C, 0x48, 0x8B, 0x44, 0x24, 0x60, 0x49, 0xF7, 0xE3, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD5, 0x4C,
    0x8B, 0x5C, 0x24, 0x28, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0xA4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48,
    0x89, 0xD6, 0x48, 0x89, 0xC5, 0x4C, 0x89, 0xC0] ++ bytes_l11d880_4

theorem code_l11d880_3 : ∀ x ∈ codeRange 0x11d99d bytes_l11d880_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1d99d 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_4

def b_l11d880_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x11d94e (mulR64Effect 0x11d94e 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[5, 126]
    (.letOp (n := 129) (.out 0x11d94e (mulR64Effect 0x11d94e 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[5, 126]
    (.letOp (n := 130) (.exec 0x11d94e (fun s => s.RIP = 0x11d94e) (mulR64Effect 0x11d94e 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[5, 126]
    (.letOp (n := 131) (.out 0x11d951 (addR64R64Effect 0x11d951 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[105, 92]
    (.letOp (n := 132) (.out 0x11d951 (addR64R64Effect 0x11d951 3 12) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 12] []) (.flag .CF)) #v[105, 92]
    (.letOp (n := 133) (.exec 0x11d951 (fun s => s.RIP = 0x11d951) (addR64R64Effect 0x11d951 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[105, 92]
    (.letOp (n := 134) (.out 0x11d954 (atFlags StatusFlags.CF (adcR64R64Effect 0x11d954 1 14)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[107, 94, 132]
    (.letOp (n := 135) (.exec 0x11d954 (fun s => s.RIP = 0x11d954) (atFlags StatusFlags.CF (adcR64R64Effect 0x11d954 1 14)) (Reg.operands [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[107, 94, 132]
    (.letOp (n := 136) (.out 0x11d957 (addR64R64Effect 0x11d957 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[131, 85]
    (.letOp (n := 137) (.out 0x11d957 (addR64R64Effect 0x11d957 3 6) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 6] []) (.flag .CF)) #v[131, 85]
    (.letOp (n := 138) (.exec 0x11d957 (fun s => s.RIP = 0x11d957) (addR64R64Effect 0x11d957 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[131, 85]
    (.letOp (n := 139) (.out 0x11d95a (atFlags StatusFlags.CF (adcR64R64Effect 0x11d95a 1 10)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[134, 83, 137]
    (.letOp (n := 140) (.exec 0x11d95a (fun s => s.RIP = 0x11d95a) (atFlags StatusFlags.CF (adcR64R64Effect 0x11d95a 1 10)) (Reg.operands [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[134, 83, 137]
    (.letOp (n := 141) (.out 0x11d95d (addR64R64Effect 0x11d95d 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[136, 73]
    (.letOp (n := 142) (.out 0x11d95d (addR64R64Effect 0x11d95d 3 9) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 9] []) (.flag .CF)) #v[136, 73]
    (.letOp (n := 143) (.exec 0x11d95d (fun s => s.RIP = 0x11d95d) (addR64R64Effect 0x11d95d 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[136, 73]
    (.letOp (n := 144) (.out 0x11d960 (atFlags StatusFlags.CF (adcR64M64Effect 0x11d960 1 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[139, 4, 142]
    (.letOp (n := 145) (.exec 0x11d960 (LoadPre 0x11d960 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11d960 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11d960 1 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[139, 4, 142]
    (.letOp (n := 146) (.out 0x11d965 (addR64R64Effect 0x11d965 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[128, 141]
    (.letOp (n := 147) (.out 0x11d965 (addR64R64Effect 0x11d965 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[128, 141]
    (.letOp (n := 148) (.exec 0x11d965 (fun s => s.RIP = 0x11d965) (addR64R64Effect 0x11d965 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[128, 141]
    (.letOp (n := 149) (.out 0x11d968 (movR64R64Effect 0x11d968 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[146]
    (.letOp (n := 150) (.exec 0x11d968 (fun s => s.RIP = 0x11d968) (movR64R64Effect 0x11d968 6 0) (Reg.operands [.gpr 0] [])) #v[146]
    (.letOp (n := 151) (.exec 0x11d96b (StorePre 0x11d96b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11d96b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d96b 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[146, 4]
    (.letOp (n := 152) (.out 0x11d973 (atFlags StatusFlags.CF (adcR64R64Effect 0x11d973 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[144, 129, 147]
    (.letOp (n := 153) (.exec 0x11d973 (fun s => s.RIP = 0x11d973) (atFlags StatusFlags.CF (adcR64R64Effect 0x11d973 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[144, 129, 147]
    (.letOp (n := 154) (.out 0x11d976 (shldR64R64Effect 0x11d976 5 8 15 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[120, 122]
    (.letOp (n := 155) (.exec 0x11d976 (fun s => s.RIP = 0x11d976) (shldR64R64Effect 0x11d976 5 8 15 12) (Reg.operands [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[120, 122]
    (.letOp (n := 156) (.out 0x11d97b (movR64R64Effect 0x11d97b 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[112]
    (.letOp (n := 157) (.exec 0x11d97b (fun s => s.RIP = 0x11d97b) (movR64R64Effect 0x11d97b 0 7) (Reg.operands [.gpr 7] [])) #v[112]
    (.letOp (n := 158) (.out 0x11d97e (movR64M64Effect 0x11d97e 9 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 159) (.exec 0x11d97e (LoadPre 0x11d97e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11d97e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11d97e 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 160) (.out 0x11d983 (mulR64Effect 0x11d983 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[158, 156]
    (.letOp (n := 161) (.out 0x11d983 (mulR64Effect 0x11d983 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[158, 156]
    (.letOp (n := 162) (.exec 0x11d983 (fun s => s.RIP = 0x11d983) (mulR64Effect 0x11d983 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[158, 156]
    (.letOp (n := 163) (.exec 0x11d986 (StorePre 0x11d986 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11d986 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d986 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[161, 4]
    (.letOp (n := 164) (.exec 0x11d98b (StorePre 0x11d98b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11d98b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d98b 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[160, 4]
    (.letOp (n := 165) (.out 0x11d990 (movR64M64Effect 0x11d990 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 166) (.exec 0x11d990 (LoadPre 0x11d990 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11d990 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11d990 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 167) (.out 0x11d995 (movR64M64Effect 0x11d995 10 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 168) (.exec 0x11d995 (LoadPre 0x11d995 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11d995 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11d995 10 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 169) (.out 0x11d99a (mulR64Effect 0x11d99a 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[167, 165]
    (.letOp (n := 170) (.out 0x11d99a (mulR64Effect 0x11d99a 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[167, 165]
    (.letOp (n := 171) (.exec 0x11d99a (fun s => s.RIP = 0x11d99a) (mulR64Effect 0x11d99a 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[167, 165]
    (b_l11d880_3))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_2 : List UInt8 :=
  [0x48, 0xF7, 0xE5, 0x4C, 0x01, 0xE3, 0x4C, 0x11, 0xF1, 0x48, 0x01, 0xF3, 0x4C, 0x11, 0xD1, 0x4C,
    0x01, 0xCB, 0x48, 0x13, 0x4C, 0x24, 0x10, 0x48, 0x01, 0xD8, 0x48, 0x89, 0xC6, 0x48, 0x89, 0x84,
    0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x11, 0xD1, 0x4D, 0x0F, 0xA4, 0xF8, 0x0C, 0x48, 0x89, 0xF8,
    0x4C, 0x8B, 0x4C, 0x24, 0x08, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x89, 0x44,
    0x24, 0x68, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x4C, 0x8B, 0x54, 0x24, 0x38, 0x49, 0xF7, 0xE2] ++ bytes_l11d880_3

theorem code_l11d880_2 : ∀ x ∈ codeRange 0x11d94e bytes_l11d880_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1d94e 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_3

def b_l11d880_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x11d8e9 (mulR64Effect 0x11d8e9 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[59, 87]
    (.letOp (n := 90) (.out 0x11d8e9 (mulR64Effect 0x11d8e9 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[59, 87]
    (.letOp (n := 91) (.exec 0x11d8e9 (fun s => s.RIP = 0x11d8e9) (mulR64Effect 0x11d8e9 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[59, 87]
    (.letOp (n := 92) (.out 0x11d8ec (movR64R64Effect 0x11d8ec 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[89]
    (.letOp (n := 93) (.exec 0x11d8ec (fun s => s.RIP = 0x11d8ec) (movR64R64Effect 0x11d8ec 12 0) (Reg.operands [.gpr 0] [])) #v[89]
    (.letOp (n := 94) (.out 0x11d8ef (movR64R64Effect 0x11d8ef 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[90]
    (.letOp (n := 95) (.exec 0x11d8ef (fun s => s.RIP = 0x11d8ef) (movR64R64Effect 0x11d8ef 14 2) (Reg.operands [.gpr 2] [])) #v[90]
    (.letOp (n := 96) (.out 0x11d8f2 (movR64M64Effect 0x11d8f2 11 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 97) (.exec 0x11d8f2 (LoadPre 0x11d8f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x11d8f2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d8f2 11 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 98) (.out 0x11d8fa (movR64M64Effect 0x11d8fa 0 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 99) (.exec 0x11d8fa (LoadPre 0x11d8fa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x11d8fa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d8fa 0 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 100) (.exec 0x11d902 (StorePre 0x11d902 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11d902 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d902 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[98, 4]
    (.letOp (n := 101) (.out 0x11d907 (mulR64Effect 0x11d907 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[96, 98]
    (.letOp (n := 102) (.out 0x11d907 (mulR64Effect 0x11d907 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[96, 98]
    (.letOp (n := 103) (.exec 0x11d907 (fun s => s.RIP = 0x11d907) (mulR64Effect 0x11d907 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[96, 98]
    (.letOp (n := 104) (.exec 0x11d90a (StorePre 0x11d90a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11d90a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d90a 11 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[96, 4]
    (.letOp (n := 105) (.out 0x11d90f (movR64R64Effect 0x11d90f 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[101]
    (.letOp (n := 106) (.exec 0x11d90f (fun s => s.RIP = 0x11d90f) (movR64R64Effect 0x11d90f 3 0) (Reg.operands [.gpr 0] [])) #v[101]
    (.letOp (n := 107) (.out 0x11d912 (movR64R64Effect 0x11d912 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[102]
    (.letOp (n := 108) (.exec 0x11d912 (fun s => s.RIP = 0x11d912) (movR64R64Effect 0x11d912 1 2) (Reg.operands [.gpr 2] [])) #v[102]
    (.letOp (n := 109) (.out 0x11d915 (movR64M64Effect 0x11d915 2 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 110) (.exec 0x11d915 (LoadPre 0x11d915 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x11d915 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d915 2 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 111) (.exec 0x11d91d (StorePre 0x11d91d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11d91d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d91d 2 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[109, 4]
    (.letOp (n := 112) (.out 0x11d925 (movR64M64Effect 0x11d925 7 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 113) (.exec 0x11d925 (LoadPre 0x11d925 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x11d925 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d925 7 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 114) (.out 0x11d92d (movR64R64Effect 0x11d92d 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[112]
    (.letOp (n := 115) (.exec 0x11d92d (fun s => s.RIP = 0x11d92d) (movR64R64Effect 0x11d92d 0 7) (Reg.operands [.gpr 7] [])) #v[112]
    (.letOp (n := 116) (.exec 0x11d930 (StorePre 0x11d930 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11d930 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d930 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[112, 4]
    (.letOp (n := 117) (.out 0x11d938 (mulR64Effect 0x11d938 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[109, 114]
    (.letOp (n := 118) (.out 0x11d938 (mulR64Effect 0x11d938 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[109, 114]
    (.letOp (n := 119) (.exec 0x11d938 (fun s => s.RIP = 0x11d938) (mulR64Effect 0x11d938 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[109, 114]
    (.letOp (n := 120) (.out 0x11d93b (movR64R64Effect 0x11d93b 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[118]
    (.letOp (n := 121) (.exec 0x11d93b (fun s => s.RIP = 0x11d93b) (movR64R64Effect 0x11d93b 8 2) (Reg.operands [.gpr 2] [])) #v[118]
    (.letOp (n := 122) (.out 0x11d93e (movR64R64Effect 0x11d93e 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[117]
    (.letOp (n := 123) (.exec 0x11d93e (fun s => s.RIP = 0x11d93e) (movR64R64Effect 0x11d93e 15 0) (Reg.operands [.gpr 0] [])) #v[117]
    (.letOp (n := 124) (.out 0x11d941 (movR64Imm64Effect 0x11d941 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 125) (.exec 0x11d941 (fun s => s.RIP = 0x11d941) (movR64Imm64Effect 0x11d941 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 126) (.out 0x11d94b (andR64R64Effect 0x11d94b 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[117, 124]
    (.letOp (n := 127) (.exec 0x11d94b (fun s => s.RIP = 0x11d94b) (andR64R64Effect 0x11d94b 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[117, 124]
    (b_l11d880_2)))))))))))))))))))))))))))))))))))))))

def bytes_l11d880_1 : List UInt8 :=
  [0x49, 0xF7, 0xE0, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD6, 0x4C, 0x8B, 0x9C, 0x24, 0x40, 0x01, 0x00,
    0x00, 0x48, 0x8B, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x28, 0x49, 0xF7,
    0xE3, 0x4C, 0x89, 0x5C, 0x24, 0x70, 0x48, 0x89, 0xC3, 0x48, 0x89, 0xD1, 0x48, 0x8B, 0x94, 0x24,
    0x48, 0x01, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xBC, 0x24,
    0x70, 0x01, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x48, 0x89, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE2, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC7, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x0F, 0x00, 0x48, 0x21, 0xD0] ++ bytes_l11d880_2

theorem code_l11d880_1 : ∀ x ∈ codeRange 0x11d8e9 bytes_l11d880_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1d8e9 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_2

def b_l11d880 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d880 (movR64M64Effect 0x11d880 2 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x11d880 (LoadPre 0x11d880 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x11d880 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d880 2 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11d888 (StorePre 0x11d888 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11d888 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d888 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11d88d (movR64M64Effect 0x11d88d 6 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 57) (.exec 0x11d88d (LoadPre 0x11d88d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x11d88d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d88d 6 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11d895 (StorePre 0x11d895 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11d895 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d895 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11d89a (movR64M64Effect 0x11d89a 8 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 60) (.exec 0x11d89a (LoadPre 0x11d89a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x11d89a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d89a 8 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11d8a2 (StorePre 0x11d8a2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11d8a2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d8a2 8 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11d8aa (movR64M64Effect 0x11d8aa 1 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x11d8aa (LoadPre 0x11d8aa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x11d8aa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d8aa 1 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x11d8b2 (StorePre 0x11d8b2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11d8b2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d8b2 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x11d8b7 (movR64M64Effect 0x11d8b7 7 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x11d8b7 (LoadPre 0x11d8b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x11d8b7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d8b7 7 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x11d8bf (movR64M64Effect 0x11d8bf 0 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 68) (.exec 0x11d8bf (LoadPre 0x11d8bf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x11d8bf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d8bf 0 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x11d8c7 (StorePre 0x11d8c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11d8c7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d8c7 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x11d8cc (mulR64Effect 0x11d8cc 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[53, 67]
    (.letOp (n := 71) (.out 0x11d8cc (mulR64Effect 0x11d8cc 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[53, 67]
    (.letOp (n := 72) (.exec 0x11d8cc (fun s => s.RIP = 0x11d8cc) (mulR64Effect 0x11d8cc 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 67]
    (.letOp (n := 73) (.out 0x11d8cf (movR64R64Effect 0x11d8cf 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[70]
    (.letOp (n := 74) (.exec 0x11d8cf (fun s => s.RIP = 0x11d8cf) (movR64R64Effect 0x11d8cf 9 0) (Reg.operands [.gpr 0] [])) #v[70]
    (.letOp (n := 75) (.exec 0x11d8d2 (StorePre 0x11d8d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11d8d2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d8d2 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 76) (.out 0x11d8d7 (movR64R64Effect 0x11d8d7 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 77) (.exec 0x11d8d7 (fun s => s.RIP = 0x11d8d7) (movR64R64Effect 0x11d8d7 0 7) (Reg.operands [.gpr 7] [])) #v[65]
    (.letOp (n := 78) (.out 0x11d8da (movR64R64Effect 0x11d8da 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 7] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 79) (.exec 0x11d8da (fun s => s.RIP = 0x11d8da) (movR64R64Effect 0x11d8da 13 7) (Reg.operands [.gpr 7] [])) #v[65]
    (.letOp (n := 80) (.out 0x11d8dd (mulR64Effect 0x11d8dd 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[56, 76]
    (.letOp (n := 81) (.out 0x11d8dd (mulR64Effect 0x11d8dd 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[56, 76]
    (.letOp (n := 82) (.exec 0x11d8dd (fun s => s.RIP = 0x11d8dd) (mulR64Effect 0x11d8dd 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[56, 76]
    (.letOp (n := 83) (.out 0x11d8e0 (movR64R64Effect 0x11d8e0 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[81]
    (.letOp (n := 84) (.exec 0x11d8e0 (fun s => s.RIP = 0x11d8e0) (movR64R64Effect 0x11d8e0 10 2) (Reg.operands [.gpr 2] [])) #v[81]
    (.letOp (n := 85) (.out 0x11d8e3 (movR64R64Effect 0x11d8e3 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[80]
    (.letOp (n := 86) (.exec 0x11d8e3 (fun s => s.RIP = 0x11d8e3) (movR64R64Effect 0x11d8e3 6 0) (Reg.operands [.gpr 0] [])) #v[80]
    (.letOp (n := 87) (.out 0x11d8e6 (movR64R64Effect 0x11d8e6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[62]
    (.letOp (n := 88) (.exec 0x11d8e6 (fun s => s.RIP = 0x11d8e6) (movR64R64Effect 0x11d8e6 0 1) (Reg.operands [.gpr 1] [])) #v[62]
    (b_l11d880_1))))))))))))))))))))))))))))))))))))

def bytes_l11d880 : List UInt8 :=
  [0x48, 0x8B, 0x94, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x08, 0x48, 0x8B, 0xB4,
    0x24, 0x30, 0x01, 0x00, 0x00, 0x48, 0x89, 0x74, 0x24, 0x38, 0x4C, 0x8B, 0x84, 0x24, 0x38, 0x01,
    0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x58, 0x01,
    0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x60, 0x48, 0x8B, 0xBC, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48,
    0x8B, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x58, 0x48, 0xF7, 0xE2, 0x49,
    0x89, 0xC1, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x89, 0xF8, 0x49, 0x89, 0xFD, 0x48, 0xF7, 0xE6,
    0x49, 0x89, 0xD2, 0x48, 0x89, 0xC6, 0x48, 0x89, 0xC8] ++ bytes_l11d880_1

theorem code_l11d880 : ∀ x ∈ codeRange 0x11d880 bytes_l11d880, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1d880 105 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d880_1

@[cfg_block] def b_l11f5e5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f5e5 (cmpMImm8Effect 0x11f5e5 9 64 (.sib 4 none 0 (.d32 0x1a0)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x11f5e5 (LoadPre 0x11f5e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x11f5e5 + BitVec.ofNat 64 9)) 8) (cmpMImm8Effect 0x11f5e5 9 64 (.sib 4 none 0 (.d32 0x1a0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11d7d0, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11f5f4, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11f5e5 : List UInt8 :=
  [0x48, 0x83, 0xBC, 0x24, 0xA0, 0x01, 0x00, 0x00, 0x00, 0x0F, 0x84, 0xDC, 0xE1, 0xFF, 0xFF]

theorem code_l11f5e5 : ∀ x ∈ codeRange 0x11f5e5 bytes_l11f5e5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f5e5 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f5f4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f5f4 (movR64M64Effect 0x11f5f4 3 (.sib 4 none 0 (.d32 0x1c0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x11f5f4 (LoadPre 0x11f5f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x11f5f4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f5f4 3 (.sib 4 none 0 (.d32 0x1c0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11f5fc (xorR32R32Effect 0x11f5fc 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 56) (.exec 0x11f5fc (fun s => s.RIP = 0x11f5fc) (xorR32R32Effect 0x11f5fc 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 57) (.exec 0x11f5ff (fun s => s.RIP = 0x11f5ff) (fun _ => nopEffect 0x11f5ff 1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l11f600, RegMap.args [(3, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l11f5f4 : List UInt8 :=
  [0x48, 0x8B, 0x9C, 0x24, 0xC0, 0x01, 0x00, 0x00, 0x45, 0x31, 0xF6, 0x90]

theorem code_l11f5f4 : ∀ x ∈ codeRange 0x11f5f4 bytes_l11f5f4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f5f4 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f600 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f600 (cmpMREffect 0x11f600 8 64 14 (.sib 4 none 0 (.d32 0x268))) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 4] []) (.flag .ZF)) #v[14, 4]
    (.letOp (n := 54) (.exec 0x11f600 (LoadPre 0x11f600 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x268)) s (0x11f600 + BitVec.ofNat 64 8)) 8) (cmpMREffect 0x11f600 8 64 14 (.sib 4 none 0 (.d32 0x268))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11f6f1, RegMap.args [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11f60e, RegMap.args [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11f600 : List UInt8 :=
  [0x4C, 0x39, 0xB4, 0x24, 0x68, 0x02, 0x00, 0x00, 0x0F, 0x84, 0xE3, 0x00, 0x00, 0x00]

theorem code_l11f600 : ∀ x ∈ codeRange 0x11f600 bytes_l11f600, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f600 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f60e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f60e (cmpMREffect 0x11f60e 8 64 14 (.sib 4 none 0 (.d32 0x260))) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 4] []) (.flag .ZF)) #v[14, 4]
    (.letOp (n := 54) (.exec 0x11f60e (LoadPre 0x11f60e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x260)) s (0x11f60e + BitVec.ofNat 64 8)) 8) (cmpMREffect 0x11f60e 8 64 14 (.sib 4 none 0 (.d32 0x260))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11f708, RegMap.args [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11f61c, RegMap.args [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11f60e : List UInt8 :=
  [0x4C, 0x39, 0xB4, 0x24, 0x60, 0x02, 0x00, 0x00, 0x0F, 0x84, 0xEC, 0x00, 0x00, 0x00]

theorem code_l11f60e : ∀ x ∈ codeRange 0x11f60e bytes_l11f60e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f60e 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f61c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f61c (movR32Imm32Effect 0x11f61c 5 2 0x3c0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x11f61c (fun s => s.RIP = 0x11f61c) (movR32Imm32Effect 0x11f61c 5 2 0x3c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11f621 (leaR64Effect 0x11f621 12 (.sib 4 none 0 (.d32 0x850))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 56) (.exec 0x11f621 (fun s => s.RIP = 0x11f621) (leaR64Effect 0x11f621 12 (.sib 4 none 0 (.d32 0x850))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11f629 (movR64R64Effect 0x11f629 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x11f629 (fun s => s.RIP = 0x11f629) (movR64R64Effect 0x11f629 7 12) (Reg.operands [.gpr 12] [])) #v[55]
    (.letOp (n := 59) (.out 0x11f62c (movR64R64Effect 0x11f62c 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 60) (.exec 0x11f62c (fun s => s.RIP = 0x11f62c) (movR64R64Effect 0x11f62c 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 61) (.out 0x11f62f (leaR64Effect 0x11f62f 5 (.rip 0xb1ea)) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 62) (.exec 0x11f62f (fun s => s.RIP = 0x11f62f) (leaR64Effect 0x11f62f 5 (.rip 0xb1ea)) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x11f636 (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x11f638) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 61]
    (.letOp (n := 64) (.exec 0x11f636 (GoesTo (CallPre 0x11f636 2 (fun s => (Operand.reg 5 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x11f638) 0x12a820) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x11f638) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 61]
    (.letOp (n := 65) (.const ⟨64, 0x11f638⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 53), (3, 3), (4, 63), (5, 61), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l11f638, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l11f61c : List UInt8 :=
  [0xBA, 0xC0, 0x03, 0x00, 0x00, 0x4C, 0x8D, 0xA4, 0x24, 0x50, 0x08, 0x00, 0x00, 0x4C, 0x89, 0xE7,
    0x48, 0x89, 0xDE, 0x48, 0x8D, 0x2D, 0xEA, 0xB1, 0x00, 0x00, 0xFF, 0xD5]

theorem code_l11f61c : ∀ x ∈ codeRange 0x11f61c bytes_l11f61c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f61c 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f638 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f638 (leaR64Effect 0x11f638 6 (.base 3 (.d32 0x3c0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 54) (.exec 0x11f638 (fun s => s.RIP = 0x11f638) (leaR64Effect 0x11f638 6 (.base 3 (.d32 0x3c0))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x11f63f (movR32Imm32Effect 0x11f63f 5 2 0x3c0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x11f63f (fun s => s.RIP = 0x11f63f) (movR32Imm32Effect 0x11f63f 5 2 0x3c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x11f644 (leaR64Effect 0x11f644 7 (.sib 4 none 0 (.d32 0x490))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x11f644 (fun s => s.RIP = 0x11f644) (leaR64Effect 0x11f644 7 (.sib 4 none 0 (.d32 0x490))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x11f64c (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x11f64e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 60) (.exec 0x11f64c (GoesTo (CallPre 0x11f64c 2 (fun s => (Operand.reg 5 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x11f64e) 0x12a820) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x11f64e) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 61) (.const ⟨64, 0x11f64e⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 59), (5, 5), (6, 53), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l11f64e, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11f638 : List UInt8 :=
  [0x48, 0x8D, 0xB3, 0xC0, 0x03, 0x00, 0x00, 0xBA, 0xC0, 0x03, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24,
    0x90, 0x04, 0x00, 0x00, 0xFF, 0xD5]

theorem code_l11f638 : ∀ x ∈ codeRange 0x11f638 bytes_l11f638, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f638 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f64e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f64e (movR64M64Effect 0x11f64e 13 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 54) (.exec 0x11f64e (LoadPre 0x11f64e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11f64e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f64e 13 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11f656 (movzxR32M8Effect 0x11f656 6 2 (.sib 13 (some 14) 0 (.d8 0xdf))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 14] []) (.reg (.gpr 2))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x11f656 (LoadPre 0x11f656 (fun s => AddrMode.addr (.sib 13 (some 14) 0 (.d8 0xdf)) s (0x11f656 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x11f656 6 2 (.sib 13 (some 14) 0 (.d8 0xdf))) (Reg.operands [.gpr 13, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x11f65c (leaR64Effect 0x11f65c 5 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 58) (.exec 0x11f65c (fun s => s.RIP = 0x11f65c) (leaR64Effect 0x11f65c 5 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x11f664 (movR64R64Effect 0x11f664 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x11f664 (fun s => s.RIP = 0x11f664) (movR64R64Effect 0x11f664 7 5) (Reg.operands [.gpr 5] [])) #v[57]
    (.letOp (n := 61) (.out 0x11f667 (movR64R64Effect 0x11f667 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 62) (.exec 0x11f667 (fun s => s.RIP = 0x11f667) (movR64R64Effect 0x11f667 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 63) (.out 0x11f66a (leaR64Effect 0x11f66a 12 (.sib 4 none 0 (.d32 0x490))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 64) (.exec 0x11f66a (fun s => s.RIP = 0x11f66a) (leaR64Effect 0x11f66a 12 (.sib 4 none 0 (.d32 0x490))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x11f672 (callEffect (fun _ => 0x11c510) 0x11f677) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x11f672 (PushPre 0x11f672 5) (callEffect (fun _ => 0x11c510) 0x11f677) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x11f677⟩) #v[]
    (.terminate (.call ⟨.l11c510, RegMap.args [(2, 55), (3, 3), (4, 65), (5, 57), (6, 61), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 63), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l11f677, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l11f64e : List UInt8 :=
  [0x4C, 0x8B, 0xAC, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x43, 0x0F, 0xB6, 0x54, 0x35, 0xDF, 0x48, 0x8D,
    0xAC, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xE6, 0x4C, 0x8D, 0xA4, 0x24,
    0x90, 0x04, 0x00, 0x00, 0xE8, 0x99, 0xCE, 0xFF, 0xFF]

theorem code_l11f64e : ∀ x ∈ codeRange 0x11f64e bytes_l11f64e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f64e 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f677 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f677 (leaR64Effect 0x11f677 15 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x11f677 (fun s => s.RIP = 0x11f677) (leaR64Effect 0x11f677 15 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11f67f (movR64R64Effect 0x11f67f 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x11f67f (fun s => s.RIP = 0x11f67f) (movR64R64Effect 0x11f67f 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 57) (.out 0x11f682 (movR64R64Effect 0x11f682 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 58) (.exec 0x11f682 (fun s => s.RIP = 0x11f682) (movR64R64Effect 0x11f682 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x11f685 (callEffect (fun _ => 0x10a410) 0x11f68a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11f685 (PushPre 0x11f685 5) (callEffect (fun _ => 0x10a410) 0x11f68a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11f68a⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l11f68a, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11f677 : List UInt8 :=
  [0x4C, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xEE, 0xE8, 0x86,
    0xAD, 0xFE, 0xFF]

theorem code_l11f677 : ∀ x ∈ codeRange 0x11f677 bytes_l11f677, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f677 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f68a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f68a (movzxR32M8Effect 0x11f68a 6 2 (.sib 13 (some 14) 0 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 14] []) (.reg (.gpr 2))) #v[13, 14]
    (.letOp (n := 54) (.exec 0x11f68a (LoadPre 0x11f68a (fun s => AddrMode.addr (.sib 13 (some 14) 0 (.d8 0x0)) s (0x11f68a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x11f68a 6 2 (.sib 13 (some 14) 0 (.d8 0x0))) (Reg.operands [.gpr 13, .gpr 14] [])) #v[13, 14]
    (.letOp (n := 55) (.out 0x11f690 (movR64R64Effect 0x11f690 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 56) (.exec 0x11f690 (fun s => s.RIP = 0x11f690) (movR64R64Effect 0x11f690 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x11f693 (movR64R64Effect 0x11f693 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x11f693 (fun s => s.RIP = 0x11f693) (movR64R64Effect 0x11f693 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11f696 (callEffect (fun _ => 0x11c510) 0x11f69b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11f696 (PushPre 0x11f696 5) (callEffect (fun _ => 0x11c510) 0x11f69b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11f69b⟩) #v[]
    (.terminate (.call ⟨.l11c510, RegMap.args [(2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l11f69b, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11f68a : List UInt8 :=
  [0x43, 0x0F, 0xB6, 0x54, 0x35, 0x00, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xE6, 0xE8, 0x75, 0xCE, 0xFF,
    0xFF]

theorem code_l11f68a : ∀ x ∈ codeRange 0x11f68a bytes_l11f68a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f68a 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f69b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f69b (movR64R64Effect 0x11f69b 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 54) (.exec 0x11f69b (fun s => s.RIP = 0x11f69b) (movR64R64Effect 0x11f69b 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x11f69e (movR64R64Effect 0x11f69e 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 56) (.exec 0x11f69e (fun s => s.RIP = 0x11f69e) (movR64R64Effect 0x11f69e 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x11f6a1 (callEffect (fun _ => 0x10a410) 0x11f6a6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x11f6a1 (PushPre 0x11f6a1 5) (callEffect (fun _ => 0x10a410) 0x11f6a6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x11f6a6⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l11f6a6, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l11f69b : List UInt8 :=
  [0x4C, 0x89, 0xFF, 0x48, 0x89, 0xEE, 0xE8, 0x6A, 0xAD, 0xFE, 0xFF]

theorem code_l11f69b : ∀ x ∈ codeRange 0x11f69b bytes_l11f69b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f69b 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f6a6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f6a6 (addR64Imm8Effect 0x11f6a6 14 0x42) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 54) (.exec 0x11f6a6 (fun s => s.RIP = 0x11f6a6) (addR64Imm8Effect 0x11f6a6 14 0x42) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x11f6aa (addR64Imm32Effect 0x11f6aa 3 0x780) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 56) (.exec 0x11f6aa (fun s => s.RIP = 0x11f6aa) (addR64Imm32Effect 0x11f6aa 3 0x780) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x11f6b1 (cmpMREffect 0x11f6b1 8 64 14 (.sib 4 none 0 (.d32 0x258))) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 4] []) (.flag .ZF)) #v[53, 4]
    (.letOp (n := 58) (.exec 0x11f6b1 (LoadPre 0x11f6b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x258)) s (0x11f6b1 + BitVec.ofNat 64 8)) 8) (cmpMREffect 0x11f6b1 8 64 14 (.sib 4 none 0 (.d32 0x258))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l11f600, RegMap.args [(3, 55), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l11f6bf, RegMap.args [(3, 55), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l11f6a6 : List UInt8 :=
  [0x49, 0x83, 0xC6, 0x42, 0x48, 0x81, 0xC3, 0x80, 0x07, 0x00, 0x00, 0x4C, 0x39, 0xB4, 0x24, 0x58,
    0x02, 0x00, 0x00, 0x0F, 0x85, 0x41, 0xFF, 0xFF, 0xFF]

theorem code_l11f6a6 : ∀ x ∈ codeRange 0x11f6a6 bytes_l11f6a6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f6a6 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f6bf : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l11d7d0, RegMap.args (entryMap (live .l11f6bf)) 53⟩)

def bytes_l11f6bf : List UInt8 :=
  [0xE9, 0x0C, 0xE1, 0xFF, 0xFF]

theorem code_l11f6bf : ∀ x ∈ codeRange 0x11f6bf bytes_l11f6bf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f6bf 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f6c4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f6c4 (leaR64Effect 0x11f6c4 6 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x11f6c4 (fun s => s.RIP = 0x11f6c4) (leaR64Effect 0x11f6c4 6 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11f6cc (movR32Imm32Effect 0x11f6cc 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x11f6cc (fun s => s.RIP = 0x11f6cc) (movR32Imm32Effect 0x11f6cc 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x11f6d1 (movR64M64Effect 0x11f6d1 0 (.sib 4 none 0 (.d32 0x248))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 58) (.exec 0x11f6d1 (LoadPre 0x11f6d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x248)) s (0x11f6d1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f6d1 0 (.sib 4 none 0 (.d32 0x248))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x11f6d9 (movR64R64Effect 0x11f6d9 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x11f6d9 (fun s => s.RIP = 0x11f6d9) (movR64R64Effect 0x11f6d9 7 0) (Reg.operands [.gpr 0] [])) #v[57]
    (.letOp (n := 61) (.out 0x11f6dc (repMovsqEffect 0x11f6dc) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[53, 59, 55, 22]
    (.letOp (n := 62) (.out 0x11f6dc (repMovsqEffect 0x11f6dc) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[53, 59, 55, 22]
    (.letOp (n := 63) (.out 0x11f6dc (repMovsqEffect 0x11f6dc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[53, 59, 55, 22]
    (.letOp (n := 64) (.exec 0x11f6dc (RepPre 0x11f6dc (RepMovsqPre 0x11f6dc)) (repMovsqEffect 0x11f6dc) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[53, 59, 55, 22]
    (.letOp (n := 65) (.out 0x11f6df (addR64Imm32Effect 0x11f6df 4 0xc88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x11f6df (fun s => s.RIP = 0x11f6df) (addR64Imm32Effect 0x11f6df 4 0xc88) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x11f6e6 (popR64Effect 0x11f6e6 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 68) (.out 0x11f6e6 (popR64Effect 0x11f6e6 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x11f6e6 (PopPre 0x11f6e6) (popR64Effect 0x11f6e6 1 3) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x11f6e7 (popR64Effect 0x11f6e7 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[68]
    (.letOp (n := 71) (.out 0x11f6e7 (popR64Effect 0x11f6e7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x11f6e7 (PopPre 0x11f6e7) (popR64Effect 0x11f6e7 2 12) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x11f6e9 (popR64Effect 0x11f6e9 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 74) (.out 0x11f6e9 (popR64Effect 0x11f6e9 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x11f6e9 (PopPre 0x11f6e9) (popR64Effect 0x11f6e9 2 13) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x11f6eb (popR64Effect 0x11f6eb 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[74]
    (.letOp (n := 77) (.out 0x11f6eb (popR64Effect 0x11f6eb 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x11f6eb (PopPre 0x11f6eb) (popR64Effect 0x11f6eb 2 14) (Reg.operands [.gpr 4] [])) #v[74]
    (.letOp (n := 79) (.out 0x11f6ed (popR64Effect 0x11f6ed 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[77]
    (.letOp (n := 80) (.out 0x11f6ed (popR64Effect 0x11f6ed 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[77]
    (.letOp (n := 81) (.exec 0x11f6ed (PopPre 0x11f6ed) (popR64Effect 0x11f6ed 2 15) (Reg.operands [.gpr 4] [])) #v[77]
    (.letOp (n := 82) (.out 0x11f6ef (popR64Effect 0x11f6ef 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[80]
    (.letOp (n := 83) (.out 0x11f6ef (popR64Effect 0x11f6ef 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[80]
    (.letOp (n := 84) (.exec 0x11f6ef (PopPre 0x11f6ef) (popR64Effect 0x11f6ef 1 5) (Reg.operands [.gpr 4] [])) #v[80]
    (.letOp (n := 85) (.out 0x11f6f0 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[83]
    (.letOp (n := 86) (.out 0x11f6f0 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x11f6f0 (RetPre 0x11f6f0) (retEffect) (Reg.operands [.gpr 4] [])) #v[83]
    (.terminate (.ret (RegMap.args [(0, 57), (1, 63), (2, 2), (3, 67), (4, 86), (5, 82), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (15, 79), (22, 22), (39, 39), (50, 50), (51, 51)] 88) (some ⟨85, by decide⟩)))))))))))))))))))))))))))))))))))))

def bytes_l11f6c4 : List UInt8 :=
  [0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84,
    0x24, 0x48, 0x02, 0x00, 0x00, 0x48, 0x89, 0xC7, 0xF3, 0x48, 0xA5, 0x48, 0x81, 0xC4, 0x88, 0x0C,
    0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l11f6c4 : ∀ x ∈ codeRange 0x11f6c4 bytes_l11f6c4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f6c4 45 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f6f1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f6f1 (movR64M64Effect 0x11f6f1 7 (.sib 4 none 0 (.d32 0xcc0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x11f6f1 (LoadPre 0x11f6f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc0)) s (0x11f6f1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f6f1 7 (.sib 4 none 0 (.d32 0xcc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11f6f9 (movR64R64Effect 0x11f6f9 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x11f6f9 (fun s => s.RIP = 0x11f6f9) (movR64R64Effect 0x11f6f9 6 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x11f6fc (movR64Imm32Effect 0x11f6fc 2 0x2032d0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x11f6fc (fun s => s.RIP = 0x11f6fc) (movR64Imm32Effect 0x11f6fc 2 0x2032d0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x11f703 (callEffect (fun _ => 0x1295f2) 0x11f708) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11f703 (PushPre 0x11f703 5) (callEffect (fun _ => 0x1295f2) 0x11f708) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11f708⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l11f708, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11f6f1 : List UInt8 :=
  [0x48, 0x8B, 0xBC, 0x24, 0xC0, 0x0C, 0x00, 0x00, 0x48, 0x89, 0xFE, 0x48, 0xC7, 0xC2, 0xD0, 0x32,
    0x20, 0x00, 0xE8, 0xEA, 0x9E, 0x00, 0x00]

theorem code_l11f6f1 : ∀ x ∈ codeRange 0x11f6f1 bytes_l11f6f1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f6f1 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f708 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f708 (movR64M64Effect 0x11f708 7 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x11f708 (LoadPre 0x11f708 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x11f708 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f708 7 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11f710 (movR64R64Effect 0x11f710 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x11f710 (fun s => s.RIP = 0x11f710) (movR64R64Effect 0x11f710 6 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x11f713 (movR64Imm32Effect 0x11f713 2 0x2032e8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x11f713 (fun s => s.RIP = 0x11f713) (movR64Imm32Effect 0x11f713 2 0x2032e8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x11f71a (callEffect (fun _ => 0x1295f2) 0x11f71f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11f71a (PushPre 0x11f71a 5) (callEffect (fun _ => 0x1295f2) 0x11f71f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11f71f⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l11f71f, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11f708 : List UInt8 :=
  [0x48, 0x8B, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x89, 0xFE, 0x48, 0xC7, 0xC2, 0xE8, 0x32,
    0x20, 0x00, 0xE8, 0xD3, 0x9E, 0x00, 0x00]

theorem code_l11f708 : ∀ x ∈ codeRange 0x11f708 bytes_l11f708, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f708 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f71f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f71f (movR64M64Effect 0x11f71f 7 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x11f71f (LoadPre 0x11f71f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x11f71f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f71f 7 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11f727 (movR64R64Effect 0x11f727 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x11f727 (fun s => s.RIP = 0x11f727) (movR64R64Effect 0x11f727 6 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x11f72a (movR64Imm32Effect 0x11f72a 2 0x203228) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x11f72a (fun s => s.RIP = 0x11f72a) (movR64Imm32Effect 0x11f72a 2 0x203228) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x11f731 (callEffect (fun _ => 0x1295f2) 0x11f736) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11f731 (PushPre 0x11f731 5) (callEffect (fun _ => 0x1295f2) 0x11f736) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11f736⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l11f736, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11f71f : List UInt8 :=
  [0x48, 0x8B, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x89, 0xFE, 0x48, 0xC7, 0xC2, 0x28, 0x32,
    0x20, 0x00, 0xE8, 0xBC, 0x9E, 0x00, 0x00]

theorem code_l11f71f : ∀ x ∈ codeRange 0x11f71f bytes_l11f71f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f71f 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f736 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f736 (movR64M64Effect 0x11f736 7 (.sib 4 none 0 (.d32 0xcc0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x11f736 (LoadPre 0x11f736 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc0)) s (0x11f736 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f736 7 (.sib 4 none 0 (.d32 0xcc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11f73e (movR64R64Effect 0x11f73e 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x11f73e (fun s => s.RIP = 0x11f73e) (movR64R64Effect 0x11f73e 6 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x11f741 (movR64Imm32Effect 0x11f741 2 0x203240) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x11f741 (fun s => s.RIP = 0x11f741) (movR64Imm32Effect 0x11f741 2 0x203240) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x11f748 (callEffect (fun _ => 0x1295f2) 0x11f74d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11f748 (PushPre 0x11f748 5) (callEffect (fun _ => 0x1295f2) 0x11f74d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11f74d⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l11f74d, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11f736 : List UInt8 :=
  [0x48, 0x8B, 0xBC, 0x24, 0xC0, 0x0C, 0x00, 0x00, 0x48, 0x89, 0xFE, 0x48, 0xC7, 0xC2, 0x40, 0x32,
    0x20, 0x00, 0xE8, 0xA5, 0x9E, 0x00, 0x00]

theorem code_l11f736 : ∀ x ∈ codeRange 0x11f736 bytes_l11f736, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f736 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f74d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f74d (movR64M64Effect 0x11f74d 7 (.sib 4 none 0 (.d32 0xcc0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x11f74d (LoadPre 0x11f74d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc0)) s (0x11f74d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f74d 7 (.sib 4 none 0 (.d32 0xcc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11f755 (movR64R64Effect 0x11f755 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x11f755 (fun s => s.RIP = 0x11f755) (movR64R64Effect 0x11f755 6 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x11f758 (movR64Imm32Effect 0x11f758 2 0x203300) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x11f758 (fun s => s.RIP = 0x11f758) (movR64Imm32Effect 0x11f758 2 0x203300) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x11f75f (callEffect (fun _ => 0x1295f2) 0x11f764) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11f75f (PushPre 0x11f75f 5) (callEffect (fun _ => 0x1295f2) 0x11f764) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11f764⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l11f764, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11f74d : List UInt8 :=
  [0x48, 0x8B, 0xBC, 0x24, 0xC0, 0x0C, 0x00, 0x00, 0x48, 0x89, 0xFE, 0x48, 0xC7, 0xC2, 0x00, 0x33,
    0x20, 0x00, 0xE8, 0x8E, 0x9E, 0x00, 0x00]

theorem code_l11f74d : ∀ x ∈ codeRange 0x11f74d bytes_l11f74d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f74d 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f764 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11f764 (movR64M64Effect 0x11f764 7 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x11f764 (LoadPre 0x11f764 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x11f764 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11f764 7 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11f76c (movR64R64Effect 0x11f76c 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x11f76c (fun s => s.RIP = 0x11f76c) (movR64R64Effect 0x11f76c 6 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x11f76f (movR64Imm32Effect 0x11f76f 2 0x203318) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x11f76f (fun s => s.RIP = 0x11f76f) (movR64Imm32Effect 0x11f76f 2 0x203318) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x11f776 (callEffect (fun _ => 0x1295f2) 0x11f77b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11f776 (PushPre 0x11f776 5) (callEffect (fun _ => 0x1295f2) 0x11f77b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11f77b⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l11f77b, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11f764 : List UInt8 :=
  [0x48, 0x8B, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x89, 0xFE, 0x48, 0xC7, 0xC2, 0x18, 0x33,
    0x20, 0x00, 0xE8, 0x77, 0x9E, 0x00, 0x00]

theorem code_l11f764 : ∀ x ∈ codeRange 0x11f764 bytes_l11f764, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f764 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11f77b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11f77b (fun s => s.RIP = 0x11f77b) (fun _ => nopEffect 0x11f77b 5) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l11f780, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l11f77b : List UInt8 :=
  [0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l11f77b : ∀ x ∈ codeRange 0x11f77b bytes_l11f77b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f77b 5 (by decide +kernel)
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

end K256.Proofs.Verify.LIR
