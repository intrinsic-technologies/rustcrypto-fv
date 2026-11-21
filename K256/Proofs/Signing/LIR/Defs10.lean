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

def b_l110d64_82 : Block Op Label signature Reg.count 3545 :=
  .letOp (n := 3545) (.out 0x112933 (popR64Effect 0x112933 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[3543]
    (.letOp (n := 3546) (.out 0x112933 (popR64Effect 0x112933 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[3543]
    (.letOp (n := 3547) (.exec 0x112933 (PopPre 0x112933) (popR64Effect 0x112933 2 15) (Reg.operands [.gpr 4] [])) #v[3543]
    (.letOp (n := 3548) (.out 0x112935 (popR64Effect 0x112935 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[3546]
    (.letOp (n := 3549) (.out 0x112935 (popR64Effect 0x112935 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[3546]
    (.letOp (n := 3550) (.exec 0x112935 (PopPre 0x112935) (popR64Effect 0x112935 1 5) (Reg.operands [.gpr 4] [])) #v[3546]
    (.letOp (n := 3551) (.out 0x112936 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[3549]
    (.letOp (n := 3552) (.out 0x112936 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[3549]
    (.letOp (n := 3553) (.exec 0x112936 (RetPre 0x112936) (retEffect) (Reg.operands [.gpr 4] [])) #v[3549]
    (.terminate (.ret (RegMap.args [(0, 3508), (1, 3529), (2, 3510), (3, 3533), (4, 3552), (5, 3548), (6, 3527), (7, 3528), (8, 3514), (9, 3456), (10, 3413), (11, 3434), (12, 3536), (13, 3539), (14, 3542), (15, 3545), (22, 22), (39, 39), (50, 50), (51, 51)] 3554) (some ⟨3551, by decide⟩)))))))))))

def bytes_l110d64_82 : List UInt8 :=
  [0x41, 0x5F, 0x5D, 0xC3]

theorem code_l110d64_82 : ∀ x ∈ codeRange 0x112933 bytes_l110d64_82, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12933 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l110d64_81 : Block Op Label signature Reg.count 3504 :=
  .letOp (n := 3504) (.out 0x1128d2 (shrR64Effect 0x1128d2 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3502]
    (.letOp (n := 3505) (.exec 0x1128d2 (fun s => s.RIP = 0x1128d2) (shrR64Effect 0x1128d2 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3502]
    (.letOp (n := 3506) (.out 0x1128d6 (addR64R64Effect 0x1128d6 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[3504, 3474]
    (.letOp (n := 3507) (.exec 0x1128d6 (fun s => s.RIP = 0x1128d6) (addR64R64Effect 0x1128d6 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[3504, 3474]
    (.letOp (n := 3508) (.out 0x1128d9 (andR64R64Effect 0x1128d9 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[3482, 3368]
    (.letOp (n := 3509) (.exec 0x1128d9 (fun s => s.RIP = 0x1128d9) (andR64R64Effect 0x1128d9 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[3482, 3368]
    (.letOp (n := 3510) (.out 0x1128dc (andR64R64Effect 0x1128dc 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[3488, 3368]
    (.letOp (n := 3511) (.exec 0x1128dc (fun s => s.RIP = 0x1128dc) (andR64R64Effect 0x1128dc 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[3488, 3368]
    (.letOp (n := 3512) (.out 0x1128df (andR64R64Effect 0x1128df 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[3494, 3368]
    (.letOp (n := 3513) (.exec 0x1128df (fun s => s.RIP = 0x1128df) (andR64R64Effect 0x1128df 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[3494, 3368]
    (.letOp (n := 3514) (.out 0x1128e2 (andR64R64Effect 0x1128e2 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[3500, 3368]
    (.letOp (n := 3515) (.exec 0x1128e2 (fun s => s.RIP = 0x1128e2) (andR64R64Effect 0x1128e2 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[3500, 3368]
    (.letOp (n := 3516) (.exec 0x1128e5 (StorePre 0x1128e5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1128e5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1128e5 0 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3508, 4]
    (.letOp (n := 3517) (.exec 0x1128ed (StorePre 0x1128ed 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x1128ed + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1128ed 2 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3510, 4]
    (.letOp (n := 3518) (.exec 0x1128f5 (StorePre 0x1128f5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x1128f5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1128f5 7 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[3512, 4]
    (.letOp (n := 3519) (.exec 0x1128fd (StorePre 0x1128fd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x1128fd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1128fd 8 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[3514, 4]
    (.letOp (n := 3520) (.exec 0x112905 (StorePre 0x112905 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x112905 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112905 6 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[3506, 4]
    (.letOp (n := 3521) (.out 0x11290d (movR32Imm32Effect 0x11290d 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 3522) (.exec 0x11290d (fun s => s.RIP = 0x11290d) (movR32Imm32Effect 0x11290d 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 3523) (.out 0x112912 (movR64M64Effect 0x112912 7 (.sib 4 none 0 (.d32 0x1a0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 3524) (.exec 0x112912 (LoadPre 0x112912 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x112912 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112912 7 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3525) (.out 0x11291a (leaR64Effect 0x11291a 6 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 3526) (.exec 0x11291a (fun s => s.RIP = 0x11291a) (leaR64Effect 0x11291a 6 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3527) (.out 0x112922 (repMovsqEffect 0x112922) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[3525, 3523, 3521, 22]
    (.letOp (n := 3528) (.out 0x112922 (repMovsqEffect 0x112922) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[3525, 3523, 3521, 22]
    (.letOp (n := 3529) (.out 0x112922 (repMovsqEffect 0x112922) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[3525, 3523, 3521, 22]
    (.letOp (n := 3530) (.exec 0x112922 (RepPre 0x112922 (RepMovsqPre 0x112922)) (repMovsqEffect 0x112922) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[3525, 3523, 3521, 22]
    (.letOp (n := 3531) (.out 0x112925 (addR64Imm32Effect 0x112925 4 0x1f8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 3532) (.exec 0x112925 (fun s => s.RIP = 0x112925) (addR64Imm32Effect 0x112925 4 0x1f8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3533) (.out 0x11292c (popR64Effect 0x11292c 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[3531]
    (.letOp (n := 3534) (.out 0x11292c (popR64Effect 0x11292c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[3531]
    (.letOp (n := 3535) (.exec 0x11292c (PopPre 0x11292c) (popR64Effect 0x11292c 1 3) (Reg.operands [.gpr 4] [])) #v[3531]
    (.letOp (n := 3536) (.out 0x11292d (popR64Effect 0x11292d 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[3534]
    (.letOp (n := 3537) (.out 0x11292d (popR64Effect 0x11292d 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[3534]
    (.letOp (n := 3538) (.exec 0x11292d (PopPre 0x11292d) (popR64Effect 0x11292d 2 12) (Reg.operands [.gpr 4] [])) #v[3534]
    (.letOp (n := 3539) (.out 0x11292f (popR64Effect 0x11292f 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[3537]
    (.letOp (n := 3540) (.out 0x11292f (popR64Effect 0x11292f 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[3537]
    (.letOp (n := 3541) (.exec 0x11292f (PopPre 0x11292f) (popR64Effect 0x11292f 2 13) (Reg.operands [.gpr 4] [])) #v[3537]
    (.letOp (n := 3542) (.out 0x112931 (popR64Effect 0x112931 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[3540]
    (.letOp (n := 3543) (.out 0x112931 (popR64Effect 0x112931 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[3540]
    (.letOp (n := 3544) (.exec 0x112931 (PopPre 0x112931) (popR64Effect 0x112931 2 14) (Reg.operands [.gpr 4] [])) #v[3540]
    (b_l110d64_82)))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_81 : List UInt8 :=
  [0x48, 0xC1, 0xEE, 0x34, 0x48, 0x01, 0xCE, 0x4C, 0x21, 0xE0, 0x4C, 0x21, 0xE2, 0x4C, 0x21, 0xE7,
    0x4D, 0x21, 0xE0, 0x48, 0x89, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0x58,
    0x01, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24, 0x60, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0x68,
    0x01, 0x00, 0x00, 0x48, 0x89, 0xB4, 0x24, 0x70, 0x01, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0xBC, 0x24, 0xA0, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00,
    0xF3, 0x48, 0xA5, 0x48, 0x81, 0xC4, 0xF8, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E] ++ bytes_l110d64_82

theorem code_l110d64_81 : ∀ x ∈ codeRange 0x1128d2 bytes_l110d64_81, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x128d2 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_82

def b_l110d64_80 : Block Op Label signature Reg.count 3464 :=
  .letOp (n := 3464) (.out 0x112884 (subR64R64Effect 0x112884 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[3462, 3460]
    (.letOp (n := 3465) (.exec 0x112884 (fun s => s.RIP = 0x112884) (subR64R64Effect 0x112884 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3462, 3460]
    (.letOp (n := 3466) (.out 0x112887 (movR64M64Effect 0x112887 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3467) (.exec 0x112887 (LoadPre 0x112887 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x112887 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112887 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3468) (.out 0x11288f (leaR64Effect 0x11288f 1 (.sib 7 (some 0) 3 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7, .gpr 0] []) (.reg (.gpr 1))) #v[3438, 3466]
    (.letOp (n := 3469) (.exec 0x11288f (fun s => s.RIP = 0x11288f) (leaR64Effect 0x11288f 1 (.sib 7 (some 0) 3 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[3438, 3466]
    (.letOp (n := 3470) (.out 0x112893 (subR64R64Effect 0x112893 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[3468, 3466]
    (.letOp (n := 3471) (.exec 0x112893 (fun s => s.RIP = 0x112893) (subR64R64Effect 0x112893 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3468, 3466]
    (.letOp (n := 3472) (.out 0x112896 (movR64R64Effect 0x112896 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[3470]
    (.letOp (n := 3473) (.exec 0x112896 (fun s => s.RIP = 0x112896) (movR64R64Effect 0x112896 0 1) (Reg.operands [.gpr 1] [])) #v[3470]
    (.letOp (n := 3474) (.out 0x112899 (andR64R64Effect 0x112899 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[3470, 3434]
    (.letOp (n := 3475) (.exec 0x112899 (fun s => s.RIP = 0x112899) (andR64R64Effect 0x112899 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[3470, 3434]
    (.letOp (n := 3476) (.out 0x11289c (shrR64Effect 0x11289c 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3472]
    (.letOp (n := 3477) (.exec 0x11289c (fun s => s.RIP = 0x11289c) (shrR64Effect 0x11289c 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3472]
    (.letOp (n := 3478) (.out 0x1128a0 (movR64Imm64Effect 0x1128a0 7 0x1000003d1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 3479) (.exec 0x1128a0 (fun s => s.RIP = 0x1128a0) (movR64Imm64Effect 0x1128a0 7 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 3480) (.out 0x1128aa (imulR64R64Effect 0x1128aa 4 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[3476, 3478]
    (.letOp (n := 3481) (.exec 0x1128aa (fun s => s.RIP = 0x1128aa) (imulR64R64Effect 0x1128aa 4 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[3476, 3478]
    (.letOp (n := 3482) (.out 0x1128ae (addR64R64Effect 0x1128ae 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3480, 3444]
    (.letOp (n := 3483) (.exec 0x1128ae (fun s => s.RIP = 0x1128ae) (addR64R64Effect 0x1128ae 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3480, 3444]
    (.letOp (n := 3484) (.out 0x1128b1 (movR64R64Effect 0x1128b1 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[3482]
    (.letOp (n := 3485) (.exec 0x1128b1 (fun s => s.RIP = 0x1128b1) (movR64R64Effect 0x1128b1 2 0) (Reg.operands [.gpr 0] [])) #v[3482]
    (.letOp (n := 3486) (.out 0x1128b4 (shrR64Effect 0x1128b4 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3484]
    (.letOp (n := 3487) (.exec 0x1128b4 (fun s => s.RIP = 0x1128b4) (shrR64Effect 0x1128b4 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3484]
    (.letOp (n := 3488) (.out 0x1128b8 (addR64R64Effect 0x1128b8 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[3486, 3450]
    (.letOp (n := 3489) (.exec 0x1128b8 (fun s => s.RIP = 0x1128b8) (addR64R64Effect 0x1128b8 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[3486, 3450]
    (.letOp (n := 3490) (.out 0x1128bb (movR64R64Effect 0x1128bb 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[3488]
    (.letOp (n := 3491) (.exec 0x1128bb (fun s => s.RIP = 0x1128bb) (movR64R64Effect 0x1128bb 7 2) (Reg.operands [.gpr 2] [])) #v[3488]
    (.letOp (n := 3492) (.out 0x1128be (shrR64Effect 0x1128be 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3490]
    (.letOp (n := 3493) (.exec 0x1128be (fun s => s.RIP = 0x1128be) (shrR64Effect 0x1128be 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3490]
    (.letOp (n := 3494) (.out 0x1128c2 (addR64R64Effect 0x1128c2 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[3492, 3456]
    (.letOp (n := 3495) (.exec 0x1128c2 (fun s => s.RIP = 0x1128c2) (addR64R64Effect 0x1128c2 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[3492, 3456]
    (.letOp (n := 3496) (.out 0x1128c5 (movR64R64Effect 0x1128c5 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[3494]
    (.letOp (n := 3497) (.exec 0x1128c5 (fun s => s.RIP = 0x1128c5) (movR64R64Effect 0x1128c5 8 7) (Reg.operands [.gpr 7] [])) #v[3494]
    (.letOp (n := 3498) (.out 0x1128c8 (shrR64Effect 0x1128c8 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[3496]
    (.letOp (n := 3499) (.exec 0x1128c8 (fun s => s.RIP = 0x1128c8) (shrR64Effect 0x1128c8 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3496]
    (.letOp (n := 3500) (.out 0x1128cc (addR64R64Effect 0x1128cc 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[3498, 3464]
    (.letOp (n := 3501) (.exec 0x1128cc (fun s => s.RIP = 0x1128cc) (addR64R64Effect 0x1128cc 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[3498, 3464]
    (.letOp (n := 3502) (.out 0x1128cf (movR64R64Effect 0x1128cf 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[3500]
    (.letOp (n := 3503) (.exec 0x1128cf (fun s => s.RIP = 0x1128cf) (movR64R64Effect 0x1128cf 6 8) (Reg.operands [.gpr 8] [])) #v[3500]
    (b_l110d64_81))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_80 : List UInt8 :=
  [0x48, 0x29, 0xC6, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x0C, 0xC7, 0x48,
    0x29, 0xC1, 0x48, 0x89, 0xC8, 0x4C, 0x21, 0xD9, 0x48, 0xC1, 0xE8, 0x30, 0x48, 0xBF, 0xD1, 0x03,
    0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xC7, 0x48, 0x01, 0xD0, 0x48, 0x89, 0xC2,
    0x48, 0xC1, 0xEA, 0x34, 0x4C, 0x01, 0xC2, 0x48, 0x89, 0xD7, 0x48, 0xC1, 0xEF, 0x34, 0x4C, 0x01,
    0xCF, 0x49, 0x89, 0xF8, 0x49, 0xC1, 0xE8, 0x34, 0x49, 0x01, 0xF0, 0x4C, 0x89, 0xC6] ++ bytes_l110d64_81

theorem code_l110d64_80 : ∀ x ∈ codeRange 0x112884 bytes_l110d64_80, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12884 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_81

def b_l110d64_79 : Block Op Label signature Reg.count 3424 :=
  .letOp (n := 3424) (.out 0x112822 (addR64R64Effect 0x112822 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[3419, 3403]
    (.letOp (n := 3425) (.out 0x112822 (addR64R64Effect 0x112822 6 3) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 3] []) (.flag .CF)) #v[3419, 3403]
    (.letOp (n := 3426) (.exec 0x112822 (fun s => s.RIP = 0x112822) (addR64R64Effect 0x112822 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[3419, 3403]
    (.letOp (n := 3427) (.out 0x112825 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112825 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[3422, 3425]
    (.letOp (n := 3428) (.exec 0x112825 (fun s => s.RIP = 0x112825) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112825 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3422, 3425]
    (.letOp (n := 3429) (.out 0x112829 (shldR64R64Effect 0x112829 5 2 6 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3427, 3424]
    (.letOp (n := 3430) (.exec 0x112829 (fun s => s.RIP = 0x112829) (shldR64R64Effect 0x112829 5 2 6 12) (Reg.operands [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3427, 3424]
    (.letOp (n := 3431) (.out 0x11282e (movR64M64Effect 0x11282e 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3432) (.exec 0x11282e (LoadPre 0x11282e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11282e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11282e 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3433) (.exec 0x112833 (StorePre 0x112833 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x112833 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112833 0 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3431, 4]
    (.letOp (n := 3434) (.out 0x11283b (movR64Imm64Effect 0x11283b 11 0xffffffffffff) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 3435) (.exec 0x11283b (fun s => s.RIP = 0x11283b) (movR64Imm64Effect 0x11283b 11 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 3436) (.out 0x112845 (andR64R64Effect 0x112845 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[3108, 3434]
    (.letOp (n := 3437) (.exec 0x112845 (fun s => s.RIP = 0x112845) (andR64R64Effect 0x112845 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[3108, 3434]
    (.letOp (n := 3438) (.out 0x112848 (addR64R64Effect 0x112848 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[3436, 3429]
    (.letOp (n := 3439) (.exec 0x112848 (fun s => s.RIP = 0x112848) (addR64R64Effect 0x112848 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[3436, 3429]
    (.letOp (n := 3440) (.out 0x11284b (movR64M64Effect 0x11284b 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3441) (.exec 0x11284b (LoadPre 0x11284b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11284b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11284b 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3442) (.out 0x112853 (leaR64Effect 0x112853 2 (.sib 8 (some 0) 3 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[3243, 3440]
    (.letOp (n := 3443) (.exec 0x112853 (fun s => s.RIP = 0x112853) (leaR64Effect 0x112853 2 (.sib 8 (some 0) 3 .none)) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3243, 3440]
    (.letOp (n := 3444) (.out 0x112857 (subR64R64Effect 0x112857 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3442, 3440]
    (.letOp (n := 3445) (.exec 0x112857 (fun s => s.RIP = 0x112857) (subR64R64Effect 0x112857 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3442, 3440]
    (.letOp (n := 3446) (.out 0x11285a (movR64M64Effect 0x11285a 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3447) (.exec 0x11285a (LoadPre 0x11285a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11285a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11285a 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3448) (.out 0x112862 (leaR64Effect 0x112862 8 (.sib 1 (some 0) 3 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1, .gpr 0] []) (.reg (.gpr 8))) #v[3334, 3446]
    (.letOp (n := 3449) (.exec 0x112862 (fun s => s.RIP = 0x112862) (leaR64Effect 0x112862 8 (.sib 1 (some 0) 3 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3334, 3446]
    (.letOp (n := 3450) (.out 0x112866 (subR64R64Effect 0x112866 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[3448, 3446]
    (.letOp (n := 3451) (.exec 0x112866 (fun s => s.RIP = 0x112866) (subR64R64Effect 0x112866 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3448, 3446]
    (.letOp (n := 3452) (.out 0x112869 (movR64M64Effect 0x112869 0 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3453) (.exec 0x112869 (LoadPre 0x112869 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x112869 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112869 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3454) (.out 0x112871 (leaR64Effect 0x112871 9 (.sib 10 (some 0) 3 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10, .gpr 0] []) (.reg (.gpr 9))) #v[3413, 3452]
    (.letOp (n := 3455) (.exec 0x112871 (fun s => s.RIP = 0x112871) (leaR64Effect 0x112871 9 (.sib 10 (some 0) 3 .none)) (Reg.operands [.gpr 10, .gpr 0] [])) #v[3413, 3452]
    (.letOp (n := 3456) (.out 0x112875 (subR64R64Effect 0x112875 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[3454, 3452]
    (.letOp (n := 3457) (.exec 0x112875 (fun s => s.RIP = 0x112875) (subR64R64Effect 0x112875 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[3454, 3452]
    (.letOp (n := 3458) (.out 0x112878 (andR64R64Effect 0x112878 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[3424, 3368]
    (.letOp (n := 3459) (.exec 0x112878 (fun s => s.RIP = 0x112878) (andR64R64Effect 0x112878 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[3424, 3368]
    (.letOp (n := 3460) (.out 0x11287b (movR64M64Effect 0x11287b 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3461) (.exec 0x11287b (LoadPre 0x11287b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11287b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11287b 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3462) (.out 0x112880 (leaR64Effect 0x112880 6 (.sib 6 (some 0) 3 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[3458, 3460]
    (.letOp (n := 3463) (.exec 0x112880 (fun s => s.RIP = 0x112880) (leaR64Effect 0x112880 6 (.sib 6 (some 0) 3 .none)) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3458, 3460]
    (b_l110d64_80))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_79 : List UInt8 :=
  [0x48, 0x01, 0xDE, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x0F, 0xA4, 0xF2, 0x0C, 0x48, 0x8B, 0x44, 0x24,
    0x28, 0x48, 0x89, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00, 0x49, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x00, 0x00, 0x4C, 0x21, 0xDF, 0x48, 0x01, 0xD7, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00,
    0x00, 0x49, 0x8D, 0x14, 0xC0, 0x48, 0x29, 0xC2, 0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00,
    0x4C, 0x8D, 0x04, 0xC1, 0x49, 0x29, 0xC0, 0x48, 0x8B, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x4D,
    0x8D, 0x0C, 0xC2, 0x49, 0x29, 0xC1, 0x4C, 0x21, 0xE6, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x8D,
    0x34, 0xC6] ++ bytes_l110d64_80

theorem code_l110d64_79 : ∀ x ∈ codeRange 0x112822 bytes_l110d64_79, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12822 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_80

def b_l110d64_78 : Block Op Label signature Reg.count 3381 :=
  .letOp (n := 3381) (.out 0x1127ce (atFlags StatusFlags.CF (adcR64M64Effect 0x1127ce 3 (.sib 4 none 0 (.d8 0x68)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[3321, 4, 3379]
    (.letOp (n := 3382) (.exec 0x1127ce (LoadPre 0x1127ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1127ce + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1127ce 3 (.sib 4 none 0 (.d8 0x68)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3321, 4, 3379]
    (.letOp (n := 3383) (.out 0x1127d3 (addR64R64Effect 0x1127d3 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15] []) (.reg (.gpr 10))) #v[3378, 3330]
    (.letOp (n := 3384) (.out 0x1127d3 (addR64R64Effect 0x1127d3 10 15) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 15] []) (.flag .CF)) #v[3378, 3330]
    (.letOp (n := 3385) (.exec 0x1127d3 (fun s => s.RIP = 0x1127d3) (addR64R64Effect 0x1127d3 10 15) (Reg.operands [.gpr 10, .gpr 15] [])) #v[3378, 3330]
    (.letOp (n := 3386) (.out 0x1127d6 (atFlags StatusFlags.CF (adcR64R64Effect 0x1127d6 3 13)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[3381, 3332, 3384]
    (.letOp (n := 3387) (.exec 0x1127d6 (fun s => s.RIP = 0x1127d6) (atFlags StatusFlags.CF (adcR64R64Effect 0x1127d6 3 13)) (Reg.operands [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3381, 3332, 3384]
    (.letOp (n := 3388) (.out 0x1127d9 (addR64R64Effect 0x1127d9 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[3383, 3372]
    (.letOp (n := 3389) (.out 0x1127d9 (addR64R64Effect 0x1127d9 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[3383, 3372]
    (.letOp (n := 3390) (.exec 0x1127d9 (fun s => s.RIP = 0x1127d9) (addR64R64Effect 0x1127d9 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[3383, 3372]
    (.letOp (n := 3391) (.out 0x1127dc (atFlags StatusFlags.CF (adcR64R64Effect 0x1127dc 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[3386, 3373, 3389]
    (.letOp (n := 3392) (.exec 0x1127dc (fun s => s.RIP = 0x1127dc) (atFlags StatusFlags.CF (adcR64R64Effect 0x1127dc 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3386, 3373, 3389]
    (.letOp (n := 3393) (.out 0x1127df (movR64M64Effect 0x1127df 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3394) (.exec 0x1127df (LoadPre 0x1127df (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1127df + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1127df 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3395) (.exec 0x1127e4 (StorePre 0x1127e4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x1127e4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1127e4 0 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3393, 4]
    (.letOp (n := 3396) (.out 0x1127ec (addR64R64Effect 0x1127ec 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[3388, 3307]
    (.letOp (n := 3397) (.out 0x1127ec (addR64R64Effect 0x1127ec 10 9) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 9] []) (.flag .CF)) #v[3388, 3307]
    (.letOp (n := 3398) (.exec 0x1127ec (fun s => s.RIP = 0x1127ec) (addR64R64Effect 0x1127ec 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[3388, 3307]
    (.letOp (n := 3399) (.out 0x1127ef (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1127ef 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[3391, 3397]
    (.letOp (n := 3400) (.exec 0x1127ef (fun s => s.RIP = 0x1127ef) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1127ef 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3391, 3397]
    (.letOp (n := 3401) (.out 0x1127f3 (shldR64R64Effect 0x1127f3 5 14 5 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[3362, 3359]
    (.letOp (n := 3402) (.exec 0x1127f3 (fun s => s.RIP = 0x1127f3) (shldR64R64Effect 0x1127f3 5 14 5 12) (Reg.operands [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3362, 3359]
    (.letOp (n := 3403) (.out 0x1127f8 (shldR64R64Effect 0x1127f8 5 3 10 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[3399, 3396]
    (.letOp (n := 3404) (.exec 0x1127f8 (fun s => s.RIP = 0x1127f8) (shldR64R64Effect 0x1127f8 5 3 10 12) (Reg.operands [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3399, 3396]
    (.letOp (n := 3405) (.out 0x1127fd (movR64M64Effect 0x1127fd 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3406) (.exec 0x1127fd (LoadPre 0x1127fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1127fd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1127fd 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3407) (.exec 0x112802 (StorePre 0x112802 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x112802 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112802 0 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3405, 4]
    (.letOp (n := 3408) (.out 0x11280a (movR64R64Effect 0x11280a 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[3401]
    (.letOp (n := 3409) (.exec 0x11280a (fun s => s.RIP = 0x11280a) (movR64R64Effect 0x11280a 0 14) (Reg.operands [.gpr 14] [])) #v[3401]
    (.letOp (n := 3410) (.out 0x11280d (mulR64Effect 0x11280d 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[3370, 3408]
    (.letOp (n := 3411) (.out 0x11280d (mulR64Effect 0x11280d 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[3370, 3408]
    (.letOp (n := 3412) (.exec 0x11280d (fun s => s.RIP = 0x11280d) (mulR64Effect 0x11280d 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3370, 3408]
    (.letOp (n := 3413) (.out 0x112810 (andR64R64Effect 0x112810 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[3396, 3368]
    (.letOp (n := 3414) (.exec 0x112810 (fun s => s.RIP = 0x112810) (andR64R64Effect 0x112810 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[3396, 3368]
    (.letOp (n := 3415) (.out 0x112813 (movR64M64Effect 0x112813 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 3416) (.exec 0x112813 (LoadPre 0x112813 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x112813 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112813 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3417) (.out 0x112818 (andR64R64Effect 0x112818 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[3415, 3368]
    (.letOp (n := 3418) (.exec 0x112818 (fun s => s.RIP = 0x112818) (andR64R64Effect 0x112818 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[3415, 3368]
    (.letOp (n := 3419) (.out 0x11281b (addR64R64Effect 0x11281b 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[3417, 3410]
    (.letOp (n := 3420) (.out 0x11281b (addR64R64Effect 0x11281b 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[3417, 3410]
    (.letOp (n := 3421) (.exec 0x11281b (fun s => s.RIP = 0x11281b) (addR64R64Effect 0x11281b 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3417, 3410]
    (.letOp (n := 3422) (.out 0x11281e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11281e 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[3411, 3420]
    (.letOp (n := 3423) (.exec 0x11281e (fun s => s.RIP = 0x11281e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11281e 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3411, 3420]
    (b_l110d64_79)))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_78 : List UInt8 :=
  [0x48, 0x13, 0x5C, 0x24, 0x68, 0x4D, 0x01, 0xFA, 0x4C, 0x11, 0xEB, 0x49, 0x01, 0xC2, 0x48, 0x11,
    0xD3, 0x48, 0x8B, 0x44, 0x24, 0x78, 0x48, 0x89, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00, 0x4D, 0x01,
    0xCA, 0x48, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xEE, 0x0C, 0x4C, 0x0F, 0xA4, 0xD3, 0x0C, 0x48,
    0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF0, 0x48,
    0xF7, 0xE6, 0x4D, 0x21, 0xE2, 0x48, 0x8B, 0x74, 0x24, 0x60, 0x4C, 0x21, 0xE6, 0x48, 0x01, 0xC6,
    0x48, 0x83, 0xD2, 0x00] ++ bytes_l110d64_79

theorem code_l110d64_78 : ∀ x ∈ codeRange 0x1127ce bytes_l110d64_78, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x127ce 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_79

def b_l110d64_77 : Block Op Label signature Reg.count 3336 :=
  .letOp (n := 3336) (.out 0x112775 (movR64R64Effect 0x112775 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[3280]
    (.letOp (n := 3337) (.exec 0x112775 (fun s => s.RIP = 0x112775) (movR64R64Effect 0x112775 6 12) (Reg.operands [.gpr 12] [])) #v[3280]
    (.letOp (n := 3338) (.out 0x112778 (movR64R64Effect 0x112778 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[3245]
    (.letOp (n := 3339) (.exec 0x112778 (fun s => s.RIP = 0x112778) (movR64R64Effect 0x112778 0 14) (Reg.operands [.gpr 14] [])) #v[3245]
    (.letOp (n := 3340) (.out 0x11277b (mulM64Effect 0x11277b 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3338, 4]
    (.letOp (n := 3341) (.out 0x11277b (mulM64Effect 0x11277b 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3338, 4]
    (.letOp (n := 3342) (.exec 0x11277b (LoadPre 0x11277b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11277b + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11277b 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3338, 4]
    (.letOp (n := 3343) (.out 0x112783 (movR64R64Effect 0x112783 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[3341]
    (.letOp (n := 3344) (.exec 0x112783 (fun s => s.RIP = 0x112783) (movR64R64Effect 0x112783 14 2) (Reg.operands [.gpr 2] [])) #v[3341]
    (.letOp (n := 3345) (.out 0x112786 (movR64R64Effect 0x112786 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[3340]
    (.letOp (n := 3346) (.exec 0x112786 (fun s => s.RIP = 0x112786) (movR64R64Effect 0x112786 12 0) (Reg.operands [.gpr 0] [])) #v[3340]
    (.letOp (n := 3347) (.out 0x112789 (movR64M64Effect 0x112789 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3348) (.exec 0x112789 (LoadPre 0x112789 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x112789 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112789 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3349) (.out 0x11278e (mulM64Effect 0x11278e 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3347, 4]
    (.letOp (n := 3350) (.out 0x11278e (mulM64Effect 0x11278e 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3347, 4]
    (.letOp (n := 3351) (.exec 0x11278e (LoadPre 0x11278e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11278e + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11278e 8 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3347, 4]
    (.letOp (n := 3352) (.out 0x112796 (movR64R64Effect 0x112796 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[3349]
    (.letOp (n := 3353) (.exec 0x112796 (fun s => s.RIP = 0x112796) (movR64R64Effect 0x112796 5 0) (Reg.operands [.gpr 0] [])) #v[3349]
    (.letOp (n := 3354) (.out 0x112799 (addR64R64Effect 0x112799 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[3352, 3345]
    (.letOp (n := 3355) (.out 0x112799 (addR64R64Effect 0x112799 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[3352, 3345]
    (.letOp (n := 3356) (.exec 0x112799 (fun s => s.RIP = 0x112799) (addR64R64Effect 0x112799 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[3352, 3345]
    (.letOp (n := 3357) (.out 0x11279c (atFlags StatusFlags.CF (adcR64R64Effect 0x11279c 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[3343, 3350, 3355]
    (.letOp (n := 3358) (.exec 0x11279c (fun s => s.RIP = 0x11279c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11279c 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3343, 3350, 3355]
    (.letOp (n := 3359) (.out 0x11279f (addR64R64Effect 0x11279f 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[3354, 3278]
    (.letOp (n := 3360) (.out 0x11279f (addR64R64Effect 0x11279f 5 11) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 11] []) (.flag .CF)) #v[3354, 3278]
    (.letOp (n := 3361) (.exec 0x11279f (fun s => s.RIP = 0x11279f) (addR64R64Effect 0x11279f 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[3354, 3278]
    (.letOp (n := 3362) (.out 0x1127a2 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1127a2 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[3357, 3360]
    (.letOp (n := 3363) (.exec 0x1127a2 (fun s => s.RIP = 0x1127a2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1127a2 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3357, 3360]
    (.letOp (n := 3364) (.out 0x1127a6 (movR64R64Effect 0x1127a6 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[3359]
    (.letOp (n := 3365) (.exec 0x1127a6 (fun s => s.RIP = 0x1127a6) (movR64R64Effect 0x1127a6 0 5) (Reg.operands [.gpr 5] [])) #v[3359]
    (.letOp (n := 3366) (.out 0x1127a9 (andR64R64Effect 0x1127a9 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[3364, 3336]
    (.letOp (n := 3367) (.exec 0x1127a9 (fun s => s.RIP = 0x1127a9) (andR64R64Effect 0x1127a9 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[3364, 3336]
    (.letOp (n := 3368) (.out 0x1127ac (movR64R64Effect 0x1127ac 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[3336]
    (.letOp (n := 3369) (.exec 0x1127ac (fun s => s.RIP = 0x1127ac) (movR64R64Effect 0x1127ac 12 6) (Reg.operands [.gpr 6] [])) #v[3336]
    (.letOp (n := 3370) (.out 0x1127af (movR64Imm64Effect 0x1127af 6 0x1000003d10) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 3371) (.exec 0x1127af (fun s => s.RIP = 0x1127af) (movR64Imm64Effect 0x1127af 6 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 3372) (.out 0x1127b9 (mulR64Effect 0x1127b9 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[3370, 3366]
    (.letOp (n := 3373) (.out 0x1127b9 (mulR64Effect 0x1127b9 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[3370, 3366]
    (.letOp (n := 3374) (.exec 0x1127b9 (fun s => s.RIP = 0x1127b9) (mulR64Effect 0x1127b9 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3370, 3366]
    (.letOp (n := 3375) (.out 0x1127bc (movR64M64Effect 0x1127bc 11 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 3376) (.exec 0x1127bc (LoadPre 0x1127bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1127bc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1127bc 11 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3377) (.exec 0x1127c1 (StorePre 0x1127c1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x1127c1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1127c1 11 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[3375, 4]
    (.letOp (n := 3378) (.out 0x1127c9 (addR64M64Effect 0x1127c9 10 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[3323, 4]
    (.letOp (n := 3379) (.out 0x1127c9 (addR64M64Effect 0x1127c9 10 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[3323, 4]
    (.letOp (n := 3380) (.exec 0x1127c9 (LoadPre 0x1127c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1127c9 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1127c9 10 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[3323, 4]
    (b_l110d64_78)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_77 : List UInt8 :=
  [0x4C, 0x89, 0xE6, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xA4, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x49, 0x89,
    0xD6, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0xF7, 0xA4, 0x24, 0xD8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xC5, 0x4C, 0x01, 0xE5, 0x49, 0x11, 0xD6, 0x4C, 0x01, 0xDD, 0x49, 0x83, 0xD6,
    0x00, 0x48, 0x89, 0xE8, 0x48, 0x21, 0xF0, 0x49, 0x89, 0xF4, 0x48, 0xBE, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE6, 0x4C, 0x8B, 0x5C, 0x24, 0x70, 0x4C, 0x89, 0x9C, 0x24,
    0x80, 0x01, 0x00, 0x00, 0x4C, 0x03, 0x54, 0x24, 0x40] ++ bytes_l110d64_78

theorem code_l110d64_77 : ∀ x ∈ codeRange 0x112775 bytes_l110d64_77, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12775 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_78

def b_l110d64_76 : Block Op Label signature Reg.count 3294 :=
  .letOp (n := 3294) (.out 0x11271a (addR64R64Effect 0x11271a 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[3289, 3286]
    (.letOp (n := 3295) (.out 0x11271a (addR64R64Effect 0x11271a 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[3289, 3286]
    (.letOp (n := 3296) (.exec 0x11271a (fun s => s.RIP = 0x11271a) (addR64R64Effect 0x11271a 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3289, 3286]
    (.letOp (n := 3297) (.out 0x11271d (atFlags StatusFlags.CF (adcR64R64Effect 0x11271d 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[3292, 3287, 3295]
    (.letOp (n := 3298) (.exec 0x11271d (fun s => s.RIP = 0x11271d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11271d 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3292, 3287, 3295]
    (.letOp (n := 3299) (.out 0x112720 (addR64R64Effect 0x112720 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[3294, 3212]
    (.letOp (n := 3300) (.out 0x112720 (addR64R64Effect 0x112720 1 3) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 3] []) (.flag .CF)) #v[3294, 3212]
    (.letOp (n := 3301) (.exec 0x112720 (fun s => s.RIP = 0x112720) (addR64R64Effect 0x112720 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[3294, 3212]
    (.letOp (n := 3302) (.out 0x112723 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112723 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[3297, 3300]
    (.letOp (n := 3303) (.exec 0x112723 (fun s => s.RIP = 0x112723) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112723 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3297, 3300]
    (.letOp (n := 3304) (.out 0x112727 (movR64M64Effect 0x112727 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3305) (.exec 0x112727 (LoadPre 0x112727 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x112727 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112727 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3306) (.exec 0x11272c (StorePre 0x11272c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x11272c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11272c 0 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3304, 4]
    (.letOp (n := 3307) (.out 0x112734 (shldR64R64Effect 0x112734 5 9 1 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[3302, 3299]
    (.letOp (n := 3308) (.exec 0x112734 (fun s => s.RIP = 0x112734) (shldR64R64Effect 0x112734 5 9 1 12) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3302, 3299]
    (.letOp (n := 3309) (.out 0x112739 (movR64M64Effect 0x112739 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3310) (.exec 0x112739 (LoadPre 0x112739 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x112739 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112739 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3311) (.out 0x11273e (mulR64Effect 0x11273e 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[3258, 3309]
    (.letOp (n := 3312) (.out 0x11273e (mulR64Effect 0x11273e 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[3258, 3309]
    (.letOp (n := 3313) (.exec 0x11273e (fun s => s.RIP = 0x11273e) (mulR64Effect 0x11273e 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3258, 3309]
    (.letOp (n := 3314) (.exec 0x112741 (StorePre 0x112741 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x112741 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112741 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3312, 4]
    (.letOp (n := 3315) (.exec 0x112746 (StorePre 0x112746 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x112746 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112746 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3311, 4]
    (.letOp (n := 3316) (.out 0x11274b (movR64M64Effect 0x11274b 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3317) (.exec 0x11274b (LoadPre 0x11274b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11274b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11274b 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3318) (.out 0x112753 (mulM64Effect 0x112753 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3316, 4]
    (.letOp (n := 3319) (.out 0x112753 (mulM64Effect 0x112753 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3316, 4]
    (.letOp (n := 3320) (.exec 0x112753 (LoadPre 0x112753 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x112753 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x112753 8 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3316, 4]
    (.letOp (n := 3321) (.out 0x11275b (movR64R64Effect 0x11275b 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[3319]
    (.letOp (n := 3322) (.exec 0x11275b (fun s => s.RIP = 0x11275b) (movR64R64Effect 0x11275b 3 2) (Reg.operands [.gpr 2] [])) #v[3319]
    (.letOp (n := 3323) (.out 0x11275e (movR64R64Effect 0x11275e 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[3318]
    (.letOp (n := 3324) (.exec 0x11275e (fun s => s.RIP = 0x11275e) (movR64R64Effect 0x11275e 10 0) (Reg.operands [.gpr 0] [])) #v[3318]
    (.letOp (n := 3325) (.out 0x112761 (movR64R64Effect 0x112761 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[3230]
    (.letOp (n := 3326) (.exec 0x112761 (fun s => s.RIP = 0x112761) (movR64R64Effect 0x112761 0 15) (Reg.operands [.gpr 15] [])) #v[3230]
    (.letOp (n := 3327) (.out 0x112764 (mulM64Effect 0x112764 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3325, 4]
    (.letOp (n := 3328) (.out 0x112764 (mulM64Effect 0x112764 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3325, 4]
    (.letOp (n := 3329) (.exec 0x112764 (LoadPre 0x112764 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x112764 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x112764 8 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3325, 4]
    (.letOp (n := 3330) (.out 0x11276c (movR64R64Effect 0x11276c 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[3327]
    (.letOp (n := 3331) (.exec 0x11276c (fun s => s.RIP = 0x11276c) (movR64R64Effect 0x11276c 15 0) (Reg.operands [.gpr 0] [])) #v[3327]
    (.letOp (n := 3332) (.out 0x11276f (movR64R64Effect 0x11276f 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[3328]
    (.letOp (n := 3333) (.exec 0x11276f (fun s => s.RIP = 0x11276f) (movR64R64Effect 0x11276f 13 2) (Reg.operands [.gpr 2] [])) #v[3328]
    (.letOp (n := 3334) (.out 0x112772 (andR64R64Effect 0x112772 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[3299, 3280]
    (.letOp (n := 3335) (.exec 0x112772 (fun s => s.RIP = 0x112772) (andR64R64Effect 0x112772 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[3299, 3280]
    (b_l110d64_77))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_76 : List UInt8 :=
  [0x48, 0x01, 0xC1, 0x49, 0x11, 0xD1, 0x48, 0x01, 0xD9, 0x49, 0x83, 0xD1, 0x00, 0x48, 0x8B, 0x44,
    0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x78, 0x01, 0x00, 0x00, 0x49, 0x0F, 0xA4, 0xC9, 0x0C, 0x48,
    0x8B, 0x44, 0x24, 0x68, 0x48, 0xF7, 0xE6, 0x48, 0x89, 0x54, 0x24, 0x68, 0x48, 0x89, 0x44, 0x24,
    0x40, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0x18, 0x01, 0x00,
    0x00, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC2, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0xA4, 0x24, 0x20, 0x01,
    0x00, 0x00, 0x49, 0x89, 0xC7, 0x49, 0x89, 0xD5, 0x4C, 0x21, 0xE1] ++ bytes_l110d64_77

theorem code_l110d64_76 : ∀ x ∈ codeRange 0x11271a bytes_l110d64_76, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1271a 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_77

def b_l110d64_75 : Block Op Label signature Reg.count 3247 :=
  .letOp (n := 3247) (.out 0x1126bd (movR64R64Effect 0x1126bd 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[3245]
    (.letOp (n := 3248) (.exec 0x1126bd (fun s => s.RIP = 0x1126bd) (movR64R64Effect 0x1126bd 0 14) (Reg.operands [.gpr 14] [])) #v[3245]
    (.letOp (n := 3249) (.out 0x1126c0 (mulM64Effect 0x1126c0 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3247, 4]
    (.letOp (n := 3250) (.out 0x1126c0 (mulM64Effect 0x1126c0 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3247, 4]
    (.letOp (n := 3251) (.exec 0x1126c0 (LoadPre 0x1126c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1126c0 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1126c0 8 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3247, 4]
    (.letOp (n := 3252) (.out 0x1126c8 (movR64R64Effect 0x1126c8 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[3250]
    (.letOp (n := 3253) (.exec 0x1126c8 (fun s => s.RIP = 0x1126c8) (movR64R64Effect 0x1126c8 11 2) (Reg.operands [.gpr 2] [])) #v[3250]
    (.letOp (n := 3254) (.out 0x1126cb (movR64R64Effect 0x1126cb 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[3249]
    (.letOp (n := 3255) (.exec 0x1126cb (fun s => s.RIP = 0x1126cb) (movR64R64Effect 0x1126cb 5 0) (Reg.operands [.gpr 0] [])) #v[3249]
    (.letOp (n := 3256) (.out 0x1126ce (movR64M64Effect 0x1126ce 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3257) (.exec 0x1126ce (LoadPre 0x1126ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1126ce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1126ce 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3258) (.out 0x1126d3 (movR64M64Effect 0x1126d3 6 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 3259) (.exec 0x1126d3 (LoadPre 0x1126d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1126d3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1126d3 6 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3260) (.out 0x1126db (mulR64Effect 0x1126db 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[3258, 3256]
    (.letOp (n := 3261) (.out 0x1126db (mulR64Effect 0x1126db 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[3258, 3256]
    (.letOp (n := 3262) (.exec 0x1126db (fun s => s.RIP = 0x1126db) (mulR64Effect 0x1126db 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3258, 3256]
    (.letOp (n := 3263) (.out 0x1126de (addR64R64Effect 0x1126de 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[3254, 3237]
    (.letOp (n := 3264) (.out 0x1126de (addR64R64Effect 0x1126de 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[3254, 3237]
    (.letOp (n := 3265) (.exec 0x1126de (fun s => s.RIP = 0x1126de) (addR64R64Effect 0x1126de 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[3254, 3237]
    (.letOp (n := 3266) (.out 0x1126e1 (atFlags StatusFlags.CF (adcR64R64Effect 0x1126e1 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3252, 3239, 3264]
    (.letOp (n := 3267) (.exec 0x1126e1 (fun s => s.RIP = 0x1126e1) (atFlags StatusFlags.CF (adcR64R64Effect 0x1126e1 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3252, 3239, 3264]
    (.letOp (n := 3268) (.out 0x1126e4 (addR64R64Effect 0x1126e4 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[3260, 3263]
    (.letOp (n := 3269) (.out 0x1126e4 (addR64R64Effect 0x1126e4 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[3260, 3263]
    (.letOp (n := 3270) (.exec 0x1126e4 (fun s => s.RIP = 0x1126e4) (addR64R64Effect 0x1126e4 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[3260, 3263]
    (.letOp (n := 3271) (.out 0x1126e7 (atFlags StatusFlags.CF (adcR64R64Effect 0x1126e7 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3266, 3261, 3269]
    (.letOp (n := 3272) (.exec 0x1126e7 (fun s => s.RIP = 0x1126e7) (atFlags StatusFlags.CF (adcR64R64Effect 0x1126e7 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3266, 3261, 3269]
    (.letOp (n := 3273) (.out 0x1126ea (addR64R64Effect 0x1126ea 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[3268, 3188]
    (.letOp (n := 3274) (.out 0x1126ea (addR64R64Effect 0x1126ea 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[3268, 3188]
    (.letOp (n := 3275) (.exec 0x1126ea (fun s => s.RIP = 0x1126ea) (addR64R64Effect 0x1126ea 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[3268, 3188]
    (.letOp (n := 3276) (.out 0x1126ed (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1126ed 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[3271, 3274]
    (.letOp (n := 3277) (.exec 0x1126ed (fun s => s.RIP = 0x1126ed) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1126ed 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3271, 3274]
    (.letOp (n := 3278) (.out 0x1126f1 (shldR64R64Effect 0x1126f1 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[3276, 3273]
    (.letOp (n := 3279) (.exec 0x1126f1 (fun s => s.RIP = 0x1126f1) (shldR64R64Effect 0x1126f1 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3276, 3273]
    (.letOp (n := 3280) (.out 0x1126f6 (movR64Imm64Effect 0x1126f6 12 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 3281) (.exec 0x1126f6 (fun s => s.RIP = 0x1126f6) (movR64Imm64Effect 0x1126f6 12 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 3282) (.out 0x112700 (andR64R64Effect 0x112700 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[3273, 3280]
    (.letOp (n := 3283) (.exec 0x112700 (fun s => s.RIP = 0x112700) (andR64R64Effect 0x112700 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[3273, 3280]
    (.letOp (n := 3284) (.out 0x112703 (movR64Imm64Effect 0x112703 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 3285) (.exec 0x112703 (fun s => s.RIP = 0x112703) (movR64Imm64Effect 0x112703 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 3286) (.out 0x11270d (mulR64Effect 0x11270d 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[3284, 3282]
    (.letOp (n := 3287) (.out 0x11270d (mulR64Effect 0x11270d 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3284, 3282]
    (.letOp (n := 3288) (.exec 0x11270d (fun s => s.RIP = 0x11270d) (mulR64Effect 0x11270d 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3284, 3282]
    (.letOp (n := 3289) (.out 0x112710 (addR64M64Effect 0x112710 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[3228, 4]
    (.letOp (n := 3290) (.out 0x112710 (addR64M64Effect 0x112710 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 4] []) (.flag .CF)) #v[3228, 4]
    (.letOp (n := 3291) (.exec 0x112710 (LoadPre 0x112710 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x112710 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x112710 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[3228, 4]
    (.letOp (n := 3292) (.out 0x112715 (atFlags StatusFlags.CF (adcR64M64Effect 0x112715 9 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[3226, 4, 3290]
    (.letOp (n := 3293) (.exec 0x112715 (LoadPre 0x112715 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112715 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x112715 9 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3226, 4, 3290]
    (b_l110d64_76)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_75 : List UInt8 :=
  [0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xA4, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD3, 0x48, 0x89,
    0xC5, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0xB4, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0xF7,
    0xE6, 0x4C, 0x01, 0xE5, 0x4D, 0x11, 0xEB, 0x48, 0x01, 0xE8, 0x49, 0x11, 0xD3, 0x4C, 0x01, 0xD0,
    0x49, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x49, 0xBC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xE0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE2, 0x48, 0x03, 0x4C, 0x24, 0x20, 0x4C, 0x13, 0x4C, 0x24, 0x08] ++ bytes_l110d64_76

theorem code_l110d64_75 : ∀ x ∈ codeRange 0x1126bd bytes_l110d64_75, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x126bd 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_76

def b_l110d64_74 : Block Op Label signature Reg.count 3205 :=
  .letOp (n := 3205) (.out 0x112664 (movR64R64Effect 0x112664 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[3200]
    (.letOp (n := 3206) (.exec 0x112664 (fun s => s.RIP = 0x112664) (movR64R64Effect 0x112664 8 0) (Reg.operands [.gpr 0] [])) #v[3200]
    (.letOp (n := 3207) (.out 0x112667 (addR64M64Effect 0x112667 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[3205, 4]
    (.letOp (n := 3208) (.out 0x112667 (addR64M64Effect 0x112667 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[3205, 4]
    (.letOp (n := 3209) (.exec 0x112667 (LoadPre 0x112667 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x112667 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x112667 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[3205, 4]
    (.letOp (n := 3210) (.out 0x11266c (atFlags StatusFlags.CF (adcR64M64Effect 0x11266c 3 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[3203, 4, 3208]
    (.letOp (n := 3211) (.exec 0x11266c (LoadPre 0x11266c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11266c + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11266c 3 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3203, 4, 3208]
    (.letOp (n := 3212) (.out 0x112671 (shldR64R64Effect 0x112671 5 3 8 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[3210, 3207]
    (.letOp (n := 3213) (.exec 0x112671 (fun s => s.RIP = 0x112671) (shldR64R64Effect 0x112671 5 3 8 12) (Reg.operands [.gpr 3, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3210, 3207]
    (.letOp (n := 3214) (.out 0x112676 (movR64R64Effect 0x112676 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[3119]
    (.letOp (n := 3215) (.exec 0x112676 (fun s => s.RIP = 0x112676) (movR64R64Effect 0x112676 0 9) (Reg.operands [.gpr 9] [])) #v[3119]
    (.letOp (n := 3216) (.out 0x112679 (mulR64Effect 0x112679 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[3163, 3214]
    (.letOp (n := 3217) (.out 0x112679 (mulR64Effect 0x112679 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[3163, 3214]
    (.letOp (n := 3218) (.exec 0x112679 (fun s => s.RIP = 0x112679) (mulR64Effect 0x112679 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[3163, 3214]
    (.letOp (n := 3219) (.exec 0x11267c (StorePre 0x11267c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11267c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11267c 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3217, 4]
    (.letOp (n := 3220) (.exec 0x112681 (StorePre 0x112681 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x112681 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112681 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3216, 4]
    (.letOp (n := 3221) (.out 0x112686 (movR64R64Effect 0x112686 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[3128]
    (.letOp (n := 3222) (.exec 0x112686 (fun s => s.RIP = 0x112686) (movR64R64Effect 0x112686 0 6) (Reg.operands [.gpr 6] [])) #v[3128]
    (.letOp (n := 3223) (.out 0x112689 (mulM64Effect 0x112689 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3221, 4]
    (.letOp (n := 3224) (.out 0x112689 (mulM64Effect 0x112689 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3221, 4]
    (.letOp (n := 3225) (.exec 0x112689 (LoadPre 0x112689 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x112689 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x112689 8 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3221, 4]
    (.letOp (n := 3226) (.out 0x112691 (movR64R64Effect 0x112691 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[3224]
    (.letOp (n := 3227) (.exec 0x112691 (fun s => s.RIP = 0x112691) (movR64R64Effect 0x112691 9 2) (Reg.operands [.gpr 2] [])) #v[3224]
    (.letOp (n := 3228) (.out 0x112694 (movR64R64Effect 0x112694 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[3223]
    (.letOp (n := 3229) (.exec 0x112694 (fun s => s.RIP = 0x112694) (movR64R64Effect 0x112694 1 0) (Reg.operands [.gpr 0] [])) #v[3223]
    (.letOp (n := 3230) (.out 0x112697 (movR64M64Effect 0x112697 15 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 3231) (.exec 0x112697 (LoadPre 0x112697 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x112697 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112697 15 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3232) (.out 0x11269f (movR64R64Effect 0x11269f 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[3230]
    (.letOp (n := 3233) (.exec 0x11269f (fun s => s.RIP = 0x11269f) (movR64R64Effect 0x11269f 0 15) (Reg.operands [.gpr 15] [])) #v[3230]
    (.letOp (n := 3234) (.out 0x1126a2 (mulR64Effect 0x1126a2 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[3132, 3232]
    (.letOp (n := 3235) (.out 0x1126a2 (mulR64Effect 0x1126a2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[3132, 3232]
    (.letOp (n := 3236) (.exec 0x1126a2 (fun s => s.RIP = 0x1126a2) (mulR64Effect 0x1126a2 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[3132, 3232]
    (.letOp (n := 3237) (.out 0x1126a5 (movR64R64Effect 0x1126a5 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[3234]
    (.letOp (n := 3238) (.exec 0x1126a5 (fun s => s.RIP = 0x1126a5) (movR64R64Effect 0x1126a5 12 0) (Reg.operands [.gpr 0] [])) #v[3234]
    (.letOp (n := 3239) (.out 0x1126a8 (movR64R64Effect 0x1126a8 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[3235]
    (.letOp (n := 3240) (.exec 0x1126a8 (fun s => s.RIP = 0x1126a8) (movR64R64Effect 0x1126a8 13 2) (Reg.operands [.gpr 2] [])) #v[3235]
    (.letOp (n := 3241) (.out 0x1126ab (movR64Imm64Effect 0x1126ab 14 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 3242) (.exec 0x1126ab (fun s => s.RIP = 0x1126ab) (movR64Imm64Effect 0x1126ab 14 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 3243) (.out 0x1126b5 (andR64R64Effect 0x1126b5 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[3207, 3241]
    (.letOp (n := 3244) (.exec 0x1126b5 (fun s => s.RIP = 0x1126b5) (andR64R64Effect 0x1126b5 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[3207, 3241]
    (.letOp (n := 3245) (.out 0x1126b8 (movR64M64Effect 0x1126b8 14 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 3246) (.exec 0x1126b8 (LoadPre 0x1126b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1126b8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1126b8 14 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l110d64_75))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_74 : List UInt8 :=
  [0x49, 0x89, 0xC0, 0x4C, 0x03, 0x44, 0x24, 0x20, 0x48, 0x13, 0x5C, 0x24, 0x08, 0x4C, 0x0F, 0xA4,
    0xC3, 0x0C, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0x54, 0x24, 0x08, 0x48, 0x89, 0x44,
    0x24, 0x20, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0xA4, 0x24, 0x20, 0x01, 0x00, 0x00, 0x49, 0x89, 0xD1,
    0x48, 0x89, 0xC1, 0x4C, 0x8B, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF8, 0x49, 0xF7,
    0xE3, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD5, 0x49, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F,
    0x00, 0x4D, 0x21, 0xF0, 0x4C, 0x8B, 0x74, 0x24, 0x38] ++ bytes_l110d64_75

theorem code_l110d64_74 : ∀ x ∈ codeRange 0x112664 bytes_l110d64_74, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12664 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_75

def b_l110d64_73 : Block Op Label signature Reg.count 3159 :=
  .letOp (n := 3159) (.out 0x11260f (movR64R64Effect 0x11260f 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[3154]
    (.letOp (n := 3160) (.exec 0x11260f (fun s => s.RIP = 0x11260f) (movR64R64Effect 0x11260f 12 0) (Reg.operands [.gpr 0] [])) #v[3154]
    (.letOp (n := 3161) (.out 0x112612 (movR64M64Effect 0x112612 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3162) (.exec 0x112612 (LoadPre 0x112612 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x112612 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112612 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3163) (.out 0x112617 (movR64M64Effect 0x112617 5 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 3164) (.exec 0x112617 (LoadPre 0x112617 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x112617 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112617 5 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3165) (.out 0x11261f (mulR64Effect 0x11261f 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[3163, 3161]
    (.letOp (n := 3166) (.out 0x11261f (mulR64Effect 0x11261f 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[3163, 3161]
    (.letOp (n := 3167) (.exec 0x11261f (fun s => s.RIP = 0x11261f) (mulR64Effect 0x11261f 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[3163, 3161]
    (.letOp (n := 3168) (.out 0x112622 (addR64R64Effect 0x112622 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[3150, 3137]
    (.letOp (n := 3169) (.out 0x112622 (addR64R64Effect 0x112622 14 8) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 8] []) (.flag .CF)) #v[3150, 3137]
    (.letOp (n := 3170) (.exec 0x112622 (fun s => s.RIP = 0x112622) (addR64R64Effect 0x112622 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[3150, 3137]
    (.letOp (n := 3171) (.out 0x112625 (atFlags StatusFlags.CF (adcR64R64Effect 0x112625 10 3)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[3148, 3139, 3169]
    (.letOp (n := 3172) (.exec 0x112625 (fun s => s.RIP = 0x112625) (atFlags StatusFlags.CF (adcR64R64Effect 0x112625 10 3)) (Reg.operands [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3148, 3139, 3169]
    (.letOp (n := 3173) (.out 0x112628 (addR64R64Effect 0x112628 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[3168, 3159]
    (.letOp (n := 3174) (.out 0x112628 (addR64R64Effect 0x112628 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[3168, 3159]
    (.letOp (n := 3175) (.exec 0x112628 (fun s => s.RIP = 0x112628) (addR64R64Effect 0x112628 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[3168, 3159]
    (.letOp (n := 3176) (.out 0x11262b (atFlags StatusFlags.CF (adcR64R64Effect 0x11262b 10 15)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[3171, 3157, 3174]
    (.letOp (n := 3177) (.exec 0x11262b (fun s => s.RIP = 0x11262b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11262b 10 15)) (Reg.operands [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3171, 3157, 3174]
    (.letOp (n := 3178) (.out 0x11262e (addR64R64Effect 0x11262e 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[3165, 3173]
    (.letOp (n := 3179) (.out 0x11262e (addR64R64Effect 0x11262e 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[3165, 3173]
    (.letOp (n := 3180) (.exec 0x11262e (fun s => s.RIP = 0x11262e) (addR64R64Effect 0x11262e 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[3165, 3173]
    (.letOp (n := 3181) (.out 0x112631 (atFlags StatusFlags.CF (adcR64R64Effect 0x112631 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[3176, 3166, 3179]
    (.letOp (n := 3182) (.exec 0x112631 (fun s => s.RIP = 0x112631) (atFlags StatusFlags.CF (adcR64R64Effect 0x112631 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3176, 3166, 3179]
    (.letOp (n := 3183) (.out 0x112634 (addR64R64Effect 0x112634 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3178, 3113]
    (.letOp (n := 3184) (.out 0x112634 (addR64R64Effect 0x112634 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[3178, 3113]
    (.letOp (n := 3185) (.exec 0x112634 (fun s => s.RIP = 0x112634) (addR64R64Effect 0x112634 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3178, 3113]
    (.letOp (n := 3186) (.out 0x112637 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112637 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[3181, 3184]
    (.letOp (n := 3187) (.exec 0x112637 (fun s => s.RIP = 0x112637) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112637 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3181, 3184]
    (.letOp (n := 3188) (.out 0x11263b (shldR64R64Effect 0x11263b 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[3186, 3183]
    (.letOp (n := 3189) (.exec 0x11263b (fun s => s.RIP = 0x11263b) (shldR64R64Effect 0x11263b 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3186, 3183]
    (.letOp (n := 3190) (.out 0x112640 (shlR64Effect 0x112640 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3183]
    (.letOp (n := 3191) (.exec 0x112640 (fun s => s.RIP = 0x112640) (shlR64Effect 0x112640 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3183]
    (.letOp (n := 3192) (.out 0x112644 (movR64Imm64Effect 0x112644 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 3193) (.exec 0x112644 (fun s => s.RIP = 0x112644) (movR64Imm64Effect 0x112644 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 3194) (.out 0x11264e (andR64R64Effect 0x11264e 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3190, 3192]
    (.letOp (n := 3195) (.exec 0x11264e (fun s => s.RIP = 0x11264e) (andR64R64Effect 0x11264e 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3190, 3192]
    (.letOp (n := 3196) (.out 0x112651 (orR64R64Effect 0x112651 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[3194, 3141]
    (.letOp (n := 3197) (.exec 0x112651 (fun s => s.RIP = 0x112651) (orR64R64Effect 0x112651 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[3194, 3141]
    (.letOp (n := 3198) (.out 0x112654 (movR64Imm64Effect 0x112654 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 3199) (.exec 0x112654 (fun s => s.RIP = 0x112654) (movR64Imm64Effect 0x112654 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 3200) (.out 0x11265e (mulR64Effect 0x11265e 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[3198, 3196]
    (.letOp (n := 3201) (.out 0x11265e (mulR64Effect 0x11265e 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[3198, 3196]
    (.letOp (n := 3202) (.exec 0x11265e (fun s => s.RIP = 0x11265e) (mulR64Effect 0x11265e 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3198, 3196]
    (.letOp (n := 3203) (.out 0x112661 (movR64R64Effect 0x112661 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[3201]
    (.letOp (n := 3204) (.exec 0x112661 (fun s => s.RIP = 0x112661) (movR64R64Effect 0x112661 3 2) (Reg.operands [.gpr 2] [])) #v[3201]
    (b_l110d64_74))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_73 : List UInt8 :=
  [0x49, 0x89, 0xC4, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0xAC, 0x24, 0x18, 0x01, 0x00, 0x00,
    0x48, 0xF7, 0xE5, 0x4D, 0x01, 0xC6, 0x49, 0x11, 0xDA, 0x4D, 0x01, 0xE6, 0x4D, 0x11, 0xFA, 0x4C,
    0x01, 0xF0, 0x49, 0x11, 0xD2, 0x48, 0x01, 0xC8, 0x49, 0x83, 0xD2, 0x00, 0x49, 0x0F, 0xA4, 0xC2,
    0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48,
    0x21, 0xC8, 0x4C, 0x09, 0xE8, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE1, 0x48, 0x89, 0xD3] ++ bytes_l110d64_74

theorem code_l110d64_73 : ∀ x ∈ codeRange 0x11260f bytes_l110d64_73, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1260f 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_74

def b_l110d64_72 : Block Op Label signature Reg.count 3117 :=
  .letOp (n := 3117) (.out 0x1125b0 (shrR64Effect 0x1125b0 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[3115]
    (.letOp (n := 3118) (.exec 0x1125b0 (fun s => s.RIP = 0x1125b0) (shrR64Effect 0x1125b0 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3115]
    (.letOp (n := 3119) (.out 0x1125b4 (movR64M64Effect 0x1125b4 9 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 3120) (.exec 0x1125b4 (LoadPre 0x1125b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1125b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1125b4 9 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3121) (.out 0x1125b9 (movR64R64Effect 0x1125b9 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[3119]
    (.letOp (n := 3122) (.exec 0x1125b9 (fun s => s.RIP = 0x1125b9) (movR64R64Effect 0x1125b9 0 9) (Reg.operands [.gpr 9] [])) #v[3119]
    (.letOp (n := 3123) (.out 0x1125bc (mulR64Effect 0x1125bc 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[3070, 3121]
    (.letOp (n := 3124) (.out 0x1125bc (mulR64Effect 0x1125bc 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[3070, 3121]
    (.letOp (n := 3125) (.exec 0x1125bc (fun s => s.RIP = 0x1125bc) (mulR64Effect 0x1125bc 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3070, 3121]
    (.letOp (n := 3126) (.exec 0x1125bf (StorePre 0x1125bf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1125bf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1125bf 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3124, 4]
    (.letOp (n := 3127) (.exec 0x1125c4 (StorePre 0x1125c4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1125c4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1125c4 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3123, 4]
    (.letOp (n := 3128) (.out 0x1125c9 (movR64M64Effect 0x1125c9 6 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 3129) (.exec 0x1125c9 (LoadPre 0x1125c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1125c9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1125c9 6 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3130) (.out 0x1125d1 (movR64R64Effect 0x1125d1 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[3128]
    (.letOp (n := 3131) (.exec 0x1125d1 (fun s => s.RIP = 0x1125d1) (movR64R64Effect 0x1125d1 0 6) (Reg.operands [.gpr 6] [])) #v[3128]
    (.letOp (n := 3132) (.out 0x1125d4 (movR64M64Effect 0x1125d4 11 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 3133) (.exec 0x1125d4 (LoadPre 0x1125d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1125d4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1125d4 11 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3134) (.out 0x1125dc (mulR64Effect 0x1125dc 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[3132, 3130]
    (.letOp (n := 3135) (.out 0x1125dc (mulR64Effect 0x1125dc 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[3132, 3130]
    (.letOp (n := 3136) (.exec 0x1125dc (fun s => s.RIP = 0x1125dc) (mulR64Effect 0x1125dc 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[3132, 3130]
    (.letOp (n := 3137) (.out 0x1125df (movR64R64Effect 0x1125df 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[3134]
    (.letOp (n := 3138) (.exec 0x1125df (fun s => s.RIP = 0x1125df) (movR64R64Effect 0x1125df 8 0) (Reg.operands [.gpr 0] [])) #v[3134]
    (.letOp (n := 3139) (.out 0x1125e2 (movR64R64Effect 0x1125e2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[3135]
    (.letOp (n := 3140) (.exec 0x1125e2 (fun s => s.RIP = 0x1125e2) (movR64R64Effect 0x1125e2 3 2) (Reg.operands [.gpr 2] [])) #v[3135]
    (.letOp (n := 3141) (.out 0x1125e5 (andR32Imm8Effect 0x1125e5 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[3117]
    (.letOp (n := 3142) (.exec 0x1125e5 (fun s => s.RIP = 0x1125e5) (andR32Imm8Effect 0x1125e5 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[3117]
    (.letOp (n := 3143) (.out 0x1125e9 (movR64M64Effect 0x1125e9 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3144) (.exec 0x1125e9 (LoadPre 0x1125e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1125e9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1125e9 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3145) (.out 0x1125f1 (mulM64Effect 0x1125f1 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3143, 4]
    (.letOp (n := 3146) (.out 0x1125f1 (mulM64Effect 0x1125f1 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3143, 4]
    (.letOp (n := 3147) (.exec 0x1125f1 (LoadPre 0x1125f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1125f1 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1125f1 8 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3143, 4]
    (.letOp (n := 3148) (.out 0x1125f9 (movR64R64Effect 0x1125f9 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[3146]
    (.letOp (n := 3149) (.exec 0x1125f9 (fun s => s.RIP = 0x1125f9) (movR64R64Effect 0x1125f9 10 2) (Reg.operands [.gpr 2] [])) #v[3146]
    (.letOp (n := 3150) (.out 0x1125fc (movR64R64Effect 0x1125fc 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[3145]
    (.letOp (n := 3151) (.exec 0x1125fc (fun s => s.RIP = 0x1125fc) (movR64R64Effect 0x1125fc 14 0) (Reg.operands [.gpr 0] [])) #v[3145]
    (.letOp (n := 3152) (.out 0x1125ff (movR64M64Effect 0x1125ff 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3153) (.exec 0x1125ff (LoadPre 0x1125ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1125ff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1125ff 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3154) (.out 0x112604 (mulM64Effect 0x112604 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3152, 4]
    (.letOp (n := 3155) (.out 0x112604 (mulM64Effect 0x112604 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3152, 4]
    (.letOp (n := 3156) (.exec 0x112604 (LoadPre 0x112604 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x112604 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x112604 8 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3152, 4]
    (.letOp (n := 3157) (.out 0x11260c (movR64R64Effect 0x11260c 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[3155]
    (.letOp (n := 3158) (.exec 0x11260c (fun s => s.RIP = 0x11260c) (movR64R64Effect 0x11260c 15 2) (Reg.operands [.gpr 2] [])) #v[3155]
    (b_l110d64_73))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_72 : List UInt8 :=
  [0x49, 0xC1, 0xED, 0x30, 0x4C, 0x8B, 0x4C, 0x24, 0x68, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0xE6, 0x48,
    0x89, 0x54, 0x24, 0x08, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0xB4, 0x24, 0xA8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xF0, 0x4C, 0x8B, 0x9C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE3, 0x49,
    0x89, 0xC0, 0x48, 0x89, 0xD3, 0x41, 0x83, 0xE5, 0x0F, 0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00,
    0x00, 0x48, 0xF7, 0xA4, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC6, 0x48,
    0x8B, 0x44, 0x24, 0x38, 0x48, 0xF7, 0xA4, 0x24, 0x10, 0x01, 0x00, 0x00, 0x49, 0x89, 0xD7] ++ bytes_l110d64_73

theorem code_l110d64_72 : ∀ x ∈ codeRange 0x1125b0 bytes_l110d64_72, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x125b0 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_73

def b_l110d64_71 : Block Op Label signature Reg.count 3070 :=
  .letOp (n := 3070) (.out 0x11256a (movR64R64Effect 0x11256a 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[2983]
    (.letOp (n := 3071) (.exec 0x11256a (fun s => s.RIP = 0x11256a) (movR64R64Effect 0x11256a 6 13) (Reg.operands [.gpr 13] [])) #v[2983]
    (.letOp (n := 3072) (.out 0x11256d (movR64R64Effect 0x11256d 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[3068]
    (.letOp (n := 3073) (.exec 0x11256d (fun s => s.RIP = 0x11256d) (movR64R64Effect 0x11256d 13 2) (Reg.operands [.gpr 2] [])) #v[3068]
    (.letOp (n := 3074) (.out 0x112570 (movR64R64Effect 0x112570 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[3067]
    (.letOp (n := 3075) (.exec 0x112570 (fun s => s.RIP = 0x112570) (movR64R64Effect 0x112570 5 0) (Reg.operands [.gpr 0] [])) #v[3067]
    (.letOp (n := 3076) (.out 0x112573 (movR64R64Effect 0x112573 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[3008]
    (.letOp (n := 3077) (.exec 0x112573 (fun s => s.RIP = 0x112573) (movR64R64Effect 0x112573 0 9) (Reg.operands [.gpr 9] [])) #v[3008]
    (.letOp (n := 3078) (.out 0x112576 (movR64Imm64Effect 0x112576 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 3079) (.exec 0x112576 (fun s => s.RIP = 0x112576) (movR64Imm64Effect 0x112576 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 3080) (.out 0x112580 (mulR64Effect 0x112580 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[3078, 3076]
    (.letOp (n := 3081) (.out 0x112580 (mulR64Effect 0x112580 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3078, 3076]
    (.letOp (n := 3082) (.exec 0x112580 (fun s => s.RIP = 0x112580) (mulR64Effect 0x112580 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3078, 3076]
    (.letOp (n := 3083) (.out 0x112583 (addR64R64Effect 0x112583 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[3045, 3036]
    (.letOp (n := 3084) (.out 0x112583 (addR64R64Effect 0x112583 7 11) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 11] []) (.flag .CF)) #v[3045, 3036]
    (.letOp (n := 3085) (.exec 0x112583 (fun s => s.RIP = 0x112583) (addR64R64Effect 0x112583 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[3045, 3036]
    (.letOp (n := 3086) (.out 0x112586 (atFlags StatusFlags.CF (adcR64R64Effect 0x112586 1 10)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[3043, 3034, 3084]
    (.letOp (n := 3087) (.exec 0x112586 (fun s => s.RIP = 0x112586) (atFlags StatusFlags.CF (adcR64R64Effect 0x112586 1 10)) (Reg.operands [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3043, 3034, 3084]
    (.letOp (n := 3088) (.out 0x112589 (addR64R64Effect 0x112589 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[3083, 3054]
    (.letOp (n := 3089) (.out 0x112589 (addR64R64Effect 0x112589 7 14) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 14] []) (.flag .CF)) #v[3083, 3054]
    (.letOp (n := 3090) (.exec 0x112589 (fun s => s.RIP = 0x112589) (addR64R64Effect 0x112589 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[3083, 3054]
    (.letOp (n := 3091) (.out 0x11258c (atFlags StatusFlags.CF (adcR64R64Effect 0x11258c 1 3)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[3086, 3052, 3089]
    (.letOp (n := 3092) (.exec 0x11258c (fun s => s.RIP = 0x11258c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11258c 1 3)) (Reg.operands [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3086, 3052, 3089]
    (.letOp (n := 3093) (.out 0x11258f (addR64R64Effect 0x11258f 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[3088, 3063]
    (.letOp (n := 3094) (.out 0x11258f (addR64R64Effect 0x11258f 7 12) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 12] []) (.flag .CF)) #v[3088, 3063]
    (.letOp (n := 3095) (.exec 0x11258f (fun s => s.RIP = 0x11258f) (addR64R64Effect 0x11258f 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[3088, 3063]
    (.letOp (n := 3096) (.out 0x112592 (atFlags StatusFlags.CF (adcR64R64Effect 0x112592 1 15)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[3091, 3061, 3094]
    (.letOp (n := 3097) (.exec 0x112592 (fun s => s.RIP = 0x112592) (atFlags StatusFlags.CF (adcR64R64Effect 0x112592 1 15)) (Reg.operands [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3091, 3061, 3094]
    (.letOp (n := 3098) (.out 0x112595 (addR64R64Effect 0x112595 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[3093, 3074]
    (.letOp (n := 3099) (.out 0x112595 (addR64R64Effect 0x112595 7 5) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 5] []) (.flag .CF)) #v[3093, 3074]
    (.letOp (n := 3100) (.exec 0x112595 (fun s => s.RIP = 0x112595) (addR64R64Effect 0x112595 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[3093, 3074]
    (.letOp (n := 3101) (.out 0x112598 (atFlags StatusFlags.CF (adcR64R64Effect 0x112598 1 13)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[3096, 3072, 3099]
    (.letOp (n := 3102) (.exec 0x112598 (fun s => s.RIP = 0x112598) (atFlags StatusFlags.CF (adcR64R64Effect 0x112598 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3096, 3072, 3099]
    (.letOp (n := 3103) (.out 0x11259b (addR64R64Effect 0x11259b 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[3098, 3080]
    (.letOp (n := 3104) (.out 0x11259b (addR64R64Effect 0x11259b 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[3098, 3080]
    (.letOp (n := 3105) (.exec 0x11259b (fun s => s.RIP = 0x11259b) (addR64R64Effect 0x11259b 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[3098, 3080]
    (.letOp (n := 3106) (.out 0x11259e (atFlags StatusFlags.CF (adcR64R64Effect 0x11259e 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[3101, 3081, 3104]
    (.letOp (n := 3107) (.exec 0x11259e (fun s => s.RIP = 0x11259e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11259e 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3101, 3081, 3104]
    (.letOp (n := 3108) (.out 0x1125a1 (addR64R64Effect 0x1125a1 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[3103, 3027]
    (.letOp (n := 3109) (.out 0x1125a1 (addR64R64Effect 0x1125a1 7 8) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 8] []) (.flag .CF)) #v[3103, 3027]
    (.letOp (n := 3110) (.exec 0x1125a1 (fun s => s.RIP = 0x1125a1) (addR64R64Effect 0x1125a1 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[3103, 3027]
    (.letOp (n := 3111) (.out 0x1125a4 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1125a4 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[3106, 3109]
    (.letOp (n := 3112) (.exec 0x1125a4 (fun s => s.RIP = 0x1125a4) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1125a4 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3106, 3109]
    (.letOp (n := 3113) (.out 0x1125a8 (shldR64R64Effect 0x1125a8 5 1 7 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3111, 3108]
    (.letOp (n := 3114) (.exec 0x1125a8 (fun s => s.RIP = 0x1125a8) (shldR64R64Effect 0x1125a8 5 1 7 12) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3111, 3108]
    (.letOp (n := 3115) (.out 0x1125ad (movR64R64Effect 0x1125ad 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 7] []) (.reg (.gpr 13))) #v[3108]
    (.letOp (n := 3116) (.exec 0x1125ad (fun s => s.RIP = 0x1125ad) (movR64R64Effect 0x1125ad 13 7) (Reg.operands [.gpr 7] [])) #v[3108]
    (b_l110d64_72)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_71 : List UInt8 :=
  [0x4C, 0x89, 0xEE, 0x49, 0x89, 0xD5, 0x48, 0x89, 0xC5, 0x4C, 0x89, 0xC8, 0x48, 0xBA, 0x10, 0x3D,
    0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x01, 0xDF, 0x4C, 0x11, 0xD1, 0x4C,
    0x01, 0xF7, 0x48, 0x11, 0xD9, 0x4C, 0x01, 0xE7, 0x4C, 0x11, 0xF9, 0x48, 0x01, 0xEF, 0x4C, 0x11,
    0xE9, 0x48, 0x01, 0xC7, 0x48, 0x11, 0xD1, 0x4C, 0x01, 0xC7, 0x48, 0x83, 0xD1, 0x00, 0x48, 0x0F,
    0xA4, 0xF9, 0x0C, 0x49, 0x89, 0xFD] ++ bytes_l110d64_72

theorem code_l110d64_71 : ∀ x ∈ codeRange 0x11256a bytes_l110d64_71, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1256a 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_72

def b_l110d64_70 : Block Op Label signature Reg.count 3025 :=
  .letOp (n := 3025) (.out 0x112527 (atFlags StatusFlags.CF (adcR64R64Effect 0x112527 8 7)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[3019, 2995, 3022]
    (.letOp (n := 3026) (.exec 0x112527 (fun s => s.RIP = 0x112527) (atFlags StatusFlags.CF (adcR64R64Effect 0x112527 8 7)) (Reg.operands [.gpr 8, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3019, 2995, 3022]
    (.letOp (n := 3027) (.out 0x11252a (shldR64R64Effect 0x11252a 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[3025, 3021]
    (.letOp (n := 3028) (.exec 0x11252a (fun s => s.RIP = 0x11252a) (shldR64R64Effect 0x11252a 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3025, 3021]
    (.letOp (n := 3029) (.out 0x11252f (movR64R64Effect 0x11252f 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2932]
    (.letOp (n := 3030) (.exec 0x11252f (fun s => s.RIP = 0x11252f) (movR64R64Effect 0x11252f 0 11) (Reg.operands [.gpr 11] [])) #v[2932]
    (.letOp (n := 3031) (.out 0x112532 (mulR64Effect 0x112532 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[3001, 3029]
    (.letOp (n := 3032) (.out 0x112532 (mulR64Effect 0x112532 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[3001, 3029]
    (.letOp (n := 3033) (.exec 0x112532 (fun s => s.RIP = 0x112532) (mulR64Effect 0x112532 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3001, 3029]
    (.letOp (n := 3034) (.out 0x112535 (movR64R64Effect 0x112535 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[3032]
    (.letOp (n := 3035) (.exec 0x112535 (fun s => s.RIP = 0x112535) (movR64R64Effect 0x112535 10 2) (Reg.operands [.gpr 2] [])) #v[3032]
    (.letOp (n := 3036) (.out 0x112538 (movR64R64Effect 0x112538 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[3031]
    (.letOp (n := 3037) (.exec 0x112538 (fun s => s.RIP = 0x112538) (movR64R64Effect 0x112538 11 0) (Reg.operands [.gpr 0] [])) #v[3031]
    (.letOp (n := 3038) (.out 0x11253b (movR64R64Effect 0x11253b 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[2943]
    (.letOp (n := 3039) (.exec 0x11253b (fun s => s.RIP = 0x11253b) (movR64R64Effect 0x11253b 0 3) (Reg.operands [.gpr 3] [])) #v[2943]
    (.letOp (n := 3040) (.out 0x11253e (mulM64Effect 0x11253e 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[3038, 4]
    (.letOp (n := 3041) (.out 0x11253e (mulM64Effect 0x11253e 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[3038, 4]
    (.letOp (n := 3042) (.exec 0x11253e (LoadPre 0x11253e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11253e + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11253e 8 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3038, 4]
    (.letOp (n := 3043) (.out 0x112546 (movR64R64Effect 0x112546 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[3041]
    (.letOp (n := 3044) (.exec 0x112546 (fun s => s.RIP = 0x112546) (movR64R64Effect 0x112546 1 2) (Reg.operands [.gpr 2] [])) #v[3041]
    (.letOp (n := 3045) (.out 0x112549 (movR64R64Effect 0x112549 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[3040]
    (.letOp (n := 3046) (.exec 0x112549 (fun s => s.RIP = 0x112549) (movR64R64Effect 0x112549 7 0) (Reg.operands [.gpr 0] [])) #v[3040]
    (.letOp (n := 3047) (.out 0x11254c (movR64R64Effect 0x11254c 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[2961]
    (.letOp (n := 3048) (.exec 0x11254c (fun s => s.RIP = 0x11254c) (movR64R64Effect 0x11254c 0 12) (Reg.operands [.gpr 12] [])) #v[2961]
    (.letOp (n := 3049) (.out 0x11254f (mulR64Effect 0x11254f 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[2947, 3047]
    (.letOp (n := 3050) (.out 0x11254f (mulR64Effect 0x11254f 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[2947, 3047]
    (.letOp (n := 3051) (.exec 0x11254f (fun s => s.RIP = 0x11254f) (mulR64Effect 0x11254f 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[2947, 3047]
    (.letOp (n := 3052) (.out 0x112552 (movR64R64Effect 0x112552 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[3050]
    (.letOp (n := 3053) (.exec 0x112552 (fun s => s.RIP = 0x112552) (movR64R64Effect 0x112552 3 2) (Reg.operands [.gpr 2] [])) #v[3050]
    (.letOp (n := 3054) (.out 0x112555 (movR64R64Effect 0x112555 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[3049]
    (.letOp (n := 3055) (.exec 0x112555 (fun s => s.RIP = 0x112555) (movR64R64Effect 0x112555 14 0) (Reg.operands [.gpr 0] [])) #v[3049]
    (.letOp (n := 3056) (.out 0x112558 (movR64R64Effect 0x112558 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[2979]
    (.letOp (n := 3057) (.exec 0x112558 (fun s => s.RIP = 0x112558) (movR64R64Effect 0x112558 0 15) (Reg.operands [.gpr 15] [])) #v[2979]
    (.letOp (n := 3058) (.out 0x11255b (mulR64Effect 0x11255b 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[2965, 3056]
    (.letOp (n := 3059) (.out 0x11255b (mulR64Effect 0x11255b 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[2965, 3056]
    (.letOp (n := 3060) (.exec 0x11255b (fun s => s.RIP = 0x11255b) (mulR64Effect 0x11255b 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[2965, 3056]
    (.letOp (n := 3061) (.out 0x11255e (movR64R64Effect 0x11255e 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[3059]
    (.letOp (n := 3062) (.exec 0x11255e (fun s => s.RIP = 0x11255e) (movR64R64Effect 0x11255e 15 2) (Reg.operands [.gpr 2] [])) #v[3059]
    (.letOp (n := 3063) (.out 0x112561 (movR64R64Effect 0x112561 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[3058]
    (.letOp (n := 3064) (.exec 0x112561 (fun s => s.RIP = 0x112561) (movR64R64Effect 0x112561 12 0) (Reg.operands [.gpr 0] [])) #v[3058]
    (.letOp (n := 3065) (.out 0x112564 (movR64R64Effect 0x112564 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2997]
    (.letOp (n := 3066) (.exec 0x112564 (fun s => s.RIP = 0x112564) (movR64R64Effect 0x112564 0 6) (Reg.operands [.gpr 6] [])) #v[2997]
    (.letOp (n := 3067) (.out 0x112567 (mulR64Effect 0x112567 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[2983, 3065]
    (.letOp (n := 3068) (.out 0x112567 (mulR64Effect 0x112567 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[2983, 3065]
    (.letOp (n := 3069) (.exec 0x112567 (fun s => s.RIP = 0x112567) (mulR64Effect 0x112567 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2983, 3065]
    (b_l110d64_71)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_70 : List UInt8 :=
  [0x49, 0x11, 0xF8, 0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0xE1, 0x49, 0x89,
    0xD2, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0xA4, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48,
    0x89, 0xD1, 0x48, 0x89, 0xC7, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0xD3, 0x49, 0x89,
    0xC6, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC4, 0x48, 0x89, 0xF0,
    0x49, 0xF7, 0xE5] ++ bytes_l110d64_71

theorem code_l110d64_70 : ∀ x ∈ codeRange 0x112527 bytes_l110d64_70, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12527 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_71

def b_l110d64_69 : Block Op Label signature Reg.count 2981 :=
  .letOp (n := 2981) (.out 0x1124cd (movR64R64Effect 0x1124cd 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[2979]
    (.letOp (n := 2982) (.exec 0x1124cd (fun s => s.RIP = 0x1124cd) (movR64R64Effect 0x1124cd 0 15) (Reg.operands [.gpr 15] [])) #v[2979]
    (.letOp (n := 2983) (.out 0x1124d0 (movR64M64Effect 0x1124d0 13 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 2984) (.exec 0x1124d0 (LoadPre 0x1124d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x1124d0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1124d0 13 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2985) (.out 0x1124d8 (mulR64Effect 0x1124d8 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[2983, 2981]
    (.letOp (n := 2986) (.out 0x1124d8 (mulR64Effect 0x1124d8 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[2983, 2981]
    (.letOp (n := 2987) (.exec 0x1124d8 (fun s => s.RIP = 0x1124d8) (mulR64Effect 0x1124d8 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2983, 2981]
    (.letOp (n := 2988) (.out 0x1124db (movR64R64Effect 0x1124db 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2986]
    (.letOp (n := 2989) (.exec 0x1124db (fun s => s.RIP = 0x1124db) (movR64R64Effect 0x1124db 7 2) (Reg.operands [.gpr 2] [])) #v[2986]
    (.letOp (n := 2990) (.out 0x1124de (movR64R64Effect 0x1124de 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2985]
    (.letOp (n := 2991) (.exec 0x1124de (fun s => s.RIP = 0x1124de) (movR64R64Effect 0x1124de 10 0) (Reg.operands [.gpr 0] [])) #v[2985]
    (.letOp (n := 2992) (.out 0x1124e1 (addR64R64Effect 0x1124e1 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[2990, 2974]
    (.letOp (n := 2993) (.out 0x1124e1 (addR64R64Effect 0x1124e1 10 6) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 6] []) (.flag .CF)) #v[2990, 2974]
    (.letOp (n := 2994) (.exec 0x1124e1 (fun s => s.RIP = 0x1124e1) (addR64R64Effect 0x1124e1 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[2990, 2974]
    (.letOp (n := 2995) (.out 0x1124e4 (atFlags StatusFlags.CF (adcR64R64Effect 0x1124e4 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[2988, 2977, 2993]
    (.letOp (n := 2996) (.exec 0x1124e4 (fun s => s.RIP = 0x1124e4) (atFlags StatusFlags.CF (adcR64R64Effect 0x1124e4 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2988, 2977, 2993]
    (.letOp (n := 2997) (.out 0x1124e7 (movR64M64Effect 0x1124e7 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 2998) (.exec 0x1124e7 (LoadPre 0x1124e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1124e7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1124e7 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2999) (.out 0x1124ec (movR64R64Effect 0x1124ec 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2997]
    (.letOp (n := 3000) (.exec 0x1124ec (fun s => s.RIP = 0x1124ec) (movR64R64Effect 0x1124ec 0 6) (Reg.operands [.gpr 6] [])) #v[2997]
    (.letOp (n := 3001) (.out 0x1124ef (movR64M64Effect 0x1124ef 1 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 3002) (.exec 0x1124ef (LoadPre 0x1124ef (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1124ef + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1124ef 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3003) (.out 0x1124f7 (mulR64Effect 0x1124f7 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[3001, 2999]
    (.letOp (n := 3004) (.out 0x1124f7 (mulR64Effect 0x1124f7 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[3001, 2999]
    (.letOp (n := 3005) (.exec 0x1124f7 (fun s => s.RIP = 0x1124f7) (mulR64Effect 0x1124f7 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3001, 2999]
    (.letOp (n := 3006) (.out 0x1124fa (movR64R64Effect 0x1124fa 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[3004]
    (.letOp (n := 3007) (.exec 0x1124fa (fun s => s.RIP = 0x1124fa) (movR64R64Effect 0x1124fa 9 2) (Reg.operands [.gpr 2] [])) #v[3004]
    (.letOp (n := 3008) (.out 0x1124fd (shldR64R64Effect 0x1124fd 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[3006, 3003]
    (.letOp (n := 3009) (.exec 0x1124fd (fun s => s.RIP = 0x1124fd) (shldR64R64Effect 0x1124fd 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3006, 3003]
    (.letOp (n := 3010) (.out 0x112502 (movR64Imm64Effect 0x112502 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 3011) (.exec 0x112502 (fun s => s.RIP = 0x112502) (movR64Imm64Effect 0x112502 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 3012) (.out 0x11250c (andR64R64Effect 0x11250c 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3003, 3010]
    (.letOp (n := 3013) (.exec 0x11250c (fun s => s.RIP = 0x11250c) (andR64R64Effect 0x11250c 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3003, 3010]
    (.letOp (n := 3014) (.out 0x11250f (movR64Imm64Effect 0x11250f 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 3015) (.exec 0x11250f (fun s => s.RIP = 0x11250f) (movR64Imm64Effect 0x11250f 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 3016) (.out 0x112519 (mulR64Effect 0x112519 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[3014, 3012]
    (.letOp (n := 3017) (.out 0x112519 (mulR64Effect 0x112519 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3014, 3012]
    (.letOp (n := 3018) (.exec 0x112519 (fun s => s.RIP = 0x112519) (mulR64Effect 0x112519 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3014, 3012]
    (.letOp (n := 3019) (.out 0x11251c (movR64R64Effect 0x11251c 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[3017]
    (.letOp (n := 3020) (.exec 0x11251c (fun s => s.RIP = 0x11251c) (movR64R64Effect 0x11251c 8 2) (Reg.operands [.gpr 2] [])) #v[3017]
    (.letOp (n := 3021) (.out 0x11251f (addR64R64Effect 0x11251f 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[3016, 2992]
    (.letOp (n := 3022) (.out 0x11251f (addR64R64Effect 0x11251f 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[3016, 2992]
    (.letOp (n := 3023) (.exec 0x11251f (fun s => s.RIP = 0x11251f) (addR64R64Effect 0x11251f 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[3016, 2992]
    (.letOp (n := 3024) (.exec 0x112522 (StorePre 0x112522 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x112522 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112522 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3021, 4]
    (b_l110d64_70))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_69 : List UInt8 :=
  [0x4C, 0x89, 0xF8, 0x4C, 0x8B, 0xAC, 0x24, 0x20, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x48, 0x89,
    0xD7, 0x49, 0x89, 0xC2, 0x49, 0x01, 0xF2, 0x48, 0x11, 0xCF, 0x48, 0x8B, 0x74, 0x24, 0x10, 0x48,
    0x89, 0xF0, 0x48, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD1,
    0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48,
    0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49,
    0x89, 0xD0, 0x4C, 0x01, 0xD0, 0x48, 0x89, 0x44, 0x24, 0x60] ++ bytes_l110d64_70

theorem code_l110d64_69 : ∀ x ∈ codeRange 0x1124cd bytes_l110d64_69, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x124cd 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_70

def b_l110d64_68 : Block Op Label signature Reg.count 2936 :=
  .letOp (n := 2936) (.out 0x112476 (mulM64Effect 0x112476 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2934, 4]
    (.letOp (n := 2937) (.out 0x112476 (mulM64Effect 0x112476 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2934, 4]
    (.letOp (n := 2938) (.exec 0x112476 (LoadPre 0x112476 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x112476 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x112476 8 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2934, 4]
    (.letOp (n := 2939) (.out 0x11247e (movR64R64Effect 0x11247e 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2937]
    (.letOp (n := 2940) (.exec 0x11247e (fun s => s.RIP = 0x11247e) (movR64R64Effect 0x11247e 1 2) (Reg.operands [.gpr 2] [])) #v[2937]
    (.letOp (n := 2941) (.out 0x112481 (movR64R64Effect 0x112481 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2936]
    (.letOp (n := 2942) (.exec 0x112481 (fun s => s.RIP = 0x112481) (movR64R64Effect 0x112481 6 0) (Reg.operands [.gpr 0] [])) #v[2936]
    (.letOp (n := 2943) (.out 0x112484 (movR64M64Effect 0x112484 3 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 2944) (.exec 0x112484 (LoadPre 0x112484 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x112484 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112484 3 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2945) (.out 0x11248c (movR64R64Effect 0x11248c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[2943]
    (.letOp (n := 2946) (.exec 0x11248c (fun s => s.RIP = 0x11248c) (movR64R64Effect 0x11248c 0 3) (Reg.operands [.gpr 3] [])) #v[2943]
    (.letOp (n := 2947) (.out 0x11248f (movR64M64Effect 0x11248f 14 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 2948) (.exec 0x11248f (LoadPre 0x11248f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x11248f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11248f 14 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2949) (.out 0x112497 (mulR64Effect 0x112497 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[2947, 2945]
    (.letOp (n := 2950) (.out 0x112497 (mulR64Effect 0x112497 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[2947, 2945]
    (.letOp (n := 2951) (.exec 0x112497 (fun s => s.RIP = 0x112497) (mulR64Effect 0x112497 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[2947, 2945]
    (.letOp (n := 2952) (.out 0x11249a (movR64R64Effect 0x11249a 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2950]
    (.letOp (n := 2953) (.exec 0x11249a (fun s => s.RIP = 0x11249a) (movR64R64Effect 0x11249a 7 2) (Reg.operands [.gpr 2] [])) #v[2950]
    (.letOp (n := 2954) (.out 0x11249d (movR64R64Effect 0x11249d 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[2949]
    (.letOp (n := 2955) (.exec 0x11249d (fun s => s.RIP = 0x11249d) (movR64R64Effect 0x11249d 8 0) (Reg.operands [.gpr 0] [])) #v[2949]
    (.letOp (n := 2956) (.out 0x1124a0 (addR64R64Effect 0x1124a0 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[2954, 2941]
    (.letOp (n := 2957) (.out 0x1124a0 (addR64R64Effect 0x1124a0 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[2954, 2941]
    (.letOp (n := 2958) (.exec 0x1124a0 (fun s => s.RIP = 0x1124a0) (addR64R64Effect 0x1124a0 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[2954, 2941]
    (.letOp (n := 2959) (.out 0x1124a3 (atFlags StatusFlags.CF (adcR64R64Effect 0x1124a3 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[2952, 2939, 2957]
    (.letOp (n := 2960) (.exec 0x1124a3 (fun s => s.RIP = 0x1124a3) (atFlags StatusFlags.CF (adcR64R64Effect 0x1124a3 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2952, 2939, 2957]
    (.letOp (n := 2961) (.out 0x1124a6 (movR64M64Effect 0x1124a6 12 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 2962) (.exec 0x1124a6 (LoadPre 0x1124a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1124a6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1124a6 12 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2963) (.out 0x1124ae (movR64R64Effect 0x1124ae 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[2961]
    (.letOp (n := 2964) (.exec 0x1124ae (fun s => s.RIP = 0x1124ae) (movR64R64Effect 0x1124ae 0 12) (Reg.operands [.gpr 12] [])) #v[2961]
    (.letOp (n := 2965) (.out 0x1124b1 (movR64M64Effect 0x1124b1 5 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 2966) (.exec 0x1124b1 (LoadPre 0x1124b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1124b1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1124b1 5 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2967) (.out 0x1124b9 (mulR64Effect 0x1124b9 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[2965, 2963]
    (.letOp (n := 2968) (.out 0x1124b9 (mulR64Effect 0x1124b9 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[2965, 2963]
    (.letOp (n := 2969) (.exec 0x1124b9 (fun s => s.RIP = 0x1124b9) (mulR64Effect 0x1124b9 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[2965, 2963]
    (.letOp (n := 2970) (.out 0x1124bc (movR64R64Effect 0x1124bc 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2968]
    (.letOp (n := 2971) (.exec 0x1124bc (fun s => s.RIP = 0x1124bc) (movR64R64Effect 0x1124bc 1 2) (Reg.operands [.gpr 2] [])) #v[2968]
    (.letOp (n := 2972) (.out 0x1124bf (movR64R64Effect 0x1124bf 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2967]
    (.letOp (n := 2973) (.exec 0x1124bf (fun s => s.RIP = 0x1124bf) (movR64R64Effect 0x1124bf 6 0) (Reg.operands [.gpr 0] [])) #v[2967]
    (.letOp (n := 2974) (.out 0x1124c2 (addR64R64Effect 0x1124c2 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[2972, 2956]
    (.letOp (n := 2975) (.out 0x1124c2 (addR64R64Effect 0x1124c2 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[2972, 2956]
    (.letOp (n := 2976) (.exec 0x1124c2 (fun s => s.RIP = 0x1124c2) (addR64R64Effect 0x1124c2 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[2972, 2956]
    (.letOp (n := 2977) (.out 0x1124c5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1124c5 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[2970, 2959, 2975]
    (.letOp (n := 2978) (.exec 0x1124c5 (fun s => s.RIP = 0x1124c5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1124c5 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2970, 2959, 2975]
    (.letOp (n := 2979) (.out 0x1124c8 (movR64M64Effect 0x1124c8 15 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 2980) (.exec 0x1124c8 (LoadPre 0x1124c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1124c8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1124c8 15 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l110d64_69)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_68 : List UInt8 :=
  [0x48, 0xF7, 0xA4, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x48, 0x8B,
    0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD8, 0x4C, 0x8B, 0xB4, 0x24, 0x10, 0x01, 0x00,
    0x00, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0, 0x49, 0x01, 0xF0, 0x48, 0x11, 0xCF,
    0x4C, 0x8B, 0xA4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x48, 0x8B, 0xAC, 0x24, 0x18,
    0x01, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x01, 0xC6, 0x48,
    0x11, 0xF9, 0x4C, 0x8B, 0x7C, 0x24, 0x38] ++ bytes_l110d64_69

theorem code_l110d64_68 : ∀ x ∈ codeRange 0x112476 bytes_l110d64_68, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12476 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_69

def b_l110d64_67 : Block Op Label signature Reg.count 2901 :=
  .letOp (n := 2901) (.out 0x112429 (shrR64Effect 0x112429 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2897]
    (.letOp (n := 2902) (.exec 0x112429 (fun s => s.RIP = 0x112429) (shrR64Effect 0x112429 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2897]
    (.letOp (n := 2903) (.out 0x11242d (leaR64Effect 0x11242d 7 (.sib 1 (some 10) 3 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1, .gpr 10] []) (.reg (.gpr 7))) #v[2901, 2895]
    (.letOp (n := 2904) (.exec 0x11242d (fun s => s.RIP = 0x11242d) (leaR64Effect 0x11242d 7 (.sib 1 (some 10) 3 .none)) (Reg.operands [.gpr 1, .gpr 10] [])) #v[2901, 2895]
    (.letOp (n := 2905) (.out 0x112431 (andR64R64Effect 0x112431 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[2858, 2811]
    (.letOp (n := 2906) (.exec 0x112431 (fun s => s.RIP = 0x112431) (andR64R64Effect 0x112431 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[2858, 2811]
    (.letOp (n := 2907) (.out 0x112434 (movR64R64Effect 0x112434 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[2903]
    (.letOp (n := 2908) (.exec 0x112434 (fun s => s.RIP = 0x112434) (movR64R64Effect 0x112434 1 7) (Reg.operands [.gpr 7] [])) #v[2903]
    (.letOp (n := 2909) (.out 0x112437 (shrR64Effect 0x112437 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2907]
    (.letOp (n := 2910) (.exec 0x112437 (fun s => s.RIP = 0x112437) (shrR64Effect 0x112437 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2907]
    (.letOp (n := 2911) (.out 0x11243b (leaR64Effect 0x11243b 6 (.sib 1 (some 9) 3 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1, .gpr 9] []) (.reg (.gpr 6))) #v[2909, 2905]
    (.letOp (n := 2912) (.exec 0x11243b (fun s => s.RIP = 0x11243b) (leaR64Effect 0x11243b 6 (.sib 1 (some 9) 3 .none)) (Reg.operands [.gpr 1, .gpr 9] [])) #v[2909, 2905]
    (.letOp (n := 2913) (.out 0x11243f (movR64R64Effect 0x11243f 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[2911]
    (.letOp (n := 2914) (.exec 0x11243f (fun s => s.RIP = 0x11243f) (movR64R64Effect 0x11243f 1 6) (Reg.operands [.gpr 6] [])) #v[2911]
    (.letOp (n := 2915) (.out 0x112442 (shrR64Effect 0x112442 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2913]
    (.letOp (n := 2916) (.exec 0x112442 (fun s => s.RIP = 0x112442) (shrR64Effect 0x112442 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2913]
    (.letOp (n := 2917) (.out 0x112446 (addR64R64Effect 0x112446 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2915, 2873]
    (.letOp (n := 2918) (.exec 0x112446 (fun s => s.RIP = 0x112446) (addR64R64Effect 0x112446 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2915, 2873]
    (.letOp (n := 2919) (.exec 0x112449 (StorePre 0x112449 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x112449 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112449 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2917, 4]
    (.letOp (n := 2920) (.out 0x11244e (andR64R64Effect 0x11244e 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[2889, 2811]
    (.letOp (n := 2921) (.exec 0x11244e (fun s => s.RIP = 0x11244e) (andR64R64Effect 0x11244e 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[2889, 2811]
    (.letOp (n := 2922) (.exec 0x112451 (StorePre 0x112451 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x112451 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112451 11 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[2920, 4]
    (.letOp (n := 2923) (.out 0x112456 (andR64R64Effect 0x112456 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[2899, 2811]
    (.letOp (n := 2924) (.exec 0x112456 (fun s => s.RIP = 0x112456) (andR64R64Effect 0x112456 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[2899, 2811]
    (.letOp (n := 2925) (.exec 0x112459 (StorePre 0x112459 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x112459 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112459 8 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[2923, 4]
    (.letOp (n := 2926) (.out 0x11245e (andR64R64Effect 0x11245e 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[2903, 2811]
    (.letOp (n := 2927) (.exec 0x11245e (fun s => s.RIP = 0x11245e) (andR64R64Effect 0x11245e 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[2903, 2811]
    (.letOp (n := 2928) (.exec 0x112461 (StorePre 0x112461 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x112461 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112461 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[2926, 4]
    (.letOp (n := 2929) (.out 0x112466 (andR64R64Effect 0x112466 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[2911, 2811]
    (.letOp (n := 2930) (.exec 0x112466 (fun s => s.RIP = 0x112466) (andR64R64Effect 0x112466 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[2911, 2811]
    (.letOp (n := 2931) (.exec 0x112469 (StorePre 0x112469 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x112469 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112469 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[2929, 4]
    (.letOp (n := 2932) (.out 0x11246e (movR64M64Effect 0x11246e 11 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 2933) (.exec 0x11246e (LoadPre 0x11246e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11246e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11246e 11 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2934) (.out 0x112473 (movR64R64Effect 0x112473 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2932]
    (.letOp (n := 2935) (.exec 0x112473 (fun s => s.RIP = 0x112473) (movR64R64Effect 0x112473 0 11) (Reg.operands [.gpr 11] [])) #v[2932]
    (b_l110d64_68)))))))))))))))))))))))))))))))))))

def bytes_l110d64_67 : List UInt8 :=
  [0x48, 0xC1, 0xE9, 0x34, 0x4A, 0x8D, 0x3C, 0xD1, 0x49, 0x21, 0xE9, 0x48, 0x89, 0xF9, 0x48, 0xC1,
    0xE9, 0x34, 0x4A, 0x8D, 0x34, 0xC9, 0x48, 0x89, 0xF1, 0x48, 0xC1, 0xE9, 0x34, 0x48, 0x01, 0xC1,
    0x48, 0x89, 0x4C, 0x24, 0x28, 0x49, 0x21, 0xEB, 0x4C, 0x89, 0x5C, 0x24, 0x40, 0x49, 0x21, 0xE8,
    0x4C, 0x89, 0x44, 0x24, 0x70, 0x48, 0x21, 0xEF, 0x48, 0x89, 0x7C, 0x24, 0x78, 0x48, 0x21, 0xEE,
    0x48, 0x89, 0x74, 0x24, 0x48, 0x4C, 0x8B, 0x5C, 0x24, 0x68, 0x4C, 0x89, 0xD8] ++ bytes_l110d64_68

theorem code_l110d64_67 : ∀ x ∈ codeRange 0x112429 bytes_l110d64_67, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12429 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_68

def b_l110d64_66 : Block Op Label signature Reg.count 2861 :=
  .letOp (n := 2861) (.out 0x1123cd (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1123cd 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2856, 2859]
    (.letOp (n := 2862) (.exec 0x1123cd (fun s => s.RIP = 0x1123cd) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1123cd 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2856, 2859]
    (.letOp (n := 2863) (.out 0x1123d1 (shldR64R64Effect 0x1123d1 5 2 9 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2861, 2858]
    (.letOp (n := 2864) (.exec 0x1123d1 (fun s => s.RIP = 0x1123d1) (shldR64R64Effect 0x1123d1 5 2 9 12) (Reg.operands [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2861, 2858]
    (.letOp (n := 2865) (.out 0x1123d6 (movR64Imm64Effect 0x1123d6 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 2866) (.exec 0x1123d6 (fun s => s.RIP = 0x1123d6) (movR64Imm64Effect 0x1123d6 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2867) (.out 0x1123e0 (andR64R64Effect 0x1123e0 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[2564, 2865]
    (.letOp (n := 2868) (.exec 0x1123e0 (fun s => s.RIP = 0x1123e0) (andR64R64Effect 0x1123e0 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[2564, 2865]
    (.letOp (n := 2869) (.out 0x1123e3 (addR64R64Effect 0x1123e3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[2867, 2863]
    (.letOp (n := 2870) (.exec 0x1123e3 (fun s => s.RIP = 0x1123e3) (addR64R64Effect 0x1123e3 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[2867, 2863]
    (.letOp (n := 2871) (.out 0x1123e6 (leaR64Effect 0x1123e6 0 (.abs (some 8) 3 0x0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2869]
    (.letOp (n := 2872) (.exec 0x1123e6 (fun s => s.RIP = 0x1123e6) (leaR64Effect 0x1123e6 0 (.abs (some 8) 3 0x0)) (Reg.operands [.gpr 8] [])) #v[2869]
    (.letOp (n := 2873) (.out 0x1123ee (andR64M64Effect 0x1123ee 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2871, 4]
    (.letOp (n := 2874) (.exec 0x1123ee (LoadPre 0x1123ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1123ee + BitVec.ofNat 64 8)) 8) (andR64M64Effect 0x1123ee 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2871, 4]
    (.letOp (n := 2875) (.out 0x1123f6 (andR64R64Effect 0x1123f6 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[2663, 2811]
    (.letOp (n := 2876) (.exec 0x1123f6 (fun s => s.RIP = 0x1123f6) (andR64R64Effect 0x1123f6 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[2663, 2811]
    (.letOp (n := 2877) (.out 0x1123f9 (shrR64Effect 0x1123f9 4 8 45) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2869]
    (.letOp (n := 2878) (.exec 0x1123f9 (fun s => s.RIP = 0x1123f9) (shrR64Effect 0x1123f9 4 8 45) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2869]
    (.letOp (n := 2879) (.out 0x1123fd (movR64Imm64Effect 0x1123fd 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2880) (.exec 0x1123fd (fun s => s.RIP = 0x1123fd) (movR64Imm64Effect 0x1123fd 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 2881) (.out 0x112407 (imulR64R64Effect 0x112407 4 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[2877, 2879]
    (.letOp (n := 2882) (.exec 0x112407 (fun s => s.RIP = 0x112407) (imulR64R64Effect 0x112407 4 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[2877, 2879]
    (.letOp (n := 2883) (.out 0x11240b (leaR64Effect 0x11240b 7 (.sib 8 (some 3) 3 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8, .gpr 3] []) (.reg (.gpr 7))) #v[2881, 2875]
    (.letOp (n := 2884) (.exec 0x11240b (fun s => s.RIP = 0x11240b) (leaR64Effect 0x11240b 7 (.sib 8 (some 3) 3 .none)) (Reg.operands [.gpr 8, .gpr 3] [])) #v[2881, 2875]
    (.letOp (n := 2885) (.out 0x11240f (andR64R64Effect 0x11240f 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[2751, 2811]
    (.letOp (n := 2886) (.exec 0x11240f (fun s => s.RIP = 0x11240f) (andR64R64Effect 0x11240f 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[2751, 2811]
    (.letOp (n := 2887) (.out 0x112412 (movR64R64Effect 0x112412 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[2883]
    (.letOp (n := 2888) (.exec 0x112412 (fun s => s.RIP = 0x112412) (movR64R64Effect 0x112412 2 7) (Reg.operands [.gpr 7] [])) #v[2883]
    (.letOp (n := 2889) (.out 0x112415 (movR64R64Effect 0x112415 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[2883]
    (.letOp (n := 2890) (.exec 0x112415 (fun s => s.RIP = 0x112415) (movR64R64Effect 0x112415 11 7) (Reg.operands [.gpr 7] [])) #v[2883]
    (.letOp (n := 2891) (.out 0x112418 (shrR64Effect 0x112418 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2887]
    (.letOp (n := 2892) (.exec 0x112418 (fun s => s.RIP = 0x112418) (shrR64Effect 0x112418 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2887]
    (.letOp (n := 2893) (.out 0x11241c (leaR64Effect 0x11241c 2 (.sib 2 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[2891, 2885]
    (.letOp (n := 2894) (.exec 0x11241c (fun s => s.RIP = 0x11241c) (leaR64Effect 0x11241c 2 (.sib 2 (some 1) 3 .none)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2891, 2885]
    (.letOp (n := 2895) (.out 0x112420 (andR64R64Effect 0x112420 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[2835, 2811]
    (.letOp (n := 2896) (.exec 0x112420 (fun s => s.RIP = 0x112420) (andR64R64Effect 0x112420 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[2835, 2811]
    (.letOp (n := 2897) (.out 0x112423 (movR64R64Effect 0x112423 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2893]
    (.letOp (n := 2898) (.exec 0x112423 (fun s => s.RIP = 0x112423) (movR64R64Effect 0x112423 1 2) (Reg.operands [.gpr 2] [])) #v[2893]
    (.letOp (n := 2899) (.out 0x112426 (movR64R64Effect 0x112426 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2893]
    (.letOp (n := 2900) (.exec 0x112426 (fun s => s.RIP = 0x112426) (movR64R64Effect 0x112426 8 2) (Reg.operands [.gpr 2] [])) #v[2893]
    (b_l110d64_67))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_66 : List UInt8 :=
  [0x48, 0x83, 0xD2, 0x00, 0x4C, 0x0F, 0xA4, 0xCA, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x00, 0x00, 0x49, 0x21, 0xC0, 0x49, 0x01, 0xD0, 0x4A, 0x8D, 0x04, 0xC5, 0x00, 0x00, 0x00,
    0x00, 0x48, 0x23, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0x21, 0xEB, 0x49, 0xC1, 0xE8, 0x2D,
    0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xC2, 0x49, 0x8D,
    0x3C, 0xD8, 0x48, 0x21, 0xE9, 0x48, 0x89, 0xFA, 0x49, 0x89, 0xFB, 0x48, 0xC1, 0xEA, 0x34, 0x48,
    0x8D, 0x14, 0xCA, 0x49, 0x21, 0xEA, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xD0] ++ bytes_l110d64_67

theorem code_l110d64_66 : ∀ x ∈ codeRange 0x1123cd bytes_l110d64_66, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x123cd 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_67

def b_l110d64_65 : Block Op Label signature Reg.count 2813 :=
  .letOp (n := 2813) (.out 0x11237b (andR64R64Effect 0x11237b 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[2809, 2811]
    (.letOp (n := 2814) (.exec 0x11237b (fun s => s.RIP = 0x11237b) (andR64R64Effect 0x11237b 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[2809, 2811]
    (.letOp (n := 2815) (.out 0x11237e (movR64Imm64Effect 0x11237e 7 0x1000003d10) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 2816) (.exec 0x11237e (fun s => s.RIP = 0x11237e) (movR64Imm64Effect 0x11237e 7 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2817) (.out 0x112388 (mulR64Effect 0x112388 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2815, 2813]
    (.letOp (n := 2818) (.out 0x112388 (mulR64Effect 0x112388 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2815, 2813]
    (.letOp (n := 2819) (.exec 0x112388 (fun s => s.RIP = 0x112388) (mulR64Effect 0x112388 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2815, 2813]
    (.letOp (n := 2820) (.out 0x11238b (addR64M64Effect 0x11238b 10 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[2772, 4]
    (.letOp (n := 2821) (.out 0x11238b (addR64M64Effect 0x11238b 10 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[2772, 4]
    (.letOp (n := 2822) (.exec 0x11238b (LoadPre 0x11238b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11238b + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11238b 10 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[2772, 4]
    (.letOp (n := 2823) (.out 0x112390 (atFlags StatusFlags.CF (adcR64M64Effect 0x112390 14 (.sib 4 none 0 (.d8 0x20)))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 14))) #v[2770, 4, 2821]
    (.letOp (n := 2824) (.exec 0x112390 (LoadPre 0x112390 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x112390 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x112390 14 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2770, 4, 2821]
    (.letOp (n := 2825) (.out 0x112395 (addR64R64Effect 0x112395 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[2820, 2781]
    (.letOp (n := 2826) (.out 0x112395 (addR64R64Effect 0x112395 10 12) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 12] []) (.flag .CF)) #v[2820, 2781]
    (.letOp (n := 2827) (.exec 0x112395 (fun s => s.RIP = 0x112395) (addR64R64Effect 0x112395 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[2820, 2781]
    (.letOp (n := 2828) (.out 0x112398 (atFlags StatusFlags.CF (adcR64R64Effect 0x112398 14 6)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2823, 2779, 2826]
    (.letOp (n := 2829) (.exec 0x112398 (fun s => s.RIP = 0x112398) (atFlags StatusFlags.CF (adcR64R64Effect 0x112398 14 6)) (Reg.operands [.gpr 14, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2823, 2779, 2826]
    (.letOp (n := 2830) (.out 0x11239b (addR64R64Effect 0x11239b 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[2825, 2817]
    (.letOp (n := 2831) (.out 0x11239b (addR64R64Effect 0x11239b 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[2825, 2817]
    (.letOp (n := 2832) (.exec 0x11239b (fun s => s.RIP = 0x11239b) (addR64R64Effect 0x11239b 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2825, 2817]
    (.letOp (n := 2833) (.out 0x11239e (atFlags StatusFlags.CF (adcR64R64Effect 0x11239e 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2828, 2818, 2831]
    (.letOp (n := 2834) (.exec 0x11239e (fun s => s.RIP = 0x11239e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11239e 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2828, 2818, 2831]
    (.letOp (n := 2835) (.out 0x1123a1 (addR64R64Effect 0x1123a1 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15] []) (.reg (.gpr 10))) #v[2830, 2756]
    (.letOp (n := 2836) (.out 0x1123a1 (addR64R64Effect 0x1123a1 10 15) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 15] []) (.flag .CF)) #v[2830, 2756]
    (.letOp (n := 2837) (.exec 0x1123a1 (fun s => s.RIP = 0x1123a1) (addR64R64Effect 0x1123a1 10 15) (Reg.operands [.gpr 10, .gpr 15] [])) #v[2830, 2756]
    (.letOp (n := 2838) (.out 0x1123a4 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1123a4 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2833, 2836]
    (.letOp (n := 2839) (.exec 0x1123a4 (fun s => s.RIP = 0x1123a4) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1123a4 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2833, 2836]
    (.letOp (n := 2840) (.out 0x1123a8 (shldR64R64Effect 0x1123a8 5 9 11 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2807, 2804]
    (.letOp (n := 2841) (.exec 0x1123a8 (fun s => s.RIP = 0x1123a8) (shldR64R64Effect 0x1123a8 5 9 11 12) (Reg.operands [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2807, 2804]
    (.letOp (n := 2842) (.out 0x1123ad (shldR64R64Effect 0x1123ad 5 14 10 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[2838, 2835]
    (.letOp (n := 2843) (.exec 0x1123ad (fun s => s.RIP = 0x1123ad) (shldR64R64Effect 0x1123ad 5 14 10 12) (Reg.operands [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2838, 2835]
    (.letOp (n := 2844) (.out 0x1123b2 (movR64R64Effect 0x1123b2 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2840]
    (.letOp (n := 2845) (.exec 0x1123b2 (fun s => s.RIP = 0x1123b2) (movR64R64Effect 0x1123b2 0 9) (Reg.operands [.gpr 9] [])) #v[2840]
    (.letOp (n := 2846) (.out 0x1123b5 (mulR64Effect 0x1123b5 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2815, 2844]
    (.letOp (n := 2847) (.out 0x1123b5 (mulR64Effect 0x1123b5 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2815, 2844]
    (.letOp (n := 2848) (.exec 0x1123b5 (fun s => s.RIP = 0x1123b5) (mulR64Effect 0x1123b5 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2815, 2844]
    (.letOp (n := 2849) (.out 0x1123b8 (movR64M64Effect 0x1123b8 9 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 2850) (.exec 0x1123b8 (LoadPre 0x1123b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1123b8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1123b8 9 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2851) (.out 0x1123c0 (andR64R64Effect 0x1123c0 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[2849, 2811]
    (.letOp (n := 2852) (.exec 0x1123c0 (fun s => s.RIP = 0x1123c0) (andR64R64Effect 0x1123c0 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[2849, 2811]
    (.letOp (n := 2853) (.out 0x1123c3 (addR64R64Effect 0x1123c3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[2851, 2846]
    (.letOp (n := 2854) (.out 0x1123c3 (addR64R64Effect 0x1123c3 9 0) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 0] []) (.flag .CF)) #v[2851, 2846]
    (.letOp (n := 2855) (.exec 0x1123c3 (fun s => s.RIP = 0x1123c3) (addR64R64Effect 0x1123c3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2851, 2846]
    (.letOp (n := 2856) (.out 0x1123c6 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1123c6 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2847, 2854]
    (.letOp (n := 2857) (.exec 0x1123c6 (fun s => s.RIP = 0x1123c6) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1123c6 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2847, 2854]
    (.letOp (n := 2858) (.out 0x1123ca (addR64R64Effect 0x1123ca 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[2853, 2842]
    (.letOp (n := 2859) (.out 0x1123ca (addR64R64Effect 0x1123ca 9 14) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 14] []) (.flag .CF)) #v[2853, 2842]
    (.letOp (n := 2860) (.exec 0x1123ca (fun s => s.RIP = 0x1123ca) (addR64R64Effect 0x1123ca 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[2853, 2842]
    (b_l110d64_66))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_65 : List UInt8 :=
  [0x48, 0x21, 0xE8, 0x48, 0xBF, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7,
    0x4C, 0x03, 0x54, 0x24, 0x50, 0x4C, 0x13, 0x74, 0x24, 0x20, 0x4D, 0x01, 0xE2, 0x49, 0x11, 0xF6,
    0x49, 0x01, 0xC2, 0x49, 0x11, 0xD6, 0x4D, 0x01, 0xFA, 0x49, 0x83, 0xD6, 0x00, 0x4D, 0x0F, 0xA4,
    0xD9, 0x0C, 0x4D, 0x0F, 0xA4, 0xD6, 0x0C, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0xE7, 0x4C, 0x8B, 0x8C,
    0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0x21, 0xE9, 0x49, 0x01, 0xC1, 0x48, 0x83, 0xD2, 0x00, 0x4D,
    0x01, 0xF1] ++ bytes_l110d64_66

theorem code_l110d64_65 : ∀ x ∈ codeRange 0x11237b bytes_l110d64_65, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1237b 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_66

def b_l110d64_64 : Block Op Label signature Reg.count 2767 :=
  .letOp (n := 2767) (.out 0x11232d (mulM64Effect 0x11232d 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2765, 4]
    (.letOp (n := 2768) (.out 0x11232d (mulM64Effect 0x11232d 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2765, 4]
    (.letOp (n := 2769) (.exec 0x11232d (LoadPre 0x11232d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11232d + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11232d 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2765, 4]
    (.letOp (n := 2770) (.out 0x112332 (movR64R64Effect 0x112332 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2768]
    (.letOp (n := 2771) (.exec 0x112332 (fun s => s.RIP = 0x112332) (movR64R64Effect 0x112332 14 2) (Reg.operands [.gpr 2] [])) #v[2768]
    (.letOp (n := 2772) (.out 0x112335 (movR64R64Effect 0x112335 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2767]
    (.letOp (n := 2773) (.exec 0x112335 (fun s => s.RIP = 0x112335) (movR64R64Effect 0x112335 10 0) (Reg.operands [.gpr 0] [])) #v[2767]
    (.letOp (n := 2774) (.out 0x112338 (movR64M64Effect 0x112338 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2775) (.exec 0x112338 (LoadPre 0x112338 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x112338 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112338 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2776) (.out 0x11233d (mulM64Effect 0x11233d 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2774, 4]
    (.letOp (n := 2777) (.out 0x11233d (mulM64Effect 0x11233d 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2774, 4]
    (.letOp (n := 2778) (.exec 0x11233d (LoadPre 0x11233d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11233d + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11233d 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2774, 4]
    (.letOp (n := 2779) (.out 0x112342 (movR64R64Effect 0x112342 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2777]
    (.letOp (n := 2780) (.exec 0x112342 (fun s => s.RIP = 0x112342) (movR64R64Effect 0x112342 6 2) (Reg.operands [.gpr 2] [])) #v[2777]
    (.letOp (n := 2781) (.out 0x112345 (movR64R64Effect 0x112345 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[2776]
    (.letOp (n := 2782) (.exec 0x112345 (fun s => s.RIP = 0x112345) (movR64R64Effect 0x112345 12 0) (Reg.operands [.gpr 0] [])) #v[2776]
    (.letOp (n := 2783) (.out 0x112348 (movR64R64Effect 0x112348 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2695]
    (.letOp (n := 2784) (.exec 0x112348 (fun s => s.RIP = 0x112348) (movR64R64Effect 0x112348 0 9) (Reg.operands [.gpr 9] [])) #v[2695]
    (.letOp (n := 2785) (.out 0x11234b (mulM64Effect 0x11234b 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2783, 4]
    (.letOp (n := 2786) (.out 0x11234b (mulM64Effect 0x11234b 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2783, 4]
    (.letOp (n := 2787) (.exec 0x11234b (LoadPre 0x11234b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11234b + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11234b 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2783, 4]
    (.letOp (n := 2788) (.out 0x112350 (movR64R64Effect 0x112350 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2786]
    (.letOp (n := 2789) (.exec 0x112350 (fun s => s.RIP = 0x112350) (movR64R64Effect 0x112350 9 2) (Reg.operands [.gpr 2] [])) #v[2786]
    (.letOp (n := 2790) (.out 0x112353 (movR64R64Effect 0x112353 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[2785]
    (.letOp (n := 2791) (.exec 0x112353 (fun s => s.RIP = 0x112353) (movR64R64Effect 0x112353 5 0) (Reg.operands [.gpr 0] [])) #v[2785]
    (.letOp (n := 2792) (.out 0x112356 (movR64R64Effect 0x112356 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2706]
    (.letOp (n := 2793) (.exec 0x112356 (fun s => s.RIP = 0x112356) (movR64R64Effect 0x112356 0 11) (Reg.operands [.gpr 11] [])) #v[2706]
    (.letOp (n := 2794) (.out 0x112359 (mulM64Effect 0x112359 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2792, 4]
    (.letOp (n := 2795) (.out 0x112359 (mulM64Effect 0x112359 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2792, 4]
    (.letOp (n := 2796) (.exec 0x112359 (LoadPre 0x112359 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x112359 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x112359 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2792, 4]
    (.letOp (n := 2797) (.out 0x11235e (movR64R64Effect 0x11235e 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[2794]
    (.letOp (n := 2798) (.exec 0x11235e (fun s => s.RIP = 0x11235e) (movR64R64Effect 0x11235e 11 0) (Reg.operands [.gpr 0] [])) #v[2794]
    (.letOp (n := 2799) (.out 0x112361 (addR64R64Effect 0x112361 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[2797, 2790]
    (.letOp (n := 2800) (.out 0x112361 (addR64R64Effect 0x112361 11 5) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 5] []) (.flag .CF)) #v[2797, 2790]
    (.letOp (n := 2801) (.exec 0x112361 (fun s => s.RIP = 0x112361) (addR64R64Effect 0x112361 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[2797, 2790]
    (.letOp (n := 2802) (.out 0x112364 (atFlags StatusFlags.CF (adcR64R64Effect 0x112364 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[2788, 2795, 2800]
    (.letOp (n := 2803) (.exec 0x112364 (fun s => s.RIP = 0x112364) (atFlags StatusFlags.CF (adcR64R64Effect 0x112364 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2788, 2795, 2800]
    (.letOp (n := 2804) (.out 0x112367 (addR64R64Effect 0x112367 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13] []) (.reg (.gpr 11))) #v[2799, 2730]
    (.letOp (n := 2805) (.out 0x112367 (addR64R64Effect 0x112367 11 13) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 13] []) (.flag .CF)) #v[2799, 2730]
    (.letOp (n := 2806) (.exec 0x112367 (fun s => s.RIP = 0x112367) (addR64R64Effect 0x112367 11 13) (Reg.operands [.gpr 11, .gpr 13] [])) #v[2799, 2730]
    (.letOp (n := 2807) (.out 0x11236a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11236a 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[2802, 2805]
    (.letOp (n := 2808) (.exec 0x11236a (fun s => s.RIP = 0x11236a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11236a 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2802, 2805]
    (.letOp (n := 2809) (.out 0x11236e (movR64R64Effect 0x11236e 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2804]
    (.letOp (n := 2810) (.exec 0x11236e (fun s => s.RIP = 0x11236e) (movR64R64Effect 0x11236e 0 11) (Reg.operands [.gpr 11] [])) #v[2804]
    (.letOp (n := 2811) (.out 0x112371 (movR64Imm64Effect 0x112371 5 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 2812) (.exec 0x112371 (fun s => s.RIP = 0x112371) (movR64Imm64Effect 0x112371 5 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l110d64_65))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_64 : List UInt8 :=
  [0x48, 0xF7, 0x64, 0x24, 0x70, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC2, 0x48, 0x8B, 0x44, 0x24, 0x60,
    0x48, 0xF7, 0x64, 0x24, 0x48, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x4C, 0x89, 0xC8, 0x48, 0xF7,
    0x64, 0x24, 0x40, 0x49, 0x89, 0xD1, 0x48, 0x89, 0xC5, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0x64, 0x24,
    0x28, 0x49, 0x89, 0xC3, 0x49, 0x01, 0xEB, 0x49, 0x11, 0xD1, 0x4D, 0x01, 0xEB, 0x49, 0x83, 0xD1,
    0x00, 0x4C, 0x89, 0xD8, 0x48, 0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] ++ bytes_l110d64_65

theorem code_l110d64_64 : ∀ x ∈ codeRange 0x11232d bytes_l110d64_64, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1232d 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_65

def b_l110d64_63 : Block Op Label signature Reg.count 2723 :=
  .letOp (n := 2723) (.out 0x1122cf (atFlags StatusFlags.CF (adcR64R64Effect 0x1122cf 13 2)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[2718, 2713, 2721]
    (.letOp (n := 2724) (.exec 0x1122cf (fun s => s.RIP = 0x1122cf) (atFlags StatusFlags.CF (adcR64R64Effect 0x1122cf 13 2)) (Reg.operands [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2718, 2713, 2721]
    (.letOp (n := 2725) (.out 0x1122d2 (addR64R64Effect 0x1122d2 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[2720, 2644]
    (.letOp (n := 2726) (.out 0x1122d2 (addR64R64Effect 0x1122d2 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[2720, 2644]
    (.letOp (n := 2727) (.exec 0x1122d2 (fun s => s.RIP = 0x1122d2) (addR64R64Effect 0x1122d2 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[2720, 2644]
    (.letOp (n := 2728) (.out 0x1122d5 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1122d5 13 0x0)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[2723, 2726]
    (.letOp (n := 2729) (.exec 0x1122d5 (fun s => s.RIP = 0x1122d5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1122d5 13 0x0)) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2723, 2726]
    (.letOp (n := 2730) (.out 0x1122d9 (shldR64R64Effect 0x1122d9 5 13 0 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[2728, 2725]
    (.letOp (n := 2731) (.exec 0x1122d9 (fun s => s.RIP = 0x1122d9) (shldR64R64Effect 0x1122d9 5 13 0 12) (Reg.operands [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2728, 2725]
    (.letOp (n := 2732) (.out 0x1122de (movR64Imm64Effect 0x1122de 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2733) (.exec 0x1122de (fun s => s.RIP = 0x1122de) (movR64Imm64Effect 0x1122de 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2734) (.out 0x1122e8 (andR64R64Effect 0x1122e8 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[2725, 2732]
    (.letOp (n := 2735) (.exec 0x1122e8 (fun s => s.RIP = 0x1122e8) (andR64R64Effect 0x1122e8 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[2725, 2732]
    (.letOp (n := 2736) (.out 0x1122eb (movR64Imm64Effect 0x1122eb 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2737) (.exec 0x1122eb (fun s => s.RIP = 0x1122eb) (movR64Imm64Effect 0x1122eb 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2738) (.out 0x1122f5 (mulR64Effect 0x1122f5 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2736, 2734]
    (.letOp (n := 2739) (.out 0x1122f5 (mulR64Effect 0x1122f5 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2736, 2734]
    (.letOp (n := 2740) (.exec 0x1122f5 (fun s => s.RIP = 0x1122f5) (mulR64Effect 0x1122f5 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2736, 2734]
    (.letOp (n := 2741) (.out 0x1122f8 (addR64M64Effect 0x1122f8 1 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[2684, 4]
    (.letOp (n := 2742) (.out 0x1122f8 (addR64M64Effect 0x1122f8 1 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 4] []) (.flag .CF)) #v[2684, 4]
    (.letOp (n := 2743) (.exec 0x1122f8 (LoadPre 0x1122f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1122f8 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x1122f8 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2684, 4]
    (.letOp (n := 2744) (.out 0x112300 (atFlags StatusFlags.CF (adcR64M64Effect 0x112300 15 (.sib 4 none 0 (.d8 0x50)))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 15))) #v[2682, 4, 2742]
    (.letOp (n := 2745) (.exec 0x112300 (LoadPre 0x112300 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x112300 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x112300 15 (.sib 4 none 0 (.d8 0x50)))) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2682, 4, 2742]
    (.letOp (n := 2746) (.out 0x112305 (addR64R64Effect 0x112305 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2741, 2738]
    (.letOp (n := 2747) (.out 0x112305 (addR64R64Effect 0x112305 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[2741, 2738]
    (.letOp (n := 2748) (.exec 0x112305 (fun s => s.RIP = 0x112305) (addR64R64Effect 0x112305 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2741, 2738]
    (.letOp (n := 2749) (.out 0x112308 (atFlags StatusFlags.CF (adcR64R64Effect 0x112308 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[2744, 2739, 2747]
    (.letOp (n := 2750) (.exec 0x112308 (fun s => s.RIP = 0x112308) (atFlags StatusFlags.CF (adcR64R64Effect 0x112308 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2744, 2739, 2747]
    (.letOp (n := 2751) (.out 0x11230b (addR64R64Effect 0x11230b 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[2746, 2668]
    (.letOp (n := 2752) (.out 0x11230b (addR64R64Effect 0x11230b 1 5) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 5] []) (.flag .CF)) #v[2746, 2668]
    (.letOp (n := 2753) (.exec 0x11230b (fun s => s.RIP = 0x11230b) (addR64R64Effect 0x11230b 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[2746, 2668]
    (.letOp (n := 2754) (.out 0x11230e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11230e 15 0x0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[2749, 2752]
    (.letOp (n := 2755) (.exec 0x11230e (fun s => s.RIP = 0x11230e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11230e 15 0x0)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2749, 2752]
    (.letOp (n := 2756) (.out 0x112312 (shldR64R64Effect 0x112312 5 15 1 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[2754, 2751]
    (.letOp (n := 2757) (.exec 0x112312 (fun s => s.RIP = 0x112312) (shldR64R64Effect 0x112312 5 15 1 12) (Reg.operands [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2754, 2751]
    (.letOp (n := 2758) (.out 0x112317 (movR64M64Effect 0x112317 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2759) (.exec 0x112317 (LoadPre 0x112317 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x112317 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112317 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2760) (.out 0x11231c (mulR64Effect 0x11231c 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2710, 2758]
    (.letOp (n := 2761) (.out 0x11231c (mulR64Effect 0x11231c 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2710, 2758]
    (.letOp (n := 2762) (.exec 0x11231c (fun s => s.RIP = 0x11231c) (mulR64Effect 0x11231c 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2710, 2758]
    (.letOp (n := 2763) (.exec 0x11231f (StorePre 0x11231f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11231f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11231f 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2761, 4]
    (.letOp (n := 2764) (.exec 0x112324 (StorePre 0x112324 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x112324 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112324 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2760, 4]
    (.letOp (n := 2765) (.out 0x112329 (movR64M64Effect 0x112329 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2766) (.exec 0x112329 (LoadPre 0x112329 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112329 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112329 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l110d64_64))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_63 : List UInt8 :=
  [0x49, 0x11, 0xD5, 0x4C, 0x01, 0xE0, 0x49, 0x83, 0xD5, 0x00, 0x49, 0x0F, 0xA4, 0xC5, 0x0C, 0x48,
    0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D,
    0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x03, 0x8C, 0x24, 0x88, 0x00, 0x00,
    0x00, 0x4C, 0x13, 0x7C, 0x24, 0x50, 0x48, 0x01, 0xC1, 0x49, 0x11, 0xD7, 0x48, 0x01, 0xE9, 0x49,
    0x83, 0xD7, 0x00, 0x49, 0x0F, 0xA4, 0xCF, 0x0C, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0xF7, 0xE7,
    0x48, 0x89, 0x54, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0x8B, 0x04, 0x24] ++ bytes_l110d64_64

theorem code_l110d64_63 : ∀ x ∈ codeRange 0x1122cf bytes_l110d64_63, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x122cf 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_64

def b_l110d64_62 : Block Op Label signature Reg.count 2677 :=
  .letOp (n := 2677) (.out 0x112287 (movR64R64Effect 0x112287 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2584]
    (.letOp (n := 2678) (.exec 0x112287 (fun s => s.RIP = 0x112287) (movR64R64Effect 0x112287 0 11) (Reg.operands [.gpr 11] [])) #v[2584]
    (.letOp (n := 2679) (.out 0x11228a (mulM64Effect 0x11228a 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2677, 4]
    (.letOp (n := 2680) (.out 0x11228a (mulM64Effect 0x11228a 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2677, 4]
    (.letOp (n := 2681) (.exec 0x11228a (LoadPre 0x11228a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11228a + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11228a 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2677, 4]
    (.letOp (n := 2682) (.out 0x11228f (movR64R64Effect 0x11228f 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2680]
    (.letOp (n := 2683) (.exec 0x11228f (fun s => s.RIP = 0x11228f) (movR64R64Effect 0x11228f 15 2) (Reg.operands [.gpr 2] [])) #v[2680]
    (.letOp (n := 2684) (.out 0x112292 (movR64R64Effect 0x112292 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[2679]
    (.letOp (n := 2685) (.exec 0x112292 (fun s => s.RIP = 0x112292) (movR64R64Effect 0x112292 1 0) (Reg.operands [.gpr 0] [])) #v[2679]
    (.letOp (n := 2686) (.out 0x112295 (movR64R64Effect 0x112295 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[2597]
    (.letOp (n := 2687) (.exec 0x112295 (fun s => s.RIP = 0x112295) (movR64R64Effect 0x112295 0 10) (Reg.operands [.gpr 10] [])) #v[2597]
    (.letOp (n := 2688) (.out 0x112298 (mulM64Effect 0x112298 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2686, 4]
    (.letOp (n := 2689) (.out 0x112298 (mulM64Effect 0x112298 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2686, 4]
    (.letOp (n := 2690) (.exec 0x112298 (LoadPre 0x112298 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x112298 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x112298 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2686, 4]
    (.letOp (n := 2691) (.out 0x11229d (movR64R64Effect 0x11229d 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2689]
    (.letOp (n := 2692) (.exec 0x11229d (fun s => s.RIP = 0x11229d) (movR64R64Effect 0x11229d 6 2) (Reg.operands [.gpr 2] [])) #v[2689]
    (.letOp (n := 2693) (.out 0x1122a0 (movR64R64Effect 0x1122a0 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[2688]
    (.letOp (n := 2694) (.exec 0x1122a0 (fun s => s.RIP = 0x1122a0) (movR64R64Effect 0x1122a0 14 0) (Reg.operands [.gpr 0] [])) #v[2688]
    (.letOp (n := 2695) (.out 0x1122a3 (movR64M64Effect 0x1122a3 9 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 2696) (.exec 0x1122a3 (LoadPre 0x1122a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1122a3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1122a3 9 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2697) (.out 0x1122a8 (movR64R64Effect 0x1122a8 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2695]
    (.letOp (n := 2698) (.exec 0x1122a8 (fun s => s.RIP = 0x1122a8) (movR64R64Effect 0x1122a8 0 9) (Reg.operands [.gpr 9] [])) #v[2695]
    (.letOp (n := 2699) (.out 0x1122ab (mulM64Effect 0x1122ab 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2697, 4]
    (.letOp (n := 2700) (.out 0x1122ab (mulM64Effect 0x1122ab 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2697, 4]
    (.letOp (n := 2701) (.exec 0x1122ab (LoadPre 0x1122ab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1122ab + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1122ab 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2697, 4]
    (.letOp (n := 2702) (.out 0x1122b0 (movR64R64Effect 0x1122b0 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2700]
    (.letOp (n := 2703) (.exec 0x1122b0 (fun s => s.RIP = 0x1122b0) (movR64R64Effect 0x1122b0 13 2) (Reg.operands [.gpr 2] [])) #v[2700]
    (.letOp (n := 2704) (.out 0x1122b3 (movR64R64Effect 0x1122b3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2699]
    (.letOp (n := 2705) (.exec 0x1122b3 (fun s => s.RIP = 0x1122b3) (movR64R64Effect 0x1122b3 10 0) (Reg.operands [.gpr 0] [])) #v[2699]
    (.letOp (n := 2706) (.out 0x1122b6 (movR64M64Effect 0x1122b6 11 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 2707) (.exec 0x1122b6 (LoadPre 0x1122b6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1122b6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1122b6 11 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2708) (.out 0x1122bb (movR64R64Effect 0x1122bb 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2706]
    (.letOp (n := 2709) (.exec 0x1122bb (fun s => s.RIP = 0x1122bb) (movR64R64Effect 0x1122bb 0 11) (Reg.operands [.gpr 11] [])) #v[2706]
    (.letOp (n := 2710) (.out 0x1122be (movR64M64Effect 0x1122be 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 2711) (.exec 0x1122be (LoadPre 0x1122be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1122be + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1122be 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2712) (.out 0x1122c3 (mulR64Effect 0x1122c3 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2710, 2708]
    (.letOp (n := 2713) (.out 0x1122c3 (mulR64Effect 0x1122c3 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2710, 2708]
    (.letOp (n := 2714) (.exec 0x1122c3 (fun s => s.RIP = 0x1122c3) (mulR64Effect 0x1122c3 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2710, 2708]
    (.letOp (n := 2715) (.out 0x1122c6 (addR64R64Effect 0x1122c6 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[2704, 2693]
    (.letOp (n := 2716) (.out 0x1122c6 (addR64R64Effect 0x1122c6 10 14) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 14] []) (.flag .CF)) #v[2704, 2693]
    (.letOp (n := 2717) (.exec 0x1122c6 (fun s => s.RIP = 0x1122c6) (addR64R64Effect 0x1122c6 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[2704, 2693]
    (.letOp (n := 2718) (.out 0x1122c9 (atFlags StatusFlags.CF (adcR64R64Effect 0x1122c9 13 6)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[2702, 2691, 2716]
    (.letOp (n := 2719) (.exec 0x1122c9 (fun s => s.RIP = 0x1122c9) (atFlags StatusFlags.CF (adcR64R64Effect 0x1122c9 13 6)) (Reg.operands [.gpr 13, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2702, 2691, 2716]
    (.letOp (n := 2720) (.out 0x1122cc (addR64R64Effect 0x1122cc 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[2712, 2715]
    (.letOp (n := 2721) (.out 0x1122cc (addR64R64Effect 0x1122cc 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[2712, 2715]
    (.letOp (n := 2722) (.exec 0x1122cc (fun s => s.RIP = 0x1122cc) (addR64R64Effect 0x1122cc 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[2712, 2715]
    (b_l110d64_63))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_62 : List UInt8 :=
  [0x4C, 0x89, 0xD8, 0x48, 0xF7, 0x64, 0x24, 0x48, 0x49, 0x89, 0xD7, 0x48, 0x89, 0xC1, 0x4C, 0x89,
    0xD0, 0x48, 0xF7, 0x64, 0x24, 0x40, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC6, 0x4C, 0x8B, 0x4C, 0x24,
    0x78, 0x4C, 0x89, 0xC8, 0x48, 0xF7, 0x64, 0x24, 0x28, 0x49, 0x89, 0xD5, 0x49, 0x89, 0xC2, 0x4C,
    0x8B, 0x5C, 0x24, 0x08, 0x4C, 0x89, 0xD8, 0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0xF7, 0xE7, 0x4D,
    0x01, 0xF2, 0x49, 0x11, 0xF5, 0x4C, 0x01, 0xD0] ++ bytes_l110d64_63

theorem code_l110d64_62 : ∀ x ∈ codeRange 0x112287 bytes_l110d64_62, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12287 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_63

def b_l110d64_61 : Block Op Label signature Reg.count 2634 :=
  .letOp (n := 2634) (.out 0x112229 (addR64R64Effect 0x112229 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[2621, 2629]
    (.letOp (n := 2635) (.out 0x112229 (addR64R64Effect 0x112229 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[2621, 2629]
    (.letOp (n := 2636) (.exec 0x112229 (fun s => s.RIP = 0x112229) (addR64R64Effect 0x112229 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[2621, 2629]
    (.letOp (n := 2637) (.out 0x11222c (atFlags StatusFlags.CF (adcR64R64Effect 0x11222c 12 2)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[2632, 2622, 2635]
    (.letOp (n := 2638) (.exec 0x11222c (fun s => s.RIP = 0x11222c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11222c 12 2)) (Reg.operands [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2632, 2622, 2635]
    (.letOp (n := 2639) (.out 0x11222f (addR64R64Effect 0x11222f 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2634, 2569]
    (.letOp (n := 2640) (.out 0x11222f (addR64R64Effect 0x11222f 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[2634, 2569]
    (.letOp (n := 2641) (.exec 0x11222f (fun s => s.RIP = 0x11222f) (addR64R64Effect 0x11222f 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2634, 2569]
    (.letOp (n := 2642) (.out 0x112232 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112232 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[2637, 2640]
    (.letOp (n := 2643) (.exec 0x112232 (fun s => s.RIP = 0x112232) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112232 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2637, 2640]
    (.letOp (n := 2644) (.out 0x112236 (shldR64R64Effect 0x112236 5 12 0 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[2642, 2639]
    (.letOp (n := 2645) (.exec 0x112236 (fun s => s.RIP = 0x112236) (shldR64R64Effect 0x112236 5 12 0 12) (Reg.operands [.gpr 12, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2642, 2639]
    (.letOp (n := 2646) (.out 0x11223b (shlR64Effect 0x11223b 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2639]
    (.letOp (n := 2647) (.exec 0x11223b (fun s => s.RIP = 0x11223b) (shlR64Effect 0x11223b 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2639]
    (.letOp (n := 2648) (.out 0x11223f (movR64Imm64Effect 0x11223f 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 2649) (.exec 0x11223f (fun s => s.RIP = 0x11223f) (movR64Imm64Effect 0x11223f 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 2650) (.out 0x112249 (andR64R64Effect 0x112249 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2646, 2648]
    (.letOp (n := 2651) (.exec 0x112249 (fun s => s.RIP = 0x112249) (andR64R64Effect 0x112249 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2646, 2648]
    (.letOp (n := 2652) (.out 0x11224c (orR64R64Effect 0x11224c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[2650, 2595]
    (.letOp (n := 2653) (.exec 0x11224c (fun s => s.RIP = 0x11224c) (orR64R64Effect 0x11224c 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[2650, 2595]
    (.letOp (n := 2654) (.out 0x11224f (movR64Imm64Effect 0x11224f 7 0x1000003d1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 2655) (.exec 0x11224f (fun s => s.RIP = 0x11224f) (movR64Imm64Effect 0x11224f 7 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 2656) (.out 0x112259 (mulR64Effect 0x112259 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2654, 2652]
    (.letOp (n := 2657) (.out 0x112259 (mulR64Effect 0x112259 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2654, 2652]
    (.letOp (n := 2658) (.exec 0x112259 (fun s => s.RIP = 0x112259) (mulR64Effect 0x112259 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2654, 2652]
    (.letOp (n := 2659) (.out 0x11225c (movR64R64Effect 0x11225c 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2657]
    (.letOp (n := 2660) (.exec 0x11225c (fun s => s.RIP = 0x11225c) (movR64R64Effect 0x11225c 5 2) (Reg.operands [.gpr 2] [])) #v[2657]
    (.letOp (n := 2661) (.out 0x11225f (movR64R64Effect 0x11225f 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[2656]
    (.letOp (n := 2662) (.exec 0x11225f (fun s => s.RIP = 0x11225f) (movR64R64Effect 0x11225f 3 0) (Reg.operands [.gpr 0] [])) #v[2656]
    (.letOp (n := 2663) (.out 0x112262 (addR64M64Effect 0x112262 3 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[2661, 4]
    (.letOp (n := 2664) (.out 0x112262 (addR64M64Effect 0x112262 3 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[2661, 4]
    (.letOp (n := 2665) (.exec 0x112262 (LoadPre 0x112262 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x112262 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x112262 3 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[2661, 4]
    (.letOp (n := 2666) (.out 0x11226a (atFlags StatusFlags.CF (adcR64M64Effect 0x11226a 5 (.sib 4 none 0 (.d8 0x50)))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 5))) #v[2659, 4, 2664]
    (.letOp (n := 2667) (.exec 0x11226a (LoadPre 0x11226a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11226a + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11226a 5 (.sib 4 none 0 (.d8 0x50)))) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2659, 4, 2664]
    (.letOp (n := 2668) (.out 0x11226f (shldR64R64Effect 0x11226f 5 5 3 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[2666, 2663]
    (.letOp (n := 2669) (.exec 0x11226f (fun s => s.RIP = 0x11226f) (shldR64R64Effect 0x11226f 5 5 3 12) (Reg.operands [.gpr 5, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2666, 2663]
    (.letOp (n := 2670) (.out 0x112274 (movR64R64Effect 0x112274 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[2575]
    (.letOp (n := 2671) (.exec 0x112274 (fun s => s.RIP = 0x112274) (movR64R64Effect 0x112274 0 15) (Reg.operands [.gpr 15] [])) #v[2575]
    (.letOp (n := 2672) (.out 0x112277 (mulR64Effect 0x112277 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[2619, 2670]
    (.letOp (n := 2673) (.out 0x112277 (mulR64Effect 0x112277 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[2619, 2670]
    (.letOp (n := 2674) (.exec 0x112277 (fun s => s.RIP = 0x112277) (mulR64Effect 0x112277 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2619, 2670]
    (.letOp (n := 2675) (.exec 0x11227a (StorePre 0x11227a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11227a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11227a 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2673, 4]
    (.letOp (n := 2676) (.exec 0x11227f (StorePre 0x11227f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11227f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11227f 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2672, 4]
    (b_l110d64_62)))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_61 : List UInt8 :=
  [0x48, 0x01, 0xD8, 0x49, 0x11, 0xD4, 0x48, 0x01, 0xC8, 0x49, 0x83, 0xD4, 0x00, 0x49, 0x0F, 0xA4,
    0xC4, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00,
    0x48, 0x21, 0xC8, 0x48, 0x09, 0xF0, 0x48, 0xBF, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD5, 0x48, 0x89, 0xC3, 0x48, 0x03, 0x9C, 0x24, 0x88, 0x00, 0x00,
    0x00, 0x48, 0x13, 0x6C, 0x24, 0x50, 0x48, 0x0F, 0xA4, 0xDD, 0x0C, 0x4C, 0x89, 0xF8, 0x49, 0xF7,
    0xE1, 0x48, 0x89, 0x54, 0x24, 0x50, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] ++ bytes_l110d64_62

theorem code_l110d64_61 : ∀ x ∈ codeRange 0x112229 bytes_l110d64_61, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12229 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_62

def b_l110d64_60 : Block Op Label signature Reg.count 2588 :=
  .letOp (n := 2588) (.out 0x1121e3 (mulR64Effect 0x1121e3 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2446, 2586]
    (.letOp (n := 2589) (.out 0x1121e3 (mulR64Effect 0x1121e3 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2446, 2586]
    (.letOp (n := 2590) (.exec 0x1121e3 (fun s => s.RIP = 0x1121e3) (mulR64Effect 0x1121e3 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2446, 2586]
    (.letOp (n := 2591) (.out 0x1121e6 (movR64R64Effect 0x1121e6 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[2588]
    (.letOp (n := 2592) (.exec 0x1121e6 (fun s => s.RIP = 0x1121e6) (movR64R64Effect 0x1121e6 7 0) (Reg.operands [.gpr 0] [])) #v[2588]
    (.letOp (n := 2593) (.out 0x1121e9 (movR64R64Effect 0x1121e9 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2589]
    (.letOp (n := 2594) (.exec 0x1121e9 (fun s => s.RIP = 0x1121e9) (movR64R64Effect 0x1121e9 13 2) (Reg.operands [.gpr 2] [])) #v[2589]
    (.letOp (n := 2595) (.out 0x1121ec (andR32Imm8Effect 0x1121ec 3 6 0xf) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[2573]
    (.letOp (n := 2596) (.exec 0x1121ec (fun s => s.RIP = 0x1121ec) (andR32Imm8Effect 0x1121ec 3 6 0xf) (Reg.operands [.gpr 6] [])) #v[2573]
    (.letOp (n := 2597) (.out 0x1121ef (movR64M64Effect 0x1121ef 10 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 2598) (.exec 0x1121ef (LoadPre 0x1121ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1121ef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1121ef 10 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2599) (.out 0x1121f4 (movR64R64Effect 0x1121f4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[2597]
    (.letOp (n := 2600) (.exec 0x1121f4 (fun s => s.RIP = 0x1121f4) (movR64R64Effect 0x1121f4 0 10) (Reg.operands [.gpr 10] [])) #v[2597]
    (.letOp (n := 2601) (.out 0x1121f7 (mulM64Effect 0x1121f7 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2599, 4]
    (.letOp (n := 2602) (.out 0x1121f7 (mulM64Effect 0x1121f7 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2599, 4]
    (.letOp (n := 2603) (.exec 0x1121f7 (LoadPre 0x1121f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1121f7 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1121f7 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2599, 4]
    (.letOp (n := 2604) (.out 0x1121fc (movR64R64Effect 0x1121fc 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2602]
    (.letOp (n := 2605) (.exec 0x1121fc (fun s => s.RIP = 0x1121fc) (movR64R64Effect 0x1121fc 12 2) (Reg.operands [.gpr 2] [])) #v[2602]
    (.letOp (n := 2606) (.out 0x1121ff (movR64R64Effect 0x1121ff 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[2601]
    (.letOp (n := 2607) (.exec 0x1121ff (fun s => s.RIP = 0x1121ff) (movR64R64Effect 0x1121ff 3 0) (Reg.operands [.gpr 0] [])) #v[2601]
    (.letOp (n := 2608) (.out 0x112202 (movR64M64Effect 0x112202 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2609) (.exec 0x112202 (LoadPre 0x112202 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x112202 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112202 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2610) (.out 0x112207 (mulR64Effect 0x112207 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[2498, 2608]
    (.letOp (n := 2611) (.out 0x112207 (mulR64Effect 0x112207 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[2498, 2608]
    (.letOp (n := 2612) (.exec 0x112207 (fun s => s.RIP = 0x112207) (mulR64Effect 0x112207 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[2498, 2608]
    (.letOp (n := 2613) (.out 0x11220a (movR64R64Effect 0x11220a 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2611]
    (.letOp (n := 2614) (.exec 0x11220a (fun s => s.RIP = 0x11220a) (movR64R64Effect 0x11220a 14 2) (Reg.operands [.gpr 2] [])) #v[2611]
    (.letOp (n := 2615) (.out 0x11220d (movR64R64Effect 0x11220d 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[2610]
    (.letOp (n := 2616) (.exec 0x11220d (fun s => s.RIP = 0x11220d) (movR64R64Effect 0x11220d 5 0) (Reg.operands [.gpr 0] [])) #v[2610]
    (.letOp (n := 2617) (.out 0x112210 (movR64M64Effect 0x112210 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2618) (.exec 0x112210 (LoadPre 0x112210 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112210 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112210 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2619) (.out 0x112215 (movR64M64Effect 0x112215 9 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 2620) (.exec 0x112215 (LoadPre 0x112215 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x112215 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112215 9 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2621) (.out 0x11221a (mulR64Effect 0x11221a 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[2619, 2617]
    (.letOp (n := 2622) (.out 0x11221a (mulR64Effect 0x11221a 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[2619, 2617]
    (.letOp (n := 2623) (.exec 0x11221a (fun s => s.RIP = 0x11221a) (mulR64Effect 0x11221a 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2619, 2617]
    (.letOp (n := 2624) (.out 0x11221d (addR64R64Effect 0x11221d 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[2606, 2591]
    (.letOp (n := 2625) (.out 0x11221d (addR64R64Effect 0x11221d 3 7) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 7] []) (.flag .CF)) #v[2606, 2591]
    (.letOp (n := 2626) (.exec 0x11221d (fun s => s.RIP = 0x11221d) (addR64R64Effect 0x11221d 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[2606, 2591]
    (.letOp (n := 2627) (.out 0x112220 (atFlags StatusFlags.CF (adcR64R64Effect 0x112220 12 13)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[2604, 2593, 2625]
    (.letOp (n := 2628) (.exec 0x112220 (fun s => s.RIP = 0x112220) (atFlags StatusFlags.CF (adcR64R64Effect 0x112220 12 13)) (Reg.operands [.gpr 12, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2604, 2593, 2625]
    (.letOp (n := 2629) (.out 0x112223 (addR64R64Effect 0x112223 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[2624, 2615]
    (.letOp (n := 2630) (.out 0x112223 (addR64R64Effect 0x112223 3 5) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 5] []) (.flag .CF)) #v[2624, 2615]
    (.letOp (n := 2631) (.exec 0x112223 (fun s => s.RIP = 0x112223) (addR64R64Effect 0x112223 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[2624, 2615]
    (.letOp (n := 2632) (.out 0x112226 (atFlags StatusFlags.CF (adcR64R64Effect 0x112226 12 14)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[2627, 2613, 2630]
    (.letOp (n := 2633) (.exec 0x112226 (fun s => s.RIP = 0x112226) (atFlags StatusFlags.CF (adcR64R64Effect 0x112226 12 14)) (Reg.operands [.gpr 12, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2627, 2613, 2630]
    (b_l110d64_61))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_60 : List UInt8 :=
  [0x48, 0xF7, 0xE7, 0x48, 0x89, 0xC7, 0x49, 0x89, 0xD5, 0x83, 0xE6, 0x0F, 0x4C, 0x8B, 0x54, 0x24,
    0x60, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0x64, 0x24, 0x28, 0x49, 0x89, 0xD4, 0x48, 0x89, 0xC3, 0x48,
    0x8B, 0x44, 0x24, 0x78, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD6, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0x44,
    0x24, 0x08, 0x4C, 0x8B, 0x4C, 0x24, 0x70, 0x49, 0xF7, 0xE1, 0x48, 0x01, 0xFB, 0x4D, 0x11, 0xEC,
    0x48, 0x01, 0xEB, 0x4D, 0x11, 0xF4] ++ bytes_l110d64_61

theorem code_l110d64_60 : ∀ x ∈ codeRange 0x1121e3 bytes_l110d64_60, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x121e3 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_61

def b_l110d64_59 : Block Op Label signature Reg.count 2544 :=
  .letOp (n := 2544) (.out 0x112197 (addR64R64Effect 0x112197 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[2539, 2504]
    (.letOp (n := 2545) (.out 0x112197 (addR64R64Effect 0x112197 8 10) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 10] []) (.flag .CF)) #v[2539, 2504]
    (.letOp (n := 2546) (.exec 0x112197 (fun s => s.RIP = 0x112197) (addR64R64Effect 0x112197 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[2539, 2504]
    (.letOp (n := 2547) (.out 0x11219a (atFlags StatusFlags.CF (adcR64M64Effect 0x11219a 1 (.sib 4 none 0 (.d8 0x30)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[2542, 4, 2545]
    (.letOp (n := 2548) (.exec 0x11219a (LoadPre 0x11219a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11219a + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11219a 1 (.sib 4 none 0 (.d8 0x30)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2542, 4, 2545]
    (.letOp (n := 2549) (.out 0x11219f (addR64R64Effect 0x11219f 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[2544, 2513]
    (.letOp (n := 2550) (.out 0x11219f (addR64R64Effect 0x11219f 8 14) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 14] []) (.flag .CF)) #v[2544, 2513]
    (.letOp (n := 2551) (.exec 0x11219f (fun s => s.RIP = 0x11219f) (addR64R64Effect 0x11219f 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[2544, 2513]
    (.letOp (n := 2552) (.out 0x1121a2 (atFlags StatusFlags.CF (adcR64R64Effect 0x1121a2 1 11)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[2547, 2511, 2550]
    (.letOp (n := 2553) (.exec 0x1121a2 (fun s => s.RIP = 0x1121a2) (atFlags StatusFlags.CF (adcR64R64Effect 0x1121a2 1 11)) (Reg.operands [.gpr 1, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2547, 2511, 2550]
    (.letOp (n := 2554) (.out 0x1121a5 (addR64R64Effect 0x1121a5 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[2549, 2522]
    (.letOp (n := 2555) (.out 0x1121a5 (addR64R64Effect 0x1121a5 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[2549, 2522]
    (.letOp (n := 2556) (.exec 0x1121a5 (fun s => s.RIP = 0x1121a5) (addR64R64Effect 0x1121a5 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[2549, 2522]
    (.letOp (n := 2557) (.out 0x1121a8 (atFlags StatusFlags.CF (adcR64R64Effect 0x1121a8 1 13)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[2552, 2524, 2555]
    (.letOp (n := 2558) (.exec 0x1121a8 (fun s => s.RIP = 0x1121a8) (atFlags StatusFlags.CF (adcR64R64Effect 0x1121a8 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2552, 2524, 2555]
    (.letOp (n := 2559) (.out 0x1121ab (addR64R64Effect 0x1121ab 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[2554, 2534]
    (.letOp (n := 2560) (.out 0x1121ab (addR64R64Effect 0x1121ab 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[2554, 2534]
    (.letOp (n := 2561) (.exec 0x1121ab (fun s => s.RIP = 0x1121ab) (addR64R64Effect 0x1121ab 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[2554, 2534]
    (.letOp (n := 2562) (.out 0x1121ae (atFlags StatusFlags.CF (adcR64R64Effect 0x1121ae 1 3)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[2557, 2537, 2560]
    (.letOp (n := 2563) (.exec 0x1121ae (fun s => s.RIP = 0x1121ae) (atFlags StatusFlags.CF (adcR64R64Effect 0x1121ae 1 3)) (Reg.operands [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2557, 2537, 2560]
    (.letOp (n := 2564) (.out 0x1121b1 (addR64R64Effect 0x1121b1 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[2559, 2477]
    (.letOp (n := 2565) (.out 0x1121b1 (addR64R64Effect 0x1121b1 8 15) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 15] []) (.flag .CF)) #v[2559, 2477]
    (.letOp (n := 2566) (.exec 0x1121b1 (fun s => s.RIP = 0x1121b1) (addR64R64Effect 0x1121b1 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[2559, 2477]
    (.letOp (n := 2567) (.out 0x1121b4 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1121b4 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[2562, 2565]
    (.letOp (n := 2568) (.exec 0x1121b4 (fun s => s.RIP = 0x1121b4) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1121b4 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2562, 2565]
    (.letOp (n := 2569) (.out 0x1121b8 (shldR64R64Effect 0x1121b8 5 1 8 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2567, 2564]
    (.letOp (n := 2570) (.exec 0x1121b8 (fun s => s.RIP = 0x1121b8) (shldR64R64Effect 0x1121b8 5 1 8 12) (Reg.operands [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2567, 2564]
    (.letOp (n := 2571) (.out 0x1121bd (movR64R64Effect 0x1121bd 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[2564]
    (.letOp (n := 2572) (.exec 0x1121bd (fun s => s.RIP = 0x1121bd) (movR64R64Effect 0x1121bd 6 8) (Reg.operands [.gpr 8] [])) #v[2564]
    (.letOp (n := 2573) (.out 0x1121c0 (shrR64Effect 0x1121c0 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[2571]
    (.letOp (n := 2574) (.exec 0x1121c0 (fun s => s.RIP = 0x1121c0) (shrR64Effect 0x1121c0 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2571]
    (.letOp (n := 2575) (.out 0x1121c4 (movR64M64Effect 0x1121c4 15 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 2576) (.exec 0x1121c4 (LoadPre 0x1121c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1121c4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1121c4 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2577) (.out 0x1121c9 (movR64R64Effect 0x1121c9 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[2575]
    (.letOp (n := 2578) (.exec 0x1121c9 (fun s => s.RIP = 0x1121c9) (movR64R64Effect 0x1121c9 0 15) (Reg.operands [.gpr 15] [])) #v[2575]
    (.letOp (n := 2579) (.out 0x1121cc (mulR64Effect 0x1121cc 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[2517, 2577]
    (.letOp (n := 2580) (.out 0x1121cc (mulR64Effect 0x1121cc 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[2517, 2577]
    (.letOp (n := 2581) (.exec 0x1121cc (fun s => s.RIP = 0x1121cc) (mulR64Effect 0x1121cc 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2517, 2577]
    (.letOp (n := 2582) (.exec 0x1121cf (StorePre 0x1121cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1121cf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1121cf 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2580, 4]
    (.letOp (n := 2583) (.exec 0x1121d4 (StorePre 0x1121d4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1121d4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1121d4 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2579, 4]
    (.letOp (n := 2584) (.out 0x1121dc (movR64M64Effect 0x1121dc 11 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 2585) (.exec 0x1121dc (LoadPre 0x1121dc (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1121dc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1121dc 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2586) (.out 0x1121e0 (movR64R64Effect 0x1121e0 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2584]
    (.letOp (n := 2587) (.exec 0x1121e0 (fun s => s.RIP = 0x1121e0) (movR64R64Effect 0x1121e0 0 11) (Reg.operands [.gpr 11] [])) #v[2584]
    (b_l110d64_60))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_59 : List UInt8 :=
  [0x4D, 0x01, 0xD0, 0x48, 0x13, 0x4C, 0x24, 0x30, 0x4D, 0x01, 0xF0, 0x4C, 0x11, 0xD9, 0x49, 0x01,
    0xF0, 0x4C, 0x11, 0xE9, 0x49, 0x01, 0xC0, 0x48, 0x11, 0xD9, 0x4D, 0x01, 0xF8, 0x48, 0x83, 0xD1,
    0x00, 0x4C, 0x0F, 0xA4, 0xC1, 0x0C, 0x4C, 0x89, 0xC6, 0x48, 0xC1, 0xEE, 0x30, 0x4C, 0x8B, 0x7C,
    0x24, 0x18, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x54, 0x24, 0x50, 0x48, 0x89, 0x84,
    0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x1C, 0x24, 0x4C, 0x89, 0xD8] ++ bytes_l110d64_60

theorem code_l110d64_59 : ∀ x ∈ codeRange 0x112197 bytes_l110d64_59, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12197 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_60

def b_l110d64_58 : Block Op Label signature Reg.count 2500 :=
  .letOp (n := 2500) (.out 0x112147 (mulR64Effect 0x112147 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[2498, 2496]
    (.letOp (n := 2501) (.out 0x112147 (mulR64Effect 0x112147 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[2498, 2496]
    (.letOp (n := 2502) (.exec 0x112147 (fun s => s.RIP = 0x112147) (mulR64Effect 0x112147 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[2498, 2496]
    (.letOp (n := 2503) (.exec 0x11214a (StorePre 0x11214a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11214a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11214a 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2501, 4]
    (.letOp (n := 2504) (.out 0x11214f (movR64R64Effect 0x11214f 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2500]
    (.letOp (n := 2505) (.exec 0x11214f (fun s => s.RIP = 0x11214f) (movR64R64Effect 0x11214f 10 0) (Reg.operands [.gpr 0] [])) #v[2500]
    (.letOp (n := 2506) (.out 0x112152 (movR64R64Effect 0x112152 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2388]
    (.letOp (n := 2507) (.exec 0x112152 (fun s => s.RIP = 0x112152) (movR64R64Effect 0x112152 0 11) (Reg.operands [.gpr 11] [])) #v[2388]
    (.letOp (n := 2508) (.out 0x112155 (mulR64Effect 0x112155 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[2410, 2506]
    (.letOp (n := 2509) (.out 0x112155 (mulR64Effect 0x112155 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[2410, 2506]
    (.letOp (n := 2510) (.exec 0x112155 (fun s => s.RIP = 0x112155) (mulR64Effect 0x112155 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2410, 2506]
    (.letOp (n := 2511) (.out 0x112158 (movR64R64Effect 0x112158 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2509]
    (.letOp (n := 2512) (.exec 0x112158 (fun s => s.RIP = 0x112158) (movR64R64Effect 0x112158 11 2) (Reg.operands [.gpr 2] [])) #v[2509]
    (.letOp (n := 2513) (.out 0x11215b (movR64R64Effect 0x11215b 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[2508]
    (.letOp (n := 2514) (.exec 0x11215b (fun s => s.RIP = 0x11215b) (movR64R64Effect 0x11215b 14 0) (Reg.operands [.gpr 0] [])) #v[2508]
    (.letOp (n := 2515) (.out 0x11215e (movR64R64Effect 0x11215e 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2448]
    (.letOp (n := 2516) (.exec 0x11215e (fun s => s.RIP = 0x11215e) (movR64R64Effect 0x11215e 0 6) (Reg.operands [.gpr 6] [])) #v[2448]
    (.letOp (n := 2517) (.out 0x112161 (movR64M64Effect 0x112161 9 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 2518) (.exec 0x112161 (LoadPre 0x112161 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x112161 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112161 9 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2519) (.out 0x112166 (mulR64Effect 0x112166 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[2517, 2515]
    (.letOp (n := 2520) (.out 0x112166 (mulR64Effect 0x112166 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[2517, 2515]
    (.letOp (n := 2521) (.exec 0x112166 (fun s => s.RIP = 0x112166) (mulR64Effect 0x112166 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2517, 2515]
    (.letOp (n := 2522) (.out 0x112169 (movR64R64Effect 0x112169 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2519]
    (.letOp (n := 2523) (.exec 0x112169 (fun s => s.RIP = 0x112169) (movR64R64Effect 0x112169 6 0) (Reg.operands [.gpr 0] [])) #v[2519]
    (.letOp (n := 2524) (.out 0x11216c (movR64R64Effect 0x11216c 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2520]
    (.letOp (n := 2525) (.exec 0x11216c (fun s => s.RIP = 0x11216c) (movR64R64Effect 0x11216c 13 2) (Reg.operands [.gpr 2] [])) #v[2520]
    (.letOp (n := 2526) (.out 0x11216f (shrR64Effect 0x11216f 4 3 52) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[2456]
    (.letOp (n := 2527) (.exec 0x11216f (fun s => s.RIP = 0x11216f) (shrR64Effect 0x11216f 4 3 52) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2456]
    (.letOp (n := 2528) (.out 0x112173 (movR64Imm64Effect 0x112173 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2529) (.exec 0x112173 (fun s => s.RIP = 0x112173) (movR64Imm64Effect 0x112173 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2530) (.out 0x11217d (imulR64R64Effect 0x11217d 4 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[2526, 2528]
    (.letOp (n := 2531) (.exec 0x11217d (fun s => s.RIP = 0x11217d) (imulR64R64Effect 0x11217d 4 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[2526, 2528]
    (.letOp (n := 2532) (.out 0x112181 (movR64R64Effect 0x112181 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[2460]
    (.letOp (n := 2533) (.exec 0x112181 (fun s => s.RIP = 0x112181) (movR64R64Effect 0x112181 0 12) (Reg.operands [.gpr 12] [])) #v[2460]
    (.letOp (n := 2534) (.out 0x112184 (mulR64Effect 0x112184 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2528, 2532]
    (.letOp (n := 2535) (.out 0x112184 (mulR64Effect 0x112184 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2528, 2532]
    (.letOp (n := 2536) (.exec 0x112184 (fun s => s.RIP = 0x112184) (mulR64Effect 0x112184 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2528, 2532]
    (.letOp (n := 2537) (.out 0x112187 (addR64R64Effect 0x112187 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[2530, 2535]
    (.letOp (n := 2538) (.exec 0x112187 (fun s => s.RIP = 0x112187) (addR64R64Effect 0x112187 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[2530, 2535]
    (.letOp (n := 2539) (.out 0x11218a (addR64M64Effect 0x11218a 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[2494, 4]
    (.letOp (n := 2540) (.out 0x11218a (addR64M64Effect 0x11218a 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[2494, 4]
    (.letOp (n := 2541) (.exec 0x11218a (LoadPre 0x11218a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11218a + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11218a 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[2494, 4]
    (.letOp (n := 2542) (.out 0x112192 (atFlags StatusFlags.CF (adcR64M64Effect 0x112192 1 (.sib 4 none 0 (.d8 0x50)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[2492, 4, 2540]
    (.letOp (n := 2543) (.exec 0x112192 (LoadPre 0x112192 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x112192 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x112192 1 (.sib 4 none 0 (.d8 0x50)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2492, 4, 2540]
    (b_l110d64_59))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_58 : List UInt8 :=
  [0x48, 0xF7, 0xE5, 0x48, 0x89, 0x54, 0x24, 0x30, 0x49, 0x89, 0xC2, 0x4C, 0x89, 0xD8, 0x49, 0xF7,
    0xE5, 0x49, 0x89, 0xD3, 0x49, 0x89, 0xC6, 0x48, 0x89, 0xF0, 0x4C, 0x8B, 0x4C, 0x24, 0x48, 0x49,
    0xF7, 0xE1, 0x48, 0x89, 0xC6, 0x49, 0x89, 0xD5, 0x48, 0xC1, 0xEB, 0x34, 0x48, 0xBA, 0x10, 0x3D,
    0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xDA, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0xE2,
    0x48, 0x01, 0xD3, 0x4C, 0x03, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x13, 0x4C, 0x24, 0x50] ++ bytes_l110d64_59

theorem code_l110d64_58 : ∀ x ∈ codeRange 0x112147 bytes_l110d64_58, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12147 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_59

def b_l110d64_57 : Block Op Label signature Reg.count 2460 :=
  .letOp (n := 2460) (.out 0x1120ee (shldR64R64Effect 0x1120ee 5 12 0 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[2458, 2453]
    (.letOp (n := 2461) (.exec 0x1120ee (fun s => s.RIP = 0x1120ee) (shldR64R64Effect 0x1120ee 5 12 0 12) (Reg.operands [.gpr 12, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2458, 2453]
    (.letOp (n := 2462) (.out 0x1120f3 (andR64R64Effect 0x1120f3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[2453, 2390]
    (.letOp (n := 2463) (.exec 0x1120f3 (fun s => s.RIP = 0x1120f3) (andR64R64Effect 0x1120f3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[2453, 2390]
    (.letOp (n := 2464) (.out 0x1120f6 (movR64Imm64Effect 0x1120f6 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2465) (.exec 0x1120f6 (fun s => s.RIP = 0x1120f6) (movR64Imm64Effect 0x1120f6 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2466) (.out 0x112100 (mulR64Effect 0x112100 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2464, 2462]
    (.letOp (n := 2467) (.out 0x112100 (mulR64Effect 0x112100 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2464, 2462]
    (.letOp (n := 2468) (.exec 0x112100 (fun s => s.RIP = 0x112100) (mulR64Effect 0x112100 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2464, 2462]
    (.letOp (n := 2469) (.out 0x112103 (movR64R64Effect 0x112103 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2467]
    (.letOp (n := 2470) (.exec 0x112103 (fun s => s.RIP = 0x112103) (movR64R64Effect 0x112103 15 2) (Reg.operands [.gpr 2] [])) #v[2467]
    (.letOp (n := 2471) (.out 0x112106 (addR64R64Effect 0x112106 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[2466, 2441]
    (.letOp (n := 2472) (.out 0x112106 (addR64R64Effect 0x112106 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[2466, 2441]
    (.letOp (n := 2473) (.exec 0x112106 (fun s => s.RIP = 0x112106) (addR64R64Effect 0x112106 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[2466, 2441]
    (.letOp (n := 2474) (.exec 0x112109 (StorePre 0x112109 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x112109 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112109 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2471, 4]
    (.letOp (n := 2475) (.out 0x112111 (atFlags StatusFlags.CF (adcR64R64Effect 0x112111 15 1)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[2469, 2444, 2472]
    (.letOp (n := 2476) (.exec 0x112111 (fun s => s.RIP = 0x112111) (atFlags StatusFlags.CF (adcR64R64Effect 0x112111 15 1)) (Reg.operands [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2469, 2444, 2472]
    (.letOp (n := 2477) (.out 0x112114 (shldR64R64Effect 0x112114 5 15 0 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[2475, 2471]
    (.letOp (n := 2478) (.exec 0x112114 (fun s => s.RIP = 0x112114) (shldR64R64Effect 0x112114 5 15 0 12) (Reg.operands [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2475, 2471]
    (.letOp (n := 2479) (.out 0x112119 (movR64R64Effect 0x112119 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[2365]
    (.letOp (n := 2480) (.exec 0x112119 (fun s => s.RIP = 0x112119) (movR64R64Effect 0x112119 0 5) (Reg.operands [.gpr 5] [])) #v[2365]
    (.letOp (n := 2481) (.out 0x11211c (mulR64Effect 0x11211c 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2446, 2479]
    (.letOp (n := 2482) (.out 0x11211c (mulR64Effect 0x11211c 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2446, 2479]
    (.letOp (n := 2483) (.exec 0x11211c (fun s => s.RIP = 0x11211c) (mulR64Effect 0x11211c 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2446, 2479]
    (.letOp (n := 2484) (.exec 0x11211f (StorePre 0x11211f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11211f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11211f 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[2446, 4]
    (.letOp (n := 2485) (.exec 0x112124 (StorePre 0x112124 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x112124 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112124 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2482, 4]
    (.letOp (n := 2486) (.exec 0x112129 (StorePre 0x112129 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x112129 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112129 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2481, 4]
    (.letOp (n := 2487) (.out 0x112131 (movR64R64Effect 0x112131 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[2369]
    (.letOp (n := 2488) (.exec 0x112131 (fun s => s.RIP = 0x112131) (movR64R64Effect 0x112131 0 14) (Reg.operands [.gpr 14] [])) #v[2369]
    (.letOp (n := 2489) (.out 0x112134 (mulM64Effect 0x112134 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2487, 4]
    (.letOp (n := 2490) (.out 0x112134 (mulM64Effect 0x112134 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2487, 4]
    (.letOp (n := 2491) (.exec 0x112134 (LoadPre 0x112134 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x112134 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x112134 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2487, 4]
    (.letOp (n := 2492) (.out 0x112139 (movR64R64Effect 0x112139 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2490]
    (.letOp (n := 2493) (.exec 0x112139 (fun s => s.RIP = 0x112139) (movR64R64Effect 0x112139 1 2) (Reg.operands [.gpr 2] [])) #v[2490]
    (.letOp (n := 2494) (.out 0x11213c (movR64R64Effect 0x11213c 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[2489]
    (.letOp (n := 2495) (.exec 0x11213c (fun s => s.RIP = 0x11213c) (movR64R64Effect 0x11213c 8 0) (Reg.operands [.gpr 0] [])) #v[2489]
    (.letOp (n := 2496) (.out 0x11213f (movR64R64Effect 0x11213f 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2371]
    (.letOp (n := 2497) (.exec 0x11213f (fun s => s.RIP = 0x11213f) (movR64R64Effect 0x11213f 0 9) (Reg.operands [.gpr 9] [])) #v[2371]
    (.letOp (n := 2498) (.out 0x112142 (movR64M64Effect 0x112142 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 2499) (.exec 0x112142 (LoadPre 0x112142 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x112142 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112142 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l110d64_58))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_57 : List UInt8 :=
  [0x49, 0x0F, 0xA4, 0xC4, 0x0C, 0x4C, 0x21, 0xF8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xD7, 0x4C, 0x01, 0xC0, 0x48, 0x89, 0x84, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x49, 0x11, 0xCF, 0x49, 0x0F, 0xA4, 0xC7, 0x0C, 0x48, 0x89, 0xE8, 0x48, 0xF7,
    0xE7, 0x48, 0x89, 0x7C, 0x24, 0x40, 0x48, 0x89, 0x54, 0x24, 0x50, 0x48, 0x89, 0x84, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0x64, 0x24, 0x28, 0x48, 0x89, 0xD1, 0x49, 0x89,
    0xC0, 0x4C, 0x89, 0xC8, 0x48, 0x8B, 0x6C, 0x24, 0x20] ++ bytes_l110d64_58

theorem code_l110d64_57 : ∀ x ∈ codeRange 0x1120ee bytes_l110d64_57, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x120ee 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_58

def b_l110d64_56 : Block Op Label signature Reg.count 2419 :=
  .letOp (n := 2419) (.out 0x1120a2 (movR64R64Effect 0x1120a2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2416]
    (.letOp (n := 2420) (.exec 0x1120a2 (fun s => s.RIP = 0x1120a2) (movR64R64Effect 0x1120a2 6 2) (Reg.operands [.gpr 2] [])) #v[2416]
    (.letOp (n := 2421) (.out 0x1120a5 (movR64R64Effect 0x1120a5 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2415]
    (.letOp (n := 2422) (.exec 0x1120a5 (fun s => s.RIP = 0x1120a5) (movR64R64Effect 0x1120a5 10 0) (Reg.operands [.gpr 0] [])) #v[2415]
    (.letOp (n := 2423) (.out 0x1120a8 (addR64R64Effect 0x1120a8 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[2421, 2405]
    (.letOp (n := 2424) (.out 0x1120a8 (addR64R64Effect 0x1120a8 10 8) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 8] []) (.flag .CF)) #v[2421, 2405]
    (.letOp (n := 2425) (.exec 0x1120a8 (fun s => s.RIP = 0x1120a8) (addR64R64Effect 0x1120a8 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[2421, 2405]
    (.letOp (n := 2426) (.out 0x1120ab (atFlags StatusFlags.CF (adcR64R64Effect 0x1120ab 6 7)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[2419, 2408, 2424]
    (.letOp (n := 2427) (.exec 0x1120ab (fun s => s.RIP = 0x1120ab) (atFlags StatusFlags.CF (adcR64R64Effect 0x1120ab 6 7)) (Reg.operands [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2419, 2408, 2424]
    (.letOp (n := 2428) (.out 0x1120ae (movR64M64Effect 0x1120ae 1 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 2429) (.exec 0x1120ae (LoadPre 0x1120ae (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x1120ae + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1120ae 1 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2430) (.exec 0x1120b6 (StorePre 0x1120b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1120b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1120b6 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2428, 4]
    (.letOp (n := 2431) (.out 0x1120bb (movR64R64Effect 0x1120bb 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2388]
    (.letOp (n := 2432) (.exec 0x1120bb (fun s => s.RIP = 0x1120bb) (movR64R64Effect 0x1120bb 0 11) (Reg.operands [.gpr 11] [])) #v[2388]
    (.letOp (n := 2433) (.exec 0x1120be (StorePre 0x1120be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1120be + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1120be 11 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[2388, 4]
    (.letOp (n := 2434) (.out 0x1120c3 (mulR64Effect 0x1120c3 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2428, 2431]
    (.letOp (n := 2435) (.out 0x1120c3 (mulR64Effect 0x1120c3 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2428, 2431]
    (.letOp (n := 2436) (.exec 0x1120c3 (fun s => s.RIP = 0x1120c3) (mulR64Effect 0x1120c3 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2428, 2431]
    (.letOp (n := 2437) (.out 0x1120c6 (movR64R64Effect 0x1120c6 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2435]
    (.letOp (n := 2438) (.exec 0x1120c6 (fun s => s.RIP = 0x1120c6) (movR64R64Effect 0x1120c6 1 2) (Reg.operands [.gpr 2] [])) #v[2435]
    (.letOp (n := 2439) (.out 0x1120c9 (movR64R64Effect 0x1120c9 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[2434]
    (.letOp (n := 2440) (.exec 0x1120c9 (fun s => s.RIP = 0x1120c9) (movR64R64Effect 0x1120c9 8 0) (Reg.operands [.gpr 0] [])) #v[2434]
    (.letOp (n := 2441) (.out 0x1120cc (addR64R64Effect 0x1120cc 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[2439, 2423]
    (.letOp (n := 2442) (.out 0x1120cc (addR64R64Effect 0x1120cc 8 10) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 10] []) (.flag .CF)) #v[2439, 2423]
    (.letOp (n := 2443) (.exec 0x1120cc (fun s => s.RIP = 0x1120cc) (addR64R64Effect 0x1120cc 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[2439, 2423]
    (.letOp (n := 2444) (.out 0x1120cf (atFlags StatusFlags.CF (adcR64R64Effect 0x1120cf 1 6)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[2437, 2426, 2442]
    (.letOp (n := 2445) (.exec 0x1120cf (fun s => s.RIP = 0x1120cf) (atFlags StatusFlags.CF (adcR64R64Effect 0x1120cf 1 6)) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2437, 2426, 2442]
    (.letOp (n := 2446) (.out 0x1120d2 (movR64M64Effect 0x1120d2 7 (.sib 4 none 0 (.d32 0x198))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 2447) (.exec 0x1120d2 (LoadPre 0x1120d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x1120d2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1120d2 7 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2448) (.out 0x1120da (movR64R64Effect 0x1120da 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[2361]
    (.letOp (n := 2449) (.exec 0x1120da (fun s => s.RIP = 0x1120da) (movR64R64Effect 0x1120da 6 3) (Reg.operands [.gpr 3] [])) #v[2361]
    (.letOp (n := 2450) (.exec 0x1120dd (StorePre 0x1120dd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1120dd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1120dd 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[2361, 4]
    (.letOp (n := 2451) (.out 0x1120e2 (movR64R64Effect 0x1120e2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[2361]
    (.letOp (n := 2452) (.exec 0x1120e2 (fun s => s.RIP = 0x1120e2) (movR64R64Effect 0x1120e2 0 3) (Reg.operands [.gpr 3] [])) #v[2361]
    (.letOp (n := 2453) (.out 0x1120e5 (mulR64Effect 0x1120e5 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[2446, 2451]
    (.letOp (n := 2454) (.out 0x1120e5 (mulR64Effect 0x1120e5 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[2446, 2451]
    (.letOp (n := 2455) (.exec 0x1120e5 (fun s => s.RIP = 0x1120e5) (mulR64Effect 0x1120e5 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2446, 2451]
    (.letOp (n := 2456) (.out 0x1120e8 (movR64R64Effect 0x1120e8 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2454]
    (.letOp (n := 2457) (.exec 0x1120e8 (fun s => s.RIP = 0x1120e8) (movR64R64Effect 0x1120e8 3 2) (Reg.operands [.gpr 2] [])) #v[2454]
    (.letOp (n := 2458) (.out 0x1120eb (movR64R64Effect 0x1120eb 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2454]
    (.letOp (n := 2459) (.exec 0x1120eb (fun s => s.RIP = 0x1120eb) (movR64R64Effect 0x1120eb 12 2) (Reg.operands [.gpr 2] [])) #v[2454]
    (b_l110d64_57)))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_56 : List UInt8 :=
  [0x48, 0x89, 0xD6, 0x49, 0x89, 0xC2, 0x4D, 0x01, 0xC2, 0x48, 0x11, 0xFE, 0x48, 0x8B, 0x8C, 0x24,
    0x78, 0x01, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x48, 0x4C, 0x89, 0xD8, 0x4C, 0x89, 0x5C, 0x24,
    0x78, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC0, 0x4D, 0x01, 0xD0, 0x48, 0x11, 0xF1,
    0x48, 0x8B, 0xBC, 0x24, 0x98, 0x01, 0x00, 0x00, 0x48, 0x89, 0xDE, 0x48, 0x89, 0x5C, 0x24, 0x08,
    0x48, 0x89, 0xD8, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xD4] ++ bytes_l110d64_57

theorem code_l110d64_56 : ∀ x ∈ codeRange 0x1120a2 bytes_l110d64_56, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x120a2 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_57

def b_l110d64_55 : Block Op Label signature Reg.count 2380 :=
  .letOp (n := 2380) (.exec 0x112053 (StorePre 0x112053 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x112053 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112053 5 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[2365, 4]
    (.letOp (n := 2381) (.out 0x112058 (mulR64Effect 0x112058 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2375, 2378]
    (.letOp (n := 2382) (.out 0x112058 (mulR64Effect 0x112058 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2375, 2378]
    (.letOp (n := 2383) (.exec 0x112058 (fun s => s.RIP = 0x112058) (mulR64Effect 0x112058 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2375, 2378]
    (.letOp (n := 2384) (.out 0x11205b (movR64R64Effect 0x11205b 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[2381]
    (.letOp (n := 2385) (.exec 0x11205b (fun s => s.RIP = 0x11205b) (movR64R64Effect 0x11205b 1 0) (Reg.operands [.gpr 0] [])) #v[2381]
    (.letOp (n := 2386) (.out 0x11205e (movR64R64Effect 0x11205e 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2382]
    (.letOp (n := 2387) (.exec 0x11205e (fun s => s.RIP = 0x11205e) (movR64R64Effect 0x11205e 6 2) (Reg.operands [.gpr 2] [])) #v[2382]
    (.letOp (n := 2388) (.out 0x112061 (andR64R64Effect 0x112061 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[2343, 2373]
    (.letOp (n := 2389) (.exec 0x112061 (fun s => s.RIP = 0x112061) (andR64R64Effect 0x112061 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[2343, 2373]
    (.letOp (n := 2390) (.out 0x112064 (movR64R64Effect 0x112064 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[2373]
    (.letOp (n := 2391) (.exec 0x112064 (fun s => s.RIP = 0x112064) (movR64R64Effect 0x112064 15 7) (Reg.operands [.gpr 7] [])) #v[2373]
    (.letOp (n := 2392) (.out 0x112067 (movR64M64Effect 0x112067 2 (.sib 4 none 0 (.d32 0x188))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 2393) (.exec 0x112067 (LoadPre 0x112067 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x112067 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112067 2 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2394) (.exec 0x11206f (StorePre 0x11206f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11206f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11206f 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2392, 4]
    (.letOp (n := 2395) (.out 0x112074 (movR64R64Effect 0x112074 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[2369]
    (.letOp (n := 2396) (.exec 0x112074 (fun s => s.RIP = 0x112074) (movR64R64Effect 0x112074 0 14) (Reg.operands [.gpr 14] [])) #v[2369]
    (.letOp (n := 2397) (.exec 0x112077 (StorePre 0x112077 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112077 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112077 14 (.sib 4 none 0 .none)) (Reg.operands [.gpr 14, .gpr 4] [])) #v[2369, 4]
    (.letOp (n := 2398) (.out 0x11207b (mulR64Effect 0x11207b 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2392, 2395]
    (.letOp (n := 2399) (.out 0x11207b (mulR64Effect 0x11207b 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2392, 2395]
    (.letOp (n := 2400) (.exec 0x11207b (fun s => s.RIP = 0x11207b) (mulR64Effect 0x11207b 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2392, 2395]
    (.letOp (n := 2401) (.out 0x11207e (movR64R64Effect 0x11207e 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2399]
    (.letOp (n := 2402) (.exec 0x11207e (fun s => s.RIP = 0x11207e) (movR64R64Effect 0x11207e 7 2) (Reg.operands [.gpr 2] [])) #v[2399]
    (.letOp (n := 2403) (.out 0x112081 (movR64R64Effect 0x112081 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[2398]
    (.letOp (n := 2404) (.exec 0x112081 (fun s => s.RIP = 0x112081) (movR64R64Effect 0x112081 8 0) (Reg.operands [.gpr 0] [])) #v[2398]
    (.letOp (n := 2405) (.out 0x112084 (addR64R64Effect 0x112084 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[2403, 2384]
    (.letOp (n := 2406) (.out 0x112084 (addR64R64Effect 0x112084 8 1) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 1] []) (.flag .CF)) #v[2403, 2384]
    (.letOp (n := 2407) (.exec 0x112084 (fun s => s.RIP = 0x112084) (addR64R64Effect 0x112084 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[2403, 2384]
    (.letOp (n := 2408) (.out 0x112087 (atFlags StatusFlags.CF (adcR64R64Effect 0x112087 7 6)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[2401, 2386, 2406]
    (.letOp (n := 2409) (.exec 0x112087 (fun s => s.RIP = 0x112087) (atFlags StatusFlags.CF (adcR64R64Effect 0x112087 7 6)) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2401, 2386, 2406]
    (.letOp (n := 2410) (.out 0x11208a (movR64M64Effect 0x11208a 13 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 2411) (.exec 0x11208a (LoadPre 0x11208a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x11208a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11208a 13 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2412) (.out 0x112092 (movR64R64Effect 0x112092 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2371]
    (.letOp (n := 2413) (.exec 0x112092 (fun s => s.RIP = 0x112092) (movR64R64Effect 0x112092 0 9) (Reg.operands [.gpr 9] [])) #v[2371]
    (.letOp (n := 2414) (.exec 0x112095 (StorePre 0x112095 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x112095 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112095 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[2371, 4]
    (.letOp (n := 2415) (.out 0x11209a (mulR64Effect 0x11209a 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[2410, 2412]
    (.letOp (n := 2416) (.out 0x11209a (mulR64Effect 0x11209a 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[2410, 2412]
    (.letOp (n := 2417) (.exec 0x11209a (fun s => s.RIP = 0x11209a) (mulR64Effect 0x11209a 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2410, 2412]
    (.letOp (n := 2418) (.exec 0x11209d (StorePre 0x11209d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11209d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11209d 13 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[2410, 4]
    (b_l110d64_56)))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_55 : List UInt8 :=
  [0x48, 0x89, 0x6C, 0x24, 0x18, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC1, 0x48, 0x89, 0xD6, 0x49, 0x21,
    0xFB, 0x49, 0x89, 0xFF, 0x48, 0x8B, 0x94, 0x24, 0x88, 0x01, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24,
    0x20, 0x4C, 0x89, 0xF0, 0x4C, 0x89, 0x34, 0x24, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD7, 0x49, 0x89,
    0xC0, 0x49, 0x01, 0xC8, 0x48, 0x11, 0xF7, 0x4C, 0x8B, 0xAC, 0x24, 0x80, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0xC8, 0x4C, 0x89, 0x4C, 0x24, 0x60, 0x49, 0xF7, 0xE5, 0x4C, 0x89, 0x6C, 0x24, 0x70] ++ bytes_l110d64_56

theorem code_l110d64_55 : ∀ x ∈ codeRange 0x112053 bytes_l110d64_55, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12053 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_56

def b_l110d64_54 : Block Op Label signature Reg.count 2342 :=
  .letOp (n := 2342) (.exec 0x111ff2 (StorePre 0x111ff2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x111ff2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111ff2 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2340, 4]
    (.letOp (n := 2343) (.out 0x111ffa (addR64R64Effect 0x111ffa 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[2335, 2320]
    (.letOp (n := 2344) (.out 0x111ffa (addR64R64Effect 0x111ffa 11 1) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 1] []) (.flag .CF)) #v[2335, 2320]
    (.letOp (n := 2345) (.exec 0x111ffa (fun s => s.RIP = 0x111ffa) (addR64R64Effect 0x111ffa 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[2335, 2320]
    (.letOp (n := 2346) (.out 0x111ffd (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111ffd 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2338, 2344]
    (.letOp (n := 2347) (.exec 0x111ffd (fun s => s.RIP = 0x111ffd) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111ffd 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2338, 2344]
    (.letOp (n := 2348) (.out 0x112001 (movR64M64Effect 0x112001 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2349) (.exec 0x112001 (LoadPre 0x112001 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x112001 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112001 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2350) (.exec 0x112009 (StorePre 0x112009 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x112009 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112009 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2348, 4]
    (.letOp (n := 2351) (.out 0x112011 (shldR64R64Effect 0x112011 5 2 11 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2346, 2343]
    (.letOp (n := 2352) (.exec 0x112011 (fun s => s.RIP = 0x112011) (shldR64R64Effect 0x112011 5 2 11 12) (Reg.operands [.gpr 2, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2346, 2343]
    (.letOp (n := 2353) (.out 0x112016 (movR64Imm64Effect 0x112016 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 2354) (.exec 0x112016 (fun s => s.RIP = 0x112016) (movR64Imm64Effect 0x112016 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2355) (.out 0x112020 (movR64M64Effect 0x112020 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 2356) (.exec 0x112020 (LoadPre 0x112020 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112020 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112020 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2357) (.out 0x112025 (andR64R64Effect 0x112025 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2355, 2353]
    (.letOp (n := 2358) (.exec 0x112025 (fun s => s.RIP = 0x112025) (andR64R64Effect 0x112025 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2355, 2353]
    (.letOp (n := 2359) (.out 0x112028 (addR64R64Effect 0x112028 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[2357, 2351]
    (.letOp (n := 2360) (.exec 0x112028 (fun s => s.RIP = 0x112028) (addR64R64Effect 0x112028 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[2357, 2351]
    (.letOp (n := 2361) (.out 0x11202b (movR64R64Effect 0x11202b 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[2359]
    (.letOp (n := 2362) (.exec 0x11202b (fun s => s.RIP = 0x11202b) (movR64R64Effect 0x11202b 3 1) (Reg.operands [.gpr 1] [])) #v[2359]
    (.letOp (n := 2363) (.out 0x11202e (movR64M64Effect 0x11202e 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 2364) (.exec 0x11202e (LoadPre 0x11202e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11202e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11202e 5 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2365) (.out 0x112033 (andR64R64Effect 0x112033 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 6] []) (.reg (.gpr 5))) #v[2363, 2329]
    (.letOp (n := 2366) (.exec 0x112033 (fun s => s.RIP = 0x112033) (andR64R64Effect 0x112033 5 6) (Reg.operands [.gpr 5, .gpr 6] [])) #v[2363, 2329]
    (.letOp (n := 2367) (.out 0x112036 (movR64M64Effect 0x112036 14 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 2368) (.exec 0x112036 (LoadPre 0x112036 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112036 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112036 14 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2369) (.out 0x11203a (andR64R64Effect 0x11203a 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[2367, 2329]
    (.letOp (n := 2370) (.exec 0x11203a (fun s => s.RIP = 0x11203a) (andR64R64Effect 0x11203a 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[2367, 2329]
    (.letOp (n := 2371) (.out 0x11203d (andR64R64Effect 0x11203d 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[2310, 2329]
    (.letOp (n := 2372) (.exec 0x11203d (fun s => s.RIP = 0x11203d) (andR64R64Effect 0x11203d 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[2310, 2329]
    (.letOp (n := 2373) (.out 0x112040 (movR64R64Effect 0x112040 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[2329]
    (.letOp (n := 2374) (.exec 0x112040 (fun s => s.RIP = 0x112040) (movR64R64Effect 0x112040 7 6) (Reg.operands [.gpr 6] [])) #v[2329]
    (.letOp (n := 2375) (.out 0x112043 (movR64M64Effect 0x112043 1 (.sib 4 none 0 (.d32 0x190))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 2376) (.exec 0x112043 (LoadPre 0x112043 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x112043 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112043 1 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2377) (.exec 0x11204b (StorePre 0x11204b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11204b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11204b 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2375, 4]
    (.letOp (n := 2378) (.out 0x112050 (movR64R64Effect 0x112050 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[2365]
    (.letOp (n := 2379) (.exec 0x112050 (fun s => s.RIP = 0x112050) (movR64R64Effect 0x112050 0 5) (Reg.operands [.gpr 5] [])) #v[2365]
    (b_l110d64_55))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_54 : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x49, 0x01, 0xCB, 0x48, 0x83, 0xD2, 0x00, 0x48,
    0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x4C,
    0x0F, 0xA4, 0xDA, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x8B,
    0x4C, 0x24, 0x08, 0x48, 0x21, 0xC1, 0x48, 0x01, 0xD1, 0x48, 0x89, 0xCB, 0x48, 0x8B, 0x6C, 0x24,
    0x18, 0x48, 0x21, 0xF5, 0x4C, 0x8B, 0x34, 0x24, 0x49, 0x21, 0xF6, 0x49, 0x21, 0xF1, 0x48, 0x89,
    0xF7, 0x48, 0x8B, 0x8C, 0x24, 0x90, 0x01, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x28, 0x48, 0x89,
    0xE8] ++ bytes_l110d64_55

theorem code_l110d64_54 : ∀ x ∈ codeRange 0x111ff2 bytes_l110d64_54, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11ff2 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_55

def b_l110d64_53 : Block Op Label signature Reg.count 2298 :=
  .letOp (n := 2298) (.out 0x111f96 (atFlags StatusFlags.CF (adcR64M64Effect 0x111f96 1 (.sib 4 none 0 (.d8 0x28)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[2251, 4, 2296]
    (.letOp (n := 2299) (.exec 0x111f96 (LoadPre 0x111f96 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x111f96 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111f96 1 (.sib 4 none 0 (.d8 0x28)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2251, 4, 2296]
    (.letOp (n := 2300) (.out 0x111f9b (addR64M64Effect 0x111f9b 7 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[2295, 4]
    (.letOp (n := 2301) (.out 0x111f9b (addR64M64Effect 0x111f9b 7 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[2295, 4]
    (.letOp (n := 2302) (.exec 0x111f9b (LoadPre 0x111f9b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x111f9b + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x111f9b 7 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[2295, 4]
    (.letOp (n := 2303) (.out 0x111fa3 (atFlags StatusFlags.CF (adcR64M64Effect 0x111fa3 1 (.sib 4 none 0 (.d8 0x20)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[2298, 4, 2301]
    (.letOp (n := 2304) (.exec 0x111fa3 (LoadPre 0x111fa3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x111fa3 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111fa3 1 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2298, 4, 2301]
    (.letOp (n := 2305) (.out 0x111fa8 (addR64R64Effect 0x111fa8 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[2293, 2300]
    (.letOp (n := 2306) (.out 0x111fa8 (addR64R64Effect 0x111fa8 9 7) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 7] []) (.flag .CF)) #v[2293, 2300]
    (.letOp (n := 2307) (.exec 0x111fa8 (fun s => s.RIP = 0x111fa8) (addR64R64Effect 0x111fa8 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[2293, 2300]
    (.letOp (n := 2308) (.out 0x111fab (atFlags StatusFlags.CF (adcR64R64Effect 0x111fab 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[2303, 2291, 2306]
    (.letOp (n := 2309) (.exec 0x111fab (fun s => s.RIP = 0x111fab) (atFlags StatusFlags.CF (adcR64R64Effect 0x111fab 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2303, 2291, 2306]
    (.letOp (n := 2310) (.out 0x111fae (addR64R64Effect 0x111fae 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[2305, 2227]
    (.letOp (n := 2311) (.out 0x111fae (addR64R64Effect 0x111fae 9 12) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 12] []) (.flag .CF)) #v[2305, 2227]
    (.letOp (n := 2312) (.exec 0x111fae (fun s => s.RIP = 0x111fae) (addR64R64Effect 0x111fae 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[2305, 2227]
    (.letOp (n := 2313) (.out 0x111fb1 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111fb1 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[2308, 2311]
    (.letOp (n := 2314) (.exec 0x111fb1 (fun s => s.RIP = 0x111fb1) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111fb1 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2308, 2311]
    (.letOp (n := 2315) (.out 0x111fb5 (shldR64R64Effect 0x111fb5 5 11 6 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[2280, 2277]
    (.letOp (n := 2316) (.exec 0x111fb5 (fun s => s.RIP = 0x111fb5) (shldR64R64Effect 0x111fb5 5 11 6 12) (Reg.operands [.gpr 11, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2280, 2277]
    (.letOp (n := 2317) (.out 0x111fba (movR64M64Effect 0x111fba 0 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2318) (.exec 0x111fba (LoadPre 0x111fba (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x111fba + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111fba 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2319) (.exec 0x111fc2 (StorePre 0x111fc2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x111fc2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111fc2 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2317, 4]
    (.letOp (n := 2320) (.out 0x111fca (shldR64R64Effect 0x111fca 5 1 9 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2313, 2310]
    (.letOp (n := 2321) (.exec 0x111fca (fun s => s.RIP = 0x111fca) (shldR64R64Effect 0x111fca 5 1 9 12) (Reg.operands [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2313, 2310]
    (.letOp (n := 2322) (.out 0x111fcf (movR64R64Effect 0x111fcf 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[2315]
    (.letOp (n := 2323) (.exec 0x111fcf (fun s => s.RIP = 0x111fcf) (movR64R64Effect 0x111fcf 0 11) (Reg.operands [.gpr 11] [])) #v[2315]
    (.letOp (n := 2324) (.out 0x111fd2 (mulR64Effect 0x111fd2 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[2288, 2322]
    (.letOp (n := 2325) (.out 0x111fd2 (mulR64Effect 0x111fd2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[2288, 2322]
    (.letOp (n := 2326) (.exec 0x111fd2 (fun s => s.RIP = 0x111fd2) (mulR64Effect 0x111fd2 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[2288, 2322]
    (.letOp (n := 2327) (.out 0x111fd5 (movR64R64Effect 0x111fd5 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[2324]
    (.letOp (n := 2328) (.exec 0x111fd5 (fun s => s.RIP = 0x111fd5) (movR64R64Effect 0x111fd5 11 0) (Reg.operands [.gpr 0] [])) #v[2324]
    (.letOp (n := 2329) (.out 0x111fd8 (movR64R64Effect 0x111fd8 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[2284]
    (.letOp (n := 2330) (.exec 0x111fd8 (fun s => s.RIP = 0x111fd8) (movR64R64Effect 0x111fd8 6 3) (Reg.operands [.gpr 3] [])) #v[2284]
    (.letOp (n := 2331) (.out 0x111fdb (movR64M64Effect 0x111fdb 0 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2332) (.exec 0x111fdb (LoadPre 0x111fdb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x111fdb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111fdb 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2333) (.out 0x111fe3 (andR64R64Effect 0x111fe3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[2331, 2284]
    (.letOp (n := 2334) (.exec 0x111fe3 (fun s => s.RIP = 0x111fe3) (andR64R64Effect 0x111fe3 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[2331, 2284]
    (.letOp (n := 2335) (.out 0x111fe6 (addR64R64Effect 0x111fe6 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[2327, 2333]
    (.letOp (n := 2336) (.out 0x111fe6 (addR64R64Effect 0x111fe6 11 0) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 0] []) (.flag .CF)) #v[2327, 2333]
    (.letOp (n := 2337) (.exec 0x111fe6 (fun s => s.RIP = 0x111fe6) (addR64R64Effect 0x111fe6 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[2327, 2333]
    (.letOp (n := 2338) (.out 0x111fe9 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111fe9 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2325, 2336]
    (.letOp (n := 2339) (.exec 0x111fe9 (fun s => s.RIP = 0x111fe9) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111fe9 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2325, 2336]
    (.letOp (n := 2340) (.out 0x111fed (movR64M64Effect 0x111fed 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2341) (.exec 0x111fed (LoadPre 0x111fed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x111fed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111fed 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l110d64_54))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_53 : List UInt8 :=
  [0x48, 0x13, 0x4C, 0x24, 0x28, 0x48, 0x03, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x13, 0x4C,
    0x24, 0x20, 0x49, 0x01, 0xF9, 0x48, 0x11, 0xD1, 0x4D, 0x01, 0xE1, 0x48, 0x83, 0xD1, 0x00, 0x49,
    0x0F, 0xA4, 0xF3, 0x0C, 0x48, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24,
    0x38, 0x01, 0x00, 0x00, 0x4C, 0x0F, 0xA4, 0xC9, 0x0C, 0x4C, 0x89, 0xD8, 0x49, 0xF7, 0xE0, 0x49,
    0x89, 0xC3, 0x48, 0x89, 0xDE, 0x48, 0x8B, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x21, 0xD8,
    0x49, 0x01, 0xC3, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x30] ++ bytes_l110d64_54

theorem code_l110d64_53 : ∀ x ∈ codeRange 0x111f96 bytes_l110d64_53, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11f96 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_54

def b_l110d64_52 : Block Op Label signature Reg.count 2253 :=
  .letOp (n := 2253) (.out 0x111f3a (movR64M64Effect 0x111f3a 0 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2254) (.exec 0x111f3a (LoadPre 0x111f3a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x111f3a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111f3a 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2255) (.exec 0x111f42 (StorePre 0x111f42 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x111f42 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111f42 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2253, 4]
    (.letOp (n := 2256) (.out 0x111f4a (movR64M64Effect 0x111f4a 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2257) (.exec 0x111f4a (LoadPre 0x111f4a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x111f4a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111f4a 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2258) (.out 0x111f52 (mulR64Effect 0x111f52 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[2162, 2256]
    (.letOp (n := 2259) (.out 0x111f52 (mulR64Effect 0x111f52 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[2162, 2256]
    (.letOp (n := 2260) (.exec 0x111f52 (fun s => s.RIP = 0x111f52) (mulR64Effect 0x111f52 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2162, 2256]
    (.letOp (n := 2261) (.out 0x111f55 (movR64R64Effect 0x111f55 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2259]
    (.letOp (n := 2262) (.exec 0x111f55 (fun s => s.RIP = 0x111f55) (movR64R64Effect 0x111f55 11 2) (Reg.operands [.gpr 2] [])) #v[2259]
    (.letOp (n := 2263) (.out 0x111f58 (movR64R64Effect 0x111f58 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[2258]
    (.letOp (n := 2264) (.exec 0x111f58 (fun s => s.RIP = 0x111f58) (movR64R64Effect 0x111f58 9 0) (Reg.operands [.gpr 0] [])) #v[2258]
    (.letOp (n := 2265) (.out 0x111f5b (movR64M64Effect 0x111f5b 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2266) (.exec 0x111f5b (LoadPre 0x111f5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x111f5b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111f5b 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2267) (.out 0x111f60 (mulR64Effect 0x111f60 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[2175, 2265]
    (.letOp (n := 2268) (.out 0x111f60 (mulR64Effect 0x111f60 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[2175, 2265]
    (.letOp (n := 2269) (.exec 0x111f60 (fun s => s.RIP = 0x111f60) (mulR64Effect 0x111f60 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[2175, 2265]
    (.letOp (n := 2270) (.out 0x111f63 (movR64R64Effect 0x111f63 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2267]
    (.letOp (n := 2271) (.exec 0x111f63 (fun s => s.RIP = 0x111f63) (movR64R64Effect 0x111f63 6 0) (Reg.operands [.gpr 0] [])) #v[2267]
    (.letOp (n := 2272) (.out 0x111f66 (addR64R64Effect 0x111f66 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[2270, 2263]
    (.letOp (n := 2273) (.out 0x111f66 (addR64R64Effect 0x111f66 6 9) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 9] []) (.flag .CF)) #v[2270, 2263]
    (.letOp (n := 2274) (.exec 0x111f66 (fun s => s.RIP = 0x111f66) (addR64R64Effect 0x111f66 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[2270, 2263]
    (.letOp (n := 2275) (.out 0x111f69 (atFlags StatusFlags.CF (adcR64R64Effect 0x111f69 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[2261, 2268, 2273]
    (.letOp (n := 2276) (.exec 0x111f69 (fun s => s.RIP = 0x111f69) (atFlags StatusFlags.CF (adcR64R64Effect 0x111f69 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2261, 2268, 2273]
    (.letOp (n := 2277) (.out 0x111f6c (addR64R64Effect 0x111f6c 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[2272, 2195]
    (.letOp (n := 2278) (.out 0x111f6c (addR64R64Effect 0x111f6c 6 13) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 13] []) (.flag .CF)) #v[2272, 2195]
    (.letOp (n := 2279) (.exec 0x111f6c (fun s => s.RIP = 0x111f6c) (addR64R64Effect 0x111f6c 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[2272, 2195]
    (.letOp (n := 2280) (.out 0x111f6f (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111f6f 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[2275, 2278]
    (.letOp (n := 2281) (.exec 0x111f6f (fun s => s.RIP = 0x111f6f) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111f6f 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2275, 2278]
    (.letOp (n := 2282) (.out 0x111f73 (movR64R64Effect 0x111f73 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2277]
    (.letOp (n := 2283) (.exec 0x111f73 (fun s => s.RIP = 0x111f73) (movR64R64Effect 0x111f73 0 6) (Reg.operands [.gpr 6] [])) #v[2277]
    (.letOp (n := 2284) (.out 0x111f76 (movR64Imm64Effect 0x111f76 3 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 2285) (.exec 0x111f76 (fun s => s.RIP = 0x111f76) (movR64Imm64Effect 0x111f76 3 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2286) (.out 0x111f80 (andR64R64Effect 0x111f80 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[2282, 2284]
    (.letOp (n := 2287) (.exec 0x111f80 (fun s => s.RIP = 0x111f80) (andR64R64Effect 0x111f80 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[2282, 2284]
    (.letOp (n := 2288) (.out 0x111f83 (movR64Imm64Effect 0x111f83 8 0x1000003d10) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 2289) (.exec 0x111f83 (fun s => s.RIP = 0x111f83) (movR64Imm64Effect 0x111f83 8 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2290) (.out 0x111f8d (mulR64Effect 0x111f8d 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[2288, 2286]
    (.letOp (n := 2291) (.out 0x111f8d (mulR64Effect 0x111f8d 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[2288, 2286]
    (.letOp (n := 2292) (.exec 0x111f8d (fun s => s.RIP = 0x111f8d) (mulR64Effect 0x111f8d 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[2288, 2286]
    (.letOp (n := 2293) (.out 0x111f90 (movR64R64Effect 0x111f90 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[2290]
    (.letOp (n := 2294) (.exec 0x111f90 (fun s => s.RIP = 0x111f90) (movR64R64Effect 0x111f90 9 0) (Reg.operands [.gpr 0] [])) #v[2290]
    (.letOp (n := 2295) (.out 0x111f93 (addR64R64Effect 0x111f93 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[2249, 2242]
    (.letOp (n := 2296) (.out 0x111f93 (addR64R64Effect 0x111f93 7 14) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 14] []) (.flag .CF)) #v[2249, 2242]
    (.letOp (n := 2297) (.exec 0x111f93 (fun s => s.RIP = 0x111f93) (addR64R64Effect 0x111f93 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[2249, 2242]
    (b_l110d64_53)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_52 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD3, 0x49, 0x89,
    0xC1, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0xC6, 0x4C, 0x01, 0xCE, 0x49,
    0x11, 0xD3, 0x4C, 0x01, 0xEE, 0x49, 0x83, 0xD3, 0x00, 0x48, 0x89, 0xF0, 0x48, 0xBB, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD8, 0x49, 0xB8, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xC1, 0x4C, 0x01, 0xF7] ++ bytes_l110d64_53

theorem code_l110d64_52 : ∀ x ∈ codeRange 0x111f3a bytes_l110d64_52, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11f3a 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_53

def b_l110d64_51 : Block Op Label signature Reg.count 2213 :=
  .letOp (n := 2213) (.out 0x111ee2 (addR64R64Effect 0x111ee2 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[2206, 2208]
    (.letOp (n := 2214) (.out 0x111ee2 (addR64R64Effect 0x111ee2 6 9) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 9] []) (.flag .CF)) #v[2206, 2208]
    (.letOp (n := 2215) (.exec 0x111ee2 (fun s => s.RIP = 0x111ee2) (addR64R64Effect 0x111ee2 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[2206, 2208]
    (.letOp (n := 2216) (.out 0x111ee5 (atFlags StatusFlags.CF (adcR64R64Effect 0x111ee5 12 2)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[2211, 2204, 2214]
    (.letOp (n := 2217) (.exec 0x111ee5 (fun s => s.RIP = 0x111ee5) (atFlags StatusFlags.CF (adcR64R64Effect 0x111ee5 12 2)) (Reg.operands [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2211, 2204, 2214]
    (.letOp (n := 2218) (.out 0x111ee8 (addR64M64Effect 0x111ee8 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[2213, 4]
    (.letOp (n := 2219) (.out 0x111ee8 (addR64M64Effect 0x111ee8 6 (.sib 4 none 0 .none)) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[2213, 4]
    (.letOp (n := 2220) (.exec 0x111ee8 (LoadPre 0x111ee8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111ee8 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x111ee8 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[2213, 4]
    (.letOp (n := 2221) (.exec 0x111eec (StorePre 0x111eec 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111eec + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111eec 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[2218, 4]
    (.letOp (n := 2222) (.out 0x111ef0 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111ef0 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[2216, 2219]
    (.letOp (n := 2223) (.exec 0x111ef0 (fun s => s.RIP = 0x111ef0) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111ef0 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2216, 2219]
    (.letOp (n := 2224) (.out 0x111ef4 (movR64M64Effect 0x111ef4 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2225) (.exec 0x111ef4 (LoadPre 0x111ef4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x111ef4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111ef4 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2226) (.exec 0x111efc (StorePre 0x111efc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x111efc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111efc 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2224, 4]
    (.letOp (n := 2227) (.out 0x111f04 (shldR64R64Effect 0x111f04 5 12 6 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[2222, 2218]
    (.letOp (n := 2228) (.exec 0x111f04 (fun s => s.RIP = 0x111f04) (shldR64R64Effect 0x111f04 5 12 6 12) (Reg.operands [.gpr 12, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2222, 2218]
    (.letOp (n := 2229) (.out 0x111f09 (movR64R64Effect 0x111f09 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2171]
    (.letOp (n := 2230) (.exec 0x111f09 (fun s => s.RIP = 0x111f09) (movR64R64Effect 0x111f09 0 8) (Reg.operands [.gpr 8] [])) #v[2171]
    (.letOp (n := 2231) (.out 0x111f0c (mulM64Effect 0x111f0c 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2229, 4]
    (.letOp (n := 2232) (.out 0x111f0c (mulM64Effect 0x111f0c 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2229, 4]
    (.letOp (n := 2233) (.exec 0x111f0c (LoadPre 0x111f0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x111f0c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x111f0c 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2229, 4]
    (.letOp (n := 2234) (.exec 0x111f11 (StorePre 0x111f11 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x111f11 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111f11 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2232, 4]
    (.letOp (n := 2235) (.exec 0x111f16 (StorePre 0x111f16 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x111f16 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111f16 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2231, 4]
    (.letOp (n := 2236) (.out 0x111f1e (movR64M64Effect 0x111f1e 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2237) (.exec 0x111f1e (LoadPre 0x111f1e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x111f1e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111f1e 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2238) (.out 0x111f23 (mulR64Effect 0x111f23 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[2140, 2236]
    (.letOp (n := 2239) (.out 0x111f23 (mulR64Effect 0x111f23 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[2140, 2236]
    (.letOp (n := 2240) (.exec 0x111f23 (fun s => s.RIP = 0x111f23) (mulR64Effect 0x111f23 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[2140, 2236]
    (.letOp (n := 2241) (.exec 0x111f26 (StorePre 0x111f26 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x111f26 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111f26 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2239, 4]
    (.letOp (n := 2242) (.out 0x111f2b (movR64R64Effect 0x111f2b 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[2238]
    (.letOp (n := 2243) (.exec 0x111f2b (fun s => s.RIP = 0x111f2b) (movR64R64Effect 0x111f2b 14 0) (Reg.operands [.gpr 0] [])) #v[2238]
    (.letOp (n := 2244) (.out 0x111f2e (movR64R64Effect 0x111f2e 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[2136]
    (.letOp (n := 2245) (.exec 0x111f2e (fun s => s.RIP = 0x111f2e) (movR64R64Effect 0x111f2e 0 5) (Reg.operands [.gpr 5] [])) #v[2136]
    (.letOp (n := 2246) (.out 0x111f31 (mulR64Effect 0x111f31 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2151, 2244]
    (.letOp (n := 2247) (.out 0x111f31 (mulR64Effect 0x111f31 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2151, 2244]
    (.letOp (n := 2248) (.exec 0x111f31 (fun s => s.RIP = 0x111f31) (mulR64Effect 0x111f31 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2151, 2244]
    (.letOp (n := 2249) (.out 0x111f34 (movR64R64Effect 0x111f34 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[2246]
    (.letOp (n := 2250) (.exec 0x111f34 (fun s => s.RIP = 0x111f34) (movR64R64Effect 0x111f34 7 0) (Reg.operands [.gpr 0] [])) #v[2246]
    (.letOp (n := 2251) (.out 0x111f37 (movR64R64Effect 0x111f37 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2247]
    (.letOp (n := 2252) (.exec 0x111f37 (fun s => s.RIP = 0x111f37) (movR64R64Effect 0x111f37 1 2) (Reg.operands [.gpr 2] [])) #v[2247]
    (b_l110d64_52))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_51 : List UInt8 :=
  [0x4C, 0x01, 0xCE, 0x49, 0x11, 0xD4, 0x48, 0x03, 0x34, 0x24, 0x48, 0x89, 0x34, 0x24, 0x49, 0x83,
    0xD4, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x28, 0x01,
    0x00, 0x00, 0x49, 0x0F, 0xA4, 0xF4, 0x0C, 0x4C, 0x89, 0xC0, 0x48, 0xF7, 0x64, 0x24, 0x20, 0x48,
    0x89, 0x54, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24,
    0x78, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0x54, 0x24, 0x28, 0x49, 0x89, 0xC6, 0x48, 0x89, 0xE8, 0x48,
    0xF7, 0xE1, 0x48, 0x89, 0xC7, 0x48, 0x89, 0xD1] ++ bytes_l110d64_52

theorem code_l110d64_51 : ∀ x ∈ codeRange 0x111ee2 bytes_l110d64_51, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11ee2 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_52

def b_l110d64_50 : Block Op Label signature Reg.count 2167 :=
  .letOp (n := 2167) (.out 0x111e84 (movR64R64Effect 0x111e84 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2165]
    (.letOp (n := 2168) (.exec 0x111e84 (fun s => s.RIP = 0x111e84) (movR64R64Effect 0x111e84 13 2) (Reg.operands [.gpr 2] [])) #v[2165]
    (.letOp (n := 2169) (.out 0x111e87 (movR64R64Effect 0x111e87 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[2164]
    (.letOp (n := 2170) (.exec 0x111e87 (fun s => s.RIP = 0x111e87) (movR64R64Effect 0x111e87 11 0) (Reg.operands [.gpr 0] [])) #v[2164]
    (.letOp (n := 2171) (.out 0x111e8a (movR64M64Effect 0x111e8a 8 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 2172) (.exec 0x111e8a (LoadPre 0x111e8a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x111e8a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111e8a 8 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2173) (.out 0x111e92 (movR64R64Effect 0x111e92 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2171]
    (.letOp (n := 2174) (.exec 0x111e92 (fun s => s.RIP = 0x111e92) (movR64R64Effect 0x111e92 0 8) (Reg.operands [.gpr 8] [])) #v[2171]
    (.letOp (n := 2175) (.out 0x111e95 (movR64M64Effect 0x111e95 15 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 2176) (.exec 0x111e95 (LoadPre 0x111e95 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x111e95 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111e95 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2177) (.out 0x111e9a (mulR64Effect 0x111e9a 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[2175, 2173]
    (.letOp (n := 2178) (.out 0x111e9a (mulR64Effect 0x111e9a 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[2175, 2173]
    (.letOp (n := 2179) (.exec 0x111e9a (fun s => s.RIP = 0x111e9a) (mulR64Effect 0x111e9a 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[2175, 2173]
    (.letOp (n := 2180) (.out 0x111e9d (addR64R64Effect 0x111e9d 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[2177, 2169]
    (.letOp (n := 2181) (.out 0x111e9d (addR64R64Effect 0x111e9d 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[2177, 2169]
    (.letOp (n := 2182) (.exec 0x111e9d (fun s => s.RIP = 0x111e9d) (addR64R64Effect 0x111e9d 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[2177, 2169]
    (.letOp (n := 2183) (.out 0x111ea0 (atFlags StatusFlags.CF (adcR64R64Effect 0x111ea0 13 2)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[2167, 2178, 2181]
    (.letOp (n := 2184) (.exec 0x111ea0 (fun s => s.RIP = 0x111ea0) (atFlags StatusFlags.CF (adcR64R64Effect 0x111ea0 13 2)) (Reg.operands [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2167, 2178, 2181]
    (.letOp (n := 2185) (.out 0x111ea3 (addR64R64Effect 0x111ea3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[2180, 2158]
    (.letOp (n := 2186) (.out 0x111ea3 (addR64R64Effect 0x111ea3 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[2180, 2158]
    (.letOp (n := 2187) (.exec 0x111ea3 (fun s => s.RIP = 0x111ea3) (addR64R64Effect 0x111ea3 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[2180, 2158]
    (.letOp (n := 2188) (.out 0x111ea6 (atFlags StatusFlags.CF (adcR64R64Effect 0x111ea6 13 6)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[2183, 2156, 2186]
    (.letOp (n := 2189) (.exec 0x111ea6 (fun s => s.RIP = 0x111ea6) (atFlags StatusFlags.CF (adcR64R64Effect 0x111ea6 13 6)) (Reg.operands [.gpr 13, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2183, 2156, 2186]
    (.letOp (n := 2190) (.out 0x111ea9 (addR64R64Effect 0x111ea9 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[2185, 2103]
    (.letOp (n := 2191) (.out 0x111ea9 (addR64R64Effect 0x111ea9 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[2185, 2103]
    (.letOp (n := 2192) (.exec 0x111ea9 (fun s => s.RIP = 0x111ea9) (addR64R64Effect 0x111ea9 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[2185, 2103]
    (.letOp (n := 2193) (.out 0x111eac (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111eac 13 0x0)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[2188, 2191]
    (.letOp (n := 2194) (.exec 0x111eac (fun s => s.RIP = 0x111eac) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111eac 13 0x0)) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2188, 2191]
    (.letOp (n := 2195) (.out 0x111eb0 (shldR64R64Effect 0x111eb0 5 13 0 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[2193, 2190]
    (.letOp (n := 2196) (.exec 0x111eb0 (fun s => s.RIP = 0x111eb0) (shldR64R64Effect 0x111eb0 5 13 0 12) (Reg.operands [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2193, 2190]
    (.letOp (n := 2197) (.out 0x111eb5 (movR64Imm64Effect 0x111eb5 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2198) (.exec 0x111eb5 (fun s => s.RIP = 0x111eb5) (movR64Imm64Effect 0x111eb5 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 2199) (.out 0x111ebf (andR64R64Effect 0x111ebf 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[2190, 2197]
    (.letOp (n := 2200) (.exec 0x111ebf (fun s => s.RIP = 0x111ebf) (andR64R64Effect 0x111ebf 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[2190, 2197]
    (.letOp (n := 2201) (.out 0x111ec2 (movR64Imm64Effect 0x111ec2 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2202) (.exec 0x111ec2 (fun s => s.RIP = 0x111ec2) (movR64Imm64Effect 0x111ec2 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 2203) (.out 0x111ecc (mulR64Effect 0x111ecc 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2201, 2199]
    (.letOp (n := 2204) (.out 0x111ecc (mulR64Effect 0x111ecc 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2201, 2199]
    (.letOp (n := 2205) (.exec 0x111ecc (fun s => s.RIP = 0x111ecc) (mulR64Effect 0x111ecc 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2201, 2199]
    (.letOp (n := 2206) (.out 0x111ecf (movR64R64Effect 0x111ecf 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2203]
    (.letOp (n := 2207) (.exec 0x111ecf (fun s => s.RIP = 0x111ecf) (movR64R64Effect 0x111ecf 6 0) (Reg.operands [.gpr 0] [])) #v[2203]
    (.letOp (n := 2208) (.out 0x111ed2 (addR64M64Effect 0x111ed2 9 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[2147, 4]
    (.letOp (n := 2209) (.out 0x111ed2 (addR64M64Effect 0x111ed2 9 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 4] []) (.flag .CF)) #v[2147, 4]
    (.letOp (n := 2210) (.exec 0x111ed2 (LoadPre 0x111ed2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x111ed2 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x111ed2 9 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[2147, 4]
    (.letOp (n := 2211) (.out 0x111eda (atFlags StatusFlags.CF (adcR64M64Effect 0x111eda 12 (.sib 4 none 0 (.d32 0xc0)))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 12))) #v[2145, 4, 2209]
    (.letOp (n := 2212) (.exec 0x111eda (LoadPre 0x111eda (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x111eda + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111eda 12 (.sib 4 none 0 (.d32 0xc0)))) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2145, 4, 2209]
    (b_l110d64_51))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_50 : List UInt8 :=
  [0x49, 0x89, 0xD5, 0x49, 0x89, 0xC3, 0x4C, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xC0, 0x4C, 0x8B, 0x7C, 0x24, 0x40, 0x49, 0xF7, 0xE7, 0x4C, 0x01, 0xD8, 0x49, 0x11, 0xD5, 0x48,
    0x01, 0xF8, 0x49, 0x11, 0xF5, 0x4C, 0x01, 0xF0, 0x49, 0x83, 0xD5, 0x00, 0x49, 0x0F, 0xA4, 0xC5,
    0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48, 0xBA,
    0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xC6, 0x4C, 0x03,
    0x8C, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x13, 0xA4, 0x24, 0xC0, 0x00, 0x00, 0x00] ++ bytes_l110d64_51

theorem code_l110d64_50 : ∀ x ∈ codeRange 0x111e84 bytes_l110d64_50, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11e84 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_51

def b_l110d64_49 : Block Op Label signature Reg.count 2126 :=
  .letOp (n := 2126) (.out 0x111e33 (shldR64R64Effect 0x111e33 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[2124, 2118]
    (.letOp (n := 2127) (.exec 0x111e33 (fun s => s.RIP = 0x111e33) (shldR64R64Effect 0x111e33 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2124, 2118]
    (.letOp (n := 2128) (.exec 0x111e38 (StorePre 0x111e38 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111e38 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111e38 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[2126, 4]
    (.letOp (n := 2129) (.out 0x111e3c (movR64R64Effect 0x111e3c 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[2076]
    (.letOp (n := 2130) (.exec 0x111e3c (fun s => s.RIP = 0x111e3c) (movR64R64Effect 0x111e3c 0 5) (Reg.operands [.gpr 5] [])) #v[2076]
    (.letOp (n := 2131) (.out 0x111e3f (mulR64Effect 0x111e3f 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[2036, 2129]
    (.letOp (n := 2132) (.out 0x111e3f (mulR64Effect 0x111e3f 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[2036, 2129]
    (.letOp (n := 2133) (.exec 0x111e3f (fun s => s.RIP = 0x111e3f) (mulR64Effect 0x111e3f 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[2036, 2129]
    (.letOp (n := 2134) (.exec 0x111e42 (StorePre 0x111e42 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x111e42 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111e42 2 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2132, 4]
    (.letOp (n := 2135) (.exec 0x111e4a (StorePre 0x111e4a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x111e4a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111e4a 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2131, 4]
    (.letOp (n := 2136) (.out 0x111e52 (movR64M64Effect 0x111e52 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 2137) (.exec 0x111e52 (LoadPre 0x111e52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x111e52 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111e52 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2138) (.out 0x111e57 (movR64R64Effect 0x111e57 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[2136]
    (.letOp (n := 2139) (.exec 0x111e57 (fun s => s.RIP = 0x111e57) (movR64R64Effect 0x111e57 0 5) (Reg.operands [.gpr 5] [])) #v[2136]
    (.letOp (n := 2140) (.out 0x111e5a (movR64M64Effect 0x111e5a 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 2141) (.exec 0x111e5a (LoadPre 0x111e5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x111e5a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111e5a 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2142) (.out 0x111e5f (mulR64Effect 0x111e5f 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[2140, 2138]
    (.letOp (n := 2143) (.out 0x111e5f (mulR64Effect 0x111e5f 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[2140, 2138]
    (.letOp (n := 2144) (.exec 0x111e5f (fun s => s.RIP = 0x111e5f) (mulR64Effect 0x111e5f 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[2140, 2138]
    (.letOp (n := 2145) (.out 0x111e62 (movR64R64Effect 0x111e62 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2143]
    (.letOp (n := 2146) (.exec 0x111e62 (fun s => s.RIP = 0x111e62) (movR64R64Effect 0x111e62 12 2) (Reg.operands [.gpr 2] [])) #v[2143]
    (.letOp (n := 2147) (.out 0x111e65 (movR64R64Effect 0x111e65 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[2142]
    (.letOp (n := 2148) (.exec 0x111e65 (fun s => s.RIP = 0x111e65) (movR64R64Effect 0x111e65 9 0) (Reg.operands [.gpr 0] [])) #v[2142]
    (.letOp (n := 2149) (.out 0x111e68 (movR64R64Effect 0x111e68 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[2043]
    (.letOp (n := 2150) (.exec 0x111e68 (fun s => s.RIP = 0x111e68) (movR64R64Effect 0x111e68 0 1) (Reg.operands [.gpr 1] [])) #v[2043]
    (.letOp (n := 2151) (.out 0x111e6b (movR64M64Effect 0x111e6b 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 2152) (.exec 0x111e6b (LoadPre 0x111e6b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x111e6b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111e6b 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2153) (.out 0x111e70 (mulR64Effect 0x111e70 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[2151, 2149]
    (.letOp (n := 2154) (.out 0x111e70 (mulR64Effect 0x111e70 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[2151, 2149]
    (.letOp (n := 2155) (.exec 0x111e70 (fun s => s.RIP = 0x111e70) (mulR64Effect 0x111e70 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2151, 2149]
    (.letOp (n := 2156) (.out 0x111e73 (movR64R64Effect 0x111e73 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2154]
    (.letOp (n := 2157) (.exec 0x111e73 (fun s => s.RIP = 0x111e73) (movR64R64Effect 0x111e73 6 2) (Reg.operands [.gpr 2] [])) #v[2154]
    (.letOp (n := 2158) (.out 0x111e76 (movR64R64Effect 0x111e76 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[2153]
    (.letOp (n := 2159) (.exec 0x111e76 (fun s => s.RIP = 0x111e76) (movR64R64Effect 0x111e76 7 0) (Reg.operands [.gpr 0] [])) #v[2153]
    (.letOp (n := 2160) (.out 0x111e79 (movR64R64Effect 0x111e79 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2054]
    (.letOp (n := 2161) (.exec 0x111e79 (fun s => s.RIP = 0x111e79) (movR64R64Effect 0x111e79 0 8) (Reg.operands [.gpr 8] [])) #v[2054]
    (.letOp (n := 2162) (.out 0x111e7c (movR64M64Effect 0x111e7c 10 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 2163) (.exec 0x111e7c (LoadPre 0x111e7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x111e7c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111e7c 10 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2164) (.out 0x111e81 (mulR64Effect 0x111e81 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[2162, 2160]
    (.letOp (n := 2165) (.out 0x111e81 (mulR64Effect 0x111e81 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[2162, 2160]
    (.letOp (n := 2166) (.exec 0x111e81 (fun s => s.RIP = 0x111e81) (mulR64Effect 0x111e81 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2162, 2160]
    (b_l110d64_50)))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_49 : List UInt8 :=
  [0x48, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0x89, 0x34, 0x24, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0xE3, 0x48,
    0x89, 0x94, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48,
    0x8B, 0x6C, 0x24, 0x50, 0x48, 0x89, 0xE8, 0x48, 0x8B, 0x5C, 0x24, 0x28, 0x48, 0xF7, 0xE3, 0x49,
    0x89, 0xD4, 0x49, 0x89, 0xC1, 0x48, 0x89, 0xC8, 0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0xF7, 0xE1,
    0x48, 0x89, 0xD6, 0x48, 0x89, 0xC7, 0x4C, 0x89, 0xC0, 0x4C, 0x8B, 0x54, 0x24, 0x60, 0x49, 0xF7,
    0xE2] ++ bytes_l110d64_50

theorem code_l110d64_49 : ∀ x ∈ codeRange 0x111e33 bytes_l110d64_49, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11e33 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_50

def b_l110d64_48 : Block Op Label signature Reg.count 2080 :=
  .letOp (n := 2080) (.out 0x111de0 (mulR64Effect 0x111de0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[1981, 2078]
    (.letOp (n := 2081) (.out 0x111de0 (mulR64Effect 0x111de0 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[1981, 2078]
    (.letOp (n := 2082) (.exec 0x111de0 (fun s => s.RIP = 0x111de0) (mulR64Effect 0x111de0 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1981, 2078]
    (.letOp (n := 2083) (.out 0x111de3 (addR64R64Effect 0x111de3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[2080, 2074]
    (.letOp (n := 2084) (.out 0x111de3 (addR64R64Effect 0x111de3 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[2080, 2074]
    (.letOp (n := 2085) (.exec 0x111de3 (fun s => s.RIP = 0x111de3) (addR64R64Effect 0x111de3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[2080, 2074]
    (.letOp (n := 2086) (.out 0x111de6 (atFlags StatusFlags.CF (adcR64R64Effect 0x111de6 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2072, 2081, 2084]
    (.letOp (n := 2087) (.exec 0x111de6 (fun s => s.RIP = 0x111de6) (atFlags StatusFlags.CF (adcR64R64Effect 0x111de6 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2072, 2081, 2084]
    (.letOp (n := 2088) (.out 0x111de9 (addR64R64Effect 0x111de9 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[2083, 2061]
    (.letOp (n := 2089) (.out 0x111de9 (addR64R64Effect 0x111de9 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[2083, 2061]
    (.letOp (n := 2090) (.exec 0x111de9 (fun s => s.RIP = 0x111de9) (addR64R64Effect 0x111de9 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[2083, 2061]
    (.letOp (n := 2091) (.out 0x111dec (atFlags StatusFlags.CF (adcR64R64Effect 0x111dec 14 11)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2086, 2063, 2089]
    (.letOp (n := 2092) (.exec 0x111dec (fun s => s.RIP = 0x111dec) (atFlags StatusFlags.CF (adcR64R64Effect 0x111dec 14 11)) (Reg.operands [.gpr 14, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2086, 2063, 2089]
    (.letOp (n := 2093) (.out 0x111def (addR64R64Effect 0x111def 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[2088, 2052]
    (.letOp (n := 2094) (.out 0x111def (addR64R64Effect 0x111def 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[2088, 2052]
    (.letOp (n := 2095) (.exec 0x111def (fun s => s.RIP = 0x111def) (addR64R64Effect 0x111def 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[2088, 2052]
    (.letOp (n := 2096) (.out 0x111df2 (atFlags StatusFlags.CF (adcR64R64Effect 0x111df2 14 12)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2091, 2050, 2094]
    (.letOp (n := 2097) (.exec 0x111df2 (fun s => s.RIP = 0x111df2) (atFlags StatusFlags.CF (adcR64R64Effect 0x111df2 14 12)) (Reg.operands [.gpr 14, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2091, 2050, 2094]
    (.letOp (n := 2098) (.out 0x111df5 (addR64R64Effect 0x111df5 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[2093, 2030]
    (.letOp (n := 2099) (.out 0x111df5 (addR64R64Effect 0x111df5 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[2093, 2030]
    (.letOp (n := 2100) (.exec 0x111df5 (fun s => s.RIP = 0x111df5) (addR64R64Effect 0x111df5 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[2093, 2030]
    (.letOp (n := 2101) (.out 0x111df8 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111df8 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[2096, 2099]
    (.letOp (n := 2102) (.exec 0x111df8 (fun s => s.RIP = 0x111df8) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111df8 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2096, 2099]
    (.letOp (n := 2103) (.out 0x111dfc (shldR64R64Effect 0x111dfc 5 14 0 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[2101, 2098]
    (.letOp (n := 2104) (.exec 0x111dfc (fun s => s.RIP = 0x111dfc) (shldR64R64Effect 0x111dfc 5 14 0 12) (Reg.operands [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2101, 2098]
    (.letOp (n := 2105) (.out 0x111e01 (shlR64Effect 0x111e01 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2098]
    (.letOp (n := 2106) (.exec 0x111e01 (fun s => s.RIP = 0x111e01) (shlR64Effect 0x111e01 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2098]
    (.letOp (n := 2107) (.out 0x111e05 (movR64Imm64Effect 0x111e05 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2108) (.exec 0x111e05 (fun s => s.RIP = 0x111e05) (movR64Imm64Effect 0x111e05 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 2109) (.out 0x111e0f (andR64R64Effect 0x111e0f 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[2105, 2107]
    (.letOp (n := 2110) (.exec 0x111e0f (fun s => s.RIP = 0x111e0f) (andR64R64Effect 0x111e0f 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[2105, 2107]
    (.letOp (n := 2111) (.out 0x111e12 (orR64R64Effect 0x111e12 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[2109, 2065]
    (.letOp (n := 2112) (.exec 0x111e12 (fun s => s.RIP = 0x111e12) (orR64R64Effect 0x111e12 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[2109, 2065]
    (.letOp (n := 2113) (.out 0x111e15 (movR64Imm64Effect 0x111e15 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2114) (.exec 0x111e15 (fun s => s.RIP = 0x111e15) (movR64Imm64Effect 0x111e15 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 2115) (.out 0x111e1f (mulR64Effect 0x111e1f 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[2113, 2111]
    (.letOp (n := 2116) (.out 0x111e1f (mulR64Effect 0x111e1f 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2113, 2111]
    (.letOp (n := 2117) (.exec 0x111e1f (fun s => s.RIP = 0x111e1f) (mulR64Effect 0x111e1f 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2113, 2111]
    (.letOp (n := 2118) (.out 0x111e22 (addR64M64Effect 0x111e22 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2115, 4]
    (.letOp (n := 2119) (.out 0x111e22 (addR64M64Effect 0x111e22 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[2115, 4]
    (.letOp (n := 2120) (.exec 0x111e22 (LoadPre 0x111e22 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111e22 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x111e22 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2115, 4]
    (.letOp (n := 2121) (.exec 0x111e27 (StorePre 0x111e27 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111e27 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111e27 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2118, 4]
    (.letOp (n := 2122) (.out 0x111e2c (movR64M64Effect 0x111e2c 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 2123) (.exec 0x111e2c (LoadPre 0x111e2c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111e2c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111e2c 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2124) (.out 0x111e30 (atFlags StatusFlags.CF (adcR64R64Effect 0x111e30 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[2122, 2116, 2119]
    (.letOp (n := 2125) (.exec 0x111e30 (fun s => s.RIP = 0x111e30) (atFlags StatusFlags.CF (adcR64R64Effect 0x111e30 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2122, 2116, 2119]
    (b_l110d64_49))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_48 : List UInt8 :=
  [0x48, 0xF7, 0xE7, 0x4C, 0x01, 0xF8, 0x49, 0x11, 0xD6, 0x4C, 0x01, 0xC8, 0x4D, 0x11, 0xDE, 0x48,
    0x01, 0xF0, 0x4D, 0x11, 0xE6, 0x4C, 0x01, 0xD0, 0x49, 0x83, 0xD6, 0x00, 0x49, 0x0F, 0xA4, 0xC6,
    0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48,
    0x21, 0xD0, 0x4C, 0x09, 0xE8, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE2, 0x48, 0x03, 0x44, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x34, 0x24,
    0x48, 0x11, 0xD6] ++ bytes_l110d64_49

theorem code_l110d64_48 : ∀ x ∈ codeRange 0x111de0 bytes_l110d64_48, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11de0 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_49

def b_l110d64_47 : Block Op Label signature Reg.count 2038 :=
  .letOp (n := 2038) (.out 0x111d8e (mulR64Effect 0x111d8e 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[2036, 2034]
    (.letOp (n := 2039) (.out 0x111d8e (mulR64Effect 0x111d8e 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[2036, 2034]
    (.letOp (n := 2040) (.exec 0x111d8e (fun s => s.RIP = 0x111d8e) (mulR64Effect 0x111d8e 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[2036, 2034]
    (.letOp (n := 2041) (.exec 0x111d91 (StorePre 0x111d91 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111d91 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111d91 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2039, 4]
    (.letOp (n := 2042) (.exec 0x111d95 (StorePre 0x111d95 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111d95 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111d95 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2038, 4]
    (.letOp (n := 2043) (.out 0x111d9a (movR64M64Effect 0x111d9a 1 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 2044) (.exec 0x111d9a (LoadPre 0x111d9a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x111d9a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111d9a 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2045) (.out 0x111da2 (movR64R64Effect 0x111da2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[2043]
    (.letOp (n := 2046) (.exec 0x111da2 (fun s => s.RIP = 0x111da2) (movR64R64Effect 0x111da2 0 1) (Reg.operands [.gpr 1] [])) #v[2043]
    (.letOp (n := 2047) (.out 0x111da5 (mulR64Effect 0x111da5 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[1954, 2045]
    (.letOp (n := 2048) (.out 0x111da5 (mulR64Effect 0x111da5 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[1954, 2045]
    (.letOp (n := 2049) (.exec 0x111da5 (fun s => s.RIP = 0x111da5) (mulR64Effect 0x111da5 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1954, 2045]
    (.letOp (n := 2050) (.out 0x111da8 (movR64R64Effect 0x111da8 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2048]
    (.letOp (n := 2051) (.exec 0x111da8 (fun s => s.RIP = 0x111da8) (movR64R64Effect 0x111da8 12 2) (Reg.operands [.gpr 2] [])) #v[2048]
    (.letOp (n := 2052) (.out 0x111dab (movR64R64Effect 0x111dab 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2047]
    (.letOp (n := 2053) (.exec 0x111dab (fun s => s.RIP = 0x111dab) (movR64R64Effect 0x111dab 6 0) (Reg.operands [.gpr 0] [])) #v[2047]
    (.letOp (n := 2054) (.out 0x111dae (movR64M64Effect 0x111dae 8 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 2055) (.exec 0x111dae (LoadPre 0x111dae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x111dae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111dae 8 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2056) (.out 0x111db3 (movR64R64Effect 0x111db3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2054]
    (.letOp (n := 2057) (.exec 0x111db3 (fun s => s.RIP = 0x111db3) (movR64R64Effect 0x111db3 0 8) (Reg.operands [.gpr 8] [])) #v[2054]
    (.letOp (n := 2058) (.out 0x111db6 (mulM64Effect 0x111db6 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2056, 4]
    (.letOp (n := 2059) (.out 0x111db6 (mulM64Effect 0x111db6 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2056, 4]
    (.letOp (n := 2060) (.exec 0x111db6 (LoadPre 0x111db6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x111db6 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x111db6 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2056, 4]
    (.letOp (n := 2061) (.out 0x111dbb (movR64R64Effect 0x111dbb 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[2058]
    (.letOp (n := 2062) (.exec 0x111dbb (fun s => s.RIP = 0x111dbb) (movR64R64Effect 0x111dbb 9 0) (Reg.operands [.gpr 0] [])) #v[2058]
    (.letOp (n := 2063) (.out 0x111dbe (movR64R64Effect 0x111dbe 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2059]
    (.letOp (n := 2064) (.exec 0x111dbe (fun s => s.RIP = 0x111dbe) (movR64R64Effect 0x111dbe 11 2) (Reg.operands [.gpr 2] [])) #v[2059]
    (.letOp (n := 2065) (.out 0x111dc1 (andR32Imm8Effect 0x111dc1 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[2032]
    (.letOp (n := 2066) (.exec 0x111dc1 (fun s => s.RIP = 0x111dc1) (andR32Imm8Effect 0x111dc1 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[2032]
    (.letOp (n := 2067) (.out 0x111dc5 (movR64M64Effect 0x111dc5 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2068) (.exec 0x111dc5 (LoadPre 0x111dc5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x111dc5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111dc5 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2069) (.out 0x111dcd (mulM64Effect 0x111dcd 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[2067, 4]
    (.letOp (n := 2070) (.out 0x111dcd (mulM64Effect 0x111dcd 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[2067, 4]
    (.letOp (n := 2071) (.exec 0x111dcd (LoadPre 0x111dcd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x111dcd + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x111dcd 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2067, 4]
    (.letOp (n := 2072) (.out 0x111dd2 (movR64R64Effect 0x111dd2 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2070]
    (.letOp (n := 2073) (.exec 0x111dd2 (fun s => s.RIP = 0x111dd2) (movR64R64Effect 0x111dd2 14 2) (Reg.operands [.gpr 2] [])) #v[2070]
    (.letOp (n := 2074) (.out 0x111dd5 (movR64R64Effect 0x111dd5 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[2069]
    (.letOp (n := 2075) (.exec 0x111dd5 (fun s => s.RIP = 0x111dd5) (movR64R64Effect 0x111dd5 15 0) (Reg.operands [.gpr 0] [])) #v[2069]
    (.letOp (n := 2076) (.out 0x111dd8 (movR64M64Effect 0x111dd8 5 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 2077) (.exec 0x111dd8 (LoadPre 0x111dd8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x111dd8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111dd8 5 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2078) (.out 0x111ddd (movR64R64Effect 0x111ddd 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[2076]
    (.letOp (n := 2079) (.exec 0x111ddd (fun s => s.RIP = 0x111ddd) (movR64R64Effect 0x111ddd 0 5) (Reg.operands [.gpr 5] [])) #v[2076]
    (b_l110d64_48))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_47 : List UInt8 :=
  [0x48, 0xF7, 0xE3, 0x48, 0x89, 0x14, 0x24, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x8C, 0x24,
    0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD4, 0x48, 0x89, 0xC6,
    0x4C, 0x8B, 0x44, 0x24, 0x70, 0x4C, 0x89, 0xC0, 0x48, 0xF7, 0x64, 0x24, 0x48, 0x49, 0x89, 0xC1,
    0x49, 0x89, 0xD3, 0x41, 0x83, 0xE5, 0x0F, 0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0x64, 0x24, 0x60, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x6C, 0x24, 0x78, 0x48,
    0x89, 0xE8] ++ bytes_l110d64_48

theorem code_l110d64_47 : ∀ x ∈ codeRange 0x111d8e bytes_l110d64_47, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11d8e 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_48

def b_l110d64_46 : Block Op Label signature Reg.count 1992 :=
  .letOp (n := 1992) (.out 0x111d39 (movR64Imm64Effect 0x111d39 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1993) (.exec 0x111d39 (fun s => s.RIP = 0x111d39) (movR64Imm64Effect 0x111d39 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1994) (.out 0x111d43 (mulR64Effect 0x111d43 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1992, 1990]
    (.letOp (n := 1995) (.out 0x111d43 (mulR64Effect 0x111d43 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1992, 1990]
    (.letOp (n := 1996) (.exec 0x111d43 (fun s => s.RIP = 0x111d43) (mulR64Effect 0x111d43 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1992, 1990]
    (.letOp (n := 1997) (.out 0x111d46 (addR64R64Effect 0x111d46 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[1988, 1977]
    (.letOp (n := 1998) (.out 0x111d46 (addR64R64Effect 0x111d46 9 5) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 5] []) (.flag .CF)) #v[1988, 1977]
    (.letOp (n := 1999) (.exec 0x111d46 (fun s => s.RIP = 0x111d46) (addR64R64Effect 0x111d46 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[1988, 1977]
    (.letOp (n := 2000) (.out 0x111d49 (atFlags StatusFlags.CF (adcR64R64Effect 0x111d49 10 13)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1986, 1975, 1998]
    (.letOp (n := 2001) (.exec 0x111d49 (fun s => s.RIP = 0x111d49) (atFlags StatusFlags.CF (adcR64R64Effect 0x111d49 10 13)) (Reg.operands [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1986, 1975, 1998]
    (.letOp (n := 2002) (.out 0x111d4c (addR64R64Effect 0x111d4c 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[1997, 1968]
    (.letOp (n := 2003) (.out 0x111d4c (addR64R64Effect 0x111d4c 9 12) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 12] []) (.flag .CF)) #v[1997, 1968]
    (.letOp (n := 2004) (.exec 0x111d4c (fun s => s.RIP = 0x111d4c) (addR64R64Effect 0x111d4c 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[1997, 1968]
    (.letOp (n := 2005) (.out 0x111d4f (atFlags StatusFlags.CF (adcR64R64Effect 0x111d4f 10 1)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[2000, 1966, 2003]
    (.letOp (n := 2006) (.exec 0x111d4f (fun s => s.RIP = 0x111d4f) (atFlags StatusFlags.CF (adcR64R64Effect 0x111d4f 10 1)) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2000, 1966, 2003]
    (.letOp (n := 2007) (.out 0x111d52 (addR64M64Effect 0x111d52 9 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[2002, 4]
    (.letOp (n := 2008) (.out 0x111d52 (addR64M64Effect 0x111d52 9 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 4] []) (.flag .CF)) #v[2002, 4]
    (.letOp (n := 2009) (.exec 0x111d52 (LoadPre 0x111d52 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x111d52 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x111d52 9 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[2002, 4]
    (.letOp (n := 2010) (.out 0x111d5a (atFlags StatusFlags.CF (adcR64M64Effect 0x111d5a 10 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 10))) #v[2005, 4, 2008]
    (.letOp (n := 2011) (.exec 0x111d5a (LoadPre 0x111d5a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111d5a + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111d5a 10 (.sib 4 none 0 .none))) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2005, 4, 2008]
    (.letOp (n := 2012) (.out 0x111d5e (addR64M64Effect 0x111d5e 9 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[2007, 4]
    (.letOp (n := 2013) (.out 0x111d5e (addR64M64Effect 0x111d5e 9 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 4] []) (.flag .CF)) #v[2007, 4]
    (.letOp (n := 2014) (.exec 0x111d5e (LoadPre 0x111d5e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111d5e + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x111d5e 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[2007, 4]
    (.letOp (n := 2015) (.out 0x111d63 (atFlags StatusFlags.CF (adcR64M64Effect 0x111d63 10 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 10))) #v[2010, 4, 2013]
    (.letOp (n := 2016) (.exec 0x111d63 (LoadPre 0x111d63 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111d63 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111d63 10 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[2010, 4, 2013]
    (.letOp (n := 2017) (.out 0x111d68 (addR64R64Effect 0x111d68 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[1994, 2012]
    (.letOp (n := 2018) (.out 0x111d68 (addR64R64Effect 0x111d68 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[1994, 2012]
    (.letOp (n := 2019) (.exec 0x111d68 (fun s => s.RIP = 0x111d68) (addR64R64Effect 0x111d68 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[1994, 2012]
    (.letOp (n := 2020) (.out 0x111d6b (atFlags StatusFlags.CF (adcR64R64Effect 0x111d6b 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[2015, 1995, 2018]
    (.letOp (n := 2021) (.exec 0x111d6b (fun s => s.RIP = 0x111d6b) (atFlags StatusFlags.CF (adcR64R64Effect 0x111d6b 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2015, 1995, 2018]
    (.letOp (n := 2022) (.out 0x111d6e (movR64R64Effect 0x111d6e 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[2017]
    (.letOp (n := 2023) (.exec 0x111d6e (fun s => s.RIP = 0x111d6e) (movR64R64Effect 0x111d6e 13 0) (Reg.operands [.gpr 0] [])) #v[2017]
    (.letOp (n := 2024) (.out 0x111d71 (addR64R64Effect 0x111d71 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 6] []) (.reg (.gpr 13))) #v[2022, 1943]
    (.letOp (n := 2025) (.out 0x111d71 (addR64R64Effect 0x111d71 13 6) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 6] []) (.flag .CF)) #v[2022, 1943]
    (.letOp (n := 2026) (.exec 0x111d71 (fun s => s.RIP = 0x111d71) (addR64R64Effect 0x111d71 13 6) (Reg.operands [.gpr 13, .gpr 6] [])) #v[2022, 1943]
    (.letOp (n := 2027) (.exec 0x111d74 (StorePre 0x111d74 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111d74 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111d74 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[2024, 4]
    (.letOp (n := 2028) (.out 0x111d79 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111d79 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[2020, 2025]
    (.letOp (n := 2029) (.exec 0x111d79 (fun s => s.RIP = 0x111d79) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111d79 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2020, 2025]
    (.letOp (n := 2030) (.out 0x111d7d (shldR64R64Effect 0x111d7d 5 10 13 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2028, 2024]
    (.letOp (n := 2031) (.exec 0x111d7d (fun s => s.RIP = 0x111d7d) (shldR64R64Effect 0x111d7d 5 10 13 12) (Reg.operands [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2028, 2024]
    (.letOp (n := 2032) (.out 0x111d82 (shrR64Effect 0x111d82 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[2024]
    (.letOp (n := 2033) (.exec 0x111d82 (fun s => s.RIP = 0x111d82) (shrR64Effect 0x111d82 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2024]
    (.letOp (n := 2034) (.out 0x111d86 (movR64R64Effect 0x111d86 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[1883]
    (.letOp (n := 2035) (.exec 0x111d86 (fun s => s.RIP = 0x111d86) (movR64R64Effect 0x111d86 0 15) (Reg.operands [.gpr 15] [])) #v[1883]
    (.letOp (n := 2036) (.out 0x111d89 (movR64M64Effect 0x111d89 3 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 2037) (.exec 0x111d89 (LoadPre 0x111d89 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x111d89 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111d89 3 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l110d64_47))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_46 : List UInt8 :=
  [0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x01, 0xE9,
    0x4D, 0x11, 0xEA, 0x4D, 0x01, 0xE1, 0x49, 0x11, 0xCA, 0x4C, 0x03, 0x8C, 0x24, 0xC0, 0x00, 0x00,
    0x00, 0x4C, 0x13, 0x14, 0x24, 0x4C, 0x03, 0x4C, 0x24, 0x18, 0x4C, 0x13, 0x54, 0x24, 0x08, 0x4C,
    0x01, 0xC8, 0x49, 0x11, 0xD2, 0x49, 0x89, 0xC5, 0x49, 0x01, 0xF5, 0x4C, 0x89, 0x6C, 0x24, 0x08,
    0x49, 0x83, 0xD2, 0x00, 0x4D, 0x0F, 0xA4, 0xEA, 0x0C, 0x49, 0xC1, 0xED, 0x30, 0x4C, 0x89, 0xF8,
    0x48, 0x8B, 0x5C, 0x24, 0x20] ++ bytes_l110d64_47

theorem code_l110d64_46 : ∀ x ∈ codeRange 0x111d39 bytes_l110d64_46, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11d39 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_47

def b_l110d64_45 : Block Op Label signature Reg.count 1951 :=
  .letOp (n := 1951) (.exec 0x111cef (StorePre 0x111cef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111cef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111cef 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1947, 4]
    (.letOp (n := 1952) (.out 0x111cf4 (movR64M64Effect 0x111cf4 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1953) (.exec 0x111cf4 (LoadPre 0x111cf4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x111cf4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111cf4 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1954) (.out 0x111cf9 (movR64M64Effect 0x111cf9 14 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 1955) (.exec 0x111cf9 (LoadPre 0x111cf9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x111cf9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111cf9 14 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1956) (.out 0x111cfe (mulR64Effect 0x111cfe 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[1954, 1952]
    (.letOp (n := 1957) (.out 0x111cfe (mulR64Effect 0x111cfe 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[1954, 1952]
    (.letOp (n := 1958) (.exec 0x111cfe (fun s => s.RIP = 0x111cfe) (mulR64Effect 0x111cfe 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1954, 1952]
    (.letOp (n := 1959) (.exec 0x111d01 (StorePre 0x111d01 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111d01 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111d01 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1957, 4]
    (.letOp (n := 1960) (.exec 0x111d05 (StorePre 0x111d05 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x111d05 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111d05 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1956, 4]
    (.letOp (n := 1961) (.out 0x111d0d (movR64R64Effect 0x111d0d 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1857]
    (.letOp (n := 1962) (.exec 0x111d0d (fun s => s.RIP = 0x111d0d) (movR64R64Effect 0x111d0d 0 5) (Reg.operands [.gpr 5] [])) #v[1857]
    (.letOp (n := 1963) (.out 0x111d10 (mulR64Effect 0x111d10 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[1876, 1961]
    (.letOp (n := 1964) (.out 0x111d10 (mulR64Effect 0x111d10 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[1876, 1961]
    (.letOp (n := 1965) (.exec 0x111d10 (fun s => s.RIP = 0x111d10) (mulR64Effect 0x111d10 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1876, 1961]
    (.letOp (n := 1966) (.out 0x111d13 (movR64R64Effect 0x111d13 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1964]
    (.letOp (n := 1967) (.exec 0x111d13 (fun s => s.RIP = 0x111d13) (movR64R64Effect 0x111d13 1 2) (Reg.operands [.gpr 2] [])) #v[1964]
    (.letOp (n := 1968) (.out 0x111d16 (movR64R64Effect 0x111d16 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[1963]
    (.letOp (n := 1969) (.exec 0x111d16 (fun s => s.RIP = 0x111d16) (movR64R64Effect 0x111d16 12 0) (Reg.operands [.gpr 0] [])) #v[1963]
    (.letOp (n := 1970) (.out 0x111d19 (movR64R64Effect 0x111d19 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[1872]
    (.letOp (n := 1971) (.exec 0x111d19 (fun s => s.RIP = 0x111d19) (movR64R64Effect 0x111d19 0 3) (Reg.operands [.gpr 3] [])) #v[1872]
    (.letOp (n := 1972) (.out 0x111d1c (mulR64Effect 0x111d1c 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1887, 1970]
    (.letOp (n := 1973) (.out 0x111d1c (mulR64Effect 0x111d1c 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1887, 1970]
    (.letOp (n := 1974) (.exec 0x111d1c (fun s => s.RIP = 0x111d1c) (mulR64Effect 0x111d1c 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1887, 1970]
    (.letOp (n := 1975) (.out 0x111d1f (movR64R64Effect 0x111d1f 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[1973]
    (.letOp (n := 1976) (.exec 0x111d1f (fun s => s.RIP = 0x111d1f) (movR64R64Effect 0x111d1f 13 2) (Reg.operands [.gpr 2] [])) #v[1973]
    (.letOp (n := 1977) (.out 0x111d22 (movR64R64Effect 0x111d22 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[1972]
    (.letOp (n := 1978) (.exec 0x111d22 (fun s => s.RIP = 0x111d22) (movR64R64Effect 0x111d22 5 0) (Reg.operands [.gpr 0] [])) #v[1972]
    (.letOp (n := 1979) (.out 0x111d25 (movR64R64Effect 0x111d25 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[1883]
    (.letOp (n := 1980) (.exec 0x111d25 (fun s => s.RIP = 0x111d25) (movR64R64Effect 0x111d25 0 15) (Reg.operands [.gpr 15] [])) #v[1883]
    (.letOp (n := 1981) (.out 0x111d28 (movR64M64Effect 0x111d28 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 1982) (.exec 0x111d28 (LoadPre 0x111d28 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x111d28 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111d28 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1983) (.out 0x111d2d (mulR64Effect 0x111d2d 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[1981, 1979]
    (.letOp (n := 1984) (.out 0x111d2d (mulR64Effect 0x111d2d 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[1981, 1979]
    (.letOp (n := 1985) (.exec 0x111d2d (fun s => s.RIP = 0x111d2d) (mulR64Effect 0x111d2d 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1981, 1979]
    (.letOp (n := 1986) (.out 0x111d30 (movR64R64Effect 0x111d30 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[1984]
    (.letOp (n := 1987) (.exec 0x111d30 (fun s => s.RIP = 0x111d30) (movR64R64Effect 0x111d30 10 2) (Reg.operands [.gpr 2] [])) #v[1984]
    (.letOp (n := 1988) (.out 0x111d33 (movR64R64Effect 0x111d33 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[1983]
    (.letOp (n := 1989) (.exec 0x111d33 (fun s => s.RIP = 0x111d33) (movR64R64Effect 0x111d33 9 0) (Reg.operands [.gpr 0] [])) #v[1983]
    (.letOp (n := 1990) (.out 0x111d36 (movR64R64Effect 0x111d36 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[1941]
    (.letOp (n := 1991) (.exec 0x111d36 (fun s => s.RIP = 0x111d36) (movR64R64Effect 0x111d36 0 11) (Reg.operands [.gpr 11] [])) #v[1941]
    (b_l110d64_46)))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_45 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x4C, 0x8B, 0x74, 0x24, 0x28, 0x49,
    0xF7, 0xE6, 0x48, 0x89, 0x14, 0x24, 0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89,
    0xE8, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC4, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE0,
    0x49, 0x89, 0xD5, 0x48, 0x89, 0xC5, 0x4C, 0x89, 0xF8, 0x48, 0x8B, 0x7C, 0x24, 0x40, 0x48, 0xF7,
    0xE7, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC1, 0x4C, 0x89, 0xD8] ++ bytes_l110d64_46

theorem code_l110d64_45 : ∀ x ∈ codeRange 0x111cef bytes_l110d64_45, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11cef 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_46

def b_l110d64_44 : Block Op Label signature Reg.count 1909 :=
  .letOp (n := 1909) (.exec 0x111c7f (StorePre 0x111c7f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x111c7f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111c7f 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1907, 4]
    (.letOp (n := 1910) (.out 0x111c87 (movR64Imm64Effect 0x111c87 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1911) (.exec 0x111c87 (fun s => s.RIP = 0x111c87) (movR64Imm64Effect 0x111c87 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1912) (.out 0x111c91 (andR64R64Effect 0x111c91 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1900, 1910]
    (.letOp (n := 1913) (.exec 0x111c91 (fun s => s.RIP = 0x111c91) (andR64R64Effect 0x111c91 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1900, 1910]
    (.letOp (n := 1914) (.out 0x111c94 (movR64Imm64Effect 0x111c94 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1915) (.exec 0x111c94 (fun s => s.RIP = 0x111c94) (movR64Imm64Effect 0x111c94 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1916) (.out 0x111c9e (mulR64Effect 0x111c9e 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1914, 1912]
    (.letOp (n := 1917) (.out 0x111c9e (mulR64Effect 0x111c9e 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1914, 1912]
    (.letOp (n := 1918) (.exec 0x111c9e (fun s => s.RIP = 0x111c9e) (mulR64Effect 0x111c9e 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1914, 1912]
    (.letOp (n := 1919) (.exec 0x111ca1 (StorePre 0x111ca1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x111ca1 + BitVec.ofNat 64 5)) 8) (andMREffect 0x111ca1 5 64 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1910, 4]
    (.letOp (n := 1920) (.out 0x111ca6 (addR64M64Effect 0x111ca6 13 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[1894, 4]
    (.letOp (n := 1921) (.out 0x111ca6 (addR64M64Effect 0x111ca6 13 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[1894, 4]
    (.letOp (n := 1922) (.exec 0x111ca6 (LoadPre 0x111ca6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x111ca6 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x111ca6 13 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[1894, 4]
    (.letOp (n := 1923) (.out 0x111cae (atFlags StatusFlags.CF (adcR64M64Effect 0x111cae 6 (.sib 4 none 0 (.d32 0xc0)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[1892, 4, 1921]
    (.letOp (n := 1924) (.exec 0x111cae (LoadPre 0x111cae (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x111cae + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111cae 6 (.sib 4 none 0 (.d32 0xc0)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1892, 4, 1921]
    (.letOp (n := 1925) (.out 0x111cb6 (addR64M64Effect 0x111cb6 13 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[1920, 4]
    (.letOp (n := 1926) (.out 0x111cb6 (addR64M64Effect 0x111cb6 13 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[1920, 4]
    (.letOp (n := 1927) (.exec 0x111cb6 (LoadPre 0x111cb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x111cb6 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x111cb6 13 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[1920, 4]
    (.letOp (n := 1928) (.out 0x111cbe (atFlags StatusFlags.CF (adcR64M64Effect 0x111cbe 6 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[1923, 4, 1926]
    (.letOp (n := 1929) (.exec 0x111cbe (LoadPre 0x111cbe (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111cbe + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111cbe 6 (.sib 4 none 0 .none))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1923, 4, 1926]
    (.letOp (n := 1930) (.out 0x111cc2 (addR64M64Effect 0x111cc2 13 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[1925, 4]
    (.letOp (n := 1931) (.out 0x111cc2 (addR64M64Effect 0x111cc2 13 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[1925, 4]
    (.letOp (n := 1932) (.exec 0x111cc2 (LoadPre 0x111cc2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111cc2 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x111cc2 13 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[1925, 4]
    (.letOp (n := 1933) (.out 0x111cc7 (atFlags StatusFlags.CF (adcR64M64Effect 0x111cc7 6 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[1928, 4, 1931]
    (.letOp (n := 1934) (.exec 0x111cc7 (LoadPre 0x111cc7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111cc7 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111cc7 6 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1928, 4, 1931]
    (.letOp (n := 1935) (.out 0x111ccc (addR64R64Effect 0x111ccc 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[1916, 1930]
    (.letOp (n := 1936) (.out 0x111ccc (addR64R64Effect 0x111ccc 0 13) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 13] []) (.flag .CF)) #v[1916, 1930]
    (.letOp (n := 1937) (.exec 0x111ccc (fun s => s.RIP = 0x111ccc) (addR64R64Effect 0x111ccc 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[1916, 1930]
    (.letOp (n := 1938) (.exec 0x111ccf (StorePre 0x111ccf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x111ccf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111ccf 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1935, 4]
    (.letOp (n := 1939) (.out 0x111cd7 (atFlags StatusFlags.CF (adcR64R64Effect 0x111cd7 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[1933, 1917, 1936]
    (.letOp (n := 1940) (.exec 0x111cd7 (fun s => s.RIP = 0x111cd7) (atFlags StatusFlags.CF (adcR64R64Effect 0x111cd7 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1933, 1917, 1936]
    (.letOp (n := 1941) (.out 0x111cda (shldR64R64Effect 0x111cda 5 11 12 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1905, 1903]
    (.letOp (n := 1942) (.exec 0x111cda (fun s => s.RIP = 0x111cda) (shldR64R64Effect 0x111cda 5 11 12 12) (Reg.operands [.gpr 11, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1905, 1903]
    (.letOp (n := 1943) (.out 0x111cdf (shldR64R64Effect 0x111cdf 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1939, 1935]
    (.letOp (n := 1944) (.exec 0x111cdf (fun s => s.RIP = 0x111cdf) (shldR64R64Effect 0x111cdf 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1939, 1935]
    (.letOp (n := 1945) (.out 0x111ce4 (movR64R64Effect 0x111ce4 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1896]
    (.letOp (n := 1946) (.exec 0x111ce4 (fun s => s.RIP = 0x111ce4) (movR64R64Effect 0x111ce4 0 7) (Reg.operands [.gpr 7] [])) #v[1896]
    (.letOp (n := 1947) (.out 0x111ce7 (mulR64Effect 0x111ce7 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[1850, 1945]
    (.letOp (n := 1948) (.out 0x111ce7 (mulR64Effect 0x111ce7 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[1850, 1945]
    (.letOp (n := 1949) (.exec 0x111ce7 (fun s => s.RIP = 0x111ce7) (mulR64Effect 0x111ce7 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[1850, 1945]
    (.letOp (n := 1950) (.exec 0x111cea (StorePre 0x111cea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111cea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111cea 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1948, 4]
    (b_l110d64_45))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_44 : List UInt8 :=
  [0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x0F, 0x00, 0x48, 0x21, 0xC8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE2, 0x48, 0x21, 0x4C, 0x24, 0x30, 0x4C, 0x03, 0xAC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48,
    0x13, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x03, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48,
    0x13, 0x34, 0x24, 0x4C, 0x03, 0x6C, 0x24, 0x18, 0x48, 0x13, 0x74, 0x24, 0x08, 0x4C, 0x01, 0xE8,
    0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x11, 0xD6, 0x4D, 0x0F, 0xA4, 0xE3, 0x0C,
    0x48, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0x89, 0xF8, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0x54, 0x24, 0x08] ++ bytes_l110d64_45

theorem code_l110d64_44 : ∀ x ∈ codeRange 0x111c7f bytes_l110d64_44, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11c7f 112 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_45

def b_l110d64_43 : Block Op Label signature Reg.count 1868 :=
  .letOp (n := 1868) (.out 0x111c25 (movR64M64Effect 0x111c25 1 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 1869) (.exec 0x111c25 (LoadPre 0x111c25 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x111c25 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111c25 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1870) (.out 0x111c2d (andR64R64Effect 0x111c2d 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1868, 1866]
    (.letOp (n := 1871) (.exec 0x111c2d (fun s => s.RIP = 0x111c2d) (andR64R64Effect 0x111c2d 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1868, 1866]
    (.letOp (n := 1872) (.out 0x111c30 (movR64M64Effect 0x111c30 3 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1873) (.exec 0x111c30 (LoadPre 0x111c30 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x111c30 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111c30 3 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1874) (.out 0x111c35 (movR64R64Effect 0x111c35 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[1872]
    (.letOp (n := 1875) (.exec 0x111c35 (fun s => s.RIP = 0x111c35) (movR64R64Effect 0x111c35 0 3) (Reg.operands [.gpr 3] [])) #v[1872]
    (.letOp (n := 1876) (.out 0x111c38 (movR64M64Effect 0x111c38 9 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 1877) (.exec 0x111c38 (LoadPre 0x111c38 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x111c38 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111c38 9 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1878) (.out 0x111c3d (mulR64Effect 0x111c3d 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[1876, 1874]
    (.letOp (n := 1879) (.out 0x111c3d (mulR64Effect 0x111c3d 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[1876, 1874]
    (.letOp (n := 1880) (.exec 0x111c3d (fun s => s.RIP = 0x111c3d) (mulR64Effect 0x111c3d 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1876, 1874]
    (.letOp (n := 1881) (.exec 0x111c40 (StorePre 0x111c40 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x111c40 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111c40 2 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1879, 4]
    (.letOp (n := 1882) (.exec 0x111c48 (StorePre 0x111c48 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x111c48 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111c48 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1878, 4]
    (.letOp (n := 1883) (.out 0x111c50 (movR64M64Effect 0x111c50 15 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 1884) (.exec 0x111c50 (LoadPre 0x111c50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x111c50 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111c50 15 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1885) (.out 0x111c55 (movR64R64Effect 0x111c55 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[1883]
    (.letOp (n := 1886) (.exec 0x111c55 (fun s => s.RIP = 0x111c55) (movR64R64Effect 0x111c55 0 15) (Reg.operands [.gpr 15] [])) #v[1883]
    (.letOp (n := 1887) (.out 0x111c58 (movR64M64Effect 0x111c58 8 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 1888) (.exec 0x111c58 (LoadPre 0x111c58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x111c58 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111c58 8 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1889) (.out 0x111c5d (mulR64Effect 0x111c5d 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1887, 1885]
    (.letOp (n := 1890) (.out 0x111c5d (mulR64Effect 0x111c5d 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1887, 1885]
    (.letOp (n := 1891) (.exec 0x111c5d (fun s => s.RIP = 0x111c5d) (mulR64Effect 0x111c5d 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1887, 1885]
    (.letOp (n := 1892) (.out 0x111c60 (movR64R64Effect 0x111c60 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1890]
    (.letOp (n := 1893) (.exec 0x111c60 (fun s => s.RIP = 0x111c60) (movR64R64Effect 0x111c60 6 2) (Reg.operands [.gpr 2] [])) #v[1890]
    (.letOp (n := 1894) (.out 0x111c63 (movR64R64Effect 0x111c63 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[1889]
    (.letOp (n := 1895) (.exec 0x111c63 (fun s => s.RIP = 0x111c63) (movR64R64Effect 0x111c63 13 0) (Reg.operands [.gpr 0] [])) #v[1889]
    (.letOp (n := 1896) (.out 0x111c66 (movR64M64Effect 0x111c66 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 1897) (.exec 0x111c66 (LoadPre 0x111c66 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x111c66 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111c66 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1898) (.out 0x111c6e (movR64R64Effect 0x111c6e 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1896]
    (.letOp (n := 1899) (.exec 0x111c6e (fun s => s.RIP = 0x111c6e) (movR64R64Effect 0x111c6e 0 7) (Reg.operands [.gpr 7] [])) #v[1896]
    (.letOp (n := 1900) (.out 0x111c71 (mulM64Effect 0x111c71 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1898, 4]
    (.letOp (n := 1901) (.out 0x111c71 (mulM64Effect 0x111c71 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1898, 4]
    (.letOp (n := 1902) (.exec 0x111c71 (LoadPre 0x111c71 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x111c71 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x111c71 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1898, 4]
    (.letOp (n := 1903) (.out 0x111c76 (movR64R64Effect 0x111c76 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[1900]
    (.letOp (n := 1904) (.exec 0x111c76 (fun s => s.RIP = 0x111c76) (movR64R64Effect 0x111c76 12 0) (Reg.operands [.gpr 0] [])) #v[1900]
    (.letOp (n := 1905) (.out 0x111c79 (movR64R64Effect 0x111c79 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[1901]
    (.letOp (n := 1906) (.exec 0x111c79 (fun s => s.RIP = 0x111c79) (movR64R64Effect 0x111c79 11 2) (Reg.operands [.gpr 2] [])) #v[1901]
    (.letOp (n := 1907) (.out 0x111c7c (addR64R64Effect 0x111c7c 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[1870, 1846]
    (.letOp (n := 1908) (.exec 0x111c7c (fun s => s.RIP = 0x111c7c) (addR64R64Effect 0x111c7c 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[1870, 1846]
    (b_l110d64_44)))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_43 : List UInt8 :=
  [0x48, 0x8B, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x21, 0xC1, 0x48, 0x8B, 0x5C, 0x24, 0x78,
    0x48, 0x89, 0xD8, 0x4C, 0x8B, 0x4C, 0x24, 0x48, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x94, 0x24, 0xC0,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x7C, 0x24, 0x50,
    0x4C, 0x89, 0xF8, 0x4C, 0x8B, 0x44, 0x24, 0x60, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0xD6, 0x49, 0x89,
    0xC5, 0x48, 0x8B, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24,
    0x40, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD3, 0x4C, 0x01, 0xF1] ++ bytes_l110d64_44

theorem code_l110d64_43 : ∀ x ∈ codeRange 0x111c25 bytes_l110d64_43, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11c25 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_44

def b_l110d64_42 : Block Op Label signature Reg.count 1828 :=
  .letOp (n := 1828) (.out 0x111bc7 (movR64R64Effect 0x111bc7 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[1815]
    (.letOp (n := 1829) (.exec 0x111bc7 (fun s => s.RIP = 0x111bc7) (movR64R64Effect 0x111bc7 0 6) (Reg.operands [.gpr 6] [])) #v[1815]
    (.letOp (n := 1830) (.out 0x111bca (mulR64Effect 0x111bca 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1790, 1828]
    (.letOp (n := 1831) (.out 0x111bca (mulR64Effect 0x111bca 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1790, 1828]
    (.letOp (n := 1832) (.exec 0x111bca (fun s => s.RIP = 0x111bca) (mulR64Effect 0x111bca 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1790, 1828]
    (.letOp (n := 1833) (.out 0x111bcd (movR64R64Effect 0x111bcd 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[1831]
    (.letOp (n := 1834) (.exec 0x111bcd (fun s => s.RIP = 0x111bcd) (movR64R64Effect 0x111bcd 14 2) (Reg.operands [.gpr 2] [])) #v[1831]
    (.letOp (n := 1835) (.out 0x111bd0 (addR64R64Effect 0x111bd0 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1821, 1830]
    (.letOp (n := 1836) (.out 0x111bd0 (addR64R64Effect 0x111bd0 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[1821, 1830]
    (.letOp (n := 1837) (.exec 0x111bd0 (fun s => s.RIP = 0x111bd0) (addR64R64Effect 0x111bd0 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1821, 1830]
    (.letOp (n := 1838) (.out 0x111bd3 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111bd3 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[1833, 1836]
    (.letOp (n := 1839) (.exec 0x111bd3 (fun s => s.RIP = 0x111bd3) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111bd3 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1833, 1836]
    (.letOp (n := 1840) (.out 0x111bd7 (addR64R64Effect 0x111bd7 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[1835, 1823]
    (.letOp (n := 1841) (.out 0x111bd7 (addR64R64Effect 0x111bd7 1 10) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 10] []) (.flag .CF)) #v[1835, 1823]
    (.letOp (n := 1842) (.exec 0x111bd7 (fun s => s.RIP = 0x111bd7) (addR64R64Effect 0x111bd7 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[1835, 1823]
    (.letOp (n := 1843) (.exec 0x111bda (StorePre 0x111bda 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x111bda + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111bda 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1840, 4]
    (.letOp (n := 1844) (.out 0x111bdf (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111bdf 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[1838, 1841]
    (.letOp (n := 1845) (.exec 0x111bdf (fun s => s.RIP = 0x111bdf) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111bdf 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1838, 1841]
    (.letOp (n := 1846) (.out 0x111be3 (shldR64R64Effect 0x111be3 5 14 1 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[1844, 1840]
    (.letOp (n := 1847) (.exec 0x111be3 (fun s => s.RIP = 0x111be3) (shldR64R64Effect 0x111be3 5 14 1 12) (Reg.operands [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1844, 1840]
    (.letOp (n := 1848) (.out 0x111be8 (movR64M64Effect 0x111be8 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1849) (.exec 0x111be8 (LoadPre 0x111be8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x111be8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111be8 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1850) (.out 0x111bed (movR64M64Effect 0x111bed 10 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 1851) (.exec 0x111bed (LoadPre 0x111bed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x111bed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111bed 10 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1852) (.out 0x111bf2 (mulR64Effect 0x111bf2 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[1850, 1848]
    (.letOp (n := 1853) (.out 0x111bf2 (mulR64Effect 0x111bf2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[1850, 1848]
    (.letOp (n := 1854) (.exec 0x111bf2 (fun s => s.RIP = 0x111bf2) (mulR64Effect 0x111bf2 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[1850, 1848]
    (.letOp (n := 1855) (.exec 0x111bf5 (StorePre 0x111bf5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111bf5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111bf5 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1853, 4]
    (.letOp (n := 1856) (.exec 0x111bfa (StorePre 0x111bfa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111bfa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111bfa 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1852, 4]
    (.letOp (n := 1857) (.out 0x111bff (movR64M64Effect 0x111bff 5 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 1858) (.exec 0x111bff (LoadPre 0x111bff (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x111bff + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111bff 5 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1859) (.out 0x111c07 (movR64R64Effect 0x111c07 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1857]
    (.letOp (n := 1860) (.exec 0x111c07 (fun s => s.RIP = 0x111c07) (movR64R64Effect 0x111c07 0 5) (Reg.operands [.gpr 5] [])) #v[1857]
    (.letOp (n := 1861) (.out 0x111c0a (mulM64Effect 0x111c0a 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1859, 4]
    (.letOp (n := 1862) (.out 0x111c0a (mulM64Effect 0x111c0a 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1859, 4]
    (.letOp (n := 1863) (.exec 0x111c0a (LoadPre 0x111c0a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x111c0a + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x111c0a 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1859, 4]
    (.letOp (n := 1864) (.exec 0x111c0f (StorePre 0x111c0f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x111c0f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111c0f 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1861, 4]
    (.letOp (n := 1865) (.exec 0x111c17 (StorePre 0x111c17 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111c17 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111c17 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1862, 4]
    (.letOp (n := 1866) (.out 0x111c1b (movR64Imm64Effect 0x111c1b 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1867) (.exec 0x111c1b (fun s => s.RIP = 0x111c1b) (movR64Imm64Effect 0x111c1b 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (b_l110d64_43))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_42 : List UInt8 :=
  [0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xD6, 0x48, 0x01, 0xC1, 0x49, 0x83, 0xD6, 0x00,
    0x4C, 0x01, 0xD1, 0x48, 0x89, 0x4C, 0x24, 0x30, 0x49, 0x83, 0xD6, 0x00, 0x49, 0x0F, 0xA4, 0xCE,
    0x0C, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x4C, 0x8B, 0x54, 0x24, 0x20, 0x49, 0xF7, 0xE2, 0x48, 0x89,
    0x54, 0x24, 0x08, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0xAC, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xE8, 0x48, 0xF7, 0x64, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x14, 0x24, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00] ++ bytes_l110d64_43

theorem code_l110d64_42 : ∀ x ∈ codeRange 0x111bc7 bytes_l110d64_42, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11bc7 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_43

def b_l110d64_41 : Block Op Label signature Reg.count 1784 :=
  .letOp (n := 1784) (.out 0x111b6a (movR64R64Effect 0x111b6a 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1779]
    (.letOp (n := 1785) (.exec 0x111b6a (fun s => s.RIP = 0x111b6a) (movR64R64Effect 0x111b6a 0 13) (Reg.operands [.gpr 13] [])) #v[1779]
    (.letOp (n := 1786) (.out 0x111b6d (movR64Imm64Effect 0x111b6d 3 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 1787) (.exec 0x111b6d (fun s => s.RIP = 0x111b6d) (movR64Imm64Effect 0x111b6d 3 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1788) (.out 0x111b77 (andR64R64Effect 0x111b77 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[1784, 1786]
    (.letOp (n := 1789) (.exec 0x111b77 (fun s => s.RIP = 0x111b77) (andR64R64Effect 0x111b77 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[1784, 1786]
    (.letOp (n := 1790) (.out 0x111b7a (movR64Imm64Effect 0x111b7a 8 0x1000003d10) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 1791) (.exec 0x111b7a (fun s => s.RIP = 0x111b7a) (movR64Imm64Effect 0x111b7a 8 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1792) (.out 0x111b84 (mulR64Effect 0x111b84 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1790, 1788]
    (.letOp (n := 1793) (.out 0x111b84 (mulR64Effect 0x111b84 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1790, 1788]
    (.letOp (n := 1794) (.exec 0x111b84 (fun s => s.RIP = 0x111b84) (mulR64Effect 0x111b84 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1790, 1788]
    (.letOp (n := 1795) (.out 0x111b87 (addR64R64Effect 0x111b87 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[1744, 1735]
    (.letOp (n := 1796) (.out 0x111b87 (addR64R64Effect 0x111b87 11 15) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 15] []) (.flag .CF)) #v[1744, 1735]
    (.letOp (n := 1797) (.exec 0x111b87 (fun s => s.RIP = 0x111b87) (addR64R64Effect 0x111b87 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[1744, 1735]
    (.letOp (n := 1798) (.out 0x111b8a (atFlags StatusFlags.CF (adcR64R64Effect 0x111b8a 10 9)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1742, 1733, 1796]
    (.letOp (n := 1799) (.exec 0x111b8a (fun s => s.RIP = 0x111b8a) (atFlags StatusFlags.CF (adcR64R64Effect 0x111b8a 10 9)) (Reg.operands [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1742, 1733, 1796]
    (.letOp (n := 1800) (.out 0x111b8d (addR64R64Effect 0x111b8d 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 12] []) (.reg (.gpr 11))) #v[1795, 1751]
    (.letOp (n := 1801) (.out 0x111b8d (addR64R64Effect 0x111b8d 11 12) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 12] []) (.flag .CF)) #v[1795, 1751]
    (.letOp (n := 1802) (.exec 0x111b8d (fun s => s.RIP = 0x111b8d) (addR64R64Effect 0x111b8d 11 12) (Reg.operands [.gpr 11, .gpr 12] [])) #v[1795, 1751]
    (.letOp (n := 1803) (.out 0x111b90 (atFlags StatusFlags.CF (adcR64R64Effect 0x111b90 10 7)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1798, 1753, 1801]
    (.letOp (n := 1804) (.exec 0x111b90 (fun s => s.RIP = 0x111b90) (atFlags StatusFlags.CF (adcR64R64Effect 0x111b90 10 7)) (Reg.operands [.gpr 10, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1798, 1753, 1801]
    (.letOp (n := 1805) (.out 0x111b93 (addR64R64Effect 0x111b93 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[1800, 1792]
    (.letOp (n := 1806) (.out 0x111b93 (addR64R64Effect 0x111b93 11 0) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 0] []) (.flag .CF)) #v[1800, 1792]
    (.letOp (n := 1807) (.exec 0x111b93 (fun s => s.RIP = 0x111b93) (addR64R64Effect 0x111b93 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[1800, 1792]
    (.letOp (n := 1808) (.out 0x111b96 (atFlags StatusFlags.CF (adcR64R64Effect 0x111b96 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1803, 1793, 1806]
    (.letOp (n := 1809) (.exec 0x111b96 (fun s => s.RIP = 0x111b96) (atFlags StatusFlags.CF (adcR64R64Effect 0x111b96 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1803, 1793, 1806]
    (.letOp (n := 1810) (.out 0x111b99 (addR64R64Effect 0x111b99 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[1805, 1724]
    (.letOp (n := 1811) (.out 0x111b99 (addR64R64Effect 0x111b99 11 1) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 1] []) (.flag .CF)) #v[1805, 1724]
    (.letOp (n := 1812) (.exec 0x111b99 (fun s => s.RIP = 0x111b99) (addR64R64Effect 0x111b99 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[1805, 1724]
    (.letOp (n := 1813) (.out 0x111b9c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111b9c 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1808, 1811]
    (.letOp (n := 1814) (.exec 0x111b9c (fun s => s.RIP = 0x111b9c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111b9c 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1808, 1811]
    (.letOp (n := 1815) (.out 0x111ba0 (shldR64R64Effect 0x111ba0 5 6 13 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1782, 1779]
    (.letOp (n := 1816) (.exec 0x111ba0 (fun s => s.RIP = 0x111ba0) (shldR64R64Effect 0x111ba0 5 6 13 12) (Reg.operands [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1782, 1779]
    (.letOp (n := 1817) (.out 0x111ba5 (movR64Imm64Effect 0x111ba5 0 0xffffffffffffe) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1818) (.exec 0x111ba5 (fun s => s.RIP = 0x111ba5) (movR64Imm64Effect 0x111ba5 0 0xffffffffffffe) (Reg.operands [] [])) #v[]
    (.letOp (n := 1819) (.out 0x111baf (movR64M64Effect 0x111baf 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 1820) (.exec 0x111baf (LoadPre 0x111baf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x111baf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111baf 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1821) (.out 0x111bb4 (andR64R64Effect 0x111bb4 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1819, 1817]
    (.letOp (n := 1822) (.exec 0x111bb4 (fun s => s.RIP = 0x111bb4) (andR64R64Effect 0x111bb4 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1819, 1817]
    (.letOp (n := 1823) (.out 0x111bb7 (shldR64R64Effect 0x111bb7 5 10 11 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[1813, 1810]
    (.letOp (n := 1824) (.exec 0x111bb7 (fun s => s.RIP = 0x111bb7) (shldR64R64Effect 0x111bb7 5 10 11 12) (Reg.operands [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1813, 1810]
    (.letOp (n := 1825) (.out 0x111bbc (andR64R64Effect 0x111bbc 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[1810, 1786]
    (.letOp (n := 1826) (.exec 0x111bbc (fun s => s.RIP = 0x111bbc) (andR64R64Effect 0x111bbc 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[1810, 1786]
    (.letOp (n := 1827) (.exec 0x111bbf (StorePre 0x111bbf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x111bbf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111bbf 11 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[1825, 4]
    (b_l110d64_42))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_41 : List UInt8 :=
  [0x4C, 0x89, 0xE8, 0x48, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD8,
    0x49, 0xB8, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE0, 0x4D, 0x01, 0xFB,
    0x4D, 0x11, 0xCA, 0x4D, 0x01, 0xE3, 0x49, 0x11, 0xFA, 0x49, 0x01, 0xC3, 0x49, 0x11, 0xD2, 0x49,
    0x01, 0xCB, 0x49, 0x83, 0xD2, 0x00, 0x4C, 0x0F, 0xA4, 0xEE, 0x0C, 0x48, 0xB8, 0xFE, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x21, 0xC1, 0x4D, 0x0F, 0xA4,
    0xDA, 0x0C, 0x49, 0x21, 0xDB, 0x4C, 0x89, 0x9C, 0x24, 0xF8, 0x00, 0x00, 0x00] ++ bytes_l110d64_42

theorem code_l110d64_41 : ∀ x ∈ codeRange 0x111b6a bytes_l110d64_41, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11b6a 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_42

def b_l110d64_40 : Block Op Label signature Reg.count 1739 :=
  .letOp (n := 1739) (.out 0x111b1d (mulM64Effect 0x111b1d 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1737, 4]
    (.letOp (n := 1740) (.out 0x111b1d (mulM64Effect 0x111b1d 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1737, 4]
    (.letOp (n := 1741) (.exec 0x111b1d (LoadPre 0x111b1d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x111b1d + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x111b1d 8 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1737, 4]
    (.letOp (n := 1742) (.out 0x111b25 (movR64R64Effect 0x111b25 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[1740]
    (.letOp (n := 1743) (.exec 0x111b25 (fun s => s.RIP = 0x111b25) (movR64R64Effect 0x111b25 10 2) (Reg.operands [.gpr 2] [])) #v[1740]
    (.letOp (n := 1744) (.out 0x111b28 (movR64R64Effect 0x111b28 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[1739]
    (.letOp (n := 1745) (.exec 0x111b28 (fun s => s.RIP = 0x111b28) (movR64R64Effect 0x111b28 11 0) (Reg.operands [.gpr 0] [])) #v[1739]
    (.letOp (n := 1746) (.out 0x111b2b (movR64R64Effect 0x111b2b 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1653]
    (.letOp (n := 1747) (.exec 0x111b2b (fun s => s.RIP = 0x111b2b) (movR64R64Effect 0x111b2b 0 13) (Reg.operands [.gpr 13] [])) #v[1653]
    (.letOp (n := 1748) (.out 0x111b2e (mulM64Effect 0x111b2e 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1746, 4]
    (.letOp (n := 1749) (.out 0x111b2e (mulM64Effect 0x111b2e 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1746, 4]
    (.letOp (n := 1750) (.exec 0x111b2e (LoadPre 0x111b2e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x111b2e + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x111b2e 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1746, 4]
    (.letOp (n := 1751) (.out 0x111b33 (movR64R64Effect 0x111b33 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[1748]
    (.letOp (n := 1752) (.exec 0x111b33 (fun s => s.RIP = 0x111b33) (movR64R64Effect 0x111b33 12 0) (Reg.operands [.gpr 0] [])) #v[1748]
    (.letOp (n := 1753) (.out 0x111b36 (movR64R64Effect 0x111b36 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[1749]
    (.letOp (n := 1754) (.exec 0x111b36 (fun s => s.RIP = 0x111b36) (movR64R64Effect 0x111b36 7 2) (Reg.operands [.gpr 2] [])) #v[1749]
    (.letOp (n := 1755) (.out 0x111b39 (andR64R64Effect 0x111b39 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[1726, 1664]
    (.letOp (n := 1756) (.exec 0x111b39 (fun s => s.RIP = 0x111b39) (andR64R64Effect 0x111b39 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[1726, 1664]
    (.letOp (n := 1757) (.exec 0x111b3c (StorePre 0x111b3c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x111b3c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111b3c 3 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1755, 4]
    (.letOp (n := 1758) (.out 0x111b44 (movR64R64Effect 0x111b44 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1571]
    (.letOp (n := 1759) (.exec 0x111b44 (fun s => s.RIP = 0x111b44) (movR64R64Effect 0x111b44 0 5) (Reg.operands [.gpr 5] [])) #v[1571]
    (.letOp (n := 1760) (.out 0x111b47 (mulM64Effect 0x111b47 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1758, 4]
    (.letOp (n := 1761) (.out 0x111b47 (mulM64Effect 0x111b47 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1758, 4]
    (.letOp (n := 1762) (.exec 0x111b47 (LoadPre 0x111b47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111b47 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x111b47 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1758, 4]
    (.letOp (n := 1763) (.out 0x111b4c (movR64R64Effect 0x111b4c 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1761]
    (.letOp (n := 1764) (.exec 0x111b4c (fun s => s.RIP = 0x111b4c) (movR64R64Effect 0x111b4c 6 2) (Reg.operands [.gpr 2] [])) #v[1761]
    (.letOp (n := 1765) (.out 0x111b4f (movR64R64Effect 0x111b4f 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[1760]
    (.letOp (n := 1766) (.exec 0x111b4f (fun s => s.RIP = 0x111b4f) (movR64R64Effect 0x111b4f 5 0) (Reg.operands [.gpr 0] [])) #v[1760]
    (.letOp (n := 1767) (.out 0x111b52 (movR64R64Effect 0x111b52 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[1582]
    (.letOp (n := 1768) (.exec 0x111b52 (fun s => s.RIP = 0x111b52) (movR64R64Effect 0x111b52 0 8) (Reg.operands [.gpr 8] [])) #v[1582]
    (.letOp (n := 1769) (.out 0x111b55 (mulM64Effect 0x111b55 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1767, 4]
    (.letOp (n := 1770) (.out 0x111b55 (mulM64Effect 0x111b55 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1767, 4]
    (.letOp (n := 1771) (.exec 0x111b55 (LoadPre 0x111b55 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x111b55 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x111b55 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1767, 4]
    (.letOp (n := 1772) (.out 0x111b5a (movR64R64Effect 0x111b5a 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[1769]
    (.letOp (n := 1773) (.exec 0x111b5a (fun s => s.RIP = 0x111b5a) (movR64R64Effect 0x111b5a 13 0) (Reg.operands [.gpr 0] [])) #v[1769]
    (.letOp (n := 1774) (.out 0x111b5d (addR64R64Effect 0x111b5d 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[1772, 1765]
    (.letOp (n := 1775) (.out 0x111b5d (addR64R64Effect 0x111b5d 13 5) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 5] []) (.flag .CF)) #v[1772, 1765]
    (.letOp (n := 1776) (.exec 0x111b5d (fun s => s.RIP = 0x111b5d) (addR64R64Effect 0x111b5d 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[1772, 1765]
    (.letOp (n := 1777) (.out 0x111b60 (atFlags StatusFlags.CF (adcR64R64Effect 0x111b60 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[1763, 1770, 1775]
    (.letOp (n := 1778) (.exec 0x111b60 (fun s => s.RIP = 0x111b60) (atFlags StatusFlags.CF (adcR64R64Effect 0x111b60 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1763, 1770, 1775]
    (.letOp (n := 1779) (.out 0x111b63 (addR64R64Effect 0x111b63 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[1774, 1700]
    (.letOp (n := 1780) (.out 0x111b63 (addR64R64Effect 0x111b63 13 14) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 14] []) (.flag .CF)) #v[1774, 1700]
    (.letOp (n := 1781) (.exec 0x111b63 (fun s => s.RIP = 0x111b63) (addR64R64Effect 0x111b63 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[1774, 1700]
    (.letOp (n := 1782) (.out 0x111b66 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111b66 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[1777, 1780]
    (.letOp (n := 1783) (.exec 0x111b66 (fun s => s.RIP = 0x111b66) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111b66 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1777, 1780]
    (b_l110d64_41)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_40 : List UInt8 :=
  [0x48, 0xF7, 0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC3, 0x4C, 0x89,
    0xE8, 0x48, 0xF7, 0x64, 0x24, 0x68, 0x49, 0x89, 0xC4, 0x48, 0x89, 0xD7, 0x48, 0x21, 0xF3, 0x48,
    0x89, 0x9C, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0x64, 0x24, 0x10, 0x48,
    0x89, 0xD6, 0x48, 0x89, 0xC5, 0x4C, 0x89, 0xC0, 0x48, 0xF7, 0x64, 0x24, 0x38, 0x49, 0x89, 0xC5,
    0x49, 0x01, 0xED, 0x48, 0x11, 0xD6, 0x4D, 0x01, 0xF5, 0x48, 0x83, 0xD6, 0x00] ++ bytes_l110d64_41

theorem code_l110d64_40 : ∀ x ∈ codeRange 0x111b1d bytes_l110d64_40, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11b1d 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_41

def b_l110d64_39 : Block Op Label signature Reg.count 1693 :=
  .letOp (n := 1693) (.out 0x111ac7 (atFlags StatusFlags.CF (adcR64R64Effect 0x111ac7 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[1688, 1683, 1691]
    (.letOp (n := 1694) (.exec 0x111ac7 (fun s => s.RIP = 0x111ac7) (atFlags StatusFlags.CF (adcR64R64Effect 0x111ac7 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1688, 1683, 1691]
    (.letOp (n := 1695) (.out 0x111aca (addR64R64Effect 0x111aca 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[1690, 1611]
    (.letOp (n := 1696) (.out 0x111aca (addR64R64Effect 0x111aca 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[1690, 1611]
    (.letOp (n := 1697) (.exec 0x111aca (fun s => s.RIP = 0x111aca) (addR64R64Effect 0x111aca 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[1690, 1611]
    (.letOp (n := 1698) (.out 0x111acd (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111acd 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[1693, 1696]
    (.letOp (n := 1699) (.exec 0x111acd (fun s => s.RIP = 0x111acd) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111acd 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1693, 1696]
    (.letOp (n := 1700) (.out 0x111ad1 (shldR64R64Effect 0x111ad1 5 14 0 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[1698, 1695]
    (.letOp (n := 1701) (.exec 0x111ad1 (fun s => s.RIP = 0x111ad1) (shldR64R64Effect 0x111ad1 5 14 0 12) (Reg.operands [.gpr 14, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1698, 1695]
    (.letOp (n := 1702) (.out 0x111ad6 (andR64R64Effect 0x111ad6 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1695, 1664]
    (.letOp (n := 1703) (.exec 0x111ad6 (fun s => s.RIP = 0x111ad6) (andR64R64Effect 0x111ad6 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1695, 1664]
    (.letOp (n := 1704) (.out 0x111ad9 (movR64Imm64Effect 0x111ad9 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1705) (.exec 0x111ad9 (fun s => s.RIP = 0x111ad9) (movR64Imm64Effect 0x111ad9 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1706) (.out 0x111ae3 (mulR64Effect 0x111ae3 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1704, 1702]
    (.letOp (n := 1707) (.out 0x111ae3 (mulR64Effect 0x111ae3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1704, 1702]
    (.letOp (n := 1708) (.exec 0x111ae3 (fun s => s.RIP = 0x111ae3) (mulR64Effect 0x111ae3 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1704, 1702]
    (.letOp (n := 1709) (.out 0x111ae6 (addR64M64Effect 0x111ae6 15 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[1651, 4]
    (.letOp (n := 1710) (.out 0x111ae6 (addR64M64Effect 0x111ae6 15 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[1651, 4]
    (.letOp (n := 1711) (.exec 0x111ae6 (LoadPre 0x111ae6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x111ae6 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x111ae6 15 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[1651, 4]
    (.letOp (n := 1712) (.out 0x111aee (atFlags StatusFlags.CF (adcR64M64Effect 0x111aee 1 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[1649, 4, 1710]
    (.letOp (n := 1713) (.exec 0x111aee (LoadPre 0x111aee (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111aee + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111aee 1 (.sib 4 none 0 .none))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1649, 4, 1710]
    (.letOp (n := 1714) (.out 0x111af2 (addR64R64Effect 0x111af2 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[1709, 1706]
    (.letOp (n := 1715) (.out 0x111af2 (addR64R64Effect 0x111af2 15 0) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 0] []) (.flag .CF)) #v[1709, 1706]
    (.letOp (n := 1716) (.exec 0x111af2 (fun s => s.RIP = 0x111af2) (addR64R64Effect 0x111af2 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[1709, 1706]
    (.letOp (n := 1717) (.out 0x111af5 (atFlags StatusFlags.CF (adcR64R64Effect 0x111af5 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1712, 1707, 1715]
    (.letOp (n := 1718) (.exec 0x111af5 (fun s => s.RIP = 0x111af5) (atFlags StatusFlags.CF (adcR64R64Effect 0x111af5 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1712, 1707, 1715]
    (.letOp (n := 1719) (.out 0x111af8 (addR64R64Effect 0x111af8 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[1714, 1633]
    (.letOp (n := 1720) (.out 0x111af8 (addR64R64Effect 0x111af8 15 10) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 10] []) (.flag .CF)) #v[1714, 1633]
    (.letOp (n := 1721) (.exec 0x111af8 (fun s => s.RIP = 0x111af8) (addR64R64Effect 0x111af8 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[1714, 1633]
    (.letOp (n := 1722) (.out 0x111afb (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111afb 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1717, 1720]
    (.letOp (n := 1723) (.exec 0x111afb (fun s => s.RIP = 0x111afb) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111afb 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1717, 1720]
    (.letOp (n := 1724) (.out 0x111aff (shldR64R64Effect 0x111aff 5 1 15 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1722, 1719]
    (.letOp (n := 1725) (.exec 0x111aff (fun s => s.RIP = 0x111aff) (shldR64R64Effect 0x111aff 5 1 15 12) (Reg.operands [.gpr 1, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1722, 1719]
    (.letOp (n := 1726) (.out 0x111b04 (movR64R64Effect 0x111b04 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[1719]
    (.letOp (n := 1727) (.exec 0x111b04 (fun s => s.RIP = 0x111b04) (movR64R64Effect 0x111b04 3 15) (Reg.operands [.gpr 15] [])) #v[1719]
    (.letOp (n := 1728) (.out 0x111b07 (movR64M64Effect 0x111b07 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1729) (.exec 0x111b07 (LoadPre 0x111b07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111b07 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111b07 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1730) (.out 0x111b0c (mulR64Effect 0x111b0c 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[1680, 1728]
    (.letOp (n := 1731) (.out 0x111b0c (mulR64Effect 0x111b0c 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[1680, 1728]
    (.letOp (n := 1732) (.exec 0x111b0c (fun s => s.RIP = 0x111b0c) (mulR64Effect 0x111b0c 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[1680, 1728]
    (.letOp (n := 1733) (.out 0x111b0f (movR64R64Effect 0x111b0f 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[1731]
    (.letOp (n := 1734) (.exec 0x111b0f (fun s => s.RIP = 0x111b0f) (movR64R64Effect 0x111b0f 9 2) (Reg.operands [.gpr 2] [])) #v[1731]
    (.letOp (n := 1735) (.out 0x111b12 (movR64R64Effect 0x111b12 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1730]
    (.letOp (n := 1736) (.exec 0x111b12 (fun s => s.RIP = 0x111b12) (movR64R64Effect 0x111b12 15 0) (Reg.operands [.gpr 0] [])) #v[1730]
    (.letOp (n := 1737) (.out 0x111b15 (movR64M64Effect 0x111b15 0 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1738) (.exec 0x111b15 (LoadPre 0x111b15 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x111b15 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111b15 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l110d64_40))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_39 : List UInt8 :=
  [0x49, 0x11, 0xD6, 0x48, 0x01, 0xD8, 0x49, 0x83, 0xD6, 0x00, 0x49, 0x0F, 0xA4, 0xC6, 0x0C, 0x48,
    0x21, 0xF0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C,
    0x03, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x13, 0x0C, 0x24, 0x49, 0x01, 0xC7, 0x48, 0x11,
    0xD1, 0x4D, 0x01, 0xD7, 0x48, 0x83, 0xD1, 0x00, 0x4C, 0x0F, 0xA4, 0xF9, 0x0C, 0x4C, 0x89, 0xFB,
    0x48, 0x8B, 0x44, 0x24, 0x08, 0x49, 0xF7, 0xE3, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC7, 0x48, 0x8B,
    0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] ++ bytes_l110d64_40

theorem code_l110d64_39 : ∀ x ∈ codeRange 0x111ac7 bytes_l110d64_39, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11ac7 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_40

def b_l110d64_38 : Block Op Label signature Reg.count 1649 :=
  .letOp (n := 1649) (.out 0x111a71 (movR64R64Effect 0x111a71 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1647]
    (.letOp (n := 1650) (.exec 0x111a71 (fun s => s.RIP = 0x111a71) (movR64R64Effect 0x111a71 1 2) (Reg.operands [.gpr 2] [])) #v[1647]
    (.letOp (n := 1651) (.out 0x111a74 (movR64R64Effect 0x111a74 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1646]
    (.letOp (n := 1652) (.exec 0x111a74 (fun s => s.RIP = 0x111a74) (movR64R64Effect 0x111a74 15 0) (Reg.operands [.gpr 0] [])) #v[1646]
    (.letOp (n := 1653) (.out 0x111a77 (movR64M64Effect 0x111a77 13 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 1654) (.exec 0x111a77 (LoadPre 0x111a77 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x111a77 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111a77 13 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1655) (.out 0x111a7f (movR64R64Effect 0x111a7f 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1653]
    (.letOp (n := 1656) (.exec 0x111a7f (fun s => s.RIP = 0x111a7f) (movR64R64Effect 0x111a7f 0 13) (Reg.operands [.gpr 13] [])) #v[1653]
    (.letOp (n := 1657) (.out 0x111a82 (mulM64Effect 0x111a82 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1655, 4]
    (.letOp (n := 1658) (.out 0x111a82 (mulM64Effect 0x111a82 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1655, 4]
    (.letOp (n := 1659) (.exec 0x111a82 (LoadPre 0x111a82 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111a82 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x111a82 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1655, 4]
    (.letOp (n := 1660) (.out 0x111a87 (movR64R64Effect 0x111a87 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[1657]
    (.letOp (n := 1661) (.exec 0x111a87 (fun s => s.RIP = 0x111a87) (movR64R64Effect 0x111a87 7 0) (Reg.operands [.gpr 0] [])) #v[1657]
    (.letOp (n := 1662) (.out 0x111a8a (movR64R64Effect 0x111a8a 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[1658]
    (.letOp (n := 1663) (.exec 0x111a8a (fun s => s.RIP = 0x111a8a) (movR64R64Effect 0x111a8a 9 2) (Reg.operands [.gpr 2] [])) #v[1658]
    (.letOp (n := 1664) (.out 0x111a8d (movR64Imm64Effect 0x111a8d 6 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 1665) (.exec 0x111a8d (fun s => s.RIP = 0x111a8d) (movR64Imm64Effect 0x111a8d 6 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1666) (.out 0x111a97 (andR64R64Effect 0x111a97 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[1635, 1664]
    (.letOp (n := 1667) (.exec 0x111a97 (fun s => s.RIP = 0x111a97) (andR64R64Effect 0x111a97 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[1635, 1664]
    (.letOp (n := 1668) (.exec 0x111a9a (StorePre 0x111a9a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x111a9a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111a9a 11 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[1666, 4]
    (.letOp (n := 1669) (.out 0x111aa2 (movR64R64Effect 0x111aa2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1571]
    (.letOp (n := 1670) (.exec 0x111aa2 (fun s => s.RIP = 0x111aa2) (movR64R64Effect 0x111aa2 0 5) (Reg.operands [.gpr 5] [])) #v[1571]
    (.letOp (n := 1671) (.out 0x111aa5 (mulM64Effect 0x111aa5 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1669, 4]
    (.letOp (n := 1672) (.out 0x111aa5 (mulM64Effect 0x111aa5 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1669, 4]
    (.letOp (n := 1673) (.exec 0x111aa5 (LoadPre 0x111aa5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x111aa5 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x111aa5 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1669, 4]
    (.letOp (n := 1674) (.out 0x111aaa (movR64R64Effect 0x111aaa 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[1672]
    (.letOp (n := 1675) (.exec 0x111aaa (fun s => s.RIP = 0x111aaa) (movR64R64Effect 0x111aaa 14 2) (Reg.operands [.gpr 2] [])) #v[1672]
    (.letOp (n := 1676) (.out 0x111aad (movR64R64Effect 0x111aad 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[1671]
    (.letOp (n := 1677) (.exec 0x111aad (fun s => s.RIP = 0x111aad) (movR64R64Effect 0x111aad 12 0) (Reg.operands [.gpr 0] [])) #v[1671]
    (.letOp (n := 1678) (.out 0x111ab0 (movR64R64Effect 0x111ab0 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[1582]
    (.letOp (n := 1679) (.exec 0x111ab0 (fun s => s.RIP = 0x111ab0) (movR64R64Effect 0x111ab0 0 8) (Reg.operands [.gpr 8] [])) #v[1582]
    (.letOp (n := 1680) (.out 0x111ab3 (movR64M64Effect 0x111ab3 11 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 1681) (.exec 0x111ab3 (LoadPre 0x111ab3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x111ab3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111ab3 11 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1682) (.out 0x111abb (mulR64Effect 0x111abb 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[1680, 1678]
    (.letOp (n := 1683) (.out 0x111abb (mulR64Effect 0x111abb 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[1680, 1678]
    (.letOp (n := 1684) (.exec 0x111abb (fun s => s.RIP = 0x111abb) (mulR64Effect 0x111abb 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[1680, 1678]
    (.letOp (n := 1685) (.out 0x111abe (addR64R64Effect 0x111abe 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[1676, 1660]
    (.letOp (n := 1686) (.out 0x111abe (addR64R64Effect 0x111abe 12 7) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 7] []) (.flag .CF)) #v[1676, 1660]
    (.letOp (n := 1687) (.exec 0x111abe (fun s => s.RIP = 0x111abe) (addR64R64Effect 0x111abe 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[1676, 1660]
    (.letOp (n := 1688) (.out 0x111ac1 (atFlags StatusFlags.CF (adcR64R64Effect 0x111ac1 14 9)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[1674, 1662, 1686]
    (.letOp (n := 1689) (.exec 0x111ac1 (fun s => s.RIP = 0x111ac1) (atFlags StatusFlags.CF (adcR64R64Effect 0x111ac1 14 9)) (Reg.operands [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1674, 1662, 1686]
    (.letOp (n := 1690) (.out 0x111ac4 (addR64R64Effect 0x111ac4 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[1682, 1685]
    (.letOp (n := 1691) (.out 0x111ac4 (addR64R64Effect 0x111ac4 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[1682, 1685]
    (.letOp (n := 1692) (.exec 0x111ac4 (fun s => s.RIP = 0x111ac4) (addR64R64Effect 0x111ac4 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[1682, 1685]
    (b_l110d64_39))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_38 : List UInt8 :=
  [0x48, 0x89, 0xD1, 0x49, 0x89, 0xC7, 0x4C, 0x8B, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xE8, 0x48, 0xF7, 0x64, 0x24, 0x10, 0x48, 0x89, 0xC7, 0x49, 0x89, 0xD1, 0x48, 0xBE, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xF3, 0x4C, 0x89, 0x9C, 0x24, 0xC8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0x64, 0x24, 0x38, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x4C,
    0x89, 0xC0, 0x4C, 0x8B, 0x9C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE3, 0x49, 0x01, 0xFC,
    0x4D, 0x11, 0xCE, 0x4C, 0x01, 0xE0] ++ bytes_l110d64_39

theorem code_l110d64_38 : ∀ x ∈ codeRange 0x111a71 bytes_l110d64_38, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11a71 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_39

def b_l110d64_37 : Block Op Label signature Reg.count 1606 :=
  .letOp (n := 1606) (.out 0x111a11 (addR64R64Effect 0x111a11 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1601, 1536]
    (.letOp (n := 1607) (.out 0x111a11 (addR64R64Effect 0x111a11 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[1601, 1536]
    (.letOp (n := 1608) (.exec 0x111a11 (fun s => s.RIP = 0x111a11) (addR64R64Effect 0x111a11 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1601, 1536]
    (.letOp (n := 1609) (.out 0x111a14 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111a14 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1604, 1607]
    (.letOp (n := 1610) (.exec 0x111a14 (fun s => s.RIP = 0x111a14) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111a14 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1604, 1607]
    (.letOp (n := 1611) (.out 0x111a18 (shldR64R64Effect 0x111a18 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1609, 1606]
    (.letOp (n := 1612) (.exec 0x111a18 (fun s => s.RIP = 0x111a18) (shldR64R64Effect 0x111a18 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1609, 1606]
    (.letOp (n := 1613) (.out 0x111a1d (shlR64Effect 0x111a1d 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1606]
    (.letOp (n := 1614) (.exec 0x111a1d (fun s => s.RIP = 0x111a1d) (shlR64Effect 0x111a1d 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1606]
    (.letOp (n := 1615) (.out 0x111a21 (movR64Imm64Effect 0x111a21 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1616) (.exec 0x111a21 (fun s => s.RIP = 0x111a21) (movR64Imm64Effect 0x111a21 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 1617) (.out 0x111a2b (andR64R64Effect 0x111a2b 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1613, 1615]
    (.letOp (n := 1618) (.exec 0x111a2b (fun s => s.RIP = 0x111a2b) (andR64R64Effect 0x111a2b 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1613, 1615]
    (.letOp (n := 1619) (.out 0x111a2e (orR64R64Effect 0x111a2e 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[1617, 1560]
    (.letOp (n := 1620) (.exec 0x111a2e (fun s => s.RIP = 0x111a2e) (orR64R64Effect 0x111a2e 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[1617, 1560]
    (.letOp (n := 1621) (.out 0x111a31 (movR64Imm64Effect 0x111a31 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1622) (.exec 0x111a31 (fun s => s.RIP = 0x111a31) (movR64Imm64Effect 0x111a31 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 1623) (.out 0x111a3b (mulR64Effect 0x111a3b 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1621, 1619]
    (.letOp (n := 1624) (.out 0x111a3b (mulR64Effect 0x111a3b 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1621, 1619]
    (.letOp (n := 1625) (.exec 0x111a3b (fun s => s.RIP = 0x111a3b) (mulR64Effect 0x111a3b 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1621, 1619]
    (.letOp (n := 1626) (.out 0x111a3e (movR64R64Effect 0x111a3e 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[1624]
    (.letOp (n := 1627) (.exec 0x111a3e (fun s => s.RIP = 0x111a3e) (movR64R64Effect 0x111a3e 10 2) (Reg.operands [.gpr 2] [])) #v[1624]
    (.letOp (n := 1628) (.out 0x111a41 (addR64M64Effect 0x111a41 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1623, 4]
    (.letOp (n := 1629) (.out 0x111a41 (addR64M64Effect 0x111a41 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[1623, 4]
    (.letOp (n := 1630) (.exec 0x111a41 (LoadPre 0x111a41 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x111a41 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x111a41 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1623, 4]
    (.letOp (n := 1631) (.out 0x111a49 (atFlags StatusFlags.CF (adcR64M64Effect 0x111a49 10 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 10))) #v[1626, 4, 1629]
    (.letOp (n := 1632) (.exec 0x111a49 (LoadPre 0x111a49 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111a49 + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111a49 10 (.sib 4 none 0 .none))) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1626, 4, 1629]
    (.letOp (n := 1633) (.out 0x111a4d (shldR64R64Effect 0x111a4d 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[1631, 1628]
    (.letOp (n := 1634) (.exec 0x111a4d (fun s => s.RIP = 0x111a4d) (shldR64R64Effect 0x111a4d 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1631, 1628]
    (.letOp (n := 1635) (.out 0x111a52 (movR64R64Effect 0x111a52 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[1628]
    (.letOp (n := 1636) (.exec 0x111a52 (fun s => s.RIP = 0x111a52) (movR64R64Effect 0x111a52 11 0) (Reg.operands [.gpr 0] [])) #v[1628]
    (.letOp (n := 1637) (.out 0x111a55 (movR64M64Effect 0x111a55 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1638) (.exec 0x111a55 (LoadPre 0x111a55 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111a55 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111a55 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1639) (.out 0x111a5a (mulR64Effect 0x111a5a 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[1586, 1637]
    (.letOp (n := 1640) (.out 0x111a5a (mulR64Effect 0x111a5a 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[1586, 1637]
    (.letOp (n := 1641) (.exec 0x111a5a (fun s => s.RIP = 0x111a5a) (mulR64Effect 0x111a5a 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1586, 1637]
    (.letOp (n := 1642) (.exec 0x111a5d (StorePre 0x111a5d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111a5d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111a5d 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1640, 4]
    (.letOp (n := 1643) (.exec 0x111a61 (StorePre 0x111a61 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x111a61 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111a61 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1639, 4]
    (.letOp (n := 1644) (.out 0x111a69 (movR64R64Effect 0x111a69 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[1549]
    (.letOp (n := 1645) (.exec 0x111a69 (fun s => s.RIP = 0x111a69) (movR64R64Effect 0x111a69 0 6) (Reg.operands [.gpr 6] [])) #v[1549]
    (.letOp (n := 1646) (.out 0x111a6c (mulM64Effect 0x111a6c 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1644, 4]
    (.letOp (n := 1647) (.out 0x111a6c (mulM64Effect 0x111a6c 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1644, 4]
    (.letOp (n := 1648) (.exec 0x111a6c (LoadPre 0x111a6c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x111a6c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x111a6c 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1644, 4]
    (b_l110d64_38)))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_37 : List UInt8 :=
  [0x48, 0x01, 0xC8, 0x48, 0x83, 0xD3, 0x00, 0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xC1, 0xE0, 0x04,
    0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C, 0x09, 0xE0,
    0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD2,
    0x48, 0x03, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x14, 0x24, 0x49, 0x0F, 0xA4, 0xC2,
    0x0C, 0x49, 0x89, 0xC3, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0x14, 0x24,
    0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0x64, 0x24, 0x68] ++ bytes_l110d64_38

theorem code_l110d64_37 : ∀ x ∈ codeRange 0x111a11 bytes_l110d64_37, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11a11 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_38

def b_l110d64_36 : Block Op Label signature Reg.count 1560 :=
  .letOp (n := 1560) (.out 0x1119c6 (andR32Imm8Effect 0x1119c6 4 12 0xf) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1540]
    (.letOp (n := 1561) (.exec 0x1119c6 (fun s => s.RIP = 0x1119c6) (andR32Imm8Effect 0x1119c6 4 12 0xf) (Reg.operands [.gpr 12] [])) #v[1540]
    (.letOp (n := 1562) (.out 0x1119ca (movR64R64Effect 0x1119ca 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[1462]
    (.letOp (n := 1563) (.exec 0x1119ca (fun s => s.RIP = 0x1119ca) (movR64R64Effect 0x1119ca 0 10) (Reg.operands [.gpr 10] [])) #v[1462]
    (.letOp (n := 1564) (.out 0x1119cd (mulM64Effect 0x1119cd 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1562, 4]
    (.letOp (n := 1565) (.out 0x1119cd (mulM64Effect 0x1119cd 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1562, 4]
    (.letOp (n := 1566) (.exec 0x1119cd (LoadPre 0x1119cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1119cd + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1119cd 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1562, 4]
    (.letOp (n := 1567) (.out 0x1119d2 (movR64R64Effect 0x1119d2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[1565]
    (.letOp (n := 1568) (.exec 0x1119d2 (fun s => s.RIP = 0x1119d2) (movR64R64Effect 0x1119d2 3 2) (Reg.operands [.gpr 2] [])) #v[1565]
    (.letOp (n := 1569) (.out 0x1119d5 (movR64R64Effect 0x1119d5 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[1564]
    (.letOp (n := 1570) (.exec 0x1119d5 (fun s => s.RIP = 0x1119d5) (movR64R64Effect 0x1119d5 10 0) (Reg.operands [.gpr 0] [])) #v[1564]
    (.letOp (n := 1571) (.out 0x1119d8 (movR64M64Effect 0x1119d8 5 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 1572) (.exec 0x1119d8 (LoadPre 0x1119d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1119d8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1119d8 5 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1573) (.out 0x1119e0 (movR64R64Effect 0x1119e0 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1571]
    (.letOp (n := 1574) (.exec 0x1119e0 (fun s => s.RIP = 0x1119e0) (movR64R64Effect 0x1119e0 0 5) (Reg.operands [.gpr 5] [])) #v[1571]
    (.letOp (n := 1575) (.out 0x1119e3 (mulR64Effect 0x1119e3 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[1464, 1573]
    (.letOp (n := 1576) (.out 0x1119e3 (mulR64Effect 0x1119e3 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[1464, 1573]
    (.letOp (n := 1577) (.exec 0x1119e3 (fun s => s.RIP = 0x1119e3) (mulR64Effect 0x1119e3 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[1464, 1573]
    (.letOp (n := 1578) (.out 0x1119e6 (movR64R64Effect 0x1119e6 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[1576]
    (.letOp (n := 1579) (.exec 0x1119e6 (fun s => s.RIP = 0x1119e6) (movR64R64Effect 0x1119e6 14 2) (Reg.operands [.gpr 2] [])) #v[1576]
    (.letOp (n := 1580) (.out 0x1119e9 (movR64R64Effect 0x1119e9 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1575]
    (.letOp (n := 1581) (.exec 0x1119e9 (fun s => s.RIP = 0x1119e9) (movR64R64Effect 0x1119e9 15 0) (Reg.operands [.gpr 0] [])) #v[1575]
    (.letOp (n := 1582) (.out 0x1119ec (movR64M64Effect 0x1119ec 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 1583) (.exec 0x1119ec (LoadPre 0x1119ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1119ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1119ec 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1584) (.out 0x1119f1 (movR64R64Effect 0x1119f1 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[1582]
    (.letOp (n := 1585) (.exec 0x1119f1 (fun s => s.RIP = 0x1119f1) (movR64R64Effect 0x1119f1 0 8) (Reg.operands [.gpr 8] [])) #v[1582]
    (.letOp (n := 1586) (.out 0x1119f4 (movR64M64Effect 0x1119f4 13 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 1587) (.exec 0x1119f4 (LoadPre 0x1119f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1119f4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1119f4 13 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1588) (.out 0x1119fc (mulR64Effect 0x1119fc 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[1586, 1584]
    (.letOp (n := 1589) (.out 0x1119fc (mulR64Effect 0x1119fc 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[1586, 1584]
    (.letOp (n := 1590) (.exec 0x1119fc (fun s => s.RIP = 0x1119fc) (mulR64Effect 0x1119fc 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1586, 1584]
    (.letOp (n := 1591) (.out 0x1119ff (addR64R64Effect 0x1119ff 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[1569, 1556]
    (.letOp (n := 1592) (.out 0x1119ff (addR64R64Effect 0x1119ff 10 7) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 7] []) (.flag .CF)) #v[1569, 1556]
    (.letOp (n := 1593) (.exec 0x1119ff (fun s => s.RIP = 0x1119ff) (addR64R64Effect 0x1119ff 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[1569, 1556]
    (.letOp (n := 1594) (.out 0x111a02 (atFlags StatusFlags.CF (adcR64R64Effect 0x111a02 3 9)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1567, 1558, 1592]
    (.letOp (n := 1595) (.exec 0x111a02 (fun s => s.RIP = 0x111a02) (atFlags StatusFlags.CF (adcR64R64Effect 0x111a02 3 9)) (Reg.operands [.gpr 3, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1567, 1558, 1592]
    (.letOp (n := 1596) (.out 0x111a05 (addR64R64Effect 0x111a05 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15] []) (.reg (.gpr 10))) #v[1591, 1580]
    (.letOp (n := 1597) (.out 0x111a05 (addR64R64Effect 0x111a05 10 15) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 15] []) (.flag .CF)) #v[1591, 1580]
    (.letOp (n := 1598) (.exec 0x111a05 (fun s => s.RIP = 0x111a05) (addR64R64Effect 0x111a05 10 15) (Reg.operands [.gpr 10, .gpr 15] [])) #v[1591, 1580]
    (.letOp (n := 1599) (.out 0x111a08 (atFlags StatusFlags.CF (adcR64R64Effect 0x111a08 3 14)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1594, 1578, 1597]
    (.letOp (n := 1600) (.exec 0x111a08 (fun s => s.RIP = 0x111a08) (atFlags StatusFlags.CF (adcR64R64Effect 0x111a08 3 14)) (Reg.operands [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1594, 1578, 1597]
    (.letOp (n := 1601) (.out 0x111a0b (addR64R64Effect 0x111a0b 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[1588, 1596]
    (.letOp (n := 1602) (.out 0x111a0b (addR64R64Effect 0x111a0b 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[1588, 1596]
    (.letOp (n := 1603) (.exec 0x111a0b (fun s => s.RIP = 0x111a0b) (addR64R64Effect 0x111a0b 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[1588, 1596]
    (.letOp (n := 1604) (.out 0x111a0e (atFlags StatusFlags.CF (adcR64R64Effect 0x111a0e 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1599, 1589, 1602]
    (.letOp (n := 1605) (.exec 0x111a0e (fun s => s.RIP = 0x111a0e) (atFlags StatusFlags.CF (adcR64R64Effect 0x111a0e 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1599, 1589, 1602]
    (b_l110d64_37))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_36 : List UInt8 :=
  [0x41, 0x83, 0xE4, 0x0F, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0x64, 0x24, 0x38, 0x48, 0x89, 0xD3, 0x49,
    0x89, 0xC2, 0x48, 0x8B, 0xAC, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE3,
    0x49, 0x89, 0xD6, 0x49, 0x89, 0xC7, 0x4C, 0x8B, 0x44, 0x24, 0x18, 0x4C, 0x89, 0xC0, 0x4C, 0x8B,
    0xAC, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x49, 0x01, 0xFA, 0x4C, 0x11, 0xCB, 0x4D,
    0x01, 0xFA, 0x4C, 0x11, 0xF3, 0x4C, 0x01, 0xD0, 0x48, 0x11, 0xD3] ++ bytes_l110d64_37

theorem code_l110d64_36 : ∀ x ∈ codeRange 0x1119c6 bytes_l110d64_36, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x119c6 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_37

def b_l110d64_35 : Block Op Label signature Reg.count 1518 :=
  .letOp (n := 1518) (.out 0x111972 (atFlags StatusFlags.CF (adcR64R64Effect 0x111972 1 14)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1513, 1477, 1516]
    (.letOp (n := 1519) (.exec 0x111972 (fun s => s.RIP = 0x111972) (atFlags StatusFlags.CF (adcR64R64Effect 0x111972 1 14)) (Reg.operands [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1513, 1477, 1516]
    (.letOp (n := 1520) (.out 0x111975 (addR64R64Effect 0x111975 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[1515, 1488]
    (.letOp (n := 1521) (.out 0x111975 (addR64R64Effect 0x111975 7 5) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 5] []) (.flag .CF)) #v[1515, 1488]
    (.letOp (n := 1522) (.exec 0x111975 (fun s => s.RIP = 0x111975) (addR64R64Effect 0x111975 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[1515, 1488]
    (.letOp (n := 1523) (.out 0x111978 (atFlags StatusFlags.CF (adcR64R64Effect 0x111978 1 13)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1518, 1490, 1521]
    (.letOp (n := 1524) (.exec 0x111978 (fun s => s.RIP = 0x111978) (atFlags StatusFlags.CF (adcR64R64Effect 0x111978 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1518, 1490, 1521]
    (.letOp (n := 1525) (.out 0x11197b (addR64R64Effect 0x11197b 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[1520, 1500]
    (.letOp (n := 1526) (.out 0x11197b (addR64R64Effect 0x11197b 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[1520, 1500]
    (.letOp (n := 1527) (.exec 0x11197b (fun s => s.RIP = 0x11197b) (addR64R64Effect 0x11197b 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1520, 1500]
    (.letOp (n := 1528) (.out 0x11197e (atFlags StatusFlags.CF (adcR64R64Effect 0x11197e 1 9)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1523, 1503, 1526]
    (.letOp (n := 1529) (.exec 0x11197e (fun s => s.RIP = 0x11197e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11197e 1 9)) (Reg.operands [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1523, 1503, 1526]
    (.letOp (n := 1530) (.out 0x111981 (addR64R64Effect 0x111981 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[1525, 1442]
    (.letOp (n := 1531) (.out 0x111981 (addR64R64Effect 0x111981 7 6) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 6] []) (.flag .CF)) #v[1525, 1442]
    (.letOp (n := 1532) (.exec 0x111981 (fun s => s.RIP = 0x111981) (addR64R64Effect 0x111981 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[1525, 1442]
    (.letOp (n := 1533) (.exec 0x111984 (StorePre 0x111984 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x111984 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111984 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1530, 4]
    (.letOp (n := 1534) (.out 0x11198c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11198c 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1528, 1531]
    (.letOp (n := 1535) (.exec 0x11198c (fun s => s.RIP = 0x11198c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11198c 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1528, 1531]
    (.letOp (n := 1536) (.out 0x111990 (shldR64R64Effect 0x111990 5 1 7 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1534, 1530]
    (.letOp (n := 1537) (.exec 0x111990 (fun s => s.RIP = 0x111990) (shldR64R64Effect 0x111990 5 1 7 12) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1534, 1530]
    (.letOp (n := 1538) (.out 0x111995 (movR64R64Effect 0x111995 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[1530]
    (.letOp (n := 1539) (.exec 0x111995 (fun s => s.RIP = 0x111995) (movR64R64Effect 0x111995 12 7) (Reg.operands [.gpr 7] [])) #v[1530]
    (.letOp (n := 1540) (.out 0x111998 (shrR64Effect 0x111998 4 12 48) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1538]
    (.letOp (n := 1541) (.exec 0x111998 (fun s => s.RIP = 0x111998) (shrR64Effect 0x111998 4 12 48) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1538]
    (.letOp (n := 1542) (.out 0x11199c (movR64M64Effect 0x11199c 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1543) (.exec 0x11199c (LoadPre 0x11199c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11199c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11199c 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1544) (.out 0x1119a1 (mulR64Effect 0x1119a1 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[1486, 1542]
    (.letOp (n := 1545) (.out 0x1119a1 (mulR64Effect 0x1119a1 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[1486, 1542]
    (.letOp (n := 1546) (.exec 0x1119a1 (fun s => s.RIP = 0x1119a1) (mulR64Effect 0x1119a1 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1486, 1542]
    (.letOp (n := 1547) (.exec 0x1119a4 (StorePre 0x1119a4 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1119a4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1119a4 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1545, 4]
    (.letOp (n := 1548) (.exec 0x1119a8 (StorePre 0x1119a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1119a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1119a8 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1544, 4]
    (.letOp (n := 1549) (.out 0x1119b0 (movR64M64Effect 0x1119b0 6 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 1550) (.exec 0x1119b0 (LoadPre 0x1119b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x1119b0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1119b0 6 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1551) (.out 0x1119b8 (movR64R64Effect 0x1119b8 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[1549]
    (.letOp (n := 1552) (.exec 0x1119b8 (fun s => s.RIP = 0x1119b8) (movR64R64Effect 0x1119b8 0 6) (Reg.operands [.gpr 6] [])) #v[1549]
    (.letOp (n := 1553) (.out 0x1119bb (mulM64Effect 0x1119bb 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1551, 4]
    (.letOp (n := 1554) (.out 0x1119bb (mulM64Effect 0x1119bb 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1551, 4]
    (.letOp (n := 1555) (.exec 0x1119bb (LoadPre 0x1119bb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1119bb + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1119bb 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1551, 4]
    (.letOp (n := 1556) (.out 0x1119c0 (movR64R64Effect 0x1119c0 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[1553]
    (.letOp (n := 1557) (.exec 0x1119c0 (fun s => s.RIP = 0x1119c0) (movR64R64Effect 0x1119c0 7 0) (Reg.operands [.gpr 0] [])) #v[1553]
    (.letOp (n := 1558) (.out 0x1119c3 (movR64R64Effect 0x1119c3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[1554]
    (.letOp (n := 1559) (.exec 0x1119c3 (fun s => s.RIP = 0x1119c3) (movR64R64Effect 0x1119c3 9 2) (Reg.operands [.gpr 2] [])) #v[1554]
    (b_l110d64_36))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_35 : List UInt8 :=
  [0x4C, 0x11, 0xF1, 0x48, 0x01, 0xEF, 0x4C, 0x11, 0xE9, 0x48, 0x01, 0xC7, 0x4C, 0x11, 0xC9, 0x48,
    0x01, 0xF7, 0x48, 0x89, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x83, 0xD1, 0x00, 0x48, 0x0F,
    0xA4, 0xF9, 0x0C, 0x49, 0x89, 0xFC, 0x49, 0xC1, 0xEC, 0x30, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x48,
    0xF7, 0xE3, 0x48, 0x89, 0x14, 0x24, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0xB4, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0x64, 0x24, 0x10, 0x48, 0x89,
    0xC7, 0x49, 0x89, 0xD1] ++ bytes_l110d64_36

theorem code_l110d64_35 : ∀ x ∈ codeRange 0x111972 bytes_l110d64_35, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11972 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_36

def b_l110d64_34 : Block Op Label signature Reg.count 1472 :=
  .letOp (n := 1472) (.out 0x111922 (movR64R64Effect 0x111922 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[1392]
    (.letOp (n := 1473) (.exec 0x111922 (fun s => s.RIP = 0x111922) (movR64R64Effect 0x111922 0 14) (Reg.operands [.gpr 14] [])) #v[1392]
    (.letOp (n := 1474) (.out 0x111925 (mulR64Effect 0x111925 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[1378, 1472]
    (.letOp (n := 1475) (.out 0x111925 (mulR64Effect 0x111925 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[1378, 1472]
    (.letOp (n := 1476) (.exec 0x111925 (fun s => s.RIP = 0x111925) (mulR64Effect 0x111925 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1378, 1472]
    (.letOp (n := 1477) (.out 0x111928 (movR64R64Effect 0x111928 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[1475]
    (.letOp (n := 1478) (.exec 0x111928 (fun s => s.RIP = 0x111928) (movR64R64Effect 0x111928 14 2) (Reg.operands [.gpr 2] [])) #v[1475]
    (.letOp (n := 1479) (.out 0x11192b (movR64R64Effect 0x11192b 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[1474]
    (.letOp (n := 1480) (.exec 0x11192b (fun s => s.RIP = 0x11192b) (movR64R64Effect 0x11192b 12 0) (Reg.operands [.gpr 0] [])) #v[1474]
    (.letOp (n := 1481) (.out 0x11192e (movR64R64Effect 0x11192e 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1410]
    (.letOp (n := 1482) (.exec 0x11192e (fun s => s.RIP = 0x11192e) (movR64R64Effect 0x11192e 0 5) (Reg.operands [.gpr 5] [])) #v[1410]
    (.letOp (n := 1483) (.out 0x111931 (mulR64Effect 0x111931 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[1396, 1481]
    (.letOp (n := 1484) (.out 0x111931 (mulR64Effect 0x111931 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[1396, 1481]
    (.letOp (n := 1485) (.exec 0x111931 (fun s => s.RIP = 0x111931) (mulR64Effect 0x111931 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1396, 1481]
    (.letOp (n := 1486) (.out 0x111934 (movR64R64Effect 0x111934 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 13] []) (.reg (.gpr 3))) #v[1396]
    (.letOp (n := 1487) (.exec 0x111934 (fun s => s.RIP = 0x111934) (movR64R64Effect 0x111934 3 13) (Reg.operands [.gpr 13] [])) #v[1396]
    (.letOp (n := 1488) (.out 0x111937 (movR64R64Effect 0x111937 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[1483]
    (.letOp (n := 1489) (.exec 0x111937 (fun s => s.RIP = 0x111937) (movR64R64Effect 0x111937 5 0) (Reg.operands [.gpr 0] [])) #v[1483]
    (.letOp (n := 1490) (.out 0x11193a (movR64R64Effect 0x11193a 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[1484]
    (.letOp (n := 1491) (.exec 0x11193a (fun s => s.RIP = 0x11193a) (movR64R64Effect 0x11193a 13 2) (Reg.operands [.gpr 2] [])) #v[1484]
    (.letOp (n := 1492) (.out 0x11193d (shrR64Effect 0x11193d 4 9 52) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[1419]
    (.letOp (n := 1493) (.exec 0x11193d (fun s => s.RIP = 0x11193d) (shrR64Effect 0x11193d 4 9 52) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1419]
    (.letOp (n := 1494) (.out 0x111941 (movR64Imm64Effect 0x111941 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1495) (.exec 0x111941 (fun s => s.RIP = 0x111941) (movR64Imm64Effect 0x111941 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1496) (.out 0x11194b (imulR64R64Effect 0x11194b 4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[1492, 1494]
    (.letOp (n := 1497) (.exec 0x11194b (fun s => s.RIP = 0x11194b) (imulR64R64Effect 0x11194b 4 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[1492, 1494]
    (.letOp (n := 1498) (.out 0x11194f (movR64R64Effect 0x11194f 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[1423]
    (.letOp (n := 1499) (.exec 0x11194f (fun s => s.RIP = 0x11194f) (movR64R64Effect 0x11194f 0 8) (Reg.operands [.gpr 8] [])) #v[1423]
    (.letOp (n := 1500) (.out 0x111952 (mulR64Effect 0x111952 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1494, 1498]
    (.letOp (n := 1501) (.out 0x111952 (mulR64Effect 0x111952 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1494, 1498]
    (.letOp (n := 1502) (.exec 0x111952 (fun s => s.RIP = 0x111952) (mulR64Effect 0x111952 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1494, 1498]
    (.letOp (n := 1503) (.out 0x111955 (addR64R64Effect 0x111955 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[1496, 1501]
    (.letOp (n := 1504) (.exec 0x111955 (fun s => s.RIP = 0x111955) (addR64R64Effect 0x111955 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[1496, 1501]
    (.letOp (n := 1505) (.out 0x111958 (addR64M64Effect 0x111958 7 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[1458, 4]
    (.letOp (n := 1506) (.out 0x111958 (addR64M64Effect 0x111958 7 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[1458, 4]
    (.letOp (n := 1507) (.exec 0x111958 (LoadPre 0x111958 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x111958 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x111958 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1458, 4]
    (.letOp (n := 1508) (.out 0x111960 (atFlags StatusFlags.CF (adcR64M64Effect 0x111960 1 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[1456, 4, 1506]
    (.letOp (n := 1509) (.exec 0x111960 (LoadPre 0x111960 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111960 + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111960 1 (.sib 4 none 0 .none))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1456, 4, 1506]
    (.letOp (n := 1510) (.out 0x111964 (addR64R64Effect 0x111964 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[1505, 1470]
    (.letOp (n := 1511) (.out 0x111964 (addR64R64Effect 0x111964 7 15) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 15] []) (.flag .CF)) #v[1505, 1470]
    (.letOp (n := 1512) (.exec 0x111964 (fun s => s.RIP = 0x111964) (addR64R64Effect 0x111964 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[1505, 1470]
    (.letOp (n := 1513) (.out 0x111967 (atFlags StatusFlags.CF (adcR64M64Effect 0x111967 1 (.sib 4 none 0 (.d32 0xc8)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[1508, 4, 1511]
    (.letOp (n := 1514) (.exec 0x111967 (LoadPre 0x111967 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x111967 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111967 1 (.sib 4 none 0 (.d32 0xc8)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1508, 4, 1511]
    (.letOp (n := 1515) (.out 0x11196f (addR64R64Effect 0x11196f 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[1510, 1479]
    (.letOp (n := 1516) (.out 0x11196f (addR64R64Effect 0x11196f 7 12) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 12] []) (.flag .CF)) #v[1510, 1479]
    (.letOp (n := 1517) (.exec 0x11196f (fun s => s.RIP = 0x11196f) (addR64R64Effect 0x11196f 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[1510, 1479]
    (b_l110d64_35))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_34 : List UInt8 :=
  [0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x48, 0x89, 0xE8, 0x49,
    0xF7, 0xE5, 0x4C, 0x89, 0xEB, 0x48, 0x89, 0xC5, 0x49, 0x89, 0xD5, 0x49, 0xC1, 0xE9, 0x34, 0x48,
    0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xCA, 0x4C, 0x89, 0xC0,
    0x48, 0xF7, 0xE2, 0x49, 0x01, 0xD1, 0x48, 0x03, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x13,
    0x0C, 0x24, 0x4C, 0x01, 0xFF, 0x48, 0x13, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xE7] ++ bytes_l110d64_35

theorem code_l110d64_34 : ∀ x ∈ codeRange 0x111922 bytes_l110d64_34, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11922 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_35

def b_l110d64_33 : Block Op Label signature Reg.count 1431 :=
  .letOp (n := 1431) (.out 0x1118d0 (mulR64Effect 0x1118d0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1429, 1427]
    (.letOp (n := 1432) (.out 0x1118d0 (mulR64Effect 0x1118d0 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1429, 1427]
    (.letOp (n := 1433) (.exec 0x1118d0 (fun s => s.RIP = 0x1118d0) (mulR64Effect 0x1118d0 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1429, 1427]
    (.letOp (n := 1434) (.out 0x1118d3 (movR64R64Effect 0x1118d3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1432]
    (.letOp (n := 1435) (.exec 0x1118d3 (fun s => s.RIP = 0x1118d3) (movR64R64Effect 0x1118d3 6 2) (Reg.operands [.gpr 2] [])) #v[1432]
    (.letOp (n := 1436) (.out 0x1118d6 (addR64R64Effect 0x1118d6 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[1431, 1405]
    (.letOp (n := 1437) (.out 0x1118d6 (addR64R64Effect 0x1118d6 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[1431, 1405]
    (.letOp (n := 1438) (.exec 0x1118d6 (fun s => s.RIP = 0x1118d6) (addR64R64Effect 0x1118d6 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[1431, 1405]
    (.letOp (n := 1439) (.exec 0x1118d9 (StorePre 0x1118d9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1118d9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1118d9 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1436, 4]
    (.letOp (n := 1440) (.out 0x1118de (atFlags StatusFlags.CF (adcR64R64Effect 0x1118de 6 1)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[1434, 1408, 1437]
    (.letOp (n := 1441) (.exec 0x1118de (fun s => s.RIP = 0x1118de) (atFlags StatusFlags.CF (adcR64R64Effect 0x1118de 6 1)) (Reg.operands [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1434, 1408, 1437]
    (.letOp (n := 1442) (.out 0x1118e1 (shldR64R64Effect 0x1118e1 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1440, 1436]
    (.letOp (n := 1443) (.exec 0x1118e1 (fun s => s.RIP = 0x1118e1) (shldR64R64Effect 0x1118e1 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1440, 1436]
    (.letOp (n := 1444) (.out 0x1118e6 (movR64R64Effect 0x1118e6 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[1344]
    (.letOp (n := 1445) (.exec 0x1118e6 (fun s => s.RIP = 0x1118e6) (movR64R64Effect 0x1118e6 0 11) (Reg.operands [.gpr 11] [])) #v[1344]
    (.letOp (n := 1446) (.out 0x1118e9 (mulR64Effect 0x1118e9 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[1414, 1444]
    (.letOp (n := 1447) (.out 0x1118e9 (mulR64Effect 0x1118e9 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[1414, 1444]
    (.letOp (n := 1448) (.exec 0x1118e9 (fun s => s.RIP = 0x1118e9) (mulR64Effect 0x1118e9 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[1414, 1444]
    (.letOp (n := 1449) (.exec 0x1118ec (StorePre 0x1118ec 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1118ec + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1118ec 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1447, 4]
    (.letOp (n := 1450) (.exec 0x1118f0 (StorePre 0x1118f0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1118f0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1118f0 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1446, 4]
    (.letOp (n := 1451) (.out 0x1118f8 (movR64R64Effect 0x1118f8 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[1358]
    (.letOp (n := 1452) (.exec 0x1118f8 (fun s => s.RIP = 0x1118f8) (movR64R64Effect 0x1118f8 0 12) (Reg.operands [.gpr 12] [])) #v[1358]
    (.letOp (n := 1453) (.out 0x1118fb (mulM64Effect 0x1118fb 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1451, 4]
    (.letOp (n := 1454) (.out 0x1118fb (mulM64Effect 0x1118fb 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1451, 4]
    (.letOp (n := 1455) (.exec 0x1118fb (LoadPre 0x1118fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1118fb + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1118fb 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1451, 4]
    (.letOp (n := 1456) (.out 0x111900 (movR64R64Effect 0x111900 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1454]
    (.letOp (n := 1457) (.exec 0x111900 (fun s => s.RIP = 0x111900) (movR64R64Effect 0x111900 1 2) (Reg.operands [.gpr 2] [])) #v[1454]
    (.letOp (n := 1458) (.out 0x111903 (movR64R64Effect 0x111903 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[1453]
    (.letOp (n := 1459) (.exec 0x111903 (fun s => s.RIP = 0x111903) (movR64R64Effect 0x111903 7 0) (Reg.operands [.gpr 0] [])) #v[1453]
    (.letOp (n := 1460) (.out 0x111906 (movR64R64Effect 0x111906 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[1374]
    (.letOp (n := 1461) (.exec 0x111906 (fun s => s.RIP = 0x111906) (movR64R64Effect 0x111906 0 15) (Reg.operands [.gpr 15] [])) #v[1374]
    (.letOp (n := 1462) (.out 0x111909 (movR64R64Effect 0x111909 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 15] []) (.reg (.gpr 10))) #v[1374]
    (.letOp (n := 1463) (.exec 0x111909 (fun s => s.RIP = 0x111909) (movR64R64Effect 0x111909 10 15) (Reg.operands [.gpr 15] [])) #v[1374]
    (.letOp (n := 1464) (.out 0x11190c (movR64M64Effect 0x11190c 11 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 1465) (.exec 0x11190c (LoadPre 0x11190c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11190c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11190c 11 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1466) (.out 0x111914 (mulR64Effect 0x111914 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[1464, 1460]
    (.letOp (n := 1467) (.out 0x111914 (mulR64Effect 0x111914 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[1464, 1460]
    (.letOp (n := 1468) (.exec 0x111914 (fun s => s.RIP = 0x111914) (mulR64Effect 0x111914 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[1464, 1460]
    (.letOp (n := 1469) (.exec 0x111917 (StorePre 0x111917 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x111917 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111917 2 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1467, 4]
    (.letOp (n := 1470) (.out 0x11191f (movR64R64Effect 0x11191f 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1466]
    (.letOp (n := 1471) (.exec 0x11191f (fun s => s.RIP = 0x11191f) (movR64R64Effect 0x11191f 15 0) (Reg.operands [.gpr 0] [])) #v[1466]
    (b_l110d64_34)))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_33 : List UInt8 :=
  [0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD6, 0x48, 0x01, 0xF8, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x11,
    0xCE, 0x48, 0x0F, 0xA4, 0xC6, 0x0C, 0x4C, 0x89, 0xD8, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0x14, 0x24,
    0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0x64, 0x24, 0x38,
    0x48, 0x89, 0xD1, 0x48, 0x89, 0xC7, 0x4C, 0x89, 0xF8, 0x4D, 0x89, 0xFA, 0x4C, 0x8B, 0x9C, 0x24,
    0xB0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE3, 0x48, 0x89, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x49,
    0x89, 0xC7] ++ bytes_l110d64_34

theorem code_l110d64_33 : ∀ x ∈ codeRange 0x1118d0 bytes_l110d64_33, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x118d0 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_34

def b_l110d64_32 : Block Op Label signature Reg.count 1387 :=
  .letOp (n := 1387) (.out 0x111879 (addR64R64Effect 0x111879 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[1385, 1369]
    (.letOp (n := 1388) (.out 0x111879 (addR64R64Effect 0x111879 9 8) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 8] []) (.flag .CF)) #v[1385, 1369]
    (.letOp (n := 1389) (.exec 0x111879 (fun s => s.RIP = 0x111879) (addR64R64Effect 0x111879 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[1385, 1369]
    (.letOp (n := 1390) (.out 0x11187c (atFlags StatusFlags.CF (adcR64R64Effect 0x11187c 6 7)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[1383, 1372, 1388]
    (.letOp (n := 1391) (.exec 0x11187c (fun s => s.RIP = 0x11187c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11187c 6 7)) (Reg.operands [.gpr 6, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1383, 1372, 1388]
    (.letOp (n := 1392) (.out 0x11187f (movR64M64Effect 0x11187f 14 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 1393) (.exec 0x11187f (LoadPre 0x11187f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11187f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11187f 14 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1394) (.out 0x111887 (movR64R64Effect 0x111887 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[1392]
    (.letOp (n := 1395) (.exec 0x111887 (fun s => s.RIP = 0x111887) (movR64R64Effect 0x111887 0 14) (Reg.operands [.gpr 14] [])) #v[1392]
    (.letOp (n := 1396) (.out 0x11188a (movR64M64Effect 0x11188a 13 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 1397) (.exec 0x11188a (LoadPre 0x11188a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11188a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11188a 13 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1398) (.out 0x11188f (mulR64Effect 0x11188f 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[1396, 1394]
    (.letOp (n := 1399) (.out 0x11188f (mulR64Effect 0x11188f 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[1396, 1394]
    (.letOp (n := 1400) (.exec 0x11188f (fun s => s.RIP = 0x11188f) (mulR64Effect 0x11188f 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1396, 1394]
    (.letOp (n := 1401) (.out 0x111892 (movR64R64Effect 0x111892 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1399]
    (.letOp (n := 1402) (.exec 0x111892 (fun s => s.RIP = 0x111892) (movR64R64Effect 0x111892 1 2) (Reg.operands [.gpr 2] [])) #v[1399]
    (.letOp (n := 1403) (.out 0x111895 (movR64R64Effect 0x111895 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[1398]
    (.letOp (n := 1404) (.exec 0x111895 (fun s => s.RIP = 0x111895) (movR64R64Effect 0x111895 7 0) (Reg.operands [.gpr 0] [])) #v[1398]
    (.letOp (n := 1405) (.out 0x111898 (addR64R64Effect 0x111898 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[1403, 1387]
    (.letOp (n := 1406) (.out 0x111898 (addR64R64Effect 0x111898 7 9) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 9] []) (.flag .CF)) #v[1403, 1387]
    (.letOp (n := 1407) (.exec 0x111898 (fun s => s.RIP = 0x111898) (addR64R64Effect 0x111898 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[1403, 1387]
    (.letOp (n := 1408) (.out 0x11189b (atFlags StatusFlags.CF (adcR64R64Effect 0x11189b 1 6)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1401, 1390, 1406]
    (.letOp (n := 1409) (.exec 0x11189b (fun s => s.RIP = 0x11189b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11189b 1 6)) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1401, 1390, 1406]
    (.letOp (n := 1410) (.out 0x11189e (movR64M64Effect 0x11189e 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 1411) (.exec 0x11189e (LoadPre 0x11189e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11189e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11189e 5 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1412) (.out 0x1118a3 (movR64R64Effect 0x1118a3 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1410]
    (.letOp (n := 1413) (.exec 0x1118a3 (fun s => s.RIP = 0x1118a3) (movR64R64Effect 0x1118a3 0 5) (Reg.operands [.gpr 5] [])) #v[1410]
    (.letOp (n := 1414) (.out 0x1118a6 (movR64M64Effect 0x1118a6 10 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 1415) (.exec 0x1118a6 (LoadPre 0x1118a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1118a6 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1416) (.out 0x1118ab (mulR64Effect 0x1118ab 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[1414, 1412]
    (.letOp (n := 1417) (.out 0x1118ab (mulR64Effect 0x1118ab 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[1414, 1412]
    (.letOp (n := 1418) (.exec 0x1118ab (fun s => s.RIP = 0x1118ab) (mulR64Effect 0x1118ab 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[1414, 1412]
    (.letOp (n := 1419) (.out 0x1118ae (movR64R64Effect 0x1118ae 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[1417]
    (.letOp (n := 1420) (.exec 0x1118ae (fun s => s.RIP = 0x1118ae) (movR64R64Effect 0x1118ae 9 2) (Reg.operands [.gpr 2] [])) #v[1417]
    (.letOp (n := 1421) (.out 0x1118b1 (movR64R64Effect 0x1118b1 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[1417]
    (.letOp (n := 1422) (.exec 0x1118b1 (fun s => s.RIP = 0x1118b1) (movR64R64Effect 0x1118b1 8 2) (Reg.operands [.gpr 2] [])) #v[1417]
    (.letOp (n := 1423) (.out 0x1118b4 (shldR64R64Effect 0x1118b4 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[1421, 1416]
    (.letOp (n := 1424) (.exec 0x1118b4 (fun s => s.RIP = 0x1118b4) (shldR64R64Effect 0x1118b4 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1421, 1416]
    (.letOp (n := 1425) (.out 0x1118b9 (movR64Imm64Effect 0x1118b9 2 0xffffffffffffe) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1426) (.exec 0x1118b9 (fun s => s.RIP = 0x1118b9) (movR64Imm64Effect 0x1118b9 2 0xffffffffffffe) (Reg.operands [] [])) #v[]
    (.letOp (n := 1427) (.out 0x1118c3 (andR64R64Effect 0x1118c3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1416, 1425]
    (.letOp (n := 1428) (.exec 0x1118c3 (fun s => s.RIP = 0x1118c3) (andR64R64Effect 0x1118c3 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1416, 1425]
    (.letOp (n := 1429) (.out 0x1118c6 (movR64Imm64Effect 0x1118c6 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1430) (.exec 0x1118c6 (fun s => s.RIP = 0x1118c6) (movR64Imm64Effect 0x1118c6 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (b_l110d64_33))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_32 : List UInt8 :=
  [0x4D, 0x01, 0xC1, 0x48, 0x11, 0xFE, 0x4C, 0x8B, 0xB4, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xF0, 0x4C, 0x8B, 0x6C, 0x24, 0x68, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC7, 0x4C,
    0x01, 0xCF, 0x48, 0x11, 0xF1, 0x48, 0x8B, 0x6C, 0x24, 0x18, 0x48, 0x89, 0xE8, 0x4C, 0x8B, 0x54,
    0x24, 0x10, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xD0, 0x49, 0x0F, 0xA4, 0xC0, 0x0C,
    0x48, 0xBA, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10,
    0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] ++ bytes_l110d64_33

theorem code_l110d64_32 : ∀ x ∈ codeRange 0x111879 bytes_l110d64_32, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11879 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_33

def b_l110d64_31 : Block Op Label signature Reg.count 1344 :=
  .letOp (n := 1344) (.out 0x111823 (movR64M64Effect 0x111823 11 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 1345) (.exec 0x111823 (LoadPre 0x111823 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111823 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111823 11 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1346) (.out 0x111828 (movR64R64Effect 0x111828 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[1344]
    (.letOp (n := 1347) (.exec 0x111828 (fun s => s.RIP = 0x111828) (movR64R64Effect 0x111828 0 11) (Reg.operands [.gpr 11] [])) #v[1344]
    (.letOp (n := 1348) (.out 0x11182b (mulM64Effect 0x11182b 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1346, 4]
    (.letOp (n := 1349) (.out 0x11182b (mulM64Effect 0x11182b 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1346, 4]
    (.letOp (n := 1350) (.exec 0x11182b (LoadPre 0x11182b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11182b + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11182b 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1346, 4]
    (.letOp (n := 1351) (.out 0x111830 (movR64R64Effect 0x111830 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1348]
    (.letOp (n := 1352) (.exec 0x111830 (fun s => s.RIP = 0x111830) (movR64R64Effect 0x111830 1 0) (Reg.operands [.gpr 0] [])) #v[1348]
    (.letOp (n := 1353) (.out 0x111833 (movR64R64Effect 0x111833 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1349]
    (.letOp (n := 1354) (.exec 0x111833 (fun s => s.RIP = 0x111833) (movR64R64Effect 0x111833 6 2) (Reg.operands [.gpr 2] [])) #v[1349]
    (.letOp (n := 1355) (.out 0x111836 (andR64R64Effect 0x111836 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[1326, 1342]
    (.letOp (n := 1356) (.exec 0x111836 (fun s => s.RIP = 0x111836) (andR64R64Effect 0x111836 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[1326, 1342]
    (.letOp (n := 1357) (.exec 0x111839 (StorePre 0x111839 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x111839 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111839 10 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[1355, 4]
    (.letOp (n := 1358) (.out 0x11183e (movR64M64Effect 0x11183e 12 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 1359) (.exec 0x11183e (LoadPre 0x11183e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11183e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11183e 12 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1360) (.out 0x111846 (movR64R64Effect 0x111846 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[1358]
    (.letOp (n := 1361) (.exec 0x111846 (fun s => s.RIP = 0x111846) (movR64R64Effect 0x111846 0 12) (Reg.operands [.gpr 12] [])) #v[1358]
    (.letOp (n := 1362) (.out 0x111849 (mulM64Effect 0x111849 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1360, 4]
    (.letOp (n := 1363) (.out 0x111849 (mulM64Effect 0x111849 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1360, 4]
    (.letOp (n := 1364) (.exec 0x111849 (LoadPre 0x111849 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x111849 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x111849 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1360, 4]
    (.letOp (n := 1365) (.out 0x111851 (movR64R64Effect 0x111851 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[1363]
    (.letOp (n := 1366) (.exec 0x111851 (fun s => s.RIP = 0x111851) (movR64R64Effect 0x111851 7 2) (Reg.operands [.gpr 2] [])) #v[1363]
    (.letOp (n := 1367) (.out 0x111854 (movR64R64Effect 0x111854 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[1362]
    (.letOp (n := 1368) (.exec 0x111854 (fun s => s.RIP = 0x111854) (movR64R64Effect 0x111854 8 0) (Reg.operands [.gpr 0] [])) #v[1362]
    (.letOp (n := 1369) (.out 0x111857 (addR64R64Effect 0x111857 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[1367, 1351]
    (.letOp (n := 1370) (.out 0x111857 (addR64R64Effect 0x111857 8 1) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 1] []) (.flag .CF)) #v[1367, 1351]
    (.letOp (n := 1371) (.exec 0x111857 (fun s => s.RIP = 0x111857) (addR64R64Effect 0x111857 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[1367, 1351]
    (.letOp (n := 1372) (.out 0x11185a (atFlags StatusFlags.CF (adcR64R64Effect 0x11185a 7 6)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[1365, 1353, 1370]
    (.letOp (n := 1373) (.exec 0x11185a (fun s => s.RIP = 0x11185a) (atFlags StatusFlags.CF (adcR64R64Effect 0x11185a 7 6)) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1365, 1353, 1370]
    (.letOp (n := 1374) (.out 0x11185d (movR64M64Effect 0x11185d 15 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 1375) (.exec 0x11185d (LoadPre 0x11185d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x11185d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11185d 15 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1376) (.out 0x111865 (movR64R64Effect 0x111865 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[1374]
    (.letOp (n := 1377) (.exec 0x111865 (fun s => s.RIP = 0x111865) (movR64R64Effect 0x111865 0 15) (Reg.operands [.gpr 15] [])) #v[1374]
    (.letOp (n := 1378) (.out 0x111868 (movR64M64Effect 0x111868 3 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1379) (.exec 0x111868 (LoadPre 0x111868 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x111868 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111868 3 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1380) (.out 0x111870 (mulR64Effect 0x111870 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[1378, 1376]
    (.letOp (n := 1381) (.out 0x111870 (mulR64Effect 0x111870 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[1378, 1376]
    (.letOp (n := 1382) (.exec 0x111870 (fun s => s.RIP = 0x111870) (mulR64Effect 0x111870 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1378, 1376]
    (.letOp (n := 1383) (.out 0x111873 (movR64R64Effect 0x111873 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1381]
    (.letOp (n := 1384) (.exec 0x111873 (fun s => s.RIP = 0x111873) (movR64R64Effect 0x111873 6 2) (Reg.operands [.gpr 2] [])) #v[1381]
    (.letOp (n := 1385) (.out 0x111876 (movR64R64Effect 0x111876 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[1380]
    (.letOp (n := 1386) (.exec 0x111876 (fun s => s.RIP = 0x111876) (movR64R64Effect 0x111876 9 0) (Reg.operands [.gpr 0] [])) #v[1380]
    (b_l110d64_32)))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_31 : List UInt8 :=
  [0x4C, 0x8B, 0x5C, 0x24, 0x08, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0x64, 0x24, 0x38, 0x48, 0x89, 0xC1,
    0x48, 0x89, 0xD6, 0x49, 0x21, 0xFA, 0x4C, 0x89, 0x54, 0x24, 0x58, 0x4C, 0x8B, 0xA4, 0x24, 0xF0,
    0x00, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x48, 0xF7, 0xA4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89,
    0xD7, 0x49, 0x89, 0xC0, 0x49, 0x01, 0xC8, 0x48, 0x11, 0xF7, 0x4C, 0x8B, 0xBC, 0x24, 0xE0, 0x00,
    0x00, 0x00, 0x4C, 0x89, 0xF8, 0x48, 0x8B, 0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE3,
    0x48, 0x89, 0xD6, 0x49, 0x89, 0xC1] ++ bytes_l110d64_32

theorem code_l110d64_31 : ∀ x ∈ codeRange 0x111823 bytes_l110d64_31, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11823 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_32

def b_l110d64_30 : Block Op Label signature Reg.count 1309 :=
  .letOp (n := 1309) (.out 0x1117c9 (andR64R64Effect 0x1117c9 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[1256, 1207]
    (.letOp (n := 1310) (.exec 0x1117c9 (fun s => s.RIP = 0x1117c9) (andR64R64Effect 0x1117c9 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[1256, 1207]
    (.letOp (n := 1311) (.out 0x1117cc (leaR64Effect 0x1117cc 1 (.sib 12 (some 12) 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12, .gpr 12] []) (.reg (.gpr 1))) #v[1309, 1309]
    (.letOp (n := 1312) (.exec 0x1117cc (fun s => s.RIP = 0x1117cc) (leaR64Effect 0x1117cc 1 (.sib 12 (some 12) 1 .none)) (Reg.operands [.gpr 12, .gpr 12] [])) #v[1309, 1309]
    (.letOp (n := 1313) (.out 0x1117d0 (movR64R64Effect 0x1117d0 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[1307]
    (.letOp (n := 1314) (.exec 0x1117d0 (fun s => s.RIP = 0x1117d0) (movR64R64Effect 0x1117d0 2 7) (Reg.operands [.gpr 7] [])) #v[1307]
    (.letOp (n := 1315) (.out 0x1117d3 (shrR64Effect 0x1117d3 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1313]
    (.letOp (n := 1316) (.exec 0x1117d3 (fun s => s.RIP = 0x1117d3) (shrR64Effect 0x1117d3 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1313]
    (.letOp (n := 1317) (.out 0x1117d7 (leaR64Effect 0x1117d7 2 (.sib 2 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[1315, 1311]
    (.letOp (n := 1318) (.exec 0x1117d7 (fun s => s.RIP = 0x1117d7) (leaR64Effect 0x1117d7 2 (.sib 2 (some 1) 3 .none)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[1315, 1311]
    (.letOp (n := 1319) (.out 0x1117db (leaR64Effect 0x1117db 1 (.base 6 (.d8 0xf9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[1263]
    (.letOp (n := 1320) (.exec 0x1117db (fun s => s.RIP = 0x1117db) (leaR64Effect 0x1117db 1 (.base 6 (.d8 0xf9))) (Reg.operands [.gpr 6] [])) #v[1263]
    (.letOp (n := 1321) (.exec 0x1117df (StorePre 0x1117df 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1117df + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1117df 1 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1319, 4]
    (.letOp (n := 1322) (.out 0x1117e7 (andR64R64Effect 0x1117e7 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1277, 1319]
    (.letOp (n := 1323) (.exec 0x1117e7 (fun s => s.RIP = 0x1117e7) (andR64R64Effect 0x1117e7 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1277, 1319]
    (.letOp (n := 1324) (.out 0x1117ea (movR64R64Effect 0x1117ea 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1317]
    (.letOp (n := 1325) (.exec 0x1117ea (fun s => s.RIP = 0x1117ea) (movR64R64Effect 0x1117ea 1 2) (Reg.operands [.gpr 2] [])) #v[1317]
    (.letOp (n := 1326) (.out 0x1117ed (movR64R64Effect 0x1117ed 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[1317]
    (.letOp (n := 1327) (.exec 0x1117ed (fun s => s.RIP = 0x1117ed) (movR64R64Effect 0x1117ed 10 2) (Reg.operands [.gpr 2] [])) #v[1317]
    (.letOp (n := 1328) (.out 0x1117f0 (shrR64Effect 0x1117f0 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1324]
    (.letOp (n := 1329) (.exec 0x1117f0 (fun s => s.RIP = 0x1117f0) (shrR64Effect 0x1117f0 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1324]
    (.letOp (n := 1330) (.out 0x1117f4 (addR64R64Effect 0x1117f4 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1328, 1322]
    (.letOp (n := 1331) (.exec 0x1117f4 (fun s => s.RIP = 0x1117f4) (addR64R64Effect 0x1117f4 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1328, 1322]
    (.letOp (n := 1332) (.exec 0x1117f7 (StorePre 0x1117f7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1117f7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1117f7 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1330, 4]
    (.letOp (n := 1333) (.out 0x1117ff (andR64R64Effect 0x1117ff 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[1293, 1249]
    (.letOp (n := 1334) (.exec 0x1117ff (fun s => s.RIP = 0x1117ff) (andR64R64Effect 0x1117ff 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[1293, 1249]
    (.letOp (n := 1335) (.exec 0x111802 (StorePre 0x111802 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x111802 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111802 9 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[1333, 4]
    (.letOp (n := 1336) (.out 0x11180a (andR64R64Effect 0x11180a 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[1303, 1249]
    (.letOp (n := 1337) (.exec 0x11180a (fun s => s.RIP = 0x11180a) (andR64R64Effect 0x11180a 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[1303, 1249]
    (.letOp (n := 1338) (.exec 0x11180d (StorePre 0x11180d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11180d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11180d 8 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1336, 4]
    (.letOp (n := 1339) (.out 0x111815 (andR64R64Effect 0x111815 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[1307, 1249]
    (.letOp (n := 1340) (.exec 0x111815 (fun s => s.RIP = 0x111815) (andR64R64Effect 0x111815 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[1307, 1249]
    (.letOp (n := 1341) (.exec 0x111818 (StorePre 0x111818 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x111818 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111818 7 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1339, 4]
    (.letOp (n := 1342) (.out 0x111820 (movR64R64Effect 0x111820 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 11] []) (.reg (.gpr 7))) #v[1249]
    (.letOp (n := 1343) (.exec 0x111820 (fun s => s.RIP = 0x111820) (movR64R64Effect 0x111820 7 11) (Reg.operands [.gpr 11] [])) #v[1249]
    (b_l110d64_31)))))))))))))))))))))))))))))))))))

def bytes_l110d64_30 : List UInt8 :=
  [0x4D, 0x21, 0xD4, 0x4B, 0x8D, 0x0C, 0x64, 0x48, 0x89, 0xFA, 0x48, 0xC1, 0xEA, 0x34, 0x48, 0x8D,
    0x14, 0xCA, 0x48, 0x8D, 0x4E, 0xF9, 0x48, 0x89, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0x21,
    0xC8, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xD2, 0x48, 0xC1, 0xE9, 0x34, 0x48, 0x01, 0xC1, 0x48, 0x89,
    0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4D, 0x21, 0xD9, 0x4C, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00,
    0x00, 0x4D, 0x21, 0xD8, 0x4C, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x21, 0xDF, 0x48,
    0x89, 0xBC, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xDF] ++ bytes_l110d64_31

theorem code_l110d64_30 : ∀ x ∈ codeRange 0x1117c9 bytes_l110d64_30, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x117c9 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_31

def b_l110d64_29 : Block Op Label signature Reg.count 1269 :=
  .letOp (n := 1269) (.out 0x111771 (movR64M64Effect 0x111771 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1270) (.exec 0x111771 (LoadPre 0x111771 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x111771 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111771 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1271) (.out 0x111779 (leaR64Effect 0x111779 1 (.sib 0 (some 0) 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0, .gpr 0] []) (.reg (.gpr 1))) #v[1269, 1269]
    (.letOp (n := 1272) (.exec 0x111779 (fun s => s.RIP = 0x111779) (leaR64Effect 0x111779 1 (.sib 0 (some 0) 1 .none)) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1269, 1269]
    (.letOp (n := 1273) (.out 0x11177d (shlR64Effect 0x11177d 4 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1267]
    (.letOp (n := 1274) (.exec 0x11177d (fun s => s.RIP = 0x11177d) (shlR64Effect 0x11177d 4 13 3) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1267]
    (.letOp (n := 1275) (.out 0x111781 (leaR64Effect 0x111781 0 (.abs (some 13) 1 0x0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1273]
    (.letOp (n := 1276) (.exec 0x111781 (fun s => s.RIP = 0x111781) (leaR64Effect 0x111781 0 (.abs (some 13) 1 0x0)) (Reg.operands [.gpr 13] [])) #v[1273]
    (.letOp (n := 1277) (.out 0x111789 (addR64R64Effect 0x111789 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[1275, 1273]
    (.letOp (n := 1278) (.exec 0x111789 (fun s => s.RIP = 0x111789) (addR64R64Effect 0x111789 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[1275, 1273]
    (.letOp (n := 1279) (.out 0x11178c (movR64R64Effect 0x11178c 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[1277]
    (.letOp (n := 1280) (.exec 0x11178c (fun s => s.RIP = 0x11178c) (movR64R64Effect 0x11178c 2 0) (Reg.operands [.gpr 0] [])) #v[1277]
    (.letOp (n := 1281) (.out 0x11178f (shrR64Effect 0x11178f 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1279]
    (.letOp (n := 1282) (.exec 0x11178f (fun s => s.RIP = 0x11178f) (shrR64Effect 0x11178f 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1279]
    (.letOp (n := 1283) (.out 0x111793 (movR64Imm64Effect 0x111793 7 0x1000003d1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 1284) (.exec 0x111793 (fun s => s.RIP = 0x111793) (movR64Imm64Effect 0x111793 7 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 1285) (.out 0x11179d (imulR64R64Effect 0x11179d 4 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[1281, 1283]
    (.letOp (n := 1286) (.exec 0x11179d (fun s => s.RIP = 0x11179d) (imulR64R64Effect 0x11179d 4 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[1281, 1283]
    (.letOp (n := 1287) (.out 0x1117a1 (leaR64Effect 0x1117a1 7 (.sib 2 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2, .gpr 1] []) (.reg (.gpr 7))) #v[1285, 1271]
    (.letOp (n := 1288) (.exec 0x1117a1 (fun s => s.RIP = 0x1117a1) (leaR64Effect 0x1117a1 7 (.sib 2 (some 1) 3 .none)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[1285, 1271]
    (.letOp (n := 1289) (.out 0x1117a5 (leaR64Effect 0x1117a5 1 (.sib 14 (some 14) 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14, .gpr 14] []) (.reg (.gpr 1))) #v[1177, 1177]
    (.letOp (n := 1290) (.exec 0x1117a5 (fun s => s.RIP = 0x1117a5) (leaR64Effect 0x1117a5 1 (.sib 14 (some 14) 1 .none)) (Reg.operands [.gpr 14, .gpr 14] [])) #v[1177, 1177]
    (.letOp (n := 1291) (.out 0x1117a9 (movR64R64Effect 0x1117a9 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[1287]
    (.letOp (n := 1292) (.exec 0x1117a9 (fun s => s.RIP = 0x1117a9) (movR64R64Effect 0x1117a9 2 7) (Reg.operands [.gpr 7] [])) #v[1287]
    (.letOp (n := 1293) (.out 0x1117ac (movR64R64Effect 0x1117ac 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[1287]
    (.letOp (n := 1294) (.exec 0x1117ac (fun s => s.RIP = 0x1117ac) (movR64R64Effect 0x1117ac 9 7) (Reg.operands [.gpr 7] [])) #v[1287]
    (.letOp (n := 1295) (.out 0x1117af (shrR64Effect 0x1117af 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1291]
    (.letOp (n := 1296) (.exec 0x1117af (fun s => s.RIP = 0x1117af) (shrR64Effect 0x1117af 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1291]
    (.letOp (n := 1297) (.out 0x1117b3 (leaR64Effect 0x1117b3 7 (.sib 2 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2, .gpr 1] []) (.reg (.gpr 7))) #v[1295, 1289]
    (.letOp (n := 1298) (.exec 0x1117b3 (fun s => s.RIP = 0x1117b3) (leaR64Effect 0x1117b3 7 (.sib 2 (some 1) 3 .none)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[1295, 1289]
    (.letOp (n := 1299) (.out 0x1117b7 (leaR64Effect 0x1117b7 1 (.sib 8 (some 8) 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8, .gpr 8] []) (.reg (.gpr 1))) #v[1240, 1240]
    (.letOp (n := 1300) (.exec 0x1117b7 (fun s => s.RIP = 0x1117b7) (leaR64Effect 0x1117b7 1 (.sib 8 (some 8) 1 .none)) (Reg.operands [.gpr 8, .gpr 8] [])) #v[1240, 1240]
    (.letOp (n := 1301) (.out 0x1117bb (movR64R64Effect 0x1117bb 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[1297]
    (.letOp (n := 1302) (.exec 0x1117bb (fun s => s.RIP = 0x1117bb) (movR64R64Effect 0x1117bb 2 7) (Reg.operands [.gpr 7] [])) #v[1297]
    (.letOp (n := 1303) (.out 0x1117be (movR64R64Effect 0x1117be 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[1297]
    (.letOp (n := 1304) (.exec 0x1117be (fun s => s.RIP = 0x1117be) (movR64R64Effect 0x1117be 8 7) (Reg.operands [.gpr 7] [])) #v[1297]
    (.letOp (n := 1305) (.out 0x1117c1 (shrR64Effect 0x1117c1 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1301]
    (.letOp (n := 1306) (.exec 0x1117c1 (fun s => s.RIP = 0x1117c1) (shrR64Effect 0x1117c1 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1301]
    (.letOp (n := 1307) (.out 0x1117c5 (leaR64Effect 0x1117c5 7 (.sib 2 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2, .gpr 1] []) (.reg (.gpr 7))) #v[1305, 1299]
    (.letOp (n := 1308) (.exec 0x1117c5 (fun s => s.RIP = 0x1117c5) (leaR64Effect 0x1117c5 7 (.sib 2 (some 1) 3 .none)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[1305, 1299]
    (b_l110d64_30))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_29 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x0C, 0x40, 0x49, 0xC1, 0xE5, 0x03,
    0x4A, 0x8D, 0x04, 0x6D, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xE8, 0x48, 0x89, 0xC2, 0x48, 0xC1,
    0xEA, 0x30, 0x48, 0xBF, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xD7,
    0x48, 0x8D, 0x3C, 0xCA, 0x4B, 0x8D, 0x0C, 0x76, 0x48, 0x89, 0xFA, 0x49, 0x89, 0xF9, 0x48, 0xC1,
    0xEA, 0x34, 0x48, 0x8D, 0x3C, 0xCA, 0x4B, 0x8D, 0x0C, 0x40, 0x48, 0x89, 0xFA, 0x49, 0x89, 0xF8,
    0x48, 0xC1, 0xEA, 0x34, 0x48, 0x8D, 0x3C, 0xCA] ++ bytes_l110d64_30

theorem code_l110d64_29 : ∀ x ∈ codeRange 0x111771 bytes_l110d64_29, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11771 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_30

def b_l110d64_28 : Block Op Label signature Reg.count 1224 :=
  .letOp (n := 1224) (.out 0x111720 (atFlags StatusFlags.CF (adcR64M64Effect 0x111720 6 (.sib 4 none 0 (.d32 0xd0)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[1219, 4, 1222]
    (.letOp (n := 1225) (.exec 0x111720 (LoadPre 0x111720 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x111720 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111720 6 (.sib 4 none 0 (.d32 0xd0)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1219, 4, 1222]
    (.letOp (n := 1226) (.out 0x111728 (addR64R64Effect 0x111728 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[1221, 1213]
    (.letOp (n := 1227) (.out 0x111728 (addR64R64Effect 0x111728 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[1221, 1213]
    (.letOp (n := 1228) (.exec 0x111728 (fun s => s.RIP = 0x111728) (addR64R64Effect 0x111728 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1221, 1213]
    (.letOp (n := 1229) (.out 0x11172b (atFlags StatusFlags.CF (adcR64R64Effect 0x11172b 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[1224, 1214, 1227]
    (.letOp (n := 1230) (.exec 0x11172b (fun s => s.RIP = 0x11172b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11172b 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1224, 1214, 1227]
    (.letOp (n := 1231) (.out 0x11172e (addR64R64Effect 0x11172e 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[1226, 1150]
    (.letOp (n := 1232) (.out 0x11172e (addR64R64Effect 0x11172e 8 3) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 3] []) (.flag .CF)) #v[1226, 1150]
    (.letOp (n := 1233) (.exec 0x11172e (fun s => s.RIP = 0x11172e) (addR64R64Effect 0x11172e 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[1226, 1150]
    (.letOp (n := 1234) (.out 0x111731 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111731 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[1229, 1232]
    (.letOp (n := 1235) (.exec 0x111731 (fun s => s.RIP = 0x111731) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111731 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1229, 1232]
    (.letOp (n := 1236) (.out 0x111735 (shldR64R64Effect 0x111735 5 11 7 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1203, 1200]
    (.letOp (n := 1237) (.exec 0x111735 (fun s => s.RIP = 0x111735) (shldR64R64Effect 0x111735 5 11 7 12) (Reg.operands [.gpr 11, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1203, 1200]
    (.letOp (n := 1238) (.out 0x11173a (shldR64R64Effect 0x11173a 5 6 8 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1234, 1231]
    (.letOp (n := 1239) (.exec 0x11173a (fun s => s.RIP = 0x11173a) (shldR64R64Effect 0x11173a 5 6 8 12) (Reg.operands [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1234, 1231]
    (.letOp (n := 1240) (.out 0x11173f (andR64R64Effect 0x11173f 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[1231, 1207]
    (.letOp (n := 1241) (.exec 0x11173f (fun s => s.RIP = 0x11173f) (andR64R64Effect 0x11173f 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[1231, 1207]
    (.letOp (n := 1242) (.out 0x111742 (movR64R64Effect 0x111742 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[1236]
    (.letOp (n := 1243) (.exec 0x111742 (fun s => s.RIP = 0x111742) (movR64R64Effect 0x111742 0 11) (Reg.operands [.gpr 11] [])) #v[1236]
    (.letOp (n := 1244) (.out 0x111745 (mulR64Effect 0x111745 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1211, 1242]
    (.letOp (n := 1245) (.out 0x111745 (mulR64Effect 0x111745 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1211, 1242]
    (.letOp (n := 1246) (.exec 0x111745 (fun s => s.RIP = 0x111745) (mulR64Effect 0x111745 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1211, 1242]
    (.letOp (n := 1247) (.out 0x111748 (andR64R64Effect 0x111748 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[867, 1207]
    (.letOp (n := 1248) (.exec 0x111748 (fun s => s.RIP = 0x111748) (andR64R64Effect 0x111748 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[867, 1207]
    (.letOp (n := 1249) (.out 0x11174b (movR64R64Effect 0x11174b 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[1207]
    (.letOp (n := 1250) (.exec 0x11174b (fun s => s.RIP = 0x11174b) (movR64R64Effect 0x11174b 11 10) (Reg.operands [.gpr 10] [])) #v[1207]
    (.letOp (n := 1251) (.out 0x11174e (addR64R64Effect 0x11174e 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[1247, 1244]
    (.letOp (n := 1252) (.out 0x11174e (addR64R64Effect 0x11174e 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[1247, 1244]
    (.letOp (n := 1253) (.exec 0x11174e (fun s => s.RIP = 0x11174e) (addR64R64Effect 0x11174e 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[1247, 1244]
    (.letOp (n := 1254) (.out 0x111751 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111751 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[1245, 1252]
    (.letOp (n := 1255) (.exec 0x111751 (fun s => s.RIP = 0x111751) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111751 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1245, 1252]
    (.letOp (n := 1256) (.out 0x111755 (addR64R64Effect 0x111755 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[1251, 1238]
    (.letOp (n := 1257) (.out 0x111755 (addR64R64Effect 0x111755 12 6) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 6] []) (.flag .CF)) #v[1251, 1238]
    (.letOp (n := 1258) (.exec 0x111755 (fun s => s.RIP = 0x111755) (addR64R64Effect 0x111755 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[1251, 1238]
    (.letOp (n := 1259) (.out 0x111758 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111758 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[1254, 1257]
    (.letOp (n := 1260) (.exec 0x111758 (fun s => s.RIP = 0x111758) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111758 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1254, 1257]
    (.letOp (n := 1261) (.out 0x11175c (shldR64R64Effect 0x11175c 5 2 12 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1259, 1256]
    (.letOp (n := 1262) (.exec 0x11175c (fun s => s.RIP = 0x11175c) (shldR64R64Effect 0x11175c 5 2 12 12) (Reg.operands [.gpr 2, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1259, 1256]
    (.letOp (n := 1263) (.out 0x111761 (movR64Imm64Effect 0x111761 6 0xffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 1264) (.exec 0x111761 (fun s => s.RIP = 0x111761) (movR64Imm64Effect 0x111761 6 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1265) (.out 0x11176b (andR64R64Effect 0x11176b 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 6] []) (.reg (.gpr 13))) #v[954, 1263]
    (.letOp (n := 1266) (.exec 0x11176b (fun s => s.RIP = 0x11176b) (andR64R64Effect 0x11176b 13 6) (Reg.operands [.gpr 13, .gpr 6] [])) #v[954, 1263]
    (.letOp (n := 1267) (.out 0x11176e (addR64R64Effect 0x11176e 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[1265, 1261]
    (.letOp (n := 1268) (.exec 0x11176e (fun s => s.RIP = 0x11176e) (addR64R64Effect 0x11176e 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[1265, 1261]
    (b_l110d64_29)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_28 : List UInt8 :=
  [0x48, 0x13, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC0, 0x48, 0x11, 0xD6, 0x49, 0x01,
    0xD8, 0x48, 0x83, 0xD6, 0x00, 0x49, 0x0F, 0xA4, 0xFB, 0x0C, 0x4C, 0x0F, 0xA4, 0xC6, 0x0C, 0x4D,
    0x21, 0xD0, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0xE1, 0x4D, 0x21, 0xD4, 0x4D, 0x89, 0xD3, 0x49, 0x01,
    0xC4, 0x48, 0x83, 0xD2, 0x00, 0x49, 0x01, 0xF4, 0x48, 0x83, 0xD2, 0x00, 0x4C, 0x0F, 0xA4, 0xE2,
    0x0C, 0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x49, 0x21, 0xF5, 0x49, 0x01,
    0xD5] ++ bytes_l110d64_29

theorem code_l110d64_28 : ∀ x ∈ codeRange 0x111720 bytes_l110d64_28, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11720 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_29

def b_l110d64_27 : Block Op Label signature Reg.count 1177 :=
  .letOp (n := 1177) (.out 0x1116ce (andR64R64Effect 0x1116ce 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[1145, 1126]
    (.letOp (n := 1178) (.exec 0x1116ce (fun s => s.RIP = 0x1116ce) (andR64R64Effect 0x1116ce 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[1145, 1126]
    (.letOp (n := 1179) (.out 0x1116d1 (movR64M64Effect 0x1116d1 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1180) (.exec 0x1116d1 (LoadPre 0x1116d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1116d1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1116d1 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1181) (.out 0x1116d6 (mulM64Effect 0x1116d6 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1179, 4]
    (.letOp (n := 1182) (.out 0x1116d6 (mulM64Effect 0x1116d6 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1179, 4]
    (.letOp (n := 1183) (.exec 0x1116d6 (LoadPre 0x1116d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1116d6 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1116d6 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1179, 4]
    (.letOp (n := 1184) (.out 0x1116db (movR64R64Effect 0x1116db 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[1182]
    (.letOp (n := 1185) (.exec 0x1116db (fun s => s.RIP = 0x1116db) (movR64R64Effect 0x1116db 11 2) (Reg.operands [.gpr 2] [])) #v[1182]
    (.letOp (n := 1186) (.out 0x1116de (movR64R64Effect 0x1116de 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1181]
    (.letOp (n := 1187) (.exec 0x1116de (fun s => s.RIP = 0x1116de) (movR64R64Effect 0x1116de 15 0) (Reg.operands [.gpr 0] [])) #v[1181]
    (.letOp (n := 1188) (.out 0x1116e1 (movR64M64Effect 0x1116e1 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1189) (.exec 0x1116e1 (LoadPre 0x1116e1 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1116e1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1116e1 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1190) (.out 0x1116e5 (mulR64Effect 0x1116e5 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1104, 1188]
    (.letOp (n := 1191) (.out 0x1116e5 (mulR64Effect 0x1116e5 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1104, 1188]
    (.letOp (n := 1192) (.exec 0x1116e5 (fun s => s.RIP = 0x1116e5) (mulR64Effect 0x1116e5 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1104, 1188]
    (.letOp (n := 1193) (.out 0x1116e8 (movR64R64Effect 0x1116e8 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[1190]
    (.letOp (n := 1194) (.exec 0x1116e8 (fun s => s.RIP = 0x1116e8) (movR64R64Effect 0x1116e8 7 0) (Reg.operands [.gpr 0] [])) #v[1190]
    (.letOp (n := 1195) (.out 0x1116eb (addR64R64Effect 0x1116eb 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[1193, 1186]
    (.letOp (n := 1196) (.out 0x1116eb (addR64R64Effect 0x1116eb 7 15) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 15] []) (.flag .CF)) #v[1193, 1186]
    (.letOp (n := 1197) (.exec 0x1116eb (fun s => s.RIP = 0x1116eb) (addR64R64Effect 0x1116eb 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[1193, 1186]
    (.letOp (n := 1198) (.out 0x1116ee (atFlags StatusFlags.CF (adcR64R64Effect 0x1116ee 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1184, 1191, 1196]
    (.letOp (n := 1199) (.exec 0x1116ee (fun s => s.RIP = 0x1116ee) (atFlags StatusFlags.CF (adcR64R64Effect 0x1116ee 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1184, 1191, 1196]
    (.letOp (n := 1200) (.out 0x1116f1 (addR64R64Effect 0x1116f1 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[1195, 1124]
    (.letOp (n := 1201) (.out 0x1116f1 (addR64R64Effect 0x1116f1 7 10) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 10] []) (.flag .CF)) #v[1195, 1124]
    (.letOp (n := 1202) (.exec 0x1116f1 (fun s => s.RIP = 0x1116f1) (addR64R64Effect 0x1116f1 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[1195, 1124]
    (.letOp (n := 1203) (.out 0x1116f4 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1116f4 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[1198, 1201]
    (.letOp (n := 1204) (.exec 0x1116f4 (fun s => s.RIP = 0x1116f4) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1116f4 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1198, 1201]
    (.letOp (n := 1205) (.out 0x1116f8 (movR64R64Effect 0x1116f8 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1200]
    (.letOp (n := 1206) (.exec 0x1116f8 (fun s => s.RIP = 0x1116f8) (movR64R64Effect 0x1116f8 0 7) (Reg.operands [.gpr 7] [])) #v[1200]
    (.letOp (n := 1207) (.out 0x1116fb (movR64Imm64Effect 0x1116fb 10 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 1208) (.exec 0x1116fb (fun s => s.RIP = 0x1116fb) (movR64Imm64Effect 0x1116fb 10 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1209) (.out 0x111705 (andR64R64Effect 0x111705 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[1205, 1207]
    (.letOp (n := 1210) (.exec 0x111705 (fun s => s.RIP = 0x111705) (andR64R64Effect 0x111705 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[1205, 1207]
    (.letOp (n := 1211) (.out 0x111708 (movR64Imm64Effect 0x111708 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1212) (.exec 0x111708 (fun s => s.RIP = 0x111708) (movR64Imm64Effect 0x111708 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1213) (.out 0x111712 (mulR64Effect 0x111712 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1211, 1209]
    (.letOp (n := 1214) (.out 0x111712 (mulR64Effect 0x111712 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1211, 1209]
    (.letOp (n := 1215) (.exec 0x111712 (fun s => s.RIP = 0x111712) (mulR64Effect 0x111712 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1211, 1209]
    (.letOp (n := 1216) (.out 0x111715 (addR64R64Effect 0x111715 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[1173, 1166]
    (.letOp (n := 1217) (.out 0x111715 (addR64R64Effect 0x111715 8 9) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 9] []) (.flag .CF)) #v[1173, 1166]
    (.letOp (n := 1218) (.exec 0x111715 (fun s => s.RIP = 0x111715) (addR64R64Effect 0x111715 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[1173, 1166]
    (.letOp (n := 1219) (.out 0x111718 (atFlags StatusFlags.CF (adcR64R64Effect 0x111718 6 5)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[1175, 1164, 1217]
    (.letOp (n := 1220) (.exec 0x111718 (fun s => s.RIP = 0x111718) (atFlags StatusFlags.CF (adcR64R64Effect 0x111718 6 5)) (Reg.operands [.gpr 6, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1175, 1164, 1217]
    (.letOp (n := 1221) (.out 0x11171b (addR64M64Effect 0x11171b 8 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[1216, 4]
    (.letOp (n := 1222) (.out 0x11171b (addR64M64Effect 0x11171b 8 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[1216, 4]
    (.letOp (n := 1223) (.exec 0x11171b (LoadPre 0x11171b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11171b + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11171b 8 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1216, 4]
    (b_l110d64_28)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_27 : List UInt8 :=
  [0x4D, 0x21, 0xDE, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0xF7, 0x64, 0x24, 0x60, 0x49, 0x89, 0xD3,
    0x49, 0x89, 0xC7, 0x48, 0x8B, 0x04, 0x24, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC7, 0x4C, 0x01, 0xFF,
    0x49, 0x11, 0xD3, 0x4C, 0x01, 0xD7, 0x49, 0x83, 0xD3, 0x00, 0x48, 0x89, 0xF8, 0x49, 0xBA, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xD0, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x4D, 0x01, 0xC8, 0x48, 0x11, 0xEE, 0x4C, 0x03, 0x44,
    0x24, 0x58] ++ bytes_l110d64_28

theorem code_l110d64_27 : ∀ x ∈ codeRange 0x1116ce bytes_l110d64_27, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x116ce 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_28

def b_l110d64_26 : Block Op Label signature Reg.count 1132 :=
  .letOp (n := 1132) (.out 0x111673 (mulR64Effect 0x111673 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[1130, 1128]
    (.letOp (n := 1133) (.out 0x111673 (mulR64Effect 0x111673 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1130, 1128]
    (.letOp (n := 1134) (.exec 0x111673 (fun s => s.RIP = 0x111673) (mulR64Effect 0x111673 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1130, 1128]
    (.letOp (n := 1135) (.out 0x111676 (addR64M64Effect 0x111676 14 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[1075, 4]
    (.letOp (n := 1136) (.out 0x111676 (addR64M64Effect 0x111676 14 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 4] []) (.flag .CF)) #v[1075, 4]
    (.letOp (n := 1137) (.exec 0x111676 (LoadPre 0x111676 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x111676 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x111676 14 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[1075, 4]
    (.letOp (n := 1138) (.out 0x11167e (atFlags StatusFlags.CF (adcR64M64Effect 0x11167e 3 (.sib 4 none 0 (.d8 0x58)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[1073, 4, 1136]
    (.letOp (n := 1139) (.exec 0x11167e (LoadPre 0x11167e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11167e + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11167e 3 (.sib 4 none 0 (.d8 0x58)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1073, 4, 1136]
    (.letOp (n := 1140) (.out 0x111683 (addR64R64Effect 0x111683 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[1135, 1132]
    (.letOp (n := 1141) (.out 0x111683 (addR64R64Effect 0x111683 14 0) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 0] []) (.flag .CF)) #v[1135, 1132]
    (.letOp (n := 1142) (.exec 0x111683 (fun s => s.RIP = 0x111683) (addR64R64Effect 0x111683 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1135, 1132]
    (.letOp (n := 1143) (.out 0x111686 (atFlags StatusFlags.CF (adcR64R64Effect 0x111686 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1138, 1133, 1141]
    (.letOp (n := 1144) (.exec 0x111686 (fun s => s.RIP = 0x111686) (atFlags StatusFlags.CF (adcR64R64Effect 0x111686 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1138, 1133, 1141]
    (.letOp (n := 1145) (.out 0x111689 (addR64R64Effect 0x111689 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[1140, 1055]
    (.letOp (n := 1146) (.out 0x111689 (addR64R64Effect 0x111689 14 6) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 6] []) (.flag .CF)) #v[1140, 1055]
    (.letOp (n := 1147) (.exec 0x111689 (fun s => s.RIP = 0x111689) (addR64R64Effect 0x111689 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[1140, 1055]
    (.letOp (n := 1148) (.out 0x11168c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11168c 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[1143, 1146]
    (.letOp (n := 1149) (.exec 0x11168c (fun s => s.RIP = 0x11168c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11168c 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1143, 1146]
    (.letOp (n := 1150) (.out 0x111690 (shldR64R64Effect 0x111690 5 3 14 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1148, 1145]
    (.letOp (n := 1151) (.exec 0x111690 (fun s => s.RIP = 0x111690) (shldR64R64Effect 0x111690 5 3 14 12) (Reg.operands [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1148, 1145]
    (.letOp (n := 1152) (.out 0x111695 (movR64R64Effect 0x111695 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[1100]
    (.letOp (n := 1153) (.exec 0x111695 (fun s => s.RIP = 0x111695) (movR64R64Effect 0x111695 0 8) (Reg.operands [.gpr 8] [])) #v[1100]
    (.letOp (n := 1154) (.out 0x111698 (mulR64Effect 0x111698 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[1061, 1152]
    (.letOp (n := 1155) (.out 0x111698 (mulR64Effect 0x111698 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[1061, 1152]
    (.letOp (n := 1156) (.exec 0x111698 (fun s => s.RIP = 0x111698) (mulR64Effect 0x111698 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1061, 1152]
    (.letOp (n := 1157) (.exec 0x11169b (StorePre 0x11169b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11169b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11169b 2 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1155, 4]
    (.letOp (n := 1158) (.exec 0x1116a3 (StorePre 0x1116a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1116a3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1116a3 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1154, 4]
    (.letOp (n := 1159) (.out 0x1116a8 (movR64M64Effect 0x1116a8 0 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1160) (.exec 0x1116a8 (LoadPre 0x1116a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1116a8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1116a8 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1161) (.out 0x1116b0 (mulM64Effect 0x1116b0 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1159, 4]
    (.letOp (n := 1162) (.out 0x1116b0 (mulM64Effect 0x1116b0 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1159, 4]
    (.letOp (n := 1163) (.exec 0x1116b0 (LoadPre 0x1116b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1116b0 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1116b0 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1159, 4]
    (.letOp (n := 1164) (.out 0x1116b5 (movR64R64Effect 0x1116b5 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[1162]
    (.letOp (n := 1165) (.exec 0x1116b5 (fun s => s.RIP = 0x1116b5) (movR64R64Effect 0x1116b5 5 2) (Reg.operands [.gpr 2] [])) #v[1162]
    (.letOp (n := 1166) (.out 0x1116b8 (movR64R64Effect 0x1116b8 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[1161]
    (.letOp (n := 1167) (.exec 0x1116b8 (fun s => s.RIP = 0x1116b8) (movR64R64Effect 0x1116b8 9 0) (Reg.operands [.gpr 0] [])) #v[1161]
    (.letOp (n := 1168) (.out 0x1116bb (movR64M64Effect 0x1116bb 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1169) (.exec 0x1116bb (LoadPre 0x1116bb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1116bb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1116bb 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1170) (.out 0x1116c3 (mulM64Effect 0x1116c3 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1168, 4]
    (.letOp (n := 1171) (.out 0x1116c3 (mulM64Effect 0x1116c3 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1168, 4]
    (.letOp (n := 1172) (.exec 0x1116c3 (LoadPre 0x1116c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1116c3 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1116c3 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1168, 4]
    (.letOp (n := 1173) (.out 0x1116c8 (movR64R64Effect 0x1116c8 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[1170]
    (.letOp (n := 1174) (.exec 0x1116c8 (fun s => s.RIP = 0x1116c8) (movR64R64Effect 0x1116c8 8 0) (Reg.operands [.gpr 0] [])) #v[1170]
    (.letOp (n := 1175) (.out 0x1116cb (movR64R64Effect 0x1116cb 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1171]
    (.letOp (n := 1176) (.exec 0x1116cb (fun s => s.RIP = 0x1116cb) (movR64R64Effect 0x1116cb 6 2) (Reg.operands [.gpr 2] [])) #v[1171]
    (b_l110d64_27)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_26 : List UInt8 :=
  [0x48, 0xF7, 0xE2, 0x4C, 0x03, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x13, 0x5C, 0x24, 0x58,
    0x49, 0x01, 0xC6, 0x48, 0x11, 0xD3, 0x49, 0x01, 0xF6, 0x48, 0x83, 0xD3, 0x00, 0x4C, 0x0F, 0xA4,
    0xF3, 0x0C, 0x4C, 0x89, 0xC0, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0x94, 0x24, 0xD0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x44, 0x24, 0x58, 0x48, 0x8B, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0x64,
    0x24, 0x28, 0x48, 0x89, 0xD5, 0x49, 0x89, 0xC1, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0x64, 0x24, 0x48, 0x49, 0x89, 0xC0, 0x48, 0x89, 0xD6] ++ bytes_l110d64_27

theorem code_l110d64_26 : ∀ x ∈ codeRange 0x111673 bytes_l110d64_26, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11673 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_27

def b_l110d64_25 : Block Op Label signature Reg.count 1088 :=
  .letOp (n := 1088) (.out 0x111619 (andR64R64Effect 0x111619 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1057, 1086]
    (.letOp (n := 1089) (.exec 0x111619 (fun s => s.RIP = 0x111619) (andR64R64Effect 0x111619 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1057, 1086]
    (.letOp (n := 1090) (.exec 0x11161c (StorePre 0x11161c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11161c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11161c 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1088, 4]
    (.letOp (n := 1091) (.out 0x111624 (movR64M64Effect 0x111624 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1092) (.exec 0x111624 (LoadPre 0x111624 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111624 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111624 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1093) (.out 0x111628 (mulR64Effect 0x111628 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[997, 1091]
    (.letOp (n := 1094) (.out 0x111628 (mulR64Effect 0x111628 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[997, 1091]
    (.letOp (n := 1095) (.exec 0x111628 (fun s => s.RIP = 0x111628) (mulR64Effect 0x111628 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[997, 1091]
    (.letOp (n := 1096) (.out 0x11162b (movR64R64Effect 0x11162b 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[1094]
    (.letOp (n := 1097) (.exec 0x11162b (fun s => s.RIP = 0x11162b) (movR64R64Effect 0x11162b 10 2) (Reg.operands [.gpr 2] [])) #v[1094]
    (.letOp (n := 1098) (.out 0x11162e (movR64R64Effect 0x11162e 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[1093]
    (.letOp (n := 1099) (.exec 0x11162e (fun s => s.RIP = 0x11162e) (movR64R64Effect 0x11162e 15 0) (Reg.operands [.gpr 0] [])) #v[1093]
    (.letOp (n := 1100) (.out 0x111631 (movR64M64Effect 0x111631 8 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 1101) (.exec 0x111631 (LoadPre 0x111631 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x111631 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111631 8 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1102) (.out 0x111639 (movR64R64Effect 0x111639 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[1100]
    (.letOp (n := 1103) (.exec 0x111639 (fun s => s.RIP = 0x111639) (movR64R64Effect 0x111639 0 8) (Reg.operands [.gpr 8] [])) #v[1100]
    (.letOp (n := 1104) (.out 0x11163c (movR64M64Effect 0x11163c 1 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 1105) (.exec 0x11163c (LoadPre 0x11163c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11163c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11163c 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1106) (.out 0x111641 (mulR64Effect 0x111641 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1104, 1102]
    (.letOp (n := 1107) (.out 0x111641 (mulR64Effect 0x111641 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1104, 1102]
    (.letOp (n := 1108) (.exec 0x111641 (fun s => s.RIP = 0x111641) (mulR64Effect 0x111641 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1104, 1102]
    (.letOp (n := 1109) (.out 0x111644 (addR64R64Effect 0x111644 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[1106, 1098]
    (.letOp (n := 1110) (.out 0x111644 (addR64R64Effect 0x111644 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[1106, 1098]
    (.letOp (n := 1111) (.exec 0x111644 (fun s => s.RIP = 0x111644) (addR64R64Effect 0x111644 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[1106, 1098]
    (.letOp (n := 1112) (.out 0x111647 (atFlags StatusFlags.CF (adcR64R64Effect 0x111647 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1096, 1107, 1110]
    (.letOp (n := 1113) (.exec 0x111647 (fun s => s.RIP = 0x111647) (atFlags StatusFlags.CF (adcR64R64Effect 0x111647 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1096, 1107, 1110]
    (.letOp (n := 1114) (.out 0x11164a (addR64R64Effect 0x11164a 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[1109, 1082]
    (.letOp (n := 1115) (.out 0x11164a (addR64R64Effect 0x11164a 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[1109, 1082]
    (.letOp (n := 1116) (.exec 0x11164a (fun s => s.RIP = 0x11164a) (addR64R64Effect 0x11164a 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[1109, 1082]
    (.letOp (n := 1117) (.out 0x11164d (atFlags StatusFlags.CF (adcR64R64Effect 0x11164d 10 11)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1112, 1084, 1115]
    (.letOp (n := 1118) (.exec 0x11164d (fun s => s.RIP = 0x11164d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11164d 10 11)) (Reg.operands [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1112, 1084, 1115]
    (.letOp (n := 1119) (.out 0x111650 (addR64R64Effect 0x111650 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[1114, 1033]
    (.letOp (n := 1120) (.out 0x111650 (addR64R64Effect 0x111650 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[1114, 1033]
    (.letOp (n := 1121) (.exec 0x111650 (fun s => s.RIP = 0x111650) (addR64R64Effect 0x111650 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[1114, 1033]
    (.letOp (n := 1122) (.out 0x111653 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111653 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[1117, 1120]
    (.letOp (n := 1123) (.exec 0x111653 (fun s => s.RIP = 0x111653) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111653 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1117, 1120]
    (.letOp (n := 1124) (.out 0x111657 (shldR64R64Effect 0x111657 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[1122, 1119]
    (.letOp (n := 1125) (.exec 0x111657 (fun s => s.RIP = 0x111657) (shldR64R64Effect 0x111657 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1122, 1119]
    (.letOp (n := 1126) (.out 0x11165c (movR64Imm64Effect 0x11165c 11 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 1127) (.exec 0x11165c (fun s => s.RIP = 0x11165c) (movR64Imm64Effect 0x11165c 11 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1128) (.out 0x111666 (andR64R64Effect 0x111666 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[1119, 1126]
    (.letOp (n := 1129) (.exec 0x111666 (fun s => s.RIP = 0x111666) (andR64R64Effect 0x111666 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[1119, 1126]
    (.letOp (n := 1130) (.out 0x111669 (movR64Imm64Effect 0x111669 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1131) (.exec 0x111669 (fun s => s.RIP = 0x111669) (movR64Imm64Effect 0x111669 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (b_l110d64_26))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_25 : List UInt8 :=
  [0x48, 0x21, 0xC1, 0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x04, 0x24, 0x49,
    0xF7, 0xE0, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC7, 0x4C, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00,
    0x4C, 0x89, 0xC0, 0x48, 0x8B, 0x4C, 0x24, 0x40, 0x48, 0xF7, 0xE1, 0x4C, 0x01, 0xF8, 0x49, 0x11,
    0xD2, 0x4C, 0x01, 0xC8, 0x4D, 0x11, 0xDA, 0x48, 0x01, 0xE8, 0x49, 0x83, 0xD2, 0x00, 0x49, 0x0F,
    0xA4, 0xC2, 0x0C, 0x49, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xD8,
    0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] ++ bytes_l110d64_26

theorem code_l110d64_25 : ∀ x ∈ codeRange 0x111619 bytes_l110d64_25, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11619 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_26

def b_l110d64_24 : Block Op Label signature Reg.count 1045 :=
  .letOp (n := 1045) (.out 0x1115bd (mulR64Effect 0x1115bd 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1043, 1041]
    (.letOp (n := 1046) (.out 0x1115bd (mulR64Effect 0x1115bd 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[1043, 1041]
    (.letOp (n := 1047) (.exec 0x1115bd (fun s => s.RIP = 0x1115bd) (mulR64Effect 0x1115bd 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1043, 1041]
    (.letOp (n := 1048) (.out 0x1115c0 (movR64R64Effect 0x1115c0 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1046]
    (.letOp (n := 1049) (.exec 0x1115c0 (fun s => s.RIP = 0x1115c0) (movR64R64Effect 0x1115c0 6 2) (Reg.operands [.gpr 2] [])) #v[1046]
    (.letOp (n := 1050) (.out 0x1115c3 (addR64M64Effect 0x1115c3 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1045, 4]
    (.letOp (n := 1051) (.out 0x1115c3 (addR64M64Effect 0x1115c3 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[1045, 4]
    (.letOp (n := 1052) (.exec 0x1115c3 (LoadPre 0x1115c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1115c3 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1115c3 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1045, 4]
    (.letOp (n := 1053) (.out 0x1115c8 (atFlags StatusFlags.CF (adcR64M64Effect 0x1115c8 6 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[1048, 4, 1051]
    (.letOp (n := 1054) (.exec 0x1115c8 (LoadPre 0x1115c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1115c8 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1115c8 6 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1048, 4, 1051]
    (.letOp (n := 1055) (.out 0x1115d0 (shldR64R64Effect 0x1115d0 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1053, 1050]
    (.letOp (n := 1056) (.exec 0x1115d0 (fun s => s.RIP = 0x1115d0) (shldR64R64Effect 0x1115d0 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1053, 1050]
    (.letOp (n := 1057) (.out 0x1115d5 (movR64R64Effect 0x1115d5 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1050]
    (.letOp (n := 1058) (.exec 0x1115d5 (fun s => s.RIP = 0x1115d5) (movR64R64Effect 0x1115d5 1 0) (Reg.operands [.gpr 0] [])) #v[1050]
    (.letOp (n := 1059) (.out 0x1115d8 (movR64R64Effect 0x1115d8 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1006]
    (.letOp (n := 1060) (.exec 0x1115d8 (fun s => s.RIP = 0x1115d8) (movR64R64Effect 0x1115d8 0 7) (Reg.operands [.gpr 7] [])) #v[1006]
    (.letOp (n := 1061) (.out 0x1115db (movR64M64Effect 0x1115db 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 1062) (.exec 0x1115db (LoadPre 0x1115db (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1115db + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1115db 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1063) (.out 0x1115e0 (mulR64Effect 0x1115e0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[1061, 1059]
    (.letOp (n := 1064) (.out 0x1115e0 (mulR64Effect 0x1115e0 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[1061, 1059]
    (.letOp (n := 1065) (.exec 0x1115e0 (fun s => s.RIP = 0x1115e0) (mulR64Effect 0x1115e0 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1061, 1059]
    (.letOp (n := 1066) (.exec 0x1115e3 (StorePre 0x1115e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1115e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1115e3 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1064, 4]
    (.letOp (n := 1067) (.exec 0x1115e8 (StorePre 0x1115e8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1115e8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1115e8 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1063, 4]
    (.letOp (n := 1068) (.out 0x1115f0 (movR64M64Effect 0x1115f0 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1069) (.exec 0x1115f0 (LoadPre 0x1115f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1115f0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1115f0 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1070) (.out 0x1115f8 (mulR64Effect 0x1115f8 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[974, 1068]
    (.letOp (n := 1071) (.out 0x1115f8 (mulR64Effect 0x1115f8 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[974, 1068]
    (.letOp (n := 1072) (.exec 0x1115f8 (fun s => s.RIP = 0x1115f8) (mulR64Effect 0x1115f8 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[974, 1068]
    (.letOp (n := 1073) (.out 0x1115fb (movR64R64Effect 0x1115fb 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[1071]
    (.letOp (n := 1074) (.exec 0x1115fb (fun s => s.RIP = 0x1115fb) (movR64R64Effect 0x1115fb 3 2) (Reg.operands [.gpr 2] [])) #v[1071]
    (.letOp (n := 1075) (.out 0x1115fe (movR64R64Effect 0x1115fe 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[1070]
    (.letOp (n := 1076) (.exec 0x1115fe (fun s => s.RIP = 0x1115fe) (movR64R64Effect 0x1115fe 14 0) (Reg.operands [.gpr 0] [])) #v[1070]
    (.letOp (n := 1077) (.out 0x111601 (movR64M64Effect 0x111601 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1078) (.exec 0x111601 (LoadPre 0x111601 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x111601 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111601 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1079) (.out 0x111606 (mulR64Effect 0x111606 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[984, 1077]
    (.letOp (n := 1080) (.out 0x111606 (mulR64Effect 0x111606 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[984, 1077]
    (.letOp (n := 1081) (.exec 0x111606 (fun s => s.RIP = 0x111606) (mulR64Effect 0x111606 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[984, 1077]
    (.letOp (n := 1082) (.out 0x111609 (movR64R64Effect 0x111609 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[1079]
    (.letOp (n := 1083) (.exec 0x111609 (fun s => s.RIP = 0x111609) (movR64R64Effect 0x111609 9 0) (Reg.operands [.gpr 0] [])) #v[1079]
    (.letOp (n := 1084) (.out 0x11160c (movR64R64Effect 0x11160c 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[1080]
    (.letOp (n := 1085) (.exec 0x11160c (fun s => s.RIP = 0x11160c) (movR64R64Effect 0x11160c 11 2) (Reg.operands [.gpr 2] [])) #v[1080]
    (.letOp (n := 1086) (.out 0x11160f (movR64Imm64Effect 0x11160f 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1087) (.exec 0x11160f (fun s => s.RIP = 0x11160f) (movR64Imm64Effect 0x11160f 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l110d64_25)))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_24 : List UInt8 :=
  [0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD6, 0x48, 0x03, 0x44, 0x24, 0x58, 0x48, 0x13, 0xB4, 0x24, 0x98,
    0x00, 0x00, 0x00, 0x48, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0x89, 0xC1, 0x48, 0x89, 0xF8, 0x48, 0x8B,
    0x7C, 0x24, 0x20, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0x54, 0x24, 0x58, 0x48, 0x89, 0x84, 0x24, 0x90,
    0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x48, 0x89,
    0xD3, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x49, 0xF7, 0xE7, 0x49, 0x89, 0xC1, 0x49,
    0x89, 0xD3, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] ++ bytes_l110d64_25

theorem code_l110d64_24 : ∀ x ∈ codeRange 0x1115bd bytes_l110d64_24, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x115bd 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_25

def b_l110d64_23 : Block Op Label signature Reg.count 999 :=
  .letOp (n := 999) (.out 0x111563 (mulR64Effect 0x111563 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[997, 995]
    (.letOp (n := 1000) (.out 0x111563 (mulR64Effect 0x111563 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[997, 995]
    (.letOp (n := 1001) (.exec 0x111563 (fun s => s.RIP = 0x111563) (mulR64Effect 0x111563 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[997, 995]
    (.letOp (n := 1002) (.out 0x111566 (movR64R64Effect 0x111566 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[1000]
    (.letOp (n := 1003) (.exec 0x111566 (fun s => s.RIP = 0x111566) (movR64R64Effect 0x111566 5 2) (Reg.operands [.gpr 2] [])) #v[1000]
    (.letOp (n := 1004) (.out 0x111569 (movR64R64Effect 0x111569 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[999]
    (.letOp (n := 1005) (.exec 0x111569 (fun s => s.RIP = 0x111569) (movR64R64Effect 0x111569 9 0) (Reg.operands [.gpr 0] [])) #v[999]
    (.letOp (n := 1006) (.out 0x11156c (movR64M64Effect 0x11156c 7 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 1007) (.exec 0x11156c (LoadPre 0x11156c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11156c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11156c 7 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1008) (.out 0x111574 (movR64R64Effect 0x111574 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1006]
    (.letOp (n := 1009) (.exec 0x111574 (fun s => s.RIP = 0x111574) (movR64R64Effect 0x111574 0 7) (Reg.operands [.gpr 7] [])) #v[1006]
    (.letOp (n := 1010) (.out 0x111577 (mulM64Effect 0x111577 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1008, 4]
    (.letOp (n := 1011) (.out 0x111577 (mulM64Effect 0x111577 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[1008, 4]
    (.letOp (n := 1012) (.exec 0x111577 (LoadPre 0x111577 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x111577 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x111577 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1008, 4]
    (.letOp (n := 1013) (.out 0x11157c (addR64R64Effect 0x11157c 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[1010, 1004]
    (.letOp (n := 1014) (.out 0x11157c (addR64R64Effect 0x11157c 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[1010, 1004]
    (.letOp (n := 1015) (.exec 0x11157c (fun s => s.RIP = 0x11157c) (addR64R64Effect 0x11157c 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[1010, 1004]
    (.letOp (n := 1016) (.out 0x11157f (atFlags StatusFlags.CF (adcR64R64Effect 0x11157f 5 2)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[1002, 1011, 1014]
    (.letOp (n := 1017) (.exec 0x11157f (fun s => s.RIP = 0x11157f) (atFlags StatusFlags.CF (adcR64R64Effect 0x11157f 5 2)) (Reg.operands [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1002, 1011, 1014]
    (.letOp (n := 1018) (.out 0x111582 (addR64R64Effect 0x111582 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1013, 989]
    (.letOp (n := 1019) (.out 0x111582 (addR64R64Effect 0x111582 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[1013, 989]
    (.letOp (n := 1020) (.exec 0x111582 (fun s => s.RIP = 0x111582) (addR64R64Effect 0x111582 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1013, 989]
    (.letOp (n := 1021) (.out 0x111585 (atFlags StatusFlags.CF (adcR64R64Effect 0x111585 5 6)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[1016, 991, 1019]
    (.letOp (n := 1022) (.exec 0x111585 (fun s => s.RIP = 0x111585) (atFlags StatusFlags.CF (adcR64R64Effect 0x111585 5 6)) (Reg.operands [.gpr 5, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1016, 991, 1019]
    (.letOp (n := 1023) (.out 0x111588 (addR64R64Effect 0x111588 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[1018, 980]
    (.letOp (n := 1024) (.out 0x111588 (addR64R64Effect 0x111588 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[1018, 980]
    (.letOp (n := 1025) (.exec 0x111588 (fun s => s.RIP = 0x111588) (addR64R64Effect 0x111588 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[1018, 980]
    (.letOp (n := 1026) (.out 0x11158b (atFlags StatusFlags.CF (adcR64M64Effect 0x11158b 5 (.sib 4 none 0 (.d32 0x90)))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 5))) #v[1021, 4, 1024]
    (.letOp (n := 1027) (.exec 0x11158b (LoadPre 0x11158b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11158b + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11158b 5 (.sib 4 none 0 (.d32 0x90)))) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[1021, 4, 1024]
    (.letOp (n := 1028) (.out 0x111593 (addR64R64Effect 0x111593 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[1023, 959]
    (.letOp (n := 1029) (.out 0x111593 (addR64R64Effect 0x111593 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[1023, 959]
    (.letOp (n := 1030) (.exec 0x111593 (fun s => s.RIP = 0x111593) (addR64R64Effect 0x111593 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[1023, 959]
    (.letOp (n := 1031) (.out 0x111596 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111596 5 0x0)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[1026, 1029]
    (.letOp (n := 1032) (.exec 0x111596 (fun s => s.RIP = 0x111596) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111596 5 0x0)) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1026, 1029]
    (.letOp (n := 1033) (.out 0x11159a (shldR64R64Effect 0x11159a 5 5 0 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[1031, 1028]
    (.letOp (n := 1034) (.exec 0x11159a (fun s => s.RIP = 0x11159a) (shldR64R64Effect 0x11159a 5 5 0 12) (Reg.operands [.gpr 5, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1031, 1028]
    (.letOp (n := 1035) (.out 0x11159f (shlR64Effect 0x11159f 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1028]
    (.letOp (n := 1036) (.exec 0x11159f (fun s => s.RIP = 0x11159f) (shlR64Effect 0x11159f 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1028]
    (.letOp (n := 1037) (.out 0x1115a3 (movR64Imm64Effect 0x1115a3 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1038) (.exec 0x1115a3 (fun s => s.RIP = 0x1115a3) (movR64Imm64Effect 0x1115a3 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 1039) (.out 0x1115ad (andR64R64Effect 0x1115ad 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1035, 1037]
    (.letOp (n := 1040) (.exec 0x1115ad (fun s => s.RIP = 0x1115ad) (andR64R64Effect 0x1115ad 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1035, 1037]
    (.letOp (n := 1041) (.out 0x1115b0 (orR64R64Effect 0x1115b0 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[1039, 993]
    (.letOp (n := 1042) (.exec 0x1115b0 (fun s => s.RIP = 0x1115b0) (orR64R64Effect 0x1115b0 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[1039, 993]
    (.letOp (n := 1043) (.out 0x1115b3 (movR64Imm64Effect 0x1115b3 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 1044) (.exec 0x1115b3 (fun s => s.RIP = 0x1115b3) (movR64Imm64Effect 0x1115b3 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (b_l110d64_24))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_23 : List UInt8 :=
  [0x49, 0xF7, 0xE0, 0x48, 0x89, 0xD5, 0x49, 0x89, 0xC1, 0x48, 0x8B, 0xBC, 0x24, 0xE8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x40, 0x4C, 0x01, 0xC8, 0x48, 0x11, 0xD5, 0x48,
    0x01, 0xC8, 0x48, 0x11, 0xF5, 0x4C, 0x01, 0xF0, 0x48, 0x13, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x48, 0x01, 0xD8, 0x48, 0x83, 0xD5, 0x00, 0x48, 0x0F, 0xA4, 0xC5, 0x0C, 0x48, 0xC1, 0xE0, 0x04,
    0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C, 0x09, 0xD8,
    0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] ++ bytes_l110d64_24

theorem code_l110d64_23 : ∀ x ∈ codeRange 0x111563 bytes_l110d64_23, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11563 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_24

def b_l110d64_22 : Block Op Label signature Reg.count 959 :=
  .letOp (n := 959) (.out 0x111509 (shldR64R64Effect 0x111509 5 3 13 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[957, 954]
    (.letOp (n := 960) (.exec 0x111509 (fun s => s.RIP = 0x111509) (shldR64R64Effect 0x111509 5 3 13 12) (Reg.operands [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[957, 954]
    (.letOp (n := 961) (.out 0x11150e (movR64R64Effect 0x11150e 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 13] []) (.reg (.gpr 11))) #v[954]
    (.letOp (n := 962) (.exec 0x11150e (fun s => s.RIP = 0x11150e) (movR64R64Effect 0x11150e 11 13) (Reg.operands [.gpr 13] [])) #v[954]
    (.letOp (n := 963) (.out 0x111511 (shrR64Effect 0x111511 4 11 48) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[961]
    (.letOp (n := 964) (.exec 0x111511 (fun s => s.RIP = 0x111511) (shrR64Effect 0x111511 4 11 48) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[961]
    (.letOp (n := 965) (.out 0x111515 (movR64R64Effect 0x111515 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[911]
    (.letOp (n := 966) (.exec 0x111515 (fun s => s.RIP = 0x111515) (movR64R64Effect 0x111515 0 1) (Reg.operands [.gpr 1] [])) #v[911]
    (.letOp (n := 967) (.out 0x111518 (mulR64Effect 0x111518 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[878, 965]
    (.letOp (n := 968) (.out 0x111518 (mulR64Effect 0x111518 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[878, 965]
    (.letOp (n := 969) (.exec 0x111518 (fun s => s.RIP = 0x111518) (mulR64Effect 0x111518 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[878, 965]
    (.letOp (n := 970) (.exec 0x11151b (StorePre 0x11151b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11151b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11151b 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[968, 4]
    (.letOp (n := 971) (.exec 0x111523 (StorePre 0x111523 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x111523 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111523 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[967, 4]
    (.letOp (n := 972) (.out 0x111528 (movR64M64Effect 0x111528 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 973) (.exec 0x111528 (LoadPre 0x111528 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x111528 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111528 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 974) (.out 0x11152d (movR64M64Effect 0x11152d 10 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 975) (.exec 0x11152d (LoadPre 0x11152d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11152d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11152d 10 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 976) (.out 0x111532 (mulR64Effect 0x111532 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[974, 972]
    (.letOp (n := 977) (.out 0x111532 (mulR64Effect 0x111532 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[974, 972]
    (.letOp (n := 978) (.exec 0x111532 (fun s => s.RIP = 0x111532) (mulR64Effect 0x111532 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[974, 972]
    (.letOp (n := 979) (.exec 0x111535 (StorePre 0x111535 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x111535 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111535 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[977, 4]
    (.letOp (n := 980) (.out 0x11153d (movR64R64Effect 0x11153d 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[976]
    (.letOp (n := 981) (.exec 0x11153d (fun s => s.RIP = 0x11153d) (movR64R64Effect 0x11153d 14 0) (Reg.operands [.gpr 0] [])) #v[976]
    (.letOp (n := 982) (.out 0x111540 (movR64M64Effect 0x111540 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 983) (.exec 0x111540 (LoadPre 0x111540 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111540 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111540 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 984) (.out 0x111544 (movR64M64Effect 0x111544 15 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 985) (.exec 0x111544 (LoadPre 0x111544 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x111544 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111544 15 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 986) (.out 0x111549 (mulR64Effect 0x111549 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[984, 982]
    (.letOp (n := 987) (.out 0x111549 (mulR64Effect 0x111549 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[984, 982]
    (.letOp (n := 988) (.exec 0x111549 (fun s => s.RIP = 0x111549) (mulR64Effect 0x111549 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[984, 982]
    (.letOp (n := 989) (.out 0x11154c (movR64R64Effect 0x11154c 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[986]
    (.letOp (n := 990) (.exec 0x11154c (fun s => s.RIP = 0x11154c) (movR64R64Effect 0x11154c 1 0) (Reg.operands [.gpr 0] [])) #v[986]
    (.letOp (n := 991) (.out 0x11154f (movR64R64Effect 0x11154f 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[987]
    (.letOp (n := 992) (.exec 0x11154f (fun s => s.RIP = 0x11154f) (movR64R64Effect 0x11154f 6 2) (Reg.operands [.gpr 2] [])) #v[987]
    (.letOp (n := 993) (.out 0x111552 (andR32Imm8Effect 0x111552 4 11 0xf) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[963]
    (.letOp (n := 994) (.exec 0x111552 (fun s => s.RIP = 0x111552) (andR32Imm8Effect 0x111552 4 11 0xf) (Reg.operands [.gpr 11] [])) #v[963]
    (.letOp (n := 995) (.out 0x111556 (movR64M64Effect 0x111556 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 996) (.exec 0x111556 (LoadPre 0x111556 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x111556 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111556 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 997) (.out 0x11155e (movR64M64Effect 0x11155e 8 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 998) (.exec 0x11155e (LoadPre 0x11155e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11155e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11155e 8 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l110d64_23))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_22 : List UInt8 :=
  [0x4C, 0x0F, 0xA4, 0xEB, 0x0C, 0x4D, 0x89, 0xEB, 0x49, 0xC1, 0xEB, 0x30, 0x48, 0x89, 0xC8, 0x49,
    0xF7, 0xE1, 0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x58, 0x48,
    0x8B, 0x44, 0x24, 0x30, 0x4C, 0x8B, 0x54, 0x24, 0x28, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0x94, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x04, 0x24, 0x4C, 0x8B, 0x7C, 0x24, 0x48,
    0x49, 0xF7, 0xE7, 0x48, 0x89, 0xC1, 0x48, 0x89, 0xD6, 0x41, 0x83, 0xE3, 0x0F, 0x48, 0x8B, 0x84,
    0x24, 0xD0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x44, 0x24, 0x60] ++ bytes_l110d64_23

theorem code_l110d64_22 : ∀ x ∈ codeRange 0x111509 bytes_l110d64_22, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11509 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_23

def b_l110d64_21 : Block Op Label signature Reg.count 911 :=
  .letOp (n := 911) (.out 0x1114b4 (movR64M64Effect 0x1114b4 1 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 912) (.exec 0x1114b4 (LoadPre 0x1114b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1114b4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1114b4 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 913) (.out 0x1114bc (movR64R64Effect 0x1114bc 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[911]
    (.letOp (n := 914) (.exec 0x1114bc (fun s => s.RIP = 0x1114bc) (movR64R64Effect 0x1114bc 0 1) (Reg.operands [.gpr 1] [])) #v[911]
    (.letOp (n := 915) (.out 0x1114bf (mulR64Effect 0x1114bf 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[850, 913]
    (.letOp (n := 916) (.out 0x1114bf (mulR64Effect 0x1114bf 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[850, 913]
    (.letOp (n := 917) (.exec 0x1114bf (fun s => s.RIP = 0x1114bf) (mulR64Effect 0x1114bf 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[850, 913]
    (.letOp (n := 918) (.out 0x1114c2 (movR64R64Effect 0x1114c2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[916]
    (.letOp (n := 919) (.exec 0x1114c2 (fun s => s.RIP = 0x1114c2) (movR64R64Effect 0x1114c2 3 2) (Reg.operands [.gpr 2] [])) #v[916]
    (.letOp (n := 920) (.out 0x1114c5 (movR64R64Effect 0x1114c5 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[915]
    (.letOp (n := 921) (.exec 0x1114c5 (fun s => s.RIP = 0x1114c5) (movR64R64Effect 0x1114c5 13 0) (Reg.operands [.gpr 0] [])) #v[915]
    (.letOp (n := 922) (.out 0x1114c8 (movR64R64Effect 0x1114c8 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[872]
    (.letOp (n := 923) (.exec 0x1114c8 (fun s => s.RIP = 0x1114c8) (movR64R64Effect 0x1114c8 0 8) (Reg.operands [.gpr 8] [])) #v[872]
    (.letOp (n := 924) (.out 0x1114cb (movR64Imm64Effect 0x1114cb 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 925) (.exec 0x1114cb (fun s => s.RIP = 0x1114cb) (movR64Imm64Effect 0x1114cb 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 926) (.out 0x1114d5 (mulR64Effect 0x1114d5 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[924, 922]
    (.letOp (n := 927) (.out 0x1114d5 (mulR64Effect 0x1114d5 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[924, 922]
    (.letOp (n := 928) (.exec 0x1114d5 (fun s => s.RIP = 0x1114d5) (mulR64Effect 0x1114d5 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[924, 922]
    (.letOp (n := 929) (.out 0x1114d8 (addR64R64Effect 0x1114d8 13 11) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 11] []) (.reg (.gpr 13))) #v[920, 909]
    (.letOp (n := 930) (.out 0x1114d8 (addR64R64Effect 0x1114d8 13 11) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 11] []) (.flag .CF)) #v[920, 909]
    (.letOp (n := 931) (.exec 0x1114d8 (fun s => s.RIP = 0x1114d8) (addR64R64Effect 0x1114d8 13 11) (Reg.operands [.gpr 13, .gpr 11] [])) #v[920, 909]
    (.letOp (n := 932) (.out 0x1114db (atFlags StatusFlags.CF (adcR64R64Effect 0x1114db 3 7)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[918, 907, 930]
    (.letOp (n := 933) (.exec 0x1114db (fun s => s.RIP = 0x1114db) (atFlags StatusFlags.CF (adcR64R64Effect 0x1114db 3 7)) (Reg.operands [.gpr 3, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[918, 907, 930]
    (.letOp (n := 934) (.out 0x1114de (addR64R64Effect 0x1114de 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[929, 900]
    (.letOp (n := 935) (.out 0x1114de (addR64R64Effect 0x1114de 13 5) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 5] []) (.flag .CF)) #v[929, 900]
    (.letOp (n := 936) (.exec 0x1114de (fun s => s.RIP = 0x1114de) (addR64R64Effect 0x1114de 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[929, 900]
    (.letOp (n := 937) (.out 0x1114e1 (atFlags StatusFlags.CF (adcR64R64Effect 0x1114e1 3 14)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[932, 898, 935]
    (.letOp (n := 938) (.exec 0x1114e1 (fun s => s.RIP = 0x1114e1) (atFlags StatusFlags.CF (adcR64R64Effect 0x1114e1 3 14)) (Reg.operands [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[932, 898, 935]
    (.letOp (n := 939) (.out 0x1114e4 (addR64R64Effect 0x1114e4 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[934, 891]
    (.letOp (n := 940) (.out 0x1114e4 (addR64R64Effect 0x1114e4 13 15) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 15] []) (.flag .CF)) #v[934, 891]
    (.letOp (n := 941) (.exec 0x1114e4 (fun s => s.RIP = 0x1114e4) (addR64R64Effect 0x1114e4 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[934, 891]
    (.letOp (n := 942) (.out 0x1114e7 (atFlags StatusFlags.CF (adcR64M64Effect 0x1114e7 3 (.sib 4 none 0 (.d32 0x90)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[937, 4, 940]
    (.letOp (n := 943) (.exec 0x1114e7 (LoadPre 0x1114e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1114e7 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1114e7 3 (.sib 4 none 0 (.d32 0x90)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[937, 4, 940]
    (.letOp (n := 944) (.out 0x1114ef (addR64M64Effect 0x1114ef 13 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[939, 4]
    (.letOp (n := 945) (.out 0x1114ef (addR64M64Effect 0x1114ef 13 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[939, 4]
    (.letOp (n := 946) (.exec 0x1114ef (LoadPre 0x1114ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1114ef + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1114ef 13 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[939, 4]
    (.letOp (n := 947) (.out 0x1114f4 (atFlags StatusFlags.CF (adcR64M64Effect 0x1114f4 3 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[942, 4, 945]
    (.letOp (n := 948) (.exec 0x1114f4 (LoadPre 0x1114f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1114f4 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1114f4 3 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[942, 4, 945]
    (.letOp (n := 949) (.out 0x1114fc (addR64R64Effect 0x1114fc 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[944, 926]
    (.letOp (n := 950) (.out 0x1114fc (addR64R64Effect 0x1114fc 13 0) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 0] []) (.flag .CF)) #v[944, 926]
    (.letOp (n := 951) (.exec 0x1114fc (fun s => s.RIP = 0x1114fc) (addR64R64Effect 0x1114fc 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[944, 926]
    (.letOp (n := 952) (.out 0x1114ff (atFlags StatusFlags.CF (adcR64R64Effect 0x1114ff 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[947, 927, 950]
    (.letOp (n := 953) (.exec 0x1114ff (fun s => s.RIP = 0x1114ff) (atFlags StatusFlags.CF (adcR64R64Effect 0x1114ff 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[947, 927, 950]
    (.letOp (n := 954) (.out 0x111502 (addR64R64Effect 0x111502 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 6] []) (.reg (.gpr 13))) #v[949, 874]
    (.letOp (n := 955) (.out 0x111502 (addR64R64Effect 0x111502 13 6) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 6] []) (.flag .CF)) #v[949, 874]
    (.letOp (n := 956) (.exec 0x111502 (fun s => s.RIP = 0x111502) (addR64R64Effect 0x111502 13 6) (Reg.operands [.gpr 13, .gpr 6] [])) #v[949, 874]
    (.letOp (n := 957) (.out 0x111505 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111505 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[952, 955]
    (.letOp (n := 958) (.exec 0x111505 (fun s => s.RIP = 0x111505) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111505 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[952, 955]
    (b_l110d64_22))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_21 : List UInt8 :=
  [0x48, 0x8B, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE5, 0x48, 0x89,
    0xD3, 0x49, 0x89, 0xC5, 0x4C, 0x89, 0xC0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00,
    0x00, 0x48, 0xF7, 0xE2, 0x4D, 0x01, 0xDD, 0x48, 0x11, 0xFB, 0x49, 0x01, 0xED, 0x4C, 0x11, 0xF3,
    0x4D, 0x01, 0xFD, 0x48, 0x13, 0x9C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x03, 0x6C, 0x24, 0x58,
    0x48, 0x13, 0x9C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC5, 0x48, 0x11, 0xD3, 0x49, 0x01,
    0xF5, 0x48, 0x83, 0xD3, 0x00] ++ bytes_l110d64_22

theorem code_l110d64_21 : ∀ x ∈ codeRange 0x1114b4 bytes_l110d64_21, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x114b4 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_22

def b_l110d64_20 : Block Op Label signature Reg.count 870 :=
  .letOp (n := 870) (.out 0x111462 (atFlags StatusFlags.CF (adcR64R64Effect 0x111462 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[865, 847, 868]
    (.letOp (n := 871) (.exec 0x111462 (fun s => s.RIP = 0x111462) (atFlags StatusFlags.CF (adcR64R64Effect 0x111462 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[865, 847, 868]
    (.letOp (n := 872) (.out 0x111465 (shldR64R64Effect 0x111465 5 8 3 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[833, 831]
    (.letOp (n := 873) (.exec 0x111465 (fun s => s.RIP = 0x111465) (shldR64R64Effect 0x111465 5 8 3 12) (Reg.operands [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[833, 831]
    (.letOp (n := 874) (.out 0x11146a (shldR64R64Effect 0x11146a 5 6 12 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[870, 867]
    (.letOp (n := 875) (.exec 0x11146a (fun s => s.RIP = 0x11146a) (shldR64R64Effect 0x11146a 5 6 12 12) (Reg.operands [.gpr 6, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[870, 867]
    (.letOp (n := 876) (.out 0x11146f (movR64R64Effect 0x11146f 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[822]
    (.letOp (n := 877) (.exec 0x11146f (fun s => s.RIP = 0x11146f) (movR64R64Effect 0x11146f 0 9) (Reg.operands [.gpr 9] [])) #v[822]
    (.letOp (n := 878) (.out 0x111472 (movR64M64Effect 0x111472 9 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 879) (.exec 0x111472 (LoadPre 0x111472 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x111472 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111472 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 880) (.out 0x111477 (mulR64Effect 0x111477 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[878, 876]
    (.letOp (n := 881) (.out 0x111477 (mulR64Effect 0x111477 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[878, 876]
    (.letOp (n := 882) (.exec 0x111477 (fun s => s.RIP = 0x111477) (mulR64Effect 0x111477 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[878, 876]
    (.letOp (n := 883) (.exec 0x11147a (StorePre 0x11147a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11147a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11147a 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[881, 4]
    (.letOp (n := 884) (.exec 0x111482 (StorePre 0x111482 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x111482 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111482 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[880, 4]
    (.letOp (n := 885) (.out 0x111487 (movR64R64Effect 0x111487 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[780]
    (.letOp (n := 886) (.exec 0x111487 (fun s => s.RIP = 0x111487) (movR64R64Effect 0x111487 0 15) (Reg.operands [.gpr 15] [])) #v[780]
    (.letOp (n := 887) (.out 0x11148a (mulM64Effect 0x11148a 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[885, 4]
    (.letOp (n := 888) (.out 0x11148a (mulM64Effect 0x11148a 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[885, 4]
    (.letOp (n := 889) (.exec 0x11148a (LoadPre 0x11148a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11148a + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11148a 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[885, 4]
    (.letOp (n := 890) (.exec 0x11148f (StorePre 0x11148f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11148f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11148f 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[888, 4]
    (.letOp (n := 891) (.out 0x111497 (movR64R64Effect 0x111497 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[887]
    (.letOp (n := 892) (.exec 0x111497 (fun s => s.RIP = 0x111497) (movR64R64Effect 0x111497 15 0) (Reg.operands [.gpr 0] [])) #v[887]
    (.letOp (n := 893) (.out 0x11149a (movR64R64Effect 0x11149a 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[789]
    (.letOp (n := 894) (.exec 0x11149a (fun s => s.RIP = 0x11149a) (movR64R64Effect 0x11149a 0 11) (Reg.operands [.gpr 11] [])) #v[789]
    (.letOp (n := 895) (.out 0x11149d (mulM64Effect 0x11149d 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[893, 4]
    (.letOp (n := 896) (.out 0x11149d (mulM64Effect 0x11149d 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[893, 4]
    (.letOp (n := 897) (.exec 0x11149d (LoadPre 0x11149d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11149d + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11149d 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[893, 4]
    (.letOp (n := 898) (.out 0x1114a2 (movR64R64Effect 0x1114a2 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[896]
    (.letOp (n := 899) (.exec 0x1114a2 (fun s => s.RIP = 0x1114a2) (movR64R64Effect 0x1114a2 14 2) (Reg.operands [.gpr 2] [])) #v[896]
    (.letOp (n := 900) (.out 0x1114a5 (movR64R64Effect 0x1114a5 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[895]
    (.letOp (n := 901) (.exec 0x1114a5 (fun s => s.RIP = 0x1114a5) (movR64R64Effect 0x1114a5 5 0) (Reg.operands [.gpr 0] [])) #v[895]
    (.letOp (n := 902) (.out 0x1114a8 (movR64R64Effect 0x1114a8 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[801]
    (.letOp (n := 903) (.exec 0x1114a8 (fun s => s.RIP = 0x1114a8) (movR64R64Effect 0x1114a8 0 10) (Reg.operands [.gpr 10] [])) #v[801]
    (.letOp (n := 904) (.out 0x1114ab (mulR64Effect 0x1114ab 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[838, 902]
    (.letOp (n := 905) (.out 0x1114ab (mulR64Effect 0x1114ab 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[838, 902]
    (.letOp (n := 906) (.exec 0x1114ab (fun s => s.RIP = 0x1114ab) (mulR64Effect 0x1114ab 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[838, 902]
    (.letOp (n := 907) (.out 0x1114ae (movR64R64Effect 0x1114ae 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[905]
    (.letOp (n := 908) (.exec 0x1114ae (fun s => s.RIP = 0x1114ae) (movR64R64Effect 0x1114ae 7 2) (Reg.operands [.gpr 2] [])) #v[905]
    (.letOp (n := 909) (.out 0x1114b1 (movR64R64Effect 0x1114b1 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[904]
    (.letOp (n := 910) (.exec 0x1114b1 (fun s => s.RIP = 0x1114b1) (movR64R64Effect 0x1114b1 11 0) (Reg.operands [.gpr 0] [])) #v[904]
    (b_l110d64_21)))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_20 : List UInt8 :=
  [0x48, 0x11, 0xD6, 0x49, 0x0F, 0xA4, 0xD8, 0x0C, 0x4C, 0x0F, 0xA4, 0xE6, 0x0C, 0x4C, 0x89, 0xC8,
    0x4C, 0x8B, 0x4C, 0x24, 0x20, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x44, 0x24, 0x58, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x28, 0x48, 0x89, 0x94,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC7, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0x64, 0x24, 0x48,
    0x49, 0x89, 0xD6, 0x48, 0x89, 0xC5, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD7, 0x49,
    0x89, 0xC3] ++ bytes_l110d64_21

theorem code_l110d64_20 : ∀ x ∈ codeRange 0x111462 bytes_l110d64_20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11462 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_21

def b_l110d64_19 : Block Op Label signature Reg.count 826 :=
  .letOp (n := 826) (.out 0x1113f8 (movR64R64Effect 0x1113f8 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 7] []) (.reg (.gpr 5))) #v[760]
    (.letOp (n := 827) (.exec 0x1113f8 (fun s => s.RIP = 0x1113f8) (movR64R64Effect 0x1113f8 5 7) (Reg.operands [.gpr 7] [])) #v[760]
    (.letOp (n := 828) (.out 0x1113fb (mulR64Effect 0x1113fb 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[760, 824]
    (.letOp (n := 829) (.out 0x1113fb (mulR64Effect 0x1113fb 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[760, 824]
    (.letOp (n := 830) (.exec 0x1113fb (fun s => s.RIP = 0x1113fb) (mulR64Effect 0x1113fb 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[760, 824]
    (.letOp (n := 831) (.out 0x1113fe (movR64R64Effect 0x1113fe 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[828]
    (.letOp (n := 832) (.exec 0x1113fe (fun s => s.RIP = 0x1113fe) (movR64R64Effect 0x1113fe 3 0) (Reg.operands [.gpr 0] [])) #v[828]
    (.letOp (n := 833) (.out 0x111401 (movR64R64Effect 0x111401 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[829]
    (.letOp (n := 834) (.exec 0x111401 (fun s => s.RIP = 0x111401) (movR64R64Effect 0x111401 8 2) (Reg.operands [.gpr 2] [])) #v[829]
    (.letOp (n := 835) (.out 0x111404 (addR64R64Effect 0x111404 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[698, 813]
    (.letOp (n := 836) (.exec 0x111404 (fun s => s.RIP = 0x111404) (addR64R64Effect 0x111404 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[698, 813]
    (.letOp (n := 837) (.exec 0x111407 (StorePre 0x111407 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x111407 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111407 13 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[835, 4]
    (.letOp (n := 838) (.out 0x11140f (movR64R64Effect 0x11140f 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[813]
    (.letOp (n := 839) (.exec 0x11140f (fun s => s.RIP = 0x11140f) (movR64R64Effect 0x11140f 7 1) (Reg.operands [.gpr 1] [])) #v[813]
    (.letOp (n := 840) (.out 0x111412 (movR64Imm64Effect 0x111412 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 841) (.exec 0x111412 (fun s => s.RIP = 0x111412) (movR64Imm64Effect 0x111412 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 842) (.out 0x11141c (andR64R64Effect 0x11141c 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[828, 840]
    (.letOp (n := 843) (.exec 0x11141c (fun s => s.RIP = 0x11141c) (andR64R64Effect 0x11141c 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[828, 840]
    (.letOp (n := 844) (.out 0x11141f (movR64Imm64Effect 0x11141f 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 845) (.exec 0x11141f (fun s => s.RIP = 0x11141f) (movR64Imm64Effect 0x11141f 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 846) (.out 0x111429 (mulR64Effect 0x111429 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[844, 842]
    (.letOp (n := 847) (.out 0x111429 (mulR64Effect 0x111429 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[844, 842]
    (.letOp (n := 848) (.exec 0x111429 (fun s => s.RIP = 0x111429) (mulR64Effect 0x111429 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[844, 842]
    (.letOp (n := 849) (.exec 0x11142c (StorePre 0x11142c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11142c + BitVec.ofNat 64 8)) 8) (addMREffect 0x11142c 8 64 5 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[826, 4]
    (.letOp (n := 850) (.out 0x111434 (movR64R64Effect 0x111434 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 5] []) (.reg (.gpr 13))) #v[826]
    (.letOp (n := 851) (.exec 0x111434 (fun s => s.RIP = 0x111434) (movR64R64Effect 0x111434 13 5) (Reg.operands [.gpr 5] [])) #v[826]
    (.letOp (n := 852) (.out 0x111437 (addR64R64Effect 0x111437 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 14] []) (.reg (.gpr 12))) #v[820, 809]
    (.letOp (n := 853) (.out 0x111437 (addR64R64Effect 0x111437 12 14) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 14] []) (.flag .CF)) #v[820, 809]
    (.letOp (n := 854) (.exec 0x111437 (fun s => s.RIP = 0x111437) (addR64R64Effect 0x111437 12 14) (Reg.operands [.gpr 12, .gpr 14] [])) #v[820, 809]
    (.letOp (n := 855) (.out 0x11143a (atFlags StatusFlags.CF (adcR64M64Effect 0x11143a 6 (.sib 4 none 0 (.d32 0xc8)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[818, 4, 853]
    (.letOp (n := 856) (.exec 0x11143a (LoadPre 0x11143a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11143a + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11143a 6 (.sib 4 none 0 (.d32 0xc8)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[818, 4, 853]
    (.letOp (n := 857) (.out 0x111442 (addR64M64Effect 0x111442 12 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[852, 4]
    (.letOp (n := 858) (.out 0x111442 (addR64M64Effect 0x111442 12 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 4] []) (.flag .CF)) #v[852, 4]
    (.letOp (n := 859) (.exec 0x111442 (LoadPre 0x111442 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x111442 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x111442 12 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[852, 4]
    (.letOp (n := 860) (.out 0x11144a (atFlags StatusFlags.CF (adcR64M64Effect 0x11144a 6 (.sib 4 none 0 (.d32 0x90)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[855, 4, 858]
    (.letOp (n := 861) (.exec 0x11144a (LoadPre 0x11144a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x11144a + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11144a 6 (.sib 4 none 0 (.d32 0x90)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[855, 4, 858]
    (.letOp (n := 862) (.out 0x111452 (addR64M64Effect 0x111452 12 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[857, 4]
    (.letOp (n := 863) (.out 0x111452 (addR64M64Effect 0x111452 12 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 4] []) (.flag .CF)) #v[857, 4]
    (.letOp (n := 864) (.exec 0x111452 (LoadPre 0x111452 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x111452 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x111452 12 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[857, 4]
    (.letOp (n := 865) (.out 0x111457 (atFlags StatusFlags.CF (adcR64M64Effect 0x111457 6 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[860, 4, 863]
    (.letOp (n := 866) (.exec 0x111457 (LoadPre 0x111457 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x111457 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111457 6 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[860, 4, 863]
    (.letOp (n := 867) (.out 0x11145f (addR64R64Effect 0x11145f 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[862, 846]
    (.letOp (n := 868) (.out 0x11145f (addR64R64Effect 0x11145f 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[862, 846]
    (.letOp (n := 869) (.exec 0x11145f (fun s => s.RIP = 0x11145f) (addR64R64Effect 0x11145f 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[862, 846]
    (b_l110d64_20))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_19 : List UInt8 :=
  [0x48, 0x89, 0xFD, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xC3, 0x49, 0x89, 0xD0, 0x49, 0x01, 0xCD, 0x4C,
    0x89, 0xAC, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xCF, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00,
    0x00, 0x48, 0xF7, 0xE1, 0x48, 0x01, 0xAC, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xED, 0x4D,
    0x01, 0xF4, 0x48, 0x13, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x4C, 0x03, 0xA4, 0x24, 0x08, 0x01,
    0x00, 0x00, 0x48, 0x13, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x03, 0x64, 0x24, 0x58, 0x48,
    0x13, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC4] ++ bytes_l110d64_20

theorem code_l110d64_19 : ∀ x ∈ codeRange 0x1113f8 bytes_l110d64_19, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x113f8 106 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_20

def b_l110d64_18 : Block Op Label signature Reg.count 788 :=
  .letOp (n := 788) (.exec 0x111395 (StorePre 0x111395 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x111395 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111395 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[784, 4]
    (.letOp (n := 789) (.out 0x11139a (movR64M64Effect 0x11139a 11 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 790) (.exec 0x11139a (LoadPre 0x11139a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11139a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11139a 11 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 791) (.out 0x1113a2 (movR64R64Effect 0x1113a2 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[789]
    (.letOp (n := 792) (.exec 0x1113a2 (fun s => s.RIP = 0x1113a2) (movR64R64Effect 0x1113a2 0 11) (Reg.operands [.gpr 11] [])) #v[789]
    (.letOp (n := 793) (.out 0x1113a5 (mulR64Effect 0x1113a5 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[735, 791]
    (.letOp (n := 794) (.out 0x1113a5 (mulR64Effect 0x1113a5 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[735, 791]
    (.letOp (n := 795) (.exec 0x1113a5 (fun s => s.RIP = 0x1113a5) (mulR64Effect 0x1113a5 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[735, 791]
    (.letOp (n := 796) (.exec 0x1113a8 (StorePre 0x1113a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1113a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1113a8 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[793, 4]
    (.letOp (n := 797) (.exec 0x1113b0 (StorePre 0x1113b0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1113b0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1113b0 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[794, 4]
    (.letOp (n := 798) (.out 0x1113b8 (addR64R64Effect 0x1113b8 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[694, 744]
    (.letOp (n := 799) (.exec 0x1113b8 (fun s => s.RIP = 0x1113b8) (addR64R64Effect 0x1113b8 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[694, 744]
    (.letOp (n := 800) (.exec 0x1113bb (StorePre 0x1113bb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1113bb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1113bb 14 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[798, 4]
    (.letOp (n := 801) (.out 0x1113c3 (movR64M64Effect 0x1113c3 10 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 802) (.exec 0x1113c3 (LoadPre 0x1113c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1113c3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1113c3 10 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 803) (.out 0x1113cb (movR64R64Effect 0x1113cb 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[801]
    (.letOp (n := 804) (.exec 0x1113cb (fun s => s.RIP = 0x1113cb) (movR64R64Effect 0x1113cb 0 10) (Reg.operands [.gpr 10] [])) #v[801]
    (.letOp (n := 805) (.out 0x1113ce (mulR64Effect 0x1113ce 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[744, 803]
    (.letOp (n := 806) (.out 0x1113ce (mulR64Effect 0x1113ce 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[744, 803]
    (.letOp (n := 807) (.exec 0x1113ce (fun s => s.RIP = 0x1113ce) (mulR64Effect 0x1113ce 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[744, 803]
    (.letOp (n := 808) (.exec 0x1113d1 (StorePre 0x1113d1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1113d1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1113d1 2 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[806, 4]
    (.letOp (n := 809) (.out 0x1113d9 (movR64R64Effect 0x1113d9 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[805]
    (.letOp (n := 810) (.exec 0x1113d9 (fun s => s.RIP = 0x1113d9) (movR64R64Effect 0x1113d9 14 0) (Reg.operands [.gpr 0] [])) #v[805]
    (.letOp (n := 811) (.out 0x1113dc (movR64M64Effect 0x1113dc 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 812) (.exec 0x1113dc (LoadPre 0x1113dc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1113dc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1113dc 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 813) (.out 0x1113e4 (movR64R64Effect 0x1113e4 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[753]
    (.letOp (n := 814) (.exec 0x1113e4 (fun s => s.RIP = 0x1113e4) (movR64R64Effect 0x1113e4 1 12) (Reg.operands [.gpr 12] [])) #v[753]
    (.letOp (n := 815) (.out 0x1113e7 (mulR64Effect 0x1113e7 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[753, 811]
    (.letOp (n := 816) (.out 0x1113e7 (mulR64Effect 0x1113e7 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[753, 811]
    (.letOp (n := 817) (.exec 0x1113e7 (fun s => s.RIP = 0x1113e7) (mulR64Effect 0x1113e7 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[753, 811]
    (.letOp (n := 818) (.out 0x1113ea (movR64R64Effect 0x1113ea 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[816]
    (.letOp (n := 819) (.exec 0x1113ea (fun s => s.RIP = 0x1113ea) (movR64R64Effect 0x1113ea 6 2) (Reg.operands [.gpr 2] [])) #v[816]
    (.letOp (n := 820) (.out 0x1113ed (movR64R64Effect 0x1113ed 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[815]
    (.letOp (n := 821) (.exec 0x1113ed (fun s => s.RIP = 0x1113ed) (movR64R64Effect 0x1113ed 12 0) (Reg.operands [.gpr 0] [])) #v[815]
    (.letOp (n := 822) (.out 0x1113f0 (movR64M64Effect 0x1113f0 9 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 823) (.exec 0x1113f0 (LoadPre 0x1113f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1113f0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1113f0 9 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 824) (.out 0x1113f5 (movR64R64Effect 0x1113f5 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[822]
    (.letOp (n := 825) (.exec 0x1113f5 (fun s => s.RIP = 0x1113f5) (movR64R64Effect 0x1113f5 0 9) (Reg.operands [.gpr 9] [])) #v[822]
    (b_l110d64_19))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_18 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x58, 0x4C, 0x8B, 0x9C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xD8,
    0x48, 0xF7, 0xE5, 0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0x90,
    0x00, 0x00, 0x00, 0x4D, 0x01, 0xCE, 0x4C, 0x89, 0xB4, 0x24, 0x10, 0x01, 0x00, 0x00, 0x4C, 0x8B,
    0x94, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xD0, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x94, 0x24,
    0xC8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C,
    0x89, 0xE1, 0x49, 0xF7, 0xE4, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x4C, 0x8B, 0x4C, 0x24, 0x30,
    0x4C, 0x89, 0xC8] ++ bytes_l110d64_19

theorem code_l110d64_18 : ∀ x ∈ codeRange 0x111395 bytes_l110d64_18, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11395 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_19

def b_l110d64_17 : Block Op Label signature Reg.count 753 :=
  .letOp (n := 753) (.out 0x111338 (movR64M64Effect 0x111338 12 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 754) (.exec 0x111338 (LoadPre 0x111338 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x111338 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111338 12 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 755) (.out 0x11133d (addR64R64Effect 0x11133d 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[733, 753]
    (.letOp (n := 756) (.exec 0x11133d (fun s => s.RIP = 0x11133d) (addR64R64Effect 0x11133d 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[733, 753]
    (.letOp (n := 757) (.out 0x111340 (subR64R64Effect 0x111340 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[755, 751]
    (.letOp (n := 758) (.exec 0x111340 (fun s => s.RIP = 0x111340) (subR64R64Effect 0x111340 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[755, 751]
    (.letOp (n := 759) (.exec 0x111343 (StorePre 0x111343 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x111343 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111343 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[757, 4]
    (.letOp (n := 760) (.out 0x111348 (movR64M64Effect 0x111348 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 761) (.exec 0x111348 (LoadPre 0x111348 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x111348 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111348 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 762) (.out 0x11134d (movR64R64Effect 0x11134d 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[760]
    (.letOp (n := 763) (.exec 0x11134d (fun s => s.RIP = 0x11134d) (movR64R64Effect 0x11134d 0 7) (Reg.operands [.gpr 7] [])) #v[760]
    (.letOp (n := 764) (.out 0x111350 (subR64R64Effect 0x111350 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[762, 716]
    (.letOp (n := 765) (.exec 0x111350 (fun s => s.RIP = 0x111350) (subR64R64Effect 0x111350 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[762, 716]
    (.letOp (n := 766) (.out 0x111353 (movR64Imm64Effect 0x111353 1 0x3fffffffffffc) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 767) (.exec 0x111353 (fun s => s.RIP = 0x111353) (movR64Imm64Effect 0x111353 1 0x3fffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 768) (.out 0x11135d (addR64R64Effect 0x11135d 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[766, 764]
    (.letOp (n := 769) (.exec 0x11135d (fun s => s.RIP = 0x11135d) (addR64R64Effect 0x11135d 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[766, 764]
    (.letOp (n := 770) (.exec 0x111360 (StorePre 0x111360 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111360 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111360 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[768, 4]
    (.letOp (n := 771) (.out 0x111365 (addR64R64Effect 0x111365 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[558, 558]
    (.letOp (n := 772) (.exec 0x111365 (fun s => s.RIP = 0x111365) (addR64R64Effect 0x111365 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[558, 558]
    (.letOp (n := 773) (.exec 0x111368 (StorePre 0x111368 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111368 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111368 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[771, 4]
    (.letOp (n := 774) (.out 0x11136d (addR64R64Effect 0x11136d 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[670, 720]
    (.letOp (n := 775) (.exec 0x11136d (fun s => s.RIP = 0x11136d) (addR64R64Effect 0x11136d 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[670, 720]
    (.letOp (n := 776) (.exec 0x111370 (StorePre 0x111370 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x111370 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111370 10 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[774, 4]
    (.letOp (n := 777) (.out 0x111378 (addR64R64Effect 0x111378 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[682, 735]
    (.letOp (n := 778) (.exec 0x111378 (fun s => s.RIP = 0x111378) (addR64R64Effect 0x111378 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[682, 735]
    (.letOp (n := 779) (.exec 0x11137b (StorePre 0x11137b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x11137b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11137b 3 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[777, 4]
    (.letOp (n := 780) (.out 0x111383 (movR64M64Effect 0x111383 15 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 781) (.exec 0x111383 (LoadPre 0x111383 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111383 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111383 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 782) (.out 0x111387 (movR64R64Effect 0x111387 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[780]
    (.letOp (n := 783) (.exec 0x111387 (fun s => s.RIP = 0x111387) (movR64R64Effect 0x111387 0 15) (Reg.operands [.gpr 15] [])) #v[780]
    (.letOp (n := 784) (.out 0x11138a (mulR64Effect 0x11138a 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[720, 782]
    (.letOp (n := 785) (.out 0x11138a (mulR64Effect 0x11138a 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[720, 782]
    (.letOp (n := 786) (.exec 0x11138a (fun s => s.RIP = 0x11138a) (mulR64Effect 0x11138a 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[720, 782]
    (.letOp (n := 787) (.exec 0x11138d (StorePre 0x11138d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11138d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11138d 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[785, 4]
    (b_l110d64_18)))))))))))))))))))))))))))))))))))

def bytes_l110d64_17 : List UInt8 :=
  [0x4C, 0x8B, 0x64, 0x24, 0x60, 0x4C, 0x01, 0xE0, 0x48, 0x29, 0xF8, 0x48, 0x89, 0x44, 0x24, 0x38,
    0x48, 0x8B, 0x7C, 0x24, 0x40, 0x48, 0x89, 0xF8, 0x4C, 0x29, 0xC0, 0x48, 0xB9, 0xFC, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x03, 0x00, 0x48, 0x01, 0xC1, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x4D, 0x01, 0xFF,
    0x4C, 0x89, 0x7C, 0x24, 0x18, 0x4D, 0x01, 0xDA, 0x4C, 0x89, 0x94, 0x24, 0x20, 0x01, 0x00, 0x00,
    0x48, 0x01, 0xEB, 0x48, 0x89, 0x9C, 0x24, 0x18, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x3C, 0x24, 0x4C,
    0x89, 0xF8, 0x49, 0xF7, 0xE3, 0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00] ++ bytes_l110d64_18

theorem code_l110d64_17 : ∀ x ∈ codeRange 0x111338 bytes_l110d64_17, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11338 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_18

def b_l110d64_16 : Block Op Label signature Reg.count 716 :=
  .letOp (n := 716) (.out 0x1112da (addR64R64Effect 0x1112da 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[714, 710]
    (.letOp (n := 717) (.exec 0x1112da (fun s => s.RIP = 0x1112da) (addR64R64Effect 0x1112da 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[714, 710]
    (.letOp (n := 718) (.out 0x1112dd (andR64R64Effect 0x1112dd 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[672, 536]
    (.letOp (n := 719) (.exec 0x1112dd (fun s => s.RIP = 0x1112dd) (andR64R64Effect 0x1112dd 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[672, 536]
    (.letOp (n := 720) (.out 0x1112e0 (movR64M64Effect 0x1112e0 11 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 721) (.exec 0x1112e0 (LoadPre 0x1112e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1112e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1112e0 11 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 722) (.out 0x1112e5 (movR64R64Effect 0x1112e5 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11] []) (.reg (.gpr 2))) #v[720]
    (.letOp (n := 723) (.exec 0x1112e5 (fun s => s.RIP = 0x1112e5) (movR64R64Effect 0x1112e5 2 11) (Reg.operands [.gpr 11] [])) #v[720]
    (.letOp (n := 724) (.out 0x1112e8 (subR64R64Effect 0x1112e8 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[722, 718]
    (.letOp (n := 725) (.exec 0x1112e8 (fun s => s.RIP = 0x1112e8) (subR64R64Effect 0x1112e8 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[722, 718]
    (.letOp (n := 726) (.out 0x1112eb (movR64Imm64Effect 0x1112eb 0 0x3ffffbfffff0bc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 727) (.exec 0x1112eb (fun s => s.RIP = 0x1112eb) (movR64Imm64Effect 0x1112eb 0 0x3ffffbfffff0bc) (Reg.operands [] [])) #v[]
    (.letOp (n := 728) (.out 0x1112f5 (addR64R64Effect 0x1112f5 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[726, 724]
    (.letOp (n := 729) (.exec 0x1112f5 (fun s => s.RIP = 0x1112f5) (addR64R64Effect 0x1112f5 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[726, 724]
    (.letOp (n := 730) (.exec 0x1112f8 (StorePre 0x1112f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1112f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1112f8 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[728, 4]
    (.letOp (n := 731) (.out 0x1112fd (andR64R64Effect 0x1112fd 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[684, 536]
    (.letOp (n := 732) (.exec 0x1112fd (fun s => s.RIP = 0x1112fd) (andR64R64Effect 0x1112fd 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[684, 536]
    (.letOp (n := 733) (.out 0x111300 (movR64Imm64Effect 0x111300 0 0x3ffffffffffffc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 734) (.exec 0x111300 (fun s => s.RIP = 0x111300) (movR64Imm64Effect 0x111300 0 0x3ffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 735) (.out 0x11130a (movR64M64Effect 0x11130a 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 736) (.exec 0x11130a (LoadPre 0x11130a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11130a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11130a 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 737) (.out 0x11130f (leaR64Effect 0x11130f 2 (.sib 0 (some 5) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 5] []) (.reg (.gpr 2))) #v[733, 735]
    (.letOp (n := 738) (.exec 0x11130f (fun s => s.RIP = 0x11130f) (leaR64Effect 0x11130f 2 (.sib 0 (some 5) 0 .none)) (Reg.operands [.gpr 0, .gpr 5] [])) #v[733, 735]
    (.letOp (n := 739) (.out 0x111313 (subR64R64Effect 0x111313 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[737, 731]
    (.letOp (n := 740) (.exec 0x111313 (fun s => s.RIP = 0x111313) (subR64R64Effect 0x111313 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[737, 731]
    (.letOp (n := 741) (.exec 0x111316 (StorePre 0x111316 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x111316 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111316 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[739, 4]
    (.letOp (n := 742) (.out 0x11131e (andR64R64Effect 0x11131e 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[696, 536]
    (.letOp (n := 743) (.exec 0x11131e (fun s => s.RIP = 0x11131e) (andR64R64Effect 0x11131e 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[696, 536]
    (.letOp (n := 744) (.out 0x111321 (movR64M64Effect 0x111321 9 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 745) (.exec 0x111321 (LoadPre 0x111321 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x111321 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111321 9 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 746) (.out 0x111326 (leaR64Effect 0x111326 1 (.sib 9 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9, .gpr 0] []) (.reg (.gpr 1))) #v[744, 733]
    (.letOp (n := 747) (.exec 0x111326 (fun s => s.RIP = 0x111326) (leaR64Effect 0x111326 1 (.sib 9 (some 0) 0 .none)) (Reg.operands [.gpr 9, .gpr 0] [])) #v[744, 733]
    (.letOp (n := 748) (.out 0x11132a (subR64R64Effect 0x11132a 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[746, 742]
    (.letOp (n := 749) (.exec 0x11132a (fun s => s.RIP = 0x11132a) (subR64R64Effect 0x11132a 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[746, 742]
    (.letOp (n := 750) (.exec 0x11132d (StorePre 0x11132d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11132d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11132d 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[748, 4]
    (.letOp (n := 751) (.out 0x111335 (andR64R64Effect 0x111335 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[708, 536]
    (.letOp (n := 752) (.exec 0x111335 (fun s => s.RIP = 0x111335) (andR64R64Effect 0x111335 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[708, 536]
    (b_l110d64_17)))))))))))))))))))))))))))))))))))))

def bytes_l110d64_16 : List UInt8 :=
  [0x49, 0x01, 0xD0, 0x4C, 0x21, 0xE0, 0x4C, 0x8B, 0x5C, 0x24, 0x20, 0x4C, 0x89, 0xDA, 0x48, 0x29,
    0xC2, 0x48, 0xB8, 0xBC, 0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00, 0x48, 0x01, 0xD0, 0x48, 0x89,
    0x44, 0x24, 0x68, 0x4C, 0x21, 0xE1, 0x48, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00,
    0x48, 0x8B, 0x6C, 0x24, 0x28, 0x48, 0x8D, 0x14, 0x28, 0x48, 0x29, 0xCA, 0x48, 0x89, 0x94, 0x24,
    0xA8, 0x00, 0x00, 0x00, 0x4C, 0x21, 0xE6, 0x4C, 0x8B, 0x4C, 0x24, 0x48, 0x49, 0x8D, 0x0C, 0x01,
    0x48, 0x29, 0xF1, 0x48, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x21, 0xE7] ++ bytes_l110d64_17

theorem code_l110d64_16 : ∀ x ∈ codeRange 0x1112da bytes_l110d64_16, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x112da 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_17

def b_l110d64_15 : Block Op Label signature Reg.count 676 :=
  .letOp (n := 676) (.out 0x111293 (movR64R64Effect 0x111293 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[672]
    (.letOp (n := 677) (.exec 0x111293 (fun s => s.RIP = 0x111293) (movR64R64Effect 0x111293 1 0) (Reg.operands [.gpr 0] [])) #v[672]
    (.letOp (n := 678) (.out 0x111296 (shrR64Effect 0x111296 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[676]
    (.letOp (n := 679) (.exec 0x111296 (fun s => s.RIP = 0x111296) (shrR64Effect 0x111296 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[676]
    (.letOp (n := 680) (.out 0x11129a (leaR64Effect 0x11129a 6 (.sib 7 (some 7) 1 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7, .gpr 7] []) (.reg (.gpr 6))) #v[674, 674]
    (.letOp (n := 681) (.exec 0x11129a (fun s => s.RIP = 0x11129a) (leaR64Effect 0x11129a 6 (.sib 7 (some 7) 1 .none)) (Reg.operands [.gpr 7, .gpr 7] [])) #v[674, 674]
    (.letOp (n := 682) (.out 0x11129e (movR64R64Effect 0x11129e 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[674]
    (.letOp (n := 683) (.exec 0x11129e (fun s => s.RIP = 0x11129e) (movR64R64Effect 0x11129e 3 7) (Reg.operands [.gpr 7] [])) #v[674]
    (.letOp (n := 684) (.out 0x1112a1 (addR64R64Effect 0x1112a1 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[678, 680]
    (.letOp (n := 685) (.exec 0x1112a1 (fun s => s.RIP = 0x1112a1) (addR64R64Effect 0x1112a1 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[678, 680]
    (.letOp (n := 686) (.out 0x1112a4 (andR64R64Effect 0x1112a4 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[634, 536]
    (.letOp (n := 687) (.exec 0x1112a4 (fun s => s.RIP = 0x1112a4) (andR64R64Effect 0x1112a4 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[634, 536]
    (.letOp (n := 688) (.out 0x1112a7 (movR64R64Effect 0x1112a7 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[684]
    (.letOp (n := 689) (.exec 0x1112a7 (fun s => s.RIP = 0x1112a7) (movR64R64Effect 0x1112a7 6 1) (Reg.operands [.gpr 1] [])) #v[684]
    (.letOp (n := 690) (.out 0x1112aa (shrR64Effect 0x1112aa 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[688]
    (.letOp (n := 691) (.exec 0x1112aa (fun s => s.RIP = 0x1112aa) (shrR64Effect 0x1112aa 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[688]
    (.letOp (n := 692) (.out 0x1112ae (leaR64Effect 0x1112ae 7 (.sib 8 (some 8) 1 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8, .gpr 8] []) (.reg (.gpr 7))) #v[686, 686]
    (.letOp (n := 693) (.exec 0x1112ae (fun s => s.RIP = 0x1112ae) (leaR64Effect 0x1112ae 7 (.sib 8 (some 8) 1 .none)) (Reg.operands [.gpr 8, .gpr 8] [])) #v[686, 686]
    (.letOp (n := 694) (.out 0x1112b2 (movR64R64Effect 0x1112b2 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[686]
    (.letOp (n := 695) (.exec 0x1112b2 (fun s => s.RIP = 0x1112b2) (movR64R64Effect 0x1112b2 14 8) (Reg.operands [.gpr 8] [])) #v[686]
    (.letOp (n := 696) (.out 0x1112b5 (addR64R64Effect 0x1112b5 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[690, 692]
    (.letOp (n := 697) (.exec 0x1112b5 (fun s => s.RIP = 0x1112b5) (addR64R64Effect 0x1112b5 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[690, 692]
    (.letOp (n := 698) (.out 0x1112b8 (andR64R64Effect 0x1112b8 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[647, 536]
    (.letOp (n := 699) (.exec 0x1112b8 (fun s => s.RIP = 0x1112b8) (andR64R64Effect 0x1112b8 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[647, 536]
    (.letOp (n := 700) (.out 0x1112bb (movR64R64Effect 0x1112bb 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[696]
    (.letOp (n := 701) (.exec 0x1112bb (fun s => s.RIP = 0x1112bb) (movR64R64Effect 0x1112bb 7 6) (Reg.operands [.gpr 6] [])) #v[696]
    (.letOp (n := 702) (.out 0x1112be (shrR64Effect 0x1112be 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[700]
    (.letOp (n := 703) (.exec 0x1112be (fun s => s.RIP = 0x1112be) (shrR64Effect 0x1112be 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[700]
    (.letOp (n := 704) (.out 0x1112c2 (leaR64Effect 0x1112c2 8 (.abs (some 13) 1 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 13] []) (.reg (.gpr 8))) #v[698]
    (.letOp (n := 705) (.exec 0x1112c2 (fun s => s.RIP = 0x1112c2) (leaR64Effect 0x1112c2 8 (.abs (some 13) 1 0x0)) (Reg.operands [.gpr 13] [])) #v[698]
    (.letOp (n := 706) (.out 0x1112ca (addR64R64Effect 0x1112ca 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[704, 698]
    (.letOp (n := 707) (.exec 0x1112ca (fun s => s.RIP = 0x1112ca) (addR64R64Effect 0x1112ca 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[704, 698]
    (.letOp (n := 708) (.out 0x1112cd (addR64R64Effect 0x1112cd 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[702, 706]
    (.letOp (n := 709) (.exec 0x1112cd (fun s => s.RIP = 0x1112cd) (addR64R64Effect 0x1112cd 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[702, 706]
    (.letOp (n := 710) (.out 0x1112d0 (andR64R64Effect 0x1112d0 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[660, 550]
    (.letOp (n := 711) (.exec 0x1112d0 (fun s => s.RIP = 0x1112d0) (andR64R64Effect 0x1112d0 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[660, 550]
    (.letOp (n := 712) (.out 0x1112d3 (movR64R64Effect 0x1112d3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[708]
    (.letOp (n := 713) (.exec 0x1112d3 (fun s => s.RIP = 0x1112d3) (movR64R64Effect 0x1112d3 8 7) (Reg.operands [.gpr 7] [])) #v[708]
    (.letOp (n := 714) (.out 0x1112d6 (shrR64Effect 0x1112d6 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[712]
    (.letOp (n := 715) (.exec 0x1112d6 (fun s => s.RIP = 0x1112d6) (shrR64Effect 0x1112d6 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[712]
    (b_l110d64_16))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_15 : List UInt8 :=
  [0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x34, 0x48, 0x8D, 0x34, 0x7F, 0x48, 0x89, 0xFB, 0x48, 0x01,
    0xF1, 0x4D, 0x21, 0xE0, 0x48, 0x89, 0xCE, 0x48, 0xC1, 0xEE, 0x34, 0x4B, 0x8D, 0x3C, 0x40, 0x4D,
    0x89, 0xC6, 0x48, 0x01, 0xFE, 0x4D, 0x21, 0xE5, 0x48, 0x89, 0xF7, 0x48, 0xC1, 0xEF, 0x34, 0x4E,
    0x8D, 0x04, 0x6D, 0x00, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xE8, 0x4C, 0x01, 0xC7, 0x4C, 0x21, 0xDA,
    0x49, 0x89, 0xF8, 0x49, 0xC1, 0xE8, 0x34] ++ bytes_l110d64_16

theorem code_l110d64_15 : ∀ x ∈ codeRange 0x111293 bytes_l110d64_15, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11293 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_16

def b_l110d64_14 : Block Op Label signature Reg.count 638 :=
  .letOp (n := 638) (.exec 0x111249 (StorePre 0x111249 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111249 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111249 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[636, 4]
    (.letOp (n := 639) (.out 0x11124d (leaR64Effect 0x11124d 1 (.sib 2 (some 2) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 2] []) (.reg (.gpr 1))) #v[636, 636]
    (.letOp (n := 640) (.exec 0x11124d (fun s => s.RIP = 0x11124d) (leaR64Effect 0x11124d 1 (.sib 2 (some 2) 2 .none)) (Reg.operands [.gpr 2, .gpr 2] [])) #v[636, 636]
    (.letOp (n := 641) (.out 0x111251 (leaR64Effect 0x111251 1 (.sib 2 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 1] []) (.reg (.gpr 1))) #v[636, 639]
    (.letOp (n := 642) (.exec 0x111251 (fun s => s.RIP = 0x111251) (leaR64Effect 0x111251 1 (.sib 2 (some 1) 2 .none)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[636, 639]
    (.letOp (n := 643) (.out 0x111255 (movR64R64Effect 0x111255 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[634]
    (.letOp (n := 644) (.exec 0x111255 (fun s => s.RIP = 0x111255) (movR64R64Effect 0x111255 13 8) (Reg.operands [.gpr 8] [])) #v[634]
    (.letOp (n := 645) (.out 0x111258 (shrR64Effect 0x111258 4 13 52) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[643]
    (.letOp (n := 646) (.exec 0x111258 (fun s => s.RIP = 0x111258) (shrR64Effect 0x111258 4 13 52) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[643]
    (.letOp (n := 647) (.out 0x11125c (addR64R64Effect 0x11125c 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[645, 641]
    (.letOp (n := 648) (.exec 0x11125c (fun s => s.RIP = 0x11125c) (addR64R64Effect 0x11125c 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[645, 641]
    (.letOp (n := 649) (.out 0x11125f (andR64R64Effect 0x11125f 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[596, 550]
    (.letOp (n := 650) (.exec 0x11125f (fun s => s.RIP = 0x11125f) (andR64R64Effect 0x11125f 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[596, 550]
    (.letOp (n := 651) (.out 0x111262 (movR64R64Effect 0x111262 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[647]
    (.letOp (n := 652) (.exec 0x111262 (fun s => s.RIP = 0x111262) (movR64R64Effect 0x111262 1 13) (Reg.operands [.gpr 13] [])) #v[647]
    (.letOp (n := 653) (.out 0x111265 (shrR64Effect 0x111265 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[651]
    (.letOp (n := 654) (.exec 0x111265 (fun s => s.RIP = 0x111265) (shrR64Effect 0x111265 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[651]
    (.letOp (n := 655) (.out 0x111269 (addR64R64Effect 0x111269 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[653, 649]
    (.letOp (n := 656) (.exec 0x111269 (fun s => s.RIP = 0x111269) (addR64R64Effect 0x111269 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[653, 649]
    (.letOp (n := 657) (.exec 0x11126c (StorePre 0x11126c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11126c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11126c 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[655, 4]
    (.letOp (n := 658) (.out 0x111274 (andR64R64Effect 0x111274 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[617, 492]
    (.letOp (n := 659) (.exec 0x111274 (fun s => s.RIP = 0x111274) (andR64R64Effect 0x111274 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[617, 492]
    (.letOp (n := 660) (.out 0x111277 (leaR64Effect 0x111277 2 (.sib 1 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 1] []) (.reg (.gpr 2))) #v[655, 655]
    (.letOp (n := 661) (.exec 0x111277 (fun s => s.RIP = 0x111277) (leaR64Effect 0x111277 2 (.sib 1 (some 1) 1 .none)) (Reg.operands [.gpr 1, .gpr 1] [])) #v[655, 655]
    (.letOp (n := 662) (.out 0x11127b (movR64R64Effect 0x11127b 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[660]
    (.letOp (n := 663) (.exec 0x11127b (fun s => s.RIP = 0x11127b) (movR64R64Effect 0x11127b 0 2) (Reg.operands [.gpr 2] [])) #v[660]
    (.letOp (n := 664) (.out 0x11127e (shrR64Effect 0x11127e 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[662]
    (.letOp (n := 665) (.exec 0x11127e (fun s => s.RIP = 0x11127e) (shrR64Effect 0x11127e 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[662]
    (.letOp (n := 666) (.out 0x111282 (imulR64R64Effect 0x111282 4 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[664, 602]
    (.letOp (n := 667) (.exec 0x111282 (fun s => s.RIP = 0x111282) (imulR64R64Effect 0x111282 4 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[664, 602]
    (.letOp (n := 668) (.out 0x111286 (leaR64Effect 0x111286 1 (.sib 6 (some 6) 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 6] []) (.reg (.gpr 1))) #v[658, 658]
    (.letOp (n := 669) (.exec 0x111286 (fun s => s.RIP = 0x111286) (leaR64Effect 0x111286 1 (.sib 6 (some 6) 1 .none)) (Reg.operands [.gpr 6, .gpr 6] [])) #v[658, 658]
    (.letOp (n := 670) (.out 0x11128a (movR64R64Effect 0x11128a 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[658]
    (.letOp (n := 671) (.exec 0x11128a (fun s => s.RIP = 0x11128a) (movR64R64Effect 0x11128a 10 6) (Reg.operands [.gpr 6] [])) #v[658]
    (.letOp (n := 672) (.out 0x11128d (addR64R64Effect 0x11128d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[666, 668]
    (.letOp (n := 673) (.exec 0x11128d (fun s => s.RIP = 0x11128d) (addR64R64Effect 0x11128d 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[666, 668]
    (.letOp (n := 674) (.out 0x111290 (andR64R64Effect 0x111290 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[621, 536]
    (.letOp (n := 675) (.exec 0x111290 (fun s => s.RIP = 0x111290) (andR64R64Effect 0x111290 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[621, 536]
    (b_l110d64_15))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_14 : List UInt8 :=
  [0x48, 0x89, 0x14, 0x24, 0x48, 0x8D, 0x0C, 0x92, 0x48, 0x8D, 0x0C, 0x8A, 0x4D, 0x89, 0xC5, 0x49,
    0xC1, 0xED, 0x34, 0x49, 0x01, 0xCD, 0x4C, 0x21, 0xD8, 0x4C, 0x89, 0xE9, 0x48, 0xC1, 0xE9, 0x34,
    0x48, 0x01, 0xC1, 0x48, 0x89, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x21, 0xD6, 0x48, 0x8D,
    0x14, 0x49, 0x48, 0x89, 0xD0, 0x48, 0xC1, 0xE8, 0x30, 0x48, 0x0F, 0xAF, 0xC5, 0x48, 0x8D, 0x0C,
    0x76, 0x49, 0x89, 0xF2, 0x48, 0x01, 0xC8, 0x4C, 0x21, 0xE7] ++ bytes_l110d64_15

theorem code_l110d64_14 : ∀ x ∈ codeRange 0x111249 bytes_l110d64_14, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11249 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_15

def b_l110d64_13 : Block Op Label signature Reg.count 600 :=
  .letOp (n := 600) (.out 0x1111e5 (shrR64Effect 0x1111e5 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[598]
    (.letOp (n := 601) (.exec 0x1111e5 (fun s => s.RIP = 0x1111e5) (shrR64Effect 0x1111e5 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[598]
    (.letOp (n := 602) (.out 0x1111e9 (movR64Imm64Effect 0x1111e9 5 0x1000003d1) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 603) (.exec 0x1111e9 (fun s => s.RIP = 0x1111e9) (movR64Imm64Effect 0x1111e9 5 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 604) (.out 0x1111f3 (imulR64R64Effect 0x1111f3 4 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[600, 602]
    (.letOp (n := 605) (.exec 0x1111f3 (fun s => s.RIP = 0x1111f3) (imulR64R64Effect 0x1111f3 4 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[600, 602]
    (.letOp (n := 606) (.out 0x1111f7 (addR64R64Effect 0x1111f7 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[604, 589]
    (.letOp (n := 607) (.exec 0x1111f7 (fun s => s.RIP = 0x1111f7) (addR64R64Effect 0x1111f7 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[604, 589]
    (.letOp (n := 608) (.out 0x1111fa (movR64M64Effect 0x1111fa 6 (.sib 4 none 0 (.d32 0x1d8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 609) (.exec 0x1111fa (LoadPre 0x1111fa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x1111fa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1111fa 6 (.sib 4 none 0 (.d32 0x1d8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 610) (.exec 0x111202 (StorePre 0x111202 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x111202 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111202 6 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[608, 4]
    (.letOp (n := 611) (.out 0x11120a (leaR64Effect 0x11120a 1 (.sib 6 (some 6) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 6] []) (.reg (.gpr 1))) #v[608, 608]
    (.letOp (n := 612) (.exec 0x11120a (fun s => s.RIP = 0x11120a) (leaR64Effect 0x11120a 1 (.sib 6 (some 6) 2 .none)) (Reg.operands [.gpr 6, .gpr 6] [])) #v[608, 608]
    (.letOp (n := 613) (.out 0x11120e (leaR64Effect 0x11120e 1 (.sib 6 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 1] []) (.reg (.gpr 1))) #v[608, 611]
    (.letOp (n := 614) (.exec 0x11120e (fun s => s.RIP = 0x11120e) (leaR64Effect 0x11120e 1 (.sib 6 (some 1) 2 .none)) (Reg.operands [.gpr 6, .gpr 1] [])) #v[608, 611]
    (.letOp (n := 615) (.out 0x111212 (movR64R64Effect 0x111212 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[606]
    (.letOp (n := 616) (.exec 0x111212 (fun s => s.RIP = 0x111212) (movR64R64Effect 0x111212 7 2) (Reg.operands [.gpr 2] [])) #v[606]
    (.letOp (n := 617) (.out 0x111215 (movR64R64Effect 0x111215 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[606]
    (.letOp (n := 618) (.exec 0x111215 (fun s => s.RIP = 0x111215) (movR64R64Effect 0x111215 6 2) (Reg.operands [.gpr 2] [])) #v[606]
    (.letOp (n := 619) (.out 0x111218 (shrR64Effect 0x111218 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[615]
    (.letOp (n := 620) (.exec 0x111218 (fun s => s.RIP = 0x111218) (shrR64Effect 0x111218 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[615]
    (.letOp (n := 621) (.out 0x11121c (addR64R64Effect 0x11121c 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[619, 613]
    (.letOp (n := 622) (.exec 0x11121c (fun s => s.RIP = 0x11121c) (addR64R64Effect 0x11121c 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[619, 613]
    (.letOp (n := 623) (.out 0x11121f (movR64M64Effect 0x11121f 2 (.sib 4 none 0 (.d32 0x1e0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 624) (.exec 0x11121f (LoadPre 0x11121f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x11121f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11121f 2 (.sib 4 none 0 (.d32 0x1e0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 625) (.exec 0x111227 (StorePre 0x111227 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x111227 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111227 2 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[623, 4]
    (.letOp (n := 626) (.out 0x11122f (leaR64Effect 0x11122f 1 (.sib 2 (some 2) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 2] []) (.reg (.gpr 1))) #v[623, 623]
    (.letOp (n := 627) (.exec 0x11122f (fun s => s.RIP = 0x11122f) (leaR64Effect 0x11122f 1 (.sib 2 (some 2) 2 .none)) (Reg.operands [.gpr 2, .gpr 2] [])) #v[623, 623]
    (.letOp (n := 628) (.out 0x111233 (leaR64Effect 0x111233 1 (.sib 2 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 1] []) (.reg (.gpr 1))) #v[623, 626]
    (.letOp (n := 629) (.exec 0x111233 (fun s => s.RIP = 0x111233) (leaR64Effect 0x111233 1 (.sib 2 (some 1) 2 .none)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[623, 626]
    (.letOp (n := 630) (.out 0x111237 (movR64R64Effect 0x111237 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[621]
    (.letOp (n := 631) (.exec 0x111237 (fun s => s.RIP = 0x111237) (movR64R64Effect 0x111237 8 7) (Reg.operands [.gpr 7] [])) #v[621]
    (.letOp (n := 632) (.out 0x11123a (shrR64Effect 0x11123a 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[630]
    (.letOp (n := 633) (.exec 0x11123a (fun s => s.RIP = 0x11123a) (shrR64Effect 0x11123a 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[630]
    (.letOp (n := 634) (.out 0x11123e (addR64R64Effect 0x11123e 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[632, 628]
    (.letOp (n := 635) (.exec 0x11123e (fun s => s.RIP = 0x11123e) (addR64R64Effect 0x11123e 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[632, 628]
    (.letOp (n := 636) (.out 0x111241 (movR64M64Effect 0x111241 2 (.sib 4 none 0 (.d32 0x1e8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 637) (.exec 0x111241 (LoadPre 0x111241 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x111241 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111241 2 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l110d64_14))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_13 : List UInt8 :=
  [0x48, 0xC1, 0xEA, 0x30, 0x48, 0xBD, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0x0F,
    0xAF, 0xD5, 0x48, 0x01, 0xCA, 0x48, 0x8B, 0xB4, 0x24, 0xD8, 0x01, 0x00, 0x00, 0x48, 0x89, 0xB4,
    0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x0C, 0xB6, 0x48, 0x8D, 0x0C, 0x8E, 0x48, 0x89, 0xD7,
    0x48, 0x89, 0xD6, 0x48, 0xC1, 0xEF, 0x34, 0x48, 0x01, 0xCF, 0x48, 0x8B, 0x94, 0x24, 0xE0, 0x01,
    0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x0C, 0x92, 0x48, 0x8D,
    0x0C, 0x8A, 0x49, 0x89, 0xF8, 0x49, 0xC1, 0xE8, 0x34, 0x49, 0x01, 0xC8, 0x48, 0x8B, 0x94, 0x24,
    0xE8, 0x01, 0x00, 0x00] ++ bytes_l110d64_14

theorem code_l110d64_13 : ∀ x ∈ codeRange 0x1111e5 bytes_l110d64_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x111e5 100 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_14

def b_l110d64_12 : Block Op Label signature Reg.count 566 :=
  .letOp (n := 566) (.out 0x111183 (andR64R64Effect 0x111183 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[562, 564]
    (.letOp (n := 567) (.exec 0x111183 (fun s => s.RIP = 0x111183) (andR64R64Effect 0x111183 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[562, 564]
    (.letOp (n := 568) (.exec 0x111186 (StorePre 0x111186 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111186 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111186 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[566, 4]
    (.letOp (n := 569) (.out 0x11118b (addR64R64Effect 0x11118b 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[432, 432]
    (.letOp (n := 570) (.exec 0x11118b (fun s => s.RIP = 0x11118b) (addR64R64Effect 0x11118b 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[432, 432]
    (.letOp (n := 571) (.out 0x11118e (andR64R64Effect 0x11118e 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[569, 564]
    (.letOp (n := 572) (.exec 0x11118e (fun s => s.RIP = 0x11118e) (andR64R64Effect 0x11118e 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[569, 564]
    (.letOp (n := 573) (.exec 0x111191 (StorePre 0x111191 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x111191 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111191 8 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[571, 4]
    (.letOp (n := 574) (.out 0x111199 (addR64R64Effect 0x111199 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[518, 518]
    (.letOp (n := 575) (.exec 0x111199 (fun s => s.RIP = 0x111199) (addR64R64Effect 0x111199 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[518, 518]
    (.letOp (n := 576) (.out 0x11119c (andR64R64Effect 0x11119c 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[574, 564]
    (.letOp (n := 577) (.exec 0x11119c (fun s => s.RIP = 0x11119c) (andR64R64Effect 0x11119c 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[574, 564]
    (.letOp (n := 578) (.exec 0x11119f (StorePre 0x11119f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x11119f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11119f 9 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[576, 4]
    (.letOp (n := 579) (.out 0x1111a7 (addR64R64Effect 0x1111a7 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[543, 543]
    (.letOp (n := 580) (.exec 0x1111a7 (fun s => s.RIP = 0x1111a7) (addR64R64Effect 0x1111a7 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[543, 543]
    (.letOp (n := 581) (.out 0x1111aa (andR64R64Effect 0x1111aa 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[579, 564]
    (.letOp (n := 582) (.exec 0x1111aa (fun s => s.RIP = 0x1111aa) (andR64R64Effect 0x1111aa 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[579, 564]
    (.letOp (n := 583) (.exec 0x1111ad (StorePre 0x1111ad 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1111ad + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1111ad 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[581, 4]
    (.letOp (n := 584) (.out 0x1111b5 (movR64M64Effect 0x1111b5 1 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 585) (.exec 0x1111b5 (LoadPre 0x1111b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x1111b5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1111b5 1 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 586) (.exec 0x1111bd (StorePre 0x1111bd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1111bd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1111bd 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[584, 4]
    (.letOp (n := 587) (.out 0x1111c5 (leaR64Effect 0x1111c5 0 (.sib 1 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 1] []) (.reg (.gpr 0))) #v[584, 584]
    (.letOp (n := 588) (.exec 0x1111c5 (fun s => s.RIP = 0x1111c5) (leaR64Effect 0x1111c5 0 (.sib 1 (some 1) 2 .none)) (Reg.operands [.gpr 1, .gpr 1] [])) #v[584, 584]
    (.letOp (n := 589) (.out 0x1111c9 (leaR64Effect 0x1111c9 1 (.sib 1 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[584, 587]
    (.letOp (n := 590) (.exec 0x1111c9 (fun s => s.RIP = 0x1111c9) (leaR64Effect 0x1111c9 1 (.sib 1 (some 0) 2 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[584, 587]
    (.letOp (n := 591) (.out 0x1111cd (movR64M64Effect 0x1111cd 2 (.sib 4 none 0 (.d32 0x1f0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 592) (.exec 0x1111cd (LoadPre 0x1111cd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f0)) s (0x1111cd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1111cd 2 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 593) (.exec 0x1111d5 (StorePre 0x1111d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1111d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1111d5 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[591, 4]
    (.letOp (n := 594) (.out 0x1111da (leaR64Effect 0x1111da 0 (.sib 2 (some 2) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 2] []) (.reg (.gpr 0))) #v[591, 591]
    (.letOp (n := 595) (.exec 0x1111da (fun s => s.RIP = 0x1111da) (leaR64Effect 0x1111da 0 (.sib 2 (some 2) 2 .none)) (Reg.operands [.gpr 2, .gpr 2] [])) #v[591, 591]
    (.letOp (n := 596) (.out 0x1111de (leaR64Effect 0x1111de 0 (.sib 2 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[591, 594]
    (.letOp (n := 597) (.exec 0x1111de (fun s => s.RIP = 0x1111de) (leaR64Effect 0x1111de 0 (.sib 2 (some 0) 2 .none)) (Reg.operands [.gpr 2, .gpr 0] [])) #v[591, 594]
    (.letOp (n := 598) (.out 0x1111e2 (movR64R64Effect 0x1111e2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[596]
    (.letOp (n := 599) (.exec 0x1111e2 (fun s => s.RIP = 0x1111e2) (movR64R64Effect 0x1111e2 2 0) (Reg.operands [.gpr 0] [])) #v[596]
    (b_l110d64_13))))))))))))))))))))))))))))))))))

def bytes_l110d64_12 : List UInt8 :=
  [0x48, 0x21, 0xD1, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x4D, 0x01, 0xC0, 0x49, 0x21, 0xD0, 0x4C, 0x89,
    0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xC9, 0x49, 0x21, 0xD1, 0x4C, 0x89, 0x8C, 0x24,
    0xE0, 0x00, 0x00, 0x00, 0x48, 0x01, 0xC0, 0x48, 0x21, 0xD0, 0x48, 0x89, 0x84, 0x24, 0xF8, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x48, 0x8D, 0x04, 0x89, 0x48, 0x8D, 0x0C, 0x81, 0x48, 0x8B, 0x94, 0x24, 0xF0, 0x01,
    0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x30, 0x48, 0x8D, 0x04, 0x92, 0x48, 0x8D, 0x04, 0x82, 0x48,
    0x89, 0xC2] ++ bytes_l110d64_13

theorem code_l110d64_12 : ∀ x ∈ codeRange 0x111183 bytes_l110d64_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11183 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_13

def b_l110d64_11 : Block Op Label signature Reg.count 523 :=
  .letOp (n := 523) (.out 0x111128 (shldR64R64Effect 0x111128 5 11 12 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[488, 485]
    (.letOp (n := 524) (.exec 0x111128 (fun s => s.RIP = 0x111128) (shldR64R64Effect 0x111128 5 11 12 12) (Reg.operands [.gpr 11, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[488, 485]
    (.letOp (n := 525) (.out 0x11112d (shldR64R64Effect 0x11112d 5 6 9 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[521, 518]
    (.letOp (n := 526) (.exec 0x11112d (fun s => s.RIP = 0x11112d) (shldR64R64Effect 0x11112d 5 6 9 12) (Reg.operands [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[521, 518]
    (.letOp (n := 527) (.out 0x111132 (movR64R64Effect 0x111132 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[523]
    (.letOp (n := 528) (.exec 0x111132 (fun s => s.RIP = 0x111132) (movR64R64Effect 0x111132 0 11) (Reg.operands [.gpr 11] [])) #v[523]
    (.letOp (n := 529) (.out 0x111135 (mulR64Effect 0x111135 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[496, 527]
    (.letOp (n := 530) (.out 0x111135 (mulR64Effect 0x111135 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[496, 527]
    (.letOp (n := 531) (.exec 0x111135 (fun s => s.RIP = 0x111135) (mulR64Effect 0x111135 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[496, 527]
    (.letOp (n := 532) (.out 0x111138 (movR64M64Effect 0x111138 1 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 533) (.exec 0x111138 (LoadPre 0x111138 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x111138 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111138 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 534) (.out 0x111140 (andR64R64Effect 0x111140 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[532, 492]
    (.letOp (n := 535) (.exec 0x111140 (fun s => s.RIP = 0x111140) (andR64R64Effect 0x111140 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[532, 492]
    (.letOp (n := 536) (.out 0x111143 (movR64R64Effect 0x111143 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 10] []) (.reg (.gpr 12))) #v[492]
    (.letOp (n := 537) (.exec 0x111143 (fun s => s.RIP = 0x111143) (movR64R64Effect 0x111143 12 10) (Reg.operands [.gpr 10] [])) #v[492]
    (.letOp (n := 538) (.out 0x111146 (addR64R64Effect 0x111146 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[529, 534]
    (.letOp (n := 539) (.out 0x111146 (addR64R64Effect 0x111146 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[529, 534]
    (.letOp (n := 540) (.exec 0x111146 (fun s => s.RIP = 0x111146) (addR64R64Effect 0x111146 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[529, 534]
    (.letOp (n := 541) (.out 0x111149 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111149 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[530, 539]
    (.letOp (n := 542) (.exec 0x111149 (fun s => s.RIP = 0x111149) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111149 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[530, 539]
    (.letOp (n := 543) (.out 0x11114d (addR64R64Effect 0x11114d 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[538, 525]
    (.letOp (n := 544) (.out 0x11114d (addR64R64Effect 0x11114d 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[538, 525]
    (.letOp (n := 545) (.exec 0x11114d (fun s => s.RIP = 0x11114d) (addR64R64Effect 0x11114d 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[538, 525]
    (.letOp (n := 546) (.out 0x111150 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111150 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[541, 544]
    (.letOp (n := 547) (.exec 0x111150 (fun s => s.RIP = 0x111150) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111150 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[541, 544]
    (.letOp (n := 548) (.out 0x111154 (shldR64R64Effect 0x111154 5 2 0 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[546, 543]
    (.letOp (n := 549) (.exec 0x111154 (fun s => s.RIP = 0x111154) (shldR64R64Effect 0x111154 5 2 0 12) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[546, 543]
    (.letOp (n := 550) (.out 0x111159 (movR64Imm64Effect 0x111159 11 0xffffffffffff) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 551) (.exec 0x111159 (fun s => s.RIP = 0x111159) (movR64Imm64Effect 0x111159 11 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 552) (.out 0x111163 (movR64M64Effect 0x111163 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 553) (.exec 0x111163 (LoadPre 0x111163 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111163 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111163 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 554) (.out 0x111168 (andR64R64Effect 0x111168 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[552, 550]
    (.letOp (n := 555) (.exec 0x111168 (fun s => s.RIP = 0x111168) (andR64R64Effect 0x111168 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[552, 550]
    (.letOp (n := 556) (.out 0x11116b (addR64R64Effect 0x11116b 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[554, 548]
    (.letOp (n := 557) (.exec 0x11116b (fun s => s.RIP = 0x11116b) (addR64R64Effect 0x11116b 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[554, 548]
    (.letOp (n := 558) (.out 0x11116e (movR64R64Effect 0x11116e 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 1] []) (.reg (.gpr 15))) #v[556]
    (.letOp (n := 559) (.exec 0x11116e (fun s => s.RIP = 0x11116e) (movR64R64Effect 0x11116e 15 1) (Reg.operands [.gpr 1] [])) #v[556]
    (.letOp (n := 560) (.out 0x111171 (movR64M64Effect 0x111171 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 561) (.exec 0x111171 (LoadPre 0x111171 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111171 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111171 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 562) (.out 0x111176 (addR64R64Effect 0x111176 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[560, 560]
    (.letOp (n := 563) (.exec 0x111176 (fun s => s.RIP = 0x111176) (addR64R64Effect 0x111176 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[560, 560]
    (.letOp (n := 564) (.out 0x111179 (movR64Imm64Effect 0x111179 2 0x1ffffffffffffe) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 565) (.exec 0x111179 (fun s => s.RIP = 0x111179) (movR64Imm64Effect 0x111179 2 0x1ffffffffffffe) (Reg.operands [] [])) #v[]
    (b_l110d64_12)))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_11 : List UInt8 :=
  [0x4D, 0x0F, 0xA4, 0xE3, 0x0C, 0x4C, 0x0F, 0xA4, 0xCE, 0x0C, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0xE1,
    0x48, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x21, 0xD1, 0x4D, 0x89, 0xD4, 0x48, 0x01,
    0xC8, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x01, 0xF0, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x0F, 0xA4, 0xC2,
    0x0C, 0x49, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x18,
    0x4C, 0x21, 0xD9, 0x48, 0x01, 0xD1, 0x49, 0x89, 0xCF, 0x48, 0x8B, 0x4C, 0x24, 0x08, 0x48, 0x01,
    0xC9, 0x48, 0xBA, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x1F, 0x00] ++ bytes_l110d64_12

theorem code_l110d64_11 : ∀ x ∈ codeRange 0x111128 bytes_l110d64_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11128 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_12

def b_l110d64_10 : Block Op Label signature Reg.count 475 :=
  .letOp (n := 475) (.out 0x1110d3 (mulM64Effect 0x1110d3 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[473, 4]
    (.letOp (n := 476) (.out 0x1110d3 (mulM64Effect 0x1110d3 8 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[473, 4]
    (.letOp (n := 477) (.exec 0x1110d3 (LoadPre 0x1110d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1110d3 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1110d3 8 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[473, 4]
    (.letOp (n := 478) (.out 0x1110db (movR64R64Effect 0x1110db 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[475]
    (.letOp (n := 479) (.exec 0x1110db (fun s => s.RIP = 0x1110db) (movR64R64Effect 0x1110db 12 0) (Reg.operands [.gpr 0] [])) #v[475]
    (.letOp (n := 480) (.out 0x1110de (addR64R64Effect 0x1110de 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[478, 471]
    (.letOp (n := 481) (.out 0x1110de (addR64R64Effect 0x1110de 12 13) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 13] []) (.flag .CF)) #v[478, 471]
    (.letOp (n := 482) (.exec 0x1110de (fun s => s.RIP = 0x1110de) (addR64R64Effect 0x1110de 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[478, 471]
    (.letOp (n := 483) (.out 0x1110e1 (atFlags StatusFlags.CF (adcR64R64Effect 0x1110e1 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[469, 476, 481]
    (.letOp (n := 484) (.exec 0x1110e1 (fun s => s.RIP = 0x1110e1) (atFlags StatusFlags.CF (adcR64R64Effect 0x1110e1 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[469, 476, 481]
    (.letOp (n := 485) (.out 0x1110e4 (addR64R64Effect 0x1110e4 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 9] []) (.reg (.gpr 12))) #v[480, 409]
    (.letOp (n := 486) (.out 0x1110e4 (addR64R64Effect 0x1110e4 12 9) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 9] []) (.flag .CF)) #v[480, 409]
    (.letOp (n := 487) (.exec 0x1110e4 (fun s => s.RIP = 0x1110e4) (addR64R64Effect 0x1110e4 12 9) (Reg.operands [.gpr 12, .gpr 9] [])) #v[480, 409]
    (.letOp (n := 488) (.out 0x1110e7 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1110e7 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[483, 486]
    (.letOp (n := 489) (.exec 0x1110e7 (fun s => s.RIP = 0x1110e7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1110e7 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[483, 486]
    (.letOp (n := 490) (.out 0x1110eb (movR64R64Effect 0x1110eb 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[485]
    (.letOp (n := 491) (.exec 0x1110eb (fun s => s.RIP = 0x1110eb) (movR64R64Effect 0x1110eb 0 12) (Reg.operands [.gpr 12] [])) #v[485]
    (.letOp (n := 492) (.out 0x1110ee (movR64Imm64Effect 0x1110ee 10 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 493) (.exec 0x1110ee (fun s => s.RIP = 0x1110ee) (movR64Imm64Effect 0x1110ee 10 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 494) (.out 0x1110f8 (andR64R64Effect 0x1110f8 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[490, 492]
    (.letOp (n := 495) (.exec 0x1110f8 (fun s => s.RIP = 0x1110f8) (andR64R64Effect 0x1110f8 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[490, 492]
    (.letOp (n := 496) (.out 0x1110fb (movR64Imm64Effect 0x1110fb 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 497) (.exec 0x1110fb (fun s => s.RIP = 0x1110fb) (movR64Imm64Effect 0x1110fb 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 498) (.out 0x111105 (mulR64Effect 0x111105 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[496, 494]
    (.letOp (n := 499) (.out 0x111105 (mulR64Effect 0x111105 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[496, 494]
    (.letOp (n := 500) (.exec 0x111105 (fun s => s.RIP = 0x111105) (mulR64Effect 0x111105 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[496, 494]
    (.letOp (n := 501) (.out 0x111108 (movR64R64Effect 0x111108 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[498]
    (.letOp (n := 502) (.exec 0x111108 (fun s => s.RIP = 0x111108) (movR64R64Effect 0x111108 9 0) (Reg.operands [.gpr 0] [])) #v[498]
    (.letOp (n := 503) (.out 0x11110b (addR64R64Effect 0x11110b 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[462, 453]
    (.letOp (n := 504) (.out 0x11110b (addR64R64Effect 0x11110b 14 15) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 15] []) (.flag .CF)) #v[462, 453]
    (.letOp (n := 505) (.exec 0x11110b (fun s => s.RIP = 0x11110b) (addR64R64Effect 0x11110b 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[462, 453]
    (.letOp (n := 506) (.out 0x11110e (atFlags StatusFlags.CF (adcR64R64Effect 0x11110e 6 3)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[460, 451, 504]
    (.letOp (n := 507) (.exec 0x11110e (fun s => s.RIP = 0x11110e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11110e 6 3)) (Reg.operands [.gpr 6, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[460, 451, 504]
    (.letOp (n := 508) (.out 0x111111 (addR64M64Effect 0x111111 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[503, 4]
    (.letOp (n := 509) (.out 0x111111 (addR64M64Effect 0x111111 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 4] []) (.flag .CF)) #v[503, 4]
    (.letOp (n := 510) (.exec 0x111111 (LoadPre 0x111111 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111111 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x111111 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[503, 4]
    (.letOp (n := 511) (.out 0x111116 (atFlags StatusFlags.CF (adcR64M64Effect 0x111116 6 (.sib 4 none 0 (.d8 0x38)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[506, 4, 509]
    (.letOp (n := 512) (.exec 0x111116 (LoadPre 0x111116 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x111116 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111116 6 (.sib 4 none 0 (.d8 0x38)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[506, 4, 509]
    (.letOp (n := 513) (.out 0x11111b (addR64R64Effect 0x11111b 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[501, 508]
    (.letOp (n := 514) (.out 0x11111b (addR64R64Effect 0x11111b 9 14) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 14] []) (.flag .CF)) #v[501, 508]
    (.letOp (n := 515) (.exec 0x11111b (fun s => s.RIP = 0x11111b) (addR64R64Effect 0x11111b 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[501, 508]
    (.letOp (n := 516) (.out 0x11111e (atFlags StatusFlags.CF (adcR64R64Effect 0x11111e 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[511, 499, 514]
    (.letOp (n := 517) (.exec 0x11111e (fun s => s.RIP = 0x11111e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11111e 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[511, 499, 514]
    (.letOp (n := 518) (.out 0x111121 (addR64R64Effect 0x111121 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[513, 437]
    (.letOp (n := 519) (.out 0x111121 (addR64R64Effect 0x111121 9 7) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 7] []) (.flag .CF)) #v[513, 437]
    (.letOp (n := 520) (.exec 0x111121 (fun s => s.RIP = 0x111121) (addR64R64Effect 0x111121 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[513, 437]
    (.letOp (n := 521) (.out 0x111124 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111124 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[516, 519]
    (.letOp (n := 522) (.exec 0x111124 (fun s => s.RIP = 0x111124) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111124 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[516, 519]
    (b_l110d64_11))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_10 : List UInt8 :=
  [0x48, 0xF7, 0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC4, 0x4D, 0x01, 0xEC, 0x49, 0x11,
    0xD3, 0x4D, 0x01, 0xCC, 0x49, 0x83, 0xD3, 0x00, 0x4C, 0x89, 0xE0, 0x49, 0xBA, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xD0, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xC1, 0x4D, 0x01, 0xFE, 0x48, 0x11, 0xDE, 0x4C, 0x03,
    0x74, 0x24, 0x10, 0x48, 0x13, 0x74, 0x24, 0x38, 0x4D, 0x01, 0xF1, 0x48, 0x11, 0xD6, 0x49, 0x01,
    0xF9, 0x48, 0x83, 0xD6, 0x00] ++ bytes_l110d64_11

theorem code_l110d64_10 : ∀ x ∈ codeRange 0x1110d3 bytes_l110d64_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x110d3 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_11

def b_l110d64_9 : Block Op Label signature Reg.count 432 :=
  .letOp (n := 432) (.out 0x111086 (addR64M64Effect 0x111086 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[427, 4]
    (.letOp (n := 433) (.out 0x111086 (addR64M64Effect 0x111086 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[427, 4]
    (.letOp (n := 434) (.exec 0x111086 (LoadPre 0x111086 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111086 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x111086 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[427, 4]
    (.letOp (n := 435) (.out 0x11108b (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11108b 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[430, 433]
    (.letOp (n := 436) (.exec 0x11108b (fun s => s.RIP = 0x11108b) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11108b 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[430, 433]
    (.letOp (n := 437) (.out 0x11108f (shldR64R64Effect 0x11108f 5 7 8 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[435, 432]
    (.letOp (n := 438) (.exec 0x11108f (fun s => s.RIP = 0x11108f) (shldR64R64Effect 0x11108f 5 7 8 12) (Reg.operands [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[435, 432]
    (.letOp (n := 439) (.out 0x111094 (movR64R64Effect 0x111094 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[387]
    (.letOp (n := 440) (.exec 0x111094 (fun s => s.RIP = 0x111094) (movR64R64Effect 0x111094 0 6) (Reg.operands [.gpr 6] [])) #v[387]
    (.letOp (n := 441) (.out 0x111097 (mulM64Effect 0x111097 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[439, 4]
    (.letOp (n := 442) (.out 0x111097 (mulM64Effect 0x111097 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[439, 4]
    (.letOp (n := 443) (.exec 0x111097 (LoadPre 0x111097 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x111097 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x111097 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[439, 4]
    (.letOp (n := 444) (.exec 0x11109c (StorePre 0x11109c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11109c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11109c 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[442, 4]
    (.letOp (n := 445) (.exec 0x1110a1 (StorePre 0x1110a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1110a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1110a1 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[441, 4]
    (.letOp (n := 446) (.out 0x1110a6 (movR64M64Effect 0x1110a6 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 447) (.exec 0x1110a6 (LoadPre 0x1110a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1110a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1110a6 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 448) (.out 0x1110ab (mulM64Effect 0x1110ab 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[446, 4]
    (.letOp (n := 449) (.out 0x1110ab (mulM64Effect 0x1110ab 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[446, 4]
    (.letOp (n := 450) (.exec 0x1110ab (LoadPre 0x1110ab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1110ab + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1110ab 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[446, 4]
    (.letOp (n := 451) (.out 0x1110b0 (movR64R64Effect 0x1110b0 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[449]
    (.letOp (n := 452) (.exec 0x1110b0 (fun s => s.RIP = 0x1110b0) (movR64R64Effect 0x1110b0 3 2) (Reg.operands [.gpr 2] [])) #v[449]
    (.letOp (n := 453) (.out 0x1110b3 (movR64R64Effect 0x1110b3 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[448]
    (.letOp (n := 454) (.exec 0x1110b3 (fun s => s.RIP = 0x1110b3) (movR64R64Effect 0x1110b3 15 0) (Reg.operands [.gpr 0] [])) #v[448]
    (.letOp (n := 455) (.out 0x1110b6 (movR64R64Effect 0x1110b6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[354]
    (.letOp (n := 456) (.exec 0x1110b6 (fun s => s.RIP = 0x1110b6) (movR64R64Effect 0x1110b6 0 1) (Reg.operands [.gpr 1] [])) #v[354]
    (.letOp (n := 457) (.out 0x1110b9 (mulR64Effect 0x1110b9 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[367, 455]
    (.letOp (n := 458) (.out 0x1110b9 (mulR64Effect 0x1110b9 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[367, 455]
    (.letOp (n := 459) (.exec 0x1110b9 (fun s => s.RIP = 0x1110b9) (mulR64Effect 0x1110b9 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[367, 455]
    (.letOp (n := 460) (.out 0x1110bc (movR64R64Effect 0x1110bc 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[458]
    (.letOp (n := 461) (.exec 0x1110bc (fun s => s.RIP = 0x1110bc) (movR64R64Effect 0x1110bc 6 2) (Reg.operands [.gpr 2] [])) #v[458]
    (.letOp (n := 462) (.out 0x1110bf (movR64R64Effect 0x1110bf 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[457]
    (.letOp (n := 463) (.exec 0x1110bf (fun s => s.RIP = 0x1110bf) (movR64R64Effect 0x1110bf 14 0) (Reg.operands [.gpr 0] [])) #v[457]
    (.letOp (n := 464) (.out 0x1110c2 (movR64R64Effect 0x1110c2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[256]
    (.letOp (n := 465) (.exec 0x1110c2 (fun s => s.RIP = 0x1110c2) (movR64R64Effect 0x1110c2 0 5) (Reg.operands [.gpr 5] [])) #v[256]
    (.letOp (n := 466) (.out 0x1110c5 (mulR64Effect 0x1110c5 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[381, 464]
    (.letOp (n := 467) (.out 0x1110c5 (mulR64Effect 0x1110c5 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[381, 464]
    (.letOp (n := 468) (.exec 0x1110c5 (fun s => s.RIP = 0x1110c5) (mulR64Effect 0x1110c5 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[381, 464]
    (.letOp (n := 469) (.out 0x1110c8 (movR64R64Effect 0x1110c8 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[467]
    (.letOp (n := 470) (.exec 0x1110c8 (fun s => s.RIP = 0x1110c8) (movR64R64Effect 0x1110c8 11 2) (Reg.operands [.gpr 2] [])) #v[467]
    (.letOp (n := 471) (.out 0x1110cb (movR64R64Effect 0x1110cb 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[466]
    (.letOp (n := 472) (.exec 0x1110cb (fun s => s.RIP = 0x1110cb) (movR64R64Effect 0x1110cb 13 0) (Reg.operands [.gpr 0] [])) #v[466]
    (.letOp (n := 473) (.out 0x1110ce (movR64M64Effect 0x1110ce 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 474) (.exec 0x1110ce (LoadPre 0x1110ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1110ce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1110ce 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l110d64_10)))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_9 : List UInt8 :=
  [0x4C, 0x03, 0x44, 0x24, 0x10, 0x48, 0x83, 0xD7, 0x00, 0x4C, 0x0F, 0xA4, 0xC7, 0x0C, 0x48, 0x89,
    0xF0, 0x48, 0xF7, 0x64, 0x24, 0x38, 0x48, 0x89, 0x54, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10,
    0x48, 0x8B, 0x44, 0x24, 0x78, 0x48, 0xF7, 0x64, 0x24, 0x68, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC7,
    0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC6, 0x48, 0x89, 0xE8, 0x49,
    0xF7, 0xE5, 0x49, 0x89, 0xD3, 0x49, 0x89, 0xC5, 0x48, 0x8B, 0x44, 0x24, 0x70] ++ bytes_l110d64_10

theorem code_l110d64_9 : ∀ x ∈ codeRange 0x111086 bytes_l110d64_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11086 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_10

def b_l110d64_8 : Block Op Label signature Reg.count 385 :=
  .letOp (n := 385) (.out 0x111031 (movR64R64Effect 0x111031 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[378]
    (.letOp (n := 386) (.exec 0x111031 (fun s => s.RIP = 0x111031) (movR64R64Effect 0x111031 12 0) (Reg.operands [.gpr 0] [])) #v[378]
    (.letOp (n := 387) (.out 0x111034 (movR64M64Effect 0x111034 6 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 388) (.exec 0x111034 (LoadPre 0x111034 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x111034 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111034 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 389) (.out 0x11103c (movR64R64Effect 0x11103c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[387]
    (.letOp (n := 390) (.exec 0x11103c (fun s => s.RIP = 0x11103c) (movR64R64Effect 0x11103c 0 6) (Reg.operands [.gpr 6] [])) #v[387]
    (.letOp (n := 391) (.out 0x11103f (mulR64Effect 0x11103f 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[296, 389]
    (.letOp (n := 392) (.out 0x11103f (mulR64Effect 0x11103f 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[296, 389]
    (.letOp (n := 393) (.exec 0x11103f (fun s => s.RIP = 0x11103f) (mulR64Effect 0x11103f 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[296, 389]
    (.letOp (n := 394) (.out 0x111042 (addR64R64Effect 0x111042 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[391, 385]
    (.letOp (n := 395) (.out 0x111042 (addR64R64Effect 0x111042 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[391, 385]
    (.letOp (n := 396) (.exec 0x111042 (fun s => s.RIP = 0x111042) (addR64R64Effect 0x111042 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[391, 385]
    (.letOp (n := 397) (.out 0x111045 (atFlags StatusFlags.CF (adcR64R64Effect 0x111045 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[383, 392, 395]
    (.letOp (n := 398) (.exec 0x111045 (fun s => s.RIP = 0x111045) (atFlags StatusFlags.CF (adcR64R64Effect 0x111045 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[383, 392, 395]
    (.letOp (n := 399) (.out 0x111048 (addR64R64Effect 0x111048 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[394, 374]
    (.letOp (n := 400) (.out 0x111048 (addR64R64Effect 0x111048 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[394, 374]
    (.letOp (n := 401) (.exec 0x111048 (fun s => s.RIP = 0x111048) (addR64R64Effect 0x111048 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[394, 374]
    (.letOp (n := 402) (.out 0x11104b (atFlags StatusFlags.CF (adcR64R64Effect 0x11104b 9 14)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[397, 372, 400]
    (.letOp (n := 403) (.exec 0x11104b (fun s => s.RIP = 0x11104b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11104b 9 14)) (Reg.operands [.gpr 9, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[397, 372, 400]
    (.letOp (n := 404) (.out 0x11104e (addR64R64Effect 0x11104e 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[399, 321]
    (.letOp (n := 405) (.out 0x11104e (addR64R64Effect 0x11104e 0 8) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 8] []) (.flag .CF)) #v[399, 321]
    (.letOp (n := 406) (.exec 0x11104e (fun s => s.RIP = 0x11104e) (addR64R64Effect 0x11104e 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[399, 321]
    (.letOp (n := 407) (.out 0x111051 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111051 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[402, 405]
    (.letOp (n := 408) (.exec 0x111051 (fun s => s.RIP = 0x111051) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111051 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[402, 405]
    (.letOp (n := 409) (.out 0x111055 (shldR64R64Effect 0x111055 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[407, 404]
    (.letOp (n := 410) (.exec 0x111055 (fun s => s.RIP = 0x111055) (shldR64R64Effect 0x111055 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[407, 404]
    (.letOp (n := 411) (.out 0x11105a (movR64Imm64Effect 0x11105a 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 412) (.exec 0x11105a (fun s => s.RIP = 0x11105a) (movR64Imm64Effect 0x11105a 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 413) (.out 0x111064 (andR64R64Effect 0x111064 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[404, 411]
    (.letOp (n := 414) (.exec 0x111064 (fun s => s.RIP = 0x111064) (andR64R64Effect 0x111064 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[404, 411]
    (.letOp (n := 415) (.out 0x111067 (movR64Imm64Effect 0x111067 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 416) (.exec 0x111067 (fun s => s.RIP = 0x111067) (movR64Imm64Effect 0x111067 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 417) (.out 0x111071 (mulR64Effect 0x111071 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[415, 413]
    (.letOp (n := 418) (.out 0x111071 (mulR64Effect 0x111071 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[415, 413]
    (.letOp (n := 419) (.exec 0x111071 (fun s => s.RIP = 0x111071) (mulR64Effect 0x111071 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[415, 413]
    (.letOp (n := 420) (.out 0x111074 (movR64R64Effect 0x111074 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[417]
    (.letOp (n := 421) (.exec 0x111074 (fun s => s.RIP = 0x111074) (movR64R64Effect 0x111074 8 0) (Reg.operands [.gpr 0] [])) #v[417]
    (.letOp (n := 422) (.out 0x111077 (addR64M64Effect 0x111077 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[363, 4]
    (.letOp (n := 423) (.out 0x111077 (addR64M64Effect 0x111077 3 (.sib 4 none 0 .none)) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[363, 4]
    (.letOp (n := 424) (.exec 0x111077 (LoadPre 0x111077 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111077 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x111077 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 3, .gpr 4] [])) #v[363, 4]
    (.letOp (n := 425) (.out 0x11107b (atFlags StatusFlags.CF (adcR64M64Effect 0x11107b 7 (.sib 4 none 0 (.d8 0x30)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[361, 4, 423]
    (.letOp (n := 426) (.exec 0x11107b (LoadPre 0x11107b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11107b + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11107b 7 (.sib 4 none 0 (.d8 0x30)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[361, 4, 423]
    (.letOp (n := 427) (.out 0x111080 (addR64R64Effect 0x111080 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[420, 422]
    (.letOp (n := 428) (.out 0x111080 (addR64R64Effect 0x111080 8 3) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 3] []) (.flag .CF)) #v[420, 422]
    (.letOp (n := 429) (.exec 0x111080 (fun s => s.RIP = 0x111080) (addR64R64Effect 0x111080 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[420, 422]
    (.letOp (n := 430) (.out 0x111083 (atFlags StatusFlags.CF (adcR64R64Effect 0x111083 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[425, 418, 428]
    (.letOp (n := 431) (.exec 0x111083 (fun s => s.RIP = 0x111083) (atFlags StatusFlags.CF (adcR64R64Effect 0x111083 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[425, 418, 428]
    (b_l110d64_9)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_8 : List UInt8 :=
  [0x49, 0x89, 0xC4, 0x48, 0x8B, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF0, 0x49, 0xF7,
    0xE3, 0x4C, 0x01, 0xE0, 0x49, 0x11, 0xD1, 0x4C, 0x01, 0xF8, 0x4D, 0x11, 0xF1, 0x4C, 0x01, 0xC0,
    0x49, 0x83, 0xD1, 0x00, 0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE2, 0x49, 0x89, 0xC0, 0x48, 0x03, 0x1C, 0x24, 0x48, 0x13, 0x7C, 0x24, 0x30, 0x49,
    0x01, 0xD8, 0x48, 0x11, 0xD7] ++ bytes_l110d64_9

theorem code_l110d64_8 : ∀ x ∈ codeRange 0x111031 bytes_l110d64_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11031 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_9

def b_l110d64_7 : Block Op Label signature Reg.count 344 :=
  .letOp (n := 344) (.out 0x110fe5 (shldR64R64Effect 0x110fe5 5 1 0 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[342, 336]
    (.letOp (n := 345) (.exec 0x110fe5 (fun s => s.RIP = 0x110fe5) (shldR64R64Effect 0x110fe5 5 1 0 12) (Reg.operands [.gpr 1, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[342, 336]
    (.letOp (n := 346) (.exec 0x110fea (StorePre 0x110fea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x110fea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110fea 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[344, 4]
    (.letOp (n := 347) (.out 0x110fef (movR64R64Effect 0x110fef 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[292]
    (.letOp (n := 348) (.exec 0x110fef (fun s => s.RIP = 0x110fef) (movR64R64Effect 0x110fef 0 10) (Reg.operands [.gpr 10] [])) #v[292]
    (.letOp (n := 349) (.out 0x110ff2 (mulM64Effect 0x110ff2 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[347, 4]
    (.letOp (n := 350) (.out 0x110ff2 (mulM64Effect 0x110ff2 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[347, 4]
    (.letOp (n := 351) (.exec 0x110ff2 (LoadPre 0x110ff2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x110ff2 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x110ff2 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[347, 4]
    (.letOp (n := 352) (.exec 0x110ff7 (StorePre 0x110ff7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x110ff7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110ff7 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[350, 4]
    (.letOp (n := 353) (.exec 0x110ffc (StorePre 0x110ffc 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110ffc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110ffc 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[349, 4]
    (.letOp (n := 354) (.out 0x111000 (movR64M64Effect 0x111000 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 355) (.exec 0x111000 (LoadPre 0x111000 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x111000 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111000 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 356) (.out 0x111005 (movR64R64Effect 0x111005 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[354]
    (.letOp (n := 357) (.exec 0x111005 (fun s => s.RIP = 0x111005) (movR64R64Effect 0x111005 0 1) (Reg.operands [.gpr 1] [])) #v[354]
    (.letOp (n := 358) (.out 0x111008 (mulR64Effect 0x111008 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[260, 356]
    (.letOp (n := 359) (.out 0x111008 (mulR64Effect 0x111008 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[260, 356]
    (.letOp (n := 360) (.exec 0x111008 (fun s => s.RIP = 0x111008) (mulR64Effect 0x111008 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[260, 356]
    (.letOp (n := 361) (.out 0x11100b (movR64R64Effect 0x11100b 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[359]
    (.letOp (n := 362) (.exec 0x11100b (fun s => s.RIP = 0x11100b) (movR64R64Effect 0x11100b 7 2) (Reg.operands [.gpr 2] [])) #v[359]
    (.letOp (n := 363) (.out 0x11100e (movR64R64Effect 0x11100e 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[358]
    (.letOp (n := 364) (.exec 0x11100e (fun s => s.RIP = 0x11100e) (movR64R64Effect 0x11100e 3 0) (Reg.operands [.gpr 0] [])) #v[358]
    (.letOp (n := 365) (.out 0x111011 (movR64R64Effect 0x111011 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[256]
    (.letOp (n := 366) (.exec 0x111011 (fun s => s.RIP = 0x111011) (movR64R64Effect 0x111011 0 5) (Reg.operands [.gpr 5] [])) #v[256]
    (.letOp (n := 367) (.out 0x111014 (movR64M64Effect 0x111014 10 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 368) (.exec 0x111014 (LoadPre 0x111014 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x111014 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111014 10 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 369) (.out 0x11101c (mulR64Effect 0x11101c 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[367, 365]
    (.letOp (n := 370) (.out 0x11101c (mulR64Effect 0x11101c 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[367, 365]
    (.letOp (n := 371) (.exec 0x11101c (fun s => s.RIP = 0x11101c) (mulR64Effect 0x11101c 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[367, 365]
    (.letOp (n := 372) (.out 0x11101f (movR64R64Effect 0x11101f 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[370]
    (.letOp (n := 373) (.exec 0x11101f (fun s => s.RIP = 0x11101f) (movR64R64Effect 0x11101f 14 2) (Reg.operands [.gpr 2] [])) #v[370]
    (.letOp (n := 374) (.out 0x111022 (movR64R64Effect 0x111022 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[369]
    (.letOp (n := 375) (.exec 0x111022 (fun s => s.RIP = 0x111022) (movR64R64Effect 0x111022 15 0) (Reg.operands [.gpr 0] [])) #v[369]
    (.letOp (n := 376) (.out 0x111025 (movR64R64Effect 0x111025 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[268]
    (.letOp (n := 377) (.exec 0x111025 (fun s => s.RIP = 0x111025) (movR64R64Effect 0x111025 0 13) (Reg.operands [.gpr 13] [])) #v[268]
    (.letOp (n := 378) (.out 0x111028 (mulR64Effect 0x111028 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[283, 376]
    (.letOp (n := 379) (.out 0x111028 (mulR64Effect 0x111028 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[283, 376]
    (.letOp (n := 380) (.exec 0x111028 (fun s => s.RIP = 0x111028) (mulR64Effect 0x111028 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[283, 376]
    (.letOp (n := 381) (.out 0x11102b (movR64R64Effect 0x11102b 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[283]
    (.letOp (n := 382) (.exec 0x11102b (fun s => s.RIP = 0x11102b) (movR64R64Effect 0x11102b 13 9) (Reg.operands [.gpr 9] [])) #v[283]
    (.letOp (n := 383) (.out 0x11102e (movR64R64Effect 0x11102e 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[379]
    (.letOp (n := 384) (.exec 0x11102e (fun s => s.RIP = 0x11102e) (movR64R64Effect 0x11102e 9 2) (Reg.operands [.gpr 2] [])) #v[379]
    (b_l110d64_8)))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_7 : List UInt8 :=
  [0x48, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0x64,
    0x24, 0x38, 0x48, 0x89, 0x54, 0x24, 0x30, 0x48, 0x89, 0x04, 0x24, 0x48, 0x8B, 0x4C, 0x24, 0x50,
    0x48, 0x89, 0xC8, 0x48, 0xF7, 0xE6, 0x48, 0x89, 0xD7, 0x48, 0x89, 0xC3, 0x48, 0x89, 0xE8, 0x4C,
    0x8B, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC7,
    0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE1, 0x4D, 0x89, 0xCD, 0x49, 0x89, 0xD1] ++ bytes_l110d64_8

theorem code_l110d64_7 : ∀ x ∈ codeRange 0x110fe5 bytes_l110d64_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10fe5 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_8

def b_l110d64_6 : Block Op Label signature Reg.count 298 :=
  .letOp (n := 298) (.out 0x110f8f (mulR64Effect 0x110f8f 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[296, 294]
    (.letOp (n := 299) (.out 0x110f8f (mulR64Effect 0x110f8f 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[296, 294]
    (.letOp (n := 300) (.exec 0x110f8f (fun s => s.RIP = 0x110f8f) (mulR64Effect 0x110f8f 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[296, 294]
    (.letOp (n := 301) (.out 0x110f92 (addR64R64Effect 0x110f92 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[298, 290]
    (.letOp (n := 302) (.out 0x110f92 (addR64R64Effect 0x110f92 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[298, 290]
    (.letOp (n := 303) (.exec 0x110f92 (fun s => s.RIP = 0x110f92) (addR64R64Effect 0x110f92 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[298, 290]
    (.letOp (n := 304) (.out 0x110f95 (atFlags StatusFlags.CF (adcR64R64Effect 0x110f95 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[288, 299, 302]
    (.letOp (n := 305) (.exec 0x110f95 (fun s => s.RIP = 0x110f95) (atFlags StatusFlags.CF (adcR64R64Effect 0x110f95 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[288, 299, 302]
    (.letOp (n := 306) (.out 0x110f98 (addR64R64Effect 0x110f98 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[301, 275]
    (.letOp (n := 307) (.out 0x110f98 (addR64R64Effect 0x110f98 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[301, 275]
    (.letOp (n := 308) (.exec 0x110f98 (fun s => s.RIP = 0x110f98) (addR64R64Effect 0x110f98 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[301, 275]
    (.letOp (n := 309) (.out 0x110f9b (atFlags StatusFlags.CF (adcR64R64Effect 0x110f9b 8 14)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[304, 277, 307]
    (.letOp (n := 310) (.exec 0x110f9b (fun s => s.RIP = 0x110f9b) (atFlags StatusFlags.CF (adcR64R64Effect 0x110f9b 8 14)) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[304, 277, 307]
    (.letOp (n := 311) (.out 0x110f9e (addR64R64Effect 0x110f9e 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[306, 266]
    (.letOp (n := 312) (.out 0x110f9e (addR64R64Effect 0x110f9e 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[306, 266]
    (.letOp (n := 313) (.exec 0x110f9e (fun s => s.RIP = 0x110f9e) (addR64R64Effect 0x110f9e 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[306, 266]
    (.letOp (n := 314) (.out 0x110fa1 (atFlags StatusFlags.CF (adcR64M64Effect 0x110fa1 8 (.sib 4 none 0 (.d8 0x30)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[309, 4, 312]
    (.letOp (n := 315) (.exec 0x110fa1 (LoadPre 0x110fa1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x110fa1 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x110fa1 8 (.sib 4 none 0 (.d8 0x30)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[309, 4, 312]
    (.letOp (n := 316) (.out 0x110fa6 (addR64R64Effect 0x110fa6 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[311, 245]
    (.letOp (n := 317) (.out 0x110fa6 (addR64R64Effect 0x110fa6 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[311, 245]
    (.letOp (n := 318) (.exec 0x110fa6 (fun s => s.RIP = 0x110fa6) (addR64R64Effect 0x110fa6 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[311, 245]
    (.letOp (n := 319) (.out 0x110fa9 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x110fa9 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[314, 317]
    (.letOp (n := 320) (.exec 0x110fa9 (fun s => s.RIP = 0x110fa9) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x110fa9 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[314, 317]
    (.letOp (n := 321) (.out 0x110fad (shldR64R64Effect 0x110fad 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[319, 316]
    (.letOp (n := 322) (.exec 0x110fad (fun s => s.RIP = 0x110fad) (shldR64R64Effect 0x110fad 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[319, 316]
    (.letOp (n := 323) (.out 0x110fb2 (shlR64Effect 0x110fb2 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[316]
    (.letOp (n := 324) (.exec 0x110fb2 (fun s => s.RIP = 0x110fb2) (shlR64Effect 0x110fb2 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[316]
    (.letOp (n := 325) (.out 0x110fb6 (movR64Imm64Effect 0x110fb6 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 326) (.exec 0x110fb6 (fun s => s.RIP = 0x110fb6) (movR64Imm64Effect 0x110fb6 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 327) (.out 0x110fc0 (andR64R64Effect 0x110fc0 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[323, 325]
    (.letOp (n := 328) (.exec 0x110fc0 (fun s => s.RIP = 0x110fc0) (andR64R64Effect 0x110fc0 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[323, 325]
    (.letOp (n := 329) (.out 0x110fc3 (orR64R64Effect 0x110fc3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[327, 279]
    (.letOp (n := 330) (.exec 0x110fc3 (fun s => s.RIP = 0x110fc3) (orR64R64Effect 0x110fc3 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[327, 279]
    (.letOp (n := 331) (.out 0x110fc6 (movR64Imm64Effect 0x110fc6 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 332) (.exec 0x110fc6 (fun s => s.RIP = 0x110fc6) (movR64Imm64Effect 0x110fc6 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 333) (.out 0x110fd0 (mulR64Effect 0x110fd0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[331, 329]
    (.letOp (n := 334) (.out 0x110fd0 (mulR64Effect 0x110fd0 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[331, 329]
    (.letOp (n := 335) (.exec 0x110fd0 (fun s => s.RIP = 0x110fd0) (mulR64Effect 0x110fd0 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[331, 329]
    (.letOp (n := 336) (.out 0x110fd3 (addR64M64Effect 0x110fd3 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[333, 4]
    (.letOp (n := 337) (.out 0x110fd3 (addR64M64Effect 0x110fd3 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[333, 4]
    (.letOp (n := 338) (.exec 0x110fd3 (LoadPre 0x110fd3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110fd3 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x110fd3 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[333, 4]
    (.letOp (n := 339) (.exec 0x110fd8 (StorePre 0x110fd8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110fd8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110fd8 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[336, 4]
    (.letOp (n := 340) (.out 0x110fdd (movR64M64Effect 0x110fdd 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 341) (.exec 0x110fdd (LoadPre 0x110fdd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x110fdd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110fdd 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 342) (.out 0x110fe2 (atFlags StatusFlags.CF (adcR64R64Effect 0x110fe2 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[340, 334, 337]
    (.letOp (n := 343) (.exec 0x110fe2 (fun s => s.RIP = 0x110fe2) (atFlags StatusFlags.CF (adcR64R64Effect 0x110fe2 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[340, 334, 337]
    (b_l110d64_7))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_6 : List UInt8 :=
  [0x49, 0xF7, 0xE3, 0x4C, 0x01, 0xF8, 0x49, 0x11, 0xD0, 0x48, 0x01, 0xD8, 0x4D, 0x11, 0xF0, 0x48,
    0x01, 0xC8, 0x4C, 0x13, 0x44, 0x24, 0x30, 0x48, 0x01, 0xF8, 0x49, 0x83, 0xD0, 0x00, 0x49, 0x0F,
    0xA4, 0xC0, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x00, 0x48, 0x21, 0xC8, 0x4C, 0x09, 0xE0, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00,
    0x00, 0x48, 0xF7, 0xE1, 0x48, 0x03, 0x44, 0x24, 0x08, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x8B,
    0x4C, 0x24, 0x10, 0x48, 0x11, 0xD1] ++ bytes_l110d64_7

theorem code_l110d64_6 : ∀ x ∈ codeRange 0x110f8f bytes_l110d64_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10f8f 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_7

def b_l110d64_5 : Block Op Label signature Reg.count 256 :=
  .letOp (n := 256) (.out 0x110f3b (movR64M64Effect 0x110f3b 5 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 257) (.exec 0x110f3b (LoadPre 0x110f3b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x110f3b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110f3b 5 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 258) (.out 0x110f43 (movR64R64Effect 0x110f43 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[256]
    (.letOp (n := 259) (.exec 0x110f43 (fun s => s.RIP = 0x110f43) (movR64R64Effect 0x110f43 0 5) (Reg.operands [.gpr 5] [])) #v[256]
    (.letOp (n := 260) (.out 0x110f46 (movR64M64Effect 0x110f46 6 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 261) (.exec 0x110f46 (LoadPre 0x110f46 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x110f46 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110f46 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 262) (.out 0x110f4b (mulR64Effect 0x110f4b 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[260, 258]
    (.letOp (n := 263) (.out 0x110f4b (mulR64Effect 0x110f4b 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[260, 258]
    (.letOp (n := 264) (.exec 0x110f4b (fun s => s.RIP = 0x110f4b) (mulR64Effect 0x110f4b 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[260, 258]
    (.letOp (n := 265) (.exec 0x110f4e (StorePre 0x110f4e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x110f4e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110f4e 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[263, 4]
    (.letOp (n := 266) (.out 0x110f53 (movR64R64Effect 0x110f53 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[262]
    (.letOp (n := 267) (.exec 0x110f53 (fun s => s.RIP = 0x110f53) (movR64R64Effect 0x110f53 1 0) (Reg.operands [.gpr 0] [])) #v[262]
    (.letOp (n := 268) (.out 0x110f56 (movR64M64Effect 0x110f56 13 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 269) (.exec 0x110f56 (LoadPre 0x110f56 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x110f56 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110f56 13 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 270) (.out 0x110f5b (movR64R64Effect 0x110f5b 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[268]
    (.letOp (n := 271) (.exec 0x110f5b (fun s => s.RIP = 0x110f5b) (movR64R64Effect 0x110f5b 0 13) (Reg.operands [.gpr 13] [])) #v[268]
    (.letOp (n := 272) (.out 0x110f5e (mulR64Effect 0x110f5e 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[176, 270]
    (.letOp (n := 273) (.out 0x110f5e (mulR64Effect 0x110f5e 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[176, 270]
    (.letOp (n := 274) (.exec 0x110f5e (fun s => s.RIP = 0x110f5e) (mulR64Effect 0x110f5e 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[176, 270]
    (.letOp (n := 275) (.out 0x110f61 (movR64R64Effect 0x110f61 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[272]
    (.letOp (n := 276) (.exec 0x110f61 (fun s => s.RIP = 0x110f61) (movR64R64Effect 0x110f61 3 0) (Reg.operands [.gpr 0] [])) #v[272]
    (.letOp (n := 277) (.out 0x110f64 (movR64R64Effect 0x110f64 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[273]
    (.letOp (n := 278) (.exec 0x110f64 (fun s => s.RIP = 0x110f64) (movR64R64Effect 0x110f64 14 2) (Reg.operands [.gpr 2] [])) #v[273]
    (.letOp (n := 279) (.out 0x110f67 (andR32Imm8Effect 0x110f67 4 12 0xf) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[247]
    (.letOp (n := 280) (.exec 0x110f67 (fun s => s.RIP = 0x110f67) (andR32Imm8Effect 0x110f67 4 12 0xf) (Reg.operands [.gpr 12] [])) #v[247]
    (.letOp (n := 281) (.out 0x110f6b (movR64R64Effect 0x110f6b 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[172]
    (.letOp (n := 282) (.exec 0x110f6b (fun s => s.RIP = 0x110f6b) (movR64R64Effect 0x110f6b 0 11) (Reg.operands [.gpr 11] [])) #v[172]
    (.letOp (n := 283) (.out 0x110f6e (movR64M64Effect 0x110f6e 9 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 284) (.exec 0x110f6e (LoadPre 0x110f6e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x110f6e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110f6e 9 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 285) (.out 0x110f76 (mulR64Effect 0x110f76 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[283, 281]
    (.letOp (n := 286) (.out 0x110f76 (mulR64Effect 0x110f76 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[283, 281]
    (.letOp (n := 287) (.exec 0x110f76 (fun s => s.RIP = 0x110f76) (mulR64Effect 0x110f76 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[283, 281]
    (.letOp (n := 288) (.out 0x110f79 (movR64R64Effect 0x110f79 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[286]
    (.letOp (n := 289) (.exec 0x110f79 (fun s => s.RIP = 0x110f79) (movR64R64Effect 0x110f79 8 2) (Reg.operands [.gpr 2] [])) #v[286]
    (.letOp (n := 290) (.out 0x110f7c (movR64R64Effect 0x110f7c 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[285]
    (.letOp (n := 291) (.exec 0x110f7c (fun s => s.RIP = 0x110f7c) (movR64R64Effect 0x110f7c 15 0) (Reg.operands [.gpr 0] [])) #v[285]
    (.letOp (n := 292) (.out 0x110f7f (movR64M64Effect 0x110f7f 10 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 293) (.exec 0x110f7f (LoadPre 0x110f7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x110f7f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110f7f 10 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 294) (.out 0x110f84 (movR64R64Effect 0x110f84 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[292]
    (.letOp (n := 295) (.exec 0x110f84 (fun s => s.RIP = 0x110f84) (movR64R64Effect 0x110f84 0 10) (Reg.operands [.gpr 10] [])) #v[292]
    (.letOp (n := 296) (.out 0x110f87 (movR64M64Effect 0x110f87 11 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 297) (.exec 0x110f87 (LoadPre 0x110f87 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x110f87 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110f87 11 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l110d64_6))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_5 : List UInt8 :=
  [0x48, 0x8B, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE8, 0x48, 0x8B, 0x74, 0x24, 0x68,
    0x48, 0xF7, 0xE6, 0x48, 0x89, 0x54, 0x24, 0x30, 0x48, 0x89, 0xC1, 0x4C, 0x8B, 0x6C, 0x24, 0x70,
    0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xC3, 0x49, 0x89, 0xD6, 0x41, 0x83, 0xE4, 0x0F,
    0x4C, 0x89, 0xD8, 0x4C, 0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE1, 0x49, 0x89,
    0xD0, 0x49, 0x89, 0xC7, 0x4C, 0x8B, 0x54, 0x24, 0x78, 0x4C, 0x89, 0xD0, 0x4C, 0x8B, 0x9C, 0x24,
    0xA8, 0x00, 0x00, 0x00] ++ bytes_l110d64_6

theorem code_l110d64_5 : ∀ x ∈ codeRange 0x110f3b bytes_l110d64_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10f3b 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_6

def b_l110d64_4 : Block Op Label signature Reg.count 212 :=
  .letOp (n := 212) (.out 0x110eef (addR64R64Effect 0x110eef 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[203, 192]
    (.letOp (n := 213) (.out 0x110eef (addR64R64Effect 0x110eef 5 13) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 13] []) (.flag .CF)) #v[203, 192]
    (.letOp (n := 214) (.exec 0x110eef (fun s => s.RIP = 0x110eef) (addR64R64Effect 0x110eef 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[203, 192]
    (.letOp (n := 215) (.out 0x110ef2 (atFlags StatusFlags.CF (adcR64R64Effect 0x110ef2 7 12)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[201, 190, 213]
    (.letOp (n := 216) (.exec 0x110ef2 (fun s => s.RIP = 0x110ef2) (atFlags StatusFlags.CF (adcR64R64Effect 0x110ef2 7 12)) (Reg.operands [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[201, 190, 213]
    (.letOp (n := 217) (.out 0x110ef5 (addR64R64Effect 0x110ef5 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[212, 183]
    (.letOp (n := 218) (.out 0x110ef5 (addR64R64Effect 0x110ef5 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[212, 183]
    (.letOp (n := 219) (.exec 0x110ef5 (fun s => s.RIP = 0x110ef5) (addR64R64Effect 0x110ef5 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[212, 183]
    (.letOp (n := 220) (.out 0x110ef8 (atFlags StatusFlags.CF (adcR64R64Effect 0x110ef8 7 14)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[215, 181, 218]
    (.letOp (n := 221) (.exec 0x110ef8 (fun s => s.RIP = 0x110ef8) (atFlags StatusFlags.CF (adcR64R64Effect 0x110ef8 7 14)) (Reg.operands [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[215, 181, 218]
    (.letOp (n := 222) (.out 0x110efb (addR64R64Effect 0x110efb 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[217, 170]
    (.letOp (n := 223) (.out 0x110efb (addR64R64Effect 0x110efb 5 3) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 3] []) (.flag .CF)) #v[217, 170]
    (.letOp (n := 224) (.exec 0x110efb (fun s => s.RIP = 0x110efb) (addR64R64Effect 0x110efb 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[217, 170]
    (.letOp (n := 225) (.out 0x110efe (atFlags StatusFlags.CF (adcR64M64Effect 0x110efe 7 (.sib 4 none 0 (.d8 0x18)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[220, 4, 223]
    (.letOp (n := 226) (.exec 0x110efe (LoadPre 0x110efe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x110efe + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x110efe 7 (.sib 4 none 0 (.d8 0x18)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[220, 4, 223]
    (.letOp (n := 227) (.out 0x110f03 (addR64M64Effect 0x110f03 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[222, 4]
    (.letOp (n := 228) (.out 0x110f03 (addR64M64Effect 0x110f03 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[222, 4]
    (.letOp (n := 229) (.exec 0x110f03 (LoadPre 0x110f03 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110f03 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x110f03 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[222, 4]
    (.letOp (n := 230) (.out 0x110f08 (atFlags StatusFlags.CF (adcR64M64Effect 0x110f08 7 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[225, 4, 228]
    (.letOp (n := 231) (.exec 0x110f08 (LoadPre 0x110f08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x110f08 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x110f08 7 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[225, 4, 228]
    (.letOp (n := 232) (.out 0x110f0d (addR64R64Effect 0x110f0d 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[209, 227]
    (.letOp (n := 233) (.out 0x110f0d (addR64R64Effect 0x110f0d 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[209, 227]
    (.letOp (n := 234) (.exec 0x110f0d (fun s => s.RIP = 0x110f0d) (addR64R64Effect 0x110f0d 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[209, 227]
    (.letOp (n := 235) (.out 0x110f10 (atFlags StatusFlags.CF (adcR64R64Effect 0x110f10 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[230, 210, 233]
    (.letOp (n := 236) (.exec 0x110f10 (fun s => s.RIP = 0x110f10) (atFlags StatusFlags.CF (adcR64R64Effect 0x110f10 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[230, 210, 233]
    (.letOp (n := 237) (.out 0x110f13 (movR64R64Effect 0x110f13 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[232]
    (.letOp (n := 238) (.exec 0x110f13 (fun s => s.RIP = 0x110f13) (movR64R64Effect 0x110f13 12 0) (Reg.operands [.gpr 0] [])) #v[232]
    (.letOp (n := 239) (.out 0x110f16 (addR64R64Effect 0x110f16 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[237, 153]
    (.letOp (n := 240) (.out 0x110f16 (addR64R64Effect 0x110f16 12 6) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 6] []) (.flag .CF)) #v[237, 153]
    (.letOp (n := 241) (.exec 0x110f16 (fun s => s.RIP = 0x110f16) (addR64R64Effect 0x110f16 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[237, 153]
    (.letOp (n := 242) (.exec 0x110f19 (StorePre 0x110f19 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x110f19 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110f19 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[239, 4]
    (.letOp (n := 243) (.out 0x110f1e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x110f1e 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[235, 240]
    (.letOp (n := 244) (.exec 0x110f1e (fun s => s.RIP = 0x110f1e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x110f1e 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[235, 240]
    (.letOp (n := 245) (.out 0x110f22 (shldR64R64Effect 0x110f22 5 7 12 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[243, 239]
    (.letOp (n := 246) (.exec 0x110f22 (fun s => s.RIP = 0x110f22) (shldR64R64Effect 0x110f22 5 7 12 12) (Reg.operands [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[243, 239]
    (.letOp (n := 247) (.out 0x110f27 (shrR64Effect 0x110f27 4 12 48) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[239]
    (.letOp (n := 248) (.exec 0x110f27 (fun s => s.RIP = 0x110f27) (shrR64Effect 0x110f27 4 12 48) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[239]
    (.letOp (n := 249) (.out 0x110f2b (movR64R64Effect 0x110f2b 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[194]
    (.letOp (n := 250) (.exec 0x110f2b (fun s => s.RIP = 0x110f2b) (movR64R64Effect 0x110f2b 0 1) (Reg.operands [.gpr 1] [])) #v[194]
    (.letOp (n := 251) (.out 0x110f2e (mulR64Effect 0x110f2e 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[157, 249]
    (.letOp (n := 252) (.out 0x110f2e (mulR64Effect 0x110f2e 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[157, 249]
    (.letOp (n := 253) (.exec 0x110f2e (fun s => s.RIP = 0x110f2e) (mulR64Effect 0x110f2e 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[157, 249]
    (.letOp (n := 254) (.exec 0x110f31 (StorePre 0x110f31 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x110f31 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110f31 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[252, 4]
    (.letOp (n := 255) (.exec 0x110f36 (StorePre 0x110f36 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110f36 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110f36 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[251, 4]
    (b_l110d64_5))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_4 : List UInt8 :=
  [0x4C, 0x01, 0xED, 0x4C, 0x11, 0xE7, 0x4C, 0x01, 0xFD, 0x4C, 0x11, 0xF7, 0x48, 0x01, 0xDD, 0x48,
    0x13, 0x7C, 0x24, 0x18, 0x48, 0x03, 0x6C, 0x24, 0x08, 0x48, 0x13, 0x7C, 0x24, 0x10, 0x48, 0x01,
    0xE8, 0x48, 0x11, 0xD7, 0x49, 0x89, 0xC4, 0x49, 0x01, 0xF4, 0x4C, 0x89, 0x64, 0x24, 0x18, 0x48,
    0x83, 0xD7, 0x00, 0x4C, 0x0F, 0xA4, 0xE7, 0x0C, 0x49, 0xC1, 0xEC, 0x30, 0x48, 0x89, 0xC8, 0x49,
    0xF7, 0xE1, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x08] ++ bytes_l110d64_5

theorem code_l110d64_4 : ∀ x ∈ codeRange 0x110eef bytes_l110d64_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10eef 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_5

def b_l110d64_3 : Block Op Label signature Reg.count 169 :=
  .letOp (n := 169) (.exec 0x110e9c (StorePre 0x110e9c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x110e9c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110e9c 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[167, 4]
    (.letOp (n := 170) (.out 0x110ea1 (movR64R64Effect 0x110ea1 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[166]
    (.letOp (n := 171) (.exec 0x110ea1 (fun s => s.RIP = 0x110ea1) (movR64R64Effect 0x110ea1 3 0) (Reg.operands [.gpr 0] [])) #v[166]
    (.letOp (n := 172) (.out 0x110ea4 (movR64M64Effect 0x110ea4 11 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 173) (.exec 0x110ea4 (LoadPre 0x110ea4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x110ea4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110ea4 11 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 174) (.out 0x110eac (movR64R64Effect 0x110eac 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[172]
    (.letOp (n := 175) (.exec 0x110eac (fun s => s.RIP = 0x110eac) (movR64R64Effect 0x110eac 0 11) (Reg.operands [.gpr 11] [])) #v[172]
    (.letOp (n := 176) (.out 0x110eaf (movR64M64Effect 0x110eaf 10 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 177) (.exec 0x110eaf (LoadPre 0x110eaf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x110eaf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110eaf 10 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 178) (.out 0x110eb7 (mulR64Effect 0x110eb7 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[176, 174]
    (.letOp (n := 179) (.out 0x110eb7 (mulR64Effect 0x110eb7 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[176, 174]
    (.letOp (n := 180) (.exec 0x110eb7 (fun s => s.RIP = 0x110eb7) (mulR64Effect 0x110eb7 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[176, 174]
    (.letOp (n := 181) (.out 0x110eba (movR64R64Effect 0x110eba 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[179]
    (.letOp (n := 182) (.exec 0x110eba (fun s => s.RIP = 0x110eba) (movR64R64Effect 0x110eba 14 2) (Reg.operands [.gpr 2] [])) #v[179]
    (.letOp (n := 183) (.out 0x110ebd (movR64R64Effect 0x110ebd 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[178]
    (.letOp (n := 184) (.exec 0x110ebd (fun s => s.RIP = 0x110ebd) (movR64R64Effect 0x110ebd 15 0) (Reg.operands [.gpr 0] [])) #v[178]
    (.letOp (n := 185) (.out 0x110ec0 (movR64M64Effect 0x110ec0 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 186) (.exec 0x110ec0 (LoadPre 0x110ec0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x110ec0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110ec0 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 187) (.out 0x110ec5 (mulR64Effect 0x110ec5 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[93, 185]
    (.letOp (n := 188) (.out 0x110ec5 (mulR64Effect 0x110ec5 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[93, 185]
    (.letOp (n := 189) (.exec 0x110ec5 (fun s => s.RIP = 0x110ec5) (mulR64Effect 0x110ec5 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[93, 185]
    (.letOp (n := 190) (.out 0x110ec8 (movR64R64Effect 0x110ec8 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[188]
    (.letOp (n := 191) (.exec 0x110ec8 (fun s => s.RIP = 0x110ec8) (movR64R64Effect 0x110ec8 12 2) (Reg.operands [.gpr 2] [])) #v[188]
    (.letOp (n := 192) (.out 0x110ecb (movR64R64Effect 0x110ecb 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[187]
    (.letOp (n := 193) (.exec 0x110ecb (fun s => s.RIP = 0x110ecb) (movR64R64Effect 0x110ecb 13 0) (Reg.operands [.gpr 0] [])) #v[187]
    (.letOp (n := 194) (.out 0x110ece (movR64M64Effect 0x110ece 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 195) (.exec 0x110ece (LoadPre 0x110ece (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x110ece + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110ece 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 196) (.out 0x110ed3 (movR64R64Effect 0x110ed3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[194]
    (.letOp (n := 197) (.exec 0x110ed3 (fun s => s.RIP = 0x110ed3) (movR64R64Effect 0x110ed3 0 1) (Reg.operands [.gpr 1] [])) #v[194]
    (.letOp (n := 198) (.out 0x110ed6 (mulR64Effect 0x110ed6 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[106, 196]
    (.letOp (n := 199) (.out 0x110ed6 (mulR64Effect 0x110ed6 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[106, 196]
    (.letOp (n := 200) (.exec 0x110ed6 (fun s => s.RIP = 0x110ed6) (mulR64Effect 0x110ed6 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[106, 196]
    (.letOp (n := 201) (.out 0x110ed9 (movR64R64Effect 0x110ed9 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[199]
    (.letOp (n := 202) (.exec 0x110ed9 (fun s => s.RIP = 0x110ed9) (movR64R64Effect 0x110ed9 7 2) (Reg.operands [.gpr 2] [])) #v[199]
    (.letOp (n := 203) (.out 0x110edc (movR64R64Effect 0x110edc 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[198]
    (.letOp (n := 204) (.exec 0x110edc (fun s => s.RIP = 0x110edc) (movR64R64Effect 0x110edc 5 0) (Reg.operands [.gpr 0] [])) #v[198]
    (.letOp (n := 205) (.out 0x110edf (movR64R64Effect 0x110edf 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[151]
    (.letOp (n := 206) (.exec 0x110edf (fun s => s.RIP = 0x110edf) (movR64R64Effect 0x110edf 0 8) (Reg.operands [.gpr 8] [])) #v[151]
    (.letOp (n := 207) (.out 0x110ee2 (movR64Imm64Effect 0x110ee2 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 208) (.exec 0x110ee2 (fun s => s.RIP = 0x110ee2) (movR64Imm64Effect 0x110ee2 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 209) (.out 0x110eec (mulR64Effect 0x110eec 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[207, 205]
    (.letOp (n := 210) (.out 0x110eec (mulR64Effect 0x110eec 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[207, 205]
    (.letOp (n := 211) (.exec 0x110eec (fun s => s.RIP = 0x110eec) (mulR64Effect 0x110eec 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[207, 205]
    (b_l110d64_4)))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_3 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x18, 0x48, 0x89, 0xC3, 0x4C, 0x8B, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x4C, 0x89, 0xD8, 0x4C, 0x8B, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x49, 0x89,
    0xD6, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x44, 0x24, 0x78, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD4, 0x49,
    0x89, 0xC5, 0x48, 0x8B, 0x4C, 0x24, 0x50, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD7,
    0x48, 0x89, 0xC5, 0x4C, 0x89, 0xC0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x48, 0xF7, 0xE2] ++ bytes_l110d64_4

theorem code_l110d64_3 : ∀ x ∈ codeRange 0x110e9c bytes_l110d64_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10e9c 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_4

def b_l110d64_2 : Block Op Label signature Reg.count 125 :=
  .letOp (n := 125) (.out 0x110e41 (movR64Imm64Effect 0x110e41 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 126) (.exec 0x110e41 (fun s => s.RIP = 0x110e41) (movR64Imm64Effect 0x110e41 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 127) (.out 0x110e4b (mulR64Effect 0x110e4b 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[125, 123]
    (.letOp (n := 128) (.out 0x110e4b (mulR64Effect 0x110e4b 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[125, 123]
    (.letOp (n := 129) (.exec 0x110e4b (fun s => s.RIP = 0x110e4b) (mulR64Effect 0x110e4b 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[125, 123]
    (.letOp (n := 130) (.out 0x110e4e (addR64R64Effect 0x110e4e 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[102, 89]
    (.letOp (n := 131) (.out 0x110e4e (addR64R64Effect 0x110e4e 3 12) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 12] []) (.flag .CF)) #v[102, 89]
    (.letOp (n := 132) (.exec 0x110e4e (fun s => s.RIP = 0x110e4e) (addR64R64Effect 0x110e4e 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[102, 89]
    (.letOp (n := 133) (.out 0x110e51 (atFlags StatusFlags.CF (adcR64R64Effect 0x110e51 6 15)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[104, 91, 131]
    (.letOp (n := 134) (.exec 0x110e51 (fun s => s.RIP = 0x110e51) (atFlags StatusFlags.CF (adcR64R64Effect 0x110e51 6 15)) (Reg.operands [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[104, 91, 131]
    (.letOp (n := 135) (.out 0x110e54 (addR64R64Effect 0x110e54 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[130, 77]
    (.letOp (n := 136) (.out 0x110e54 (addR64R64Effect 0x110e54 3 9) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 9] []) (.flag .CF)) #v[130, 77]
    (.letOp (n := 137) (.exec 0x110e54 (fun s => s.RIP = 0x110e54) (addR64R64Effect 0x110e54 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[130, 77]
    (.letOp (n := 138) (.out 0x110e57 (atFlags StatusFlags.CF (adcR64M64Effect 0x110e57 6 (.sib 4 none 0 (.d32 0xb8)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[133, 4, 136]
    (.letOp (n := 139) (.exec 0x110e57 (LoadPre 0x110e57 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x110e57 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x110e57 6 (.sib 4 none 0 (.d32 0xb8)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[133, 4, 136]
    (.letOp (n := 140) (.out 0x110e5f (addR64M64Effect 0x110e5f 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[135, 4]
    (.letOp (n := 141) (.out 0x110e5f (addR64M64Effect 0x110e5f 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[135, 4]
    (.letOp (n := 142) (.exec 0x110e5f (LoadPre 0x110e5f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110e5f + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x110e5f 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[135, 4]
    (.letOp (n := 143) (.out 0x110e64 (atFlags StatusFlags.CF (adcR64M64Effect 0x110e64 6 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[138, 4, 141]
    (.letOp (n := 144) (.exec 0x110e64 (LoadPre 0x110e64 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x110e64 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x110e64 6 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[138, 4, 141]
    (.letOp (n := 145) (.out 0x110e69 (addR64R64Effect 0x110e69 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[127, 140]
    (.letOp (n := 146) (.out 0x110e69 (addR64R64Effect 0x110e69 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[127, 140]
    (.letOp (n := 147) (.exec 0x110e69 (fun s => s.RIP = 0x110e69) (addR64R64Effect 0x110e69 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[127, 140]
    (.letOp (n := 148) (.exec 0x110e6c (StorePre 0x110e6c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x110e6c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110e6c 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[145, 4]
    (.letOp (n := 149) (.out 0x110e74 (atFlags StatusFlags.CF (adcR64R64Effect 0x110e74 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[143, 128, 146]
    (.letOp (n := 150) (.exec 0x110e74 (fun s => s.RIP = 0x110e74) (atFlags StatusFlags.CF (adcR64R64Effect 0x110e74 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[143, 128, 146]
    (.letOp (n := 151) (.out 0x110e77 (shldR64R64Effect 0x110e77 5 8 14 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[119, 117]
    (.letOp (n := 152) (.exec 0x110e77 (fun s => s.RIP = 0x110e77) (shldR64R64Effect 0x110e77 5 8 14 12) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119, 117]
    (.letOp (n := 153) (.out 0x110e7c (shldR64R64Effect 0x110e7c 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[149, 145]
    (.letOp (n := 154) (.exec 0x110e7c (fun s => s.RIP = 0x110e7c) (shldR64R64Effect 0x110e7c 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[149, 145]
    (.letOp (n := 155) (.out 0x110e81 (movR64R64Effect 0x110e81 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[108]
    (.letOp (n := 156) (.exec 0x110e81 (fun s => s.RIP = 0x110e81) (movR64R64Effect 0x110e81 0 13) (Reg.operands [.gpr 13] [])) #v[108]
    (.letOp (n := 157) (.out 0x110e84 (movR64M64Effect 0x110e84 9 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 158) (.exec 0x110e84 (LoadPre 0x110e84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x110e84 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110e84 9 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 159) (.out 0x110e89 (mulR64Effect 0x110e89 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[157, 155]
    (.letOp (n := 160) (.out 0x110e89 (mulR64Effect 0x110e89 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[157, 155]
    (.letOp (n := 161) (.exec 0x110e89 (fun s => s.RIP = 0x110e89) (mulR64Effect 0x110e89 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[157, 155]
    (.letOp (n := 162) (.exec 0x110e8c (StorePre 0x110e8c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x110e8c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110e8c 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[160, 4]
    (.letOp (n := 163) (.exec 0x110e91 (StorePre 0x110e91 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110e91 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110e91 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[159, 4]
    (.letOp (n := 164) (.out 0x110e96 (movR64R64Effect 0x110e96 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[61]
    (.letOp (n := 165) (.exec 0x110e96 (fun s => s.RIP = 0x110e96) (movR64R64Effect 0x110e96 0 11) (Reg.operands [.gpr 11] [])) #v[61]
    (.letOp (n := 166) (.out 0x110e99 (mulR64Effect 0x110e99 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[56, 164]
    (.letOp (n := 167) (.out 0x110e99 (mulR64Effect 0x110e99 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[56, 164]
    (.letOp (n := 168) (.exec 0x110e99 (fun s => s.RIP = 0x110e99) (mulR64Effect 0x110e99 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[56, 164]
    (b_l110d64_3))))))))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_2 : List UInt8 :=
  [0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x4C, 0x01, 0xE3,
    0x4C, 0x11, 0xFE, 0x4C, 0x01, 0xCB, 0x48, 0x13, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x03,
    0x5C, 0x24, 0x08, 0x48, 0x13, 0x74, 0x24, 0x10, 0x48, 0x01, 0xD8, 0x48, 0x89, 0x84, 0x24, 0xB8,
    0x00, 0x00, 0x00, 0x48, 0x11, 0xD6, 0x4D, 0x0F, 0xA4, 0xF0, 0x0C, 0x48, 0x0F, 0xA4, 0xC6, 0x0C,
    0x4C, 0x89, 0xE8, 0x4C, 0x8B, 0x4C, 0x24, 0x38, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x54, 0x24, 0x10,
    0x48, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x89, 0xD8, 0x49, 0xF7, 0xE2] ++ bytes_l110d64_3

theorem code_l110d64_2 : ∀ x ∈ codeRange 0x110e41 bytes_l110d64_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10e41 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_3

def b_l110d64_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.out 0x110dd9 (mulR64Effect 0x110dd9 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[80, 83]
    (.letOp (n := 87) (.out 0x110dd9 (mulR64Effect 0x110dd9 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[80, 83]
    (.letOp (n := 88) (.exec 0x110dd9 (fun s => s.RIP = 0x110dd9) (mulR64Effect 0x110dd9 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[80, 83]
    (.letOp (n := 89) (.out 0x110ddc (movR64R64Effect 0x110ddc 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[86]
    (.letOp (n := 90) (.exec 0x110ddc (fun s => s.RIP = 0x110ddc) (movR64R64Effect 0x110ddc 12 0) (Reg.operands [.gpr 0] [])) #v[86]
    (.letOp (n := 91) (.out 0x110ddf (movR64R64Effect 0x110ddf 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[87]
    (.letOp (n := 92) (.exec 0x110ddf (fun s => s.RIP = 0x110ddf) (movR64R64Effect 0x110ddf 15 2) (Reg.operands [.gpr 2] [])) #v[87]
    (.letOp (n := 93) (.out 0x110de2 (movR64M64Effect 0x110de2 5 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 94) (.exec 0x110de2 (LoadPre 0x110de2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x110de2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110de2 5 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x110dea (movR64M64Effect 0x110dea 0 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 96) (.exec 0x110dea (LoadPre 0x110dea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x110dea + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110dea 0 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.exec 0x110df2 (StorePre 0x110df2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x110df2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110df2 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 98) (.out 0x110df7 (mulR64Effect 0x110df7 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[93, 95]
    (.letOp (n := 99) (.out 0x110df7 (mulR64Effect 0x110df7 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[93, 95]
    (.letOp (n := 100) (.exec 0x110df7 (fun s => s.RIP = 0x110df7) (mulR64Effect 0x110df7 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[93, 95]
    (.letOp (n := 101) (.exec 0x110dfa (StorePre 0x110dfa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x110dfa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110dfa 5 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[93, 4]
    (.letOp (n := 102) (.out 0x110e02 (movR64R64Effect 0x110e02 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[98]
    (.letOp (n := 103) (.exec 0x110e02 (fun s => s.RIP = 0x110e02) (movR64R64Effect 0x110e02 3 0) (Reg.operands [.gpr 0] [])) #v[98]
    (.letOp (n := 104) (.out 0x110e05 (movR64R64Effect 0x110e05 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[99]
    (.letOp (n := 105) (.exec 0x110e05 (fun s => s.RIP = 0x110e05) (movR64R64Effect 0x110e05 6 2) (Reg.operands [.gpr 2] [])) #v[99]
    (.letOp (n := 106) (.out 0x110e08 (movR64M64Effect 0x110e08 7 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 107) (.exec 0x110e08 (LoadPre 0x110e08 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x110e08 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110e08 7 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 108) (.out 0x110e10 (movR64M64Effect 0x110e10 13 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 109) (.exec 0x110e10 (LoadPre 0x110e10 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x110e10 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110e10 13 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 110) (.out 0x110e18 (movR64R64Effect 0x110e18 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[108]
    (.letOp (n := 111) (.exec 0x110e18 (fun s => s.RIP = 0x110e18) (movR64R64Effect 0x110e18 0 13) (Reg.operands [.gpr 13] [])) #v[108]
    (.letOp (n := 112) (.exec 0x110e1b (StorePre 0x110e1b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x110e1b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110e1b 13 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[108, 4]
    (.letOp (n := 113) (.out 0x110e23 (mulR64Effect 0x110e23 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[106, 110]
    (.letOp (n := 114) (.out 0x110e23 (mulR64Effect 0x110e23 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[106, 110]
    (.letOp (n := 115) (.exec 0x110e23 (fun s => s.RIP = 0x110e23) (mulR64Effect 0x110e23 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[106, 110]
    (.letOp (n := 116) (.exec 0x110e26 (StorePre 0x110e26 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x110e26 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110e26 7 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[106, 4]
    (.letOp (n := 117) (.out 0x110e2e (movR64R64Effect 0x110e2e 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[113]
    (.letOp (n := 118) (.exec 0x110e2e (fun s => s.RIP = 0x110e2e) (movR64R64Effect 0x110e2e 14 0) (Reg.operands [.gpr 0] [])) #v[113]
    (.letOp (n := 119) (.out 0x110e31 (movR64R64Effect 0x110e31 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[114]
    (.letOp (n := 120) (.exec 0x110e31 (fun s => s.RIP = 0x110e31) (movR64R64Effect 0x110e31 8 2) (Reg.operands [.gpr 2] [])) #v[114]
    (.letOp (n := 121) (.out 0x110e34 (movR64Imm64Effect 0x110e34 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 122) (.exec 0x110e34 (fun s => s.RIP = 0x110e34) (movR64Imm64Effect 0x110e34 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 123) (.out 0x110e3e (andR64R64Effect 0x110e3e 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[113, 121]
    (.letOp (n := 124) (.exec 0x110e3e (fun s => s.RIP = 0x110e3e) (andR64R64Effect 0x110e3e 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[113, 121]
    (b_l110d64_2)))))))))))))))))))))))))))))))))))))))

def bytes_l110d64_1 : List UInt8 :=
  [0x48, 0xF7, 0xE1, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD7, 0x48, 0x8B, 0xAC, 0x24, 0x40, 0x01, 0x00,
    0x00, 0x48, 0x8B, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0xF7,
    0xE5, 0x48, 0x89, 0xAC, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC3, 0x48, 0x89, 0xD6, 0x48,
    0x8B, 0xBC, 0x24, 0x48, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0xAC, 0x24, 0x70, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0xE8, 0x4C, 0x89, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xBC,
    0x24, 0xA8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC6, 0x49, 0x89, 0xD0, 0x48, 0xB9, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8] ++ bytes_l110d64_2

theorem code_l110d64_1 : ∀ x ∈ codeRange 0x110dd9 bytes_l110d64_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10dd9 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_2

def b_l110d64 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110d64 (movR64M64Effect 0x110d64 2 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x110d64 (LoadPre 0x110d64 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x110d64 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110d64 2 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x110d6c (StorePre 0x110d6c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x110d6c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110d6c 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x110d71 (movR64M64Effect 0x110d71 10 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 57) (.exec 0x110d71 (LoadPre 0x110d71 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x110d71 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110d71 10 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x110d79 (movR64M64Effect 0x110d79 1 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x110d79 (LoadPre 0x110d79 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x110d79 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110d79 1 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x110d81 (StorePre 0x110d81 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x110d81 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110d81 1 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x110d89 (movR64M64Effect 0x110d89 11 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 62) (.exec 0x110d89 (LoadPre 0x110d89 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x110d89 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110d89 11 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x110d91 (movR64R64Effect 0x110d91 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[61]
    (.letOp (n := 64) (.exec 0x110d91 (fun s => s.RIP = 0x110d91) (movR64R64Effect 0x110d91 0 11) (Reg.operands [.gpr 11] [])) #v[61]
    (.letOp (n := 65) (.exec 0x110d94 (StorePre 0x110d94 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x110d94 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110d94 11 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 66) (.out 0x110d99 (mulR64Effect 0x110d99 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[53, 63]
    (.letOp (n := 67) (.out 0x110d99 (mulR64Effect 0x110d99 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[53, 63]
    (.letOp (n := 68) (.exec 0x110d99 (fun s => s.RIP = 0x110d99) (mulR64Effect 0x110d99 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 63]
    (.letOp (n := 69) (.exec 0x110d9c (StorePre 0x110d9c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x110d9c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110d9c 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.exec 0x110da1 (StorePre 0x110da1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110da1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110da1 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 71) (.out 0x110da6 (movR64R64Effect 0x110da6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[58]
    (.letOp (n := 72) (.exec 0x110da6 (fun s => s.RIP = 0x110da6) (movR64R64Effect 0x110da6 0 1) (Reg.operands [.gpr 1] [])) #v[58]
    (.letOp (n := 73) (.out 0x110da9 (mulR64Effect 0x110da9 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[56, 71]
    (.letOp (n := 74) (.out 0x110da9 (mulR64Effect 0x110da9 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[56, 71]
    (.letOp (n := 75) (.exec 0x110da9 (fun s => s.RIP = 0x110da9) (mulR64Effect 0x110da9 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[56, 71]
    (.letOp (n := 76) (.exec 0x110dac (StorePre 0x110dac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x110dac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110dac 10 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 77) (.out 0x110db1 (movR64R64Effect 0x110db1 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[73]
    (.letOp (n := 78) (.exec 0x110db1 (fun s => s.RIP = 0x110db1) (movR64R64Effect 0x110db1 9 0) (Reg.operands [.gpr 0] [])) #v[73]
    (.letOp (n := 79) (.exec 0x110db4 (StorePre 0x110db4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x110db4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110db4 2 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 80) (.out 0x110dbc (movR64M64Effect 0x110dbc 1 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 81) (.exec 0x110dbc (LoadPre 0x110dbc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x110dbc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110dbc 1 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x110dc4 (StorePre 0x110dc4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x110dc4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110dc4 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.out 0x110dcc (movR64M64Effect 0x110dcc 0 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 84) (.exec 0x110dcc (LoadPre 0x110dcc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x110dcc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110dcc 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.exec 0x110dd4 (StorePre 0x110dd4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x110dd4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110dd4 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 4]
    (b_l110d64_1)))))))))))))))))))))))))))))))))

def bytes_l110d64 : List UInt8 :=
  [0x48, 0x8B, 0x94, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x38, 0x4C, 0x8B, 0x94,
    0x24, 0x30, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x89, 0x8C,
    0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x9C, 0x24, 0x68, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xD8,
    0x4C, 0x89, 0x5C, 0x24, 0x70, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x89, 0x44,
    0x24, 0x08, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE2, 0x4C, 0x89, 0x54, 0x24, 0x68, 0x49, 0x89, 0xC1,
    0x48, 0x89, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x38, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x44, 0x24, 0x78] ++ bytes_l110d64_1

theorem code_l110d64 : ∀ x ∈ codeRange 0x110d64 bytes_l110d64, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10d64 117 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110d64_1

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

@[cfg_block] def b_l115408 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x115408 (subR64Imm8Effect 0x115408 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x115408 (fun s => s.RIP = 0x115408) (subR64Imm8Effect 0x115408 4 0x18) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11540c (movR64R64Effect 0x11540c 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[9]
    (.letOp (n := 56) (.exec 0x11540c (fun s => s.RIP = 0x11540c) (movR64R64Effect 0x11540c 0 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 57) (.out 0x11540f (movR64R64Effect 0x11540f 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[8]
    (.letOp (n := 58) (.exec 0x11540f (fun s => s.RIP = 0x11540f) (movR64R64Effect 0x11540f 10 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 59) (.out 0x115412 (movR64R64Effect 0x115412 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[1]
    (.letOp (n := 60) (.exec 0x115412 (fun s => s.RIP = 0x115412) (movR64R64Effect 0x115412 9 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 61) (.out 0x115415 (leaR64Effect 0x115415 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 62) (.exec 0x115415 (fun s => s.RIP = 0x115415) (leaR64Effect 0x115415 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 63) (.exec 0x11541a (StorePre 0x11541a 3 (fun s => AddrMode.addr (.base 8 .none) s (0x11541a + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11541a 6 (.base 8 .none)) (Reg.operands [.gpr 6, .gpr 8] [])) #v[6, 61]
    (.letOp (n := 64) (.out 0x11541d (leaR64Effect 0x11541d 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 65) (.exec 0x11541d (fun s => s.RIP = 0x11541d) (leaR64Effect 0x11541d 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 66) (.exec 0x115422 (StorePre 0x115422 3 (fun s => AddrMode.addr (.base 1 .none) s (0x115422 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x115422 2 (.base 1 .none)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2, 64]
    (.letOp (n := 67) (.out 0x115425 (movR64R64Effect 0x115425 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 68) (.exec 0x115425 (fun s => s.RIP = 0x115425) (movR64R64Effect 0x115425 6 8) (Reg.operands [.gpr 8] [])) #v[61]
    (.letOp (n := 69) (.out 0x115428 (movR64Imm32Effect 0x115428 2 0x202e98) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 70) (.exec 0x115428 (fun s => s.RIP = 0x115428) (movR64Imm32Effect 0x115428 2 0x202e98) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x11542f (movR64Imm32Effect 0x11542f 8 0x202e98) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 72) (.exec 0x11542f (fun s => s.RIP = 0x11542f) (movR64Imm32Effect 0x11542f 8 0x202e98) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x115436 (pushR64Effect 0x115436 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[53, 55]
    (.letOp (n := 74) (.exec 0x115436 (PushPre 0x115436 1) (pushR64Effect 0x115436 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[53, 55]
    (.letOp (n := 75) (.out 0x115437 (pushR64Effect 0x115437 2 10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 10] []) (.reg (.gpr 4))) #v[73, 57]
    (.letOp (n := 76) (.exec 0x115437 (PushPre 0x115437 2) (pushR64Effect 0x115437 2 10) (Reg.operands [.gpr 4, .gpr 10] [])) #v[73, 57]
    (.letOp (n := 77) (.out 0x115439 (callEffect (fun _ => 0x12965d) 0x11543e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[75]
    (.letOp (n := 78) (.exec 0x115439 (PushPre 0x115439 5) (callEffect (fun _ => 0x12965d) 0x11543e) (Reg.operands [.gpr 4] [])) #v[75]
    (.letOp (n := 79) (.const ⟨64, 0x11543e⟩) #v[]
    (.terminate (.call ⟨.l12965d, RegMap.args [(0, 55), (1, 64), (2, 69), (4, 77), (5, 5), (6, 67), (7, 7), (8, 71), (9, 59), (10, 57)] 80⟩ { target := .l11543e, kept := #v[], arity := rfl, guard := some (Fin.last 79) }))))))))))))))))))))))))))))

def bytes_l115408 : List UInt8 :=
  [0x48, 0x83, 0xEC, 0x18, 0x4C, 0x89, 0xC8, 0x4D, 0x89, 0xC2, 0x49, 0x89, 0xC9, 0x4C, 0x8D, 0x44,
    0x24, 0x08, 0x49, 0x89, 0x30, 0x48, 0x8D, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x11, 0x4C, 0x89, 0xC6,
    0x48, 0xC7, 0xC2, 0x98, 0x2E, 0x20, 0x00, 0x49, 0xC7, 0xC0, 0x98, 0x2E, 0x20, 0x00, 0x50, 0x41,
    0x52, 0xE8, 0x1F, 0x42, 0x01, 0x00]

theorem code_l115408 : ∀ x ∈ codeRange 0x115408 bytes_l115408, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15408 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Signing.LIR
