import K256.Proofs.Verify.LIR.Defs18
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

def b_l121930_98 : Block Op Label signature Reg.count 3877 :=
  .letOp (n := 3877) (.out 0x1230a2 (xorR32R32Effect 0x1230a2 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3875, 3871]
    (.letOp (n := 3878) (.exec 0x1230a2 (fun s => s.RIP = 0x1230a2) (xorR32R32Effect 0x1230a2 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3875, 3871]
    (.letOp (n := 3879) (.out 0x1230a4 (movR32R32Effect 0x1230a4 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[3721]
    (.letOp (n := 3880) (.exec 0x1230a4 (fun s => s.RIP = 0x1230a4) (movR32R32Effect 0x1230a4 3 2 13) (Reg.operands [.gpr 13] [])) #v[3721]
    (.letOp (n := 3881) (.out 0x1230a7 (xorR32R32Effect 0x1230a7 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[3879, 3611]
    (.letOp (n := 3882) (.exec 0x1230a7 (fun s => s.RIP = 0x1230a7) (xorR32R32Effect 0x1230a7 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[3879, 3611]
    (.letOp (n := 3883) (.out 0x1230aa (andR32R32Effect 0x1230aa 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[3881, 3819]
    (.letOp (n := 3884) (.exec 0x1230aa (fun s => s.RIP = 0x1230aa) (andR32R32Effect 0x1230aa 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[3881, 3819]
    (.letOp (n := 3885) (.out 0x1230ad (xorR32R32Effect 0x1230ad 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[3883, 3611]
    (.letOp (n := 3886) (.exec 0x1230ad (fun s => s.RIP = 0x1230ad) (xorR32R32Effect 0x1230ad 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[3883, 3611]
    (.letOp (n := 3887) (.out 0x1230b0 (addR32R32Effect 0x1230b0 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[3501, 3861]
    (.letOp (n := 3888) (.exec 0x1230b0 (fun s => s.RIP = 0x1230b0) (addR32R32Effect 0x1230b0 3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[3501, 3861]
    (.letOp (n := 3889) (.out 0x1230b3 (addR32R32Effect 0x1230b3 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[3887, 3885]
    (.letOp (n := 3890) (.exec 0x1230b3 (fun s => s.RIP = 0x1230b3) (addR32R32Effect 0x1230b3 3 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[3887, 3885]
    (.letOp (n := 3891) (.out 0x1230b6 (movR32R32Effect 0x1230b6 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[3821]
    (.letOp (n := 3892) (.exec 0x1230b6 (fun s => s.RIP = 0x1230b6) (movR32R32Effect 0x1230b6 2 2 7) (Reg.operands [.gpr 7] [])) #v[3821]
    (.letOp (n := 3893) (.out 0x1230b8 (rolR32Effect 0x1230b8 3 2 30) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3891]
    (.letOp (n := 3894) (.exec 0x1230b8 (fun s => s.RIP = 0x1230b8) (rolR32Effect 0x1230b8 3 2 30) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3891]
    (.letOp (n := 3895) (.out 0x1230bb (leaR32Effect 0x1230bb 4 6 (.sib 0 (some 9) 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0, .gpr 9] []) (.reg (.gpr 6))) #v[3877, 3889]
    (.letOp (n := 3896) (.exec 0x1230bb (fun s => s.RIP = 0x1230bb) (leaR32Effect 0x1230bb 4 6 (.sib 0 (some 9) 0 .none)) (Reg.operands [.gpr 0, .gpr 9] [])) #v[3877, 3889]
    (.letOp (n := 3897) (.out 0x1230bf (addR32Imm32Effect 0x1230bf 6 6 0x650a7354) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[3895]
    (.letOp (n := 3898) (.exec 0x1230bf (fun s => s.RIP = 0x1230bf) (addR32Imm32Effect 0x1230bf 6 6 0x650a7354) (Reg.operands [.gpr 6] [])) #v[3895]
    (.letOp (n := 3899) (.out 0x1230c5 (movR32R32Effect 0x1230c5 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[3821]
    (.letOp (n := 3900) (.exec 0x1230c5 (fun s => s.RIP = 0x1230c5) (movR32R32Effect 0x1230c5 2 0 7) (Reg.operands [.gpr 7] [])) #v[3821]
    (.letOp (n := 3901) (.out 0x1230c7 (rolR32Effect 0x1230c7 3 0 19) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3899]
    (.letOp (n := 3902) (.exec 0x1230c7 (fun s => s.RIP = 0x1230c7) (rolR32Effect 0x1230c7 3 0 19) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3899]
    (.letOp (n := 3903) (.out 0x1230ca (xorR32R32Effect 0x1230ca 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3901, 3893]
    (.letOp (n := 3904) (.exec 0x1230ca (fun s => s.RIP = 0x1230ca) (xorR32R32Effect 0x1230ca 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3901, 3893]
    (.letOp (n := 3905) (.out 0x1230cc (movR32R32Effect 0x1230cc 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[3821]
    (.letOp (n := 3906) (.exec 0x1230cc (fun s => s.RIP = 0x1230cc) (movR32R32Effect 0x1230cc 2 2 7) (Reg.operands [.gpr 7] [])) #v[3821]
    (.letOp (n := 3907) (.out 0x1230ce (rolR32Effect 0x1230ce 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3905]
    (.letOp (n := 3908) (.exec 0x1230ce (fun s => s.RIP = 0x1230ce) (rolR32Effect 0x1230ce 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3905]
    (.letOp (n := 3909) (.out 0x1230d1 (xorR32R32Effect 0x1230d1 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3907, 3903]
    (.letOp (n := 3910) (.exec 0x1230d1 (fun s => s.RIP = 0x1230d1) (xorR32R32Effect 0x1230d1 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3907, 3903]
    (.letOp (n := 3911) (.out 0x1230d3 (movR32R32Effect 0x1230d3 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[3727]
    (.letOp (n := 3912) (.exec 0x1230d3 (fun s => s.RIP = 0x1230d3) (movR32R32Effect 0x1230d3 3 9 14) (Reg.operands [.gpr 14] [])) #v[3727]
    (.letOp (n := 3913) (.out 0x1230d6 (andR32R32Effect 0x1230d6 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[3911, 3617]
    (.letOp (n := 3914) (.exec 0x1230d6 (fun s => s.RIP = 0x1230d6) (andR32R32Effect 0x1230d6 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[3911, 3617]
    (.letOp (n := 3915) (.out 0x1230d9 (movR32R32Effect 0x1230d9 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[3727]
    (.letOp (n := 3916) (.exec 0x1230d9 (fun s => s.RIP = 0x1230d9) (movR32R32Effect 0x1230d9 3 0 14) (Reg.operands [.gpr 14] [])) #v[3727]
    (b_l121930_99))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_98 : List UInt8 :=
  [0x31, 0xD0, 0x44, 0x89, 0xEA, 0x44, 0x31, 0xDA, 0x44, 0x21, 0xC2, 0x44, 0x31, 0xDA, 0x41, 0x01,
    0xD9, 0x41, 0x01, 0xD1, 0x89, 0xFA, 0xC1, 0xC2, 0x1E, 0x42, 0x8D, 0x34, 0x08, 0x81, 0xC6, 0x54,
    0x73, 0x0A, 0x65, 0x89, 0xF8, 0xC1, 0xC0, 0x13, 0x31, 0xD0, 0x89, 0xFA, 0xC1, 0xC2, 0x0A, 0x31,
    0xC2, 0x45, 0x89, 0xF1, 0x45, 0x21, 0xD1, 0x44, 0x89, 0xF0] ++ bytes_l121930_99

theorem code_l121930_98 : ∀ x ∈ codeRange 0x1230a2 bytes_l121930_98, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x230a2 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_99

def b_l121930_97 : Block Op Label signature Reg.count 3839 :=
  .letOp (n := 3839) (.out 0x123069 (rolR32Effect 0x123069 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3837]
    (.letOp (n := 3840) (.exec 0x123069 (fun s => s.RIP = 0x123069) (rolR32Effect 0x123069 3 6 14) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3837]
    (.letOp (n := 3841) (.out 0x12306c (xorR32R32Effect 0x12306c 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[3839, 3835]
    (.letOp (n := 3842) (.exec 0x12306c (fun s => s.RIP = 0x12306c) (xorR32R32Effect 0x12306c 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[3839, 3835]
    (.letOp (n := 3843) (.out 0x12306e (movR32R32Effect 0x12306e 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[3763]
    (.letOp (n := 3844) (.exec 0x12306e (fun s => s.RIP = 0x12306e) (movR32R32Effect 0x12306e 2 2 5) (Reg.operands [.gpr 5] [])) #v[3763]
    (.letOp (n := 3845) (.out 0x123070 (shrR32Effect 0x123070 3 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3843]
    (.letOp (n := 3846) (.exec 0x123070 (fun s => s.RIP = 0x123070) (shrR32Effect 0x123070 3 2 3) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3843]
    (.letOp (n := 3847) (.out 0x123073 (xorR32R32Effect 0x123073 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[3845, 3841]
    (.letOp (n := 3848) (.exec 0x123073 (fun s => s.RIP = 0x123073) (xorR32R32Effect 0x123073 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[3845, 3841]
    (.letOp (n := 3849) (.exec 0x123075 (StorePre 0x123075 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x123075 + BitVec.ofNat 64 4)) 4) (addMREffect 0x123075 4 32 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 15, .gpr 4] [])) #v[3653, 4]
    (.letOp (n := 3850) (.out 0x123079 (addR32R32Effect 0x123079 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[3847, 3653]
    (.letOp (n := 3851) (.exec 0x123079 (fun s => s.RIP = 0x123079) (addR32R32Effect 0x123079 3 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[3847, 3653]
    (.letOp (n := 3852) (.exec 0x12307c (StorePre 0x12307c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12307c + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x12307c 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3850, 4]
    (.letOp (n := 3853) (.out 0x123080 (movR32R32Effect 0x123080 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[3653]
    (.letOp (n := 3854) (.exec 0x123080 (fun s => s.RIP = 0x123080) (movR32R32Effect 0x123080 3 2 15) (Reg.operands [.gpr 15] [])) #v[3653]
    (.letOp (n := 3855) (.out 0x123083 (shrR32Effect 0x123083 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3853]
    (.letOp (n := 3856) (.exec 0x123083 (fun s => s.RIP = 0x123083) (shrR32Effect 0x123083 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3853]
    (.letOp (n := 3857) (.out 0x123086 (xorR32R32Effect 0x123086 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3855, 3831]
    (.letOp (n := 3858) (.exec 0x123086 (fun s => s.RIP = 0x123086) (xorR32R32Effect 0x123086 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3855, 3831]
    (.letOp (n := 3859) (.out 0x123088 (movR32M32LowEffect 0x123088 3 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 3860) (.exec 0x123088 (LoadPre 0x123088 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x123088 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x123088 3 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3861) (.out 0x12308c (addR32R32Effect 0x12308c 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[3859, 3857]
    (.letOp (n := 3862) (.exec 0x12308c (fun s => s.RIP = 0x12308c) (addR32R32Effect 0x12308c 2 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[3859, 3857]
    (.letOp (n := 3863) (.out 0x12308e (movR32R32Effect 0x12308e 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[3819]
    (.letOp (n := 3864) (.exec 0x12308e (fun s => s.RIP = 0x12308e) (movR32R32Effect 0x12308e 3 0 8) (Reg.operands [.gpr 8] [])) #v[3819]
    (.letOp (n := 3865) (.out 0x123091 (rolR32Effect 0x123091 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3863]
    (.letOp (n := 3866) (.exec 0x123091 (fun s => s.RIP = 0x123091) (rolR32Effect 0x123091 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3863]
    (.letOp (n := 3867) (.out 0x123094 (movR32R32Effect 0x123094 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[3819]
    (.letOp (n := 3868) (.exec 0x123094 (fun s => s.RIP = 0x123094) (movR32R32Effect 0x123094 3 2 8) (Reg.operands [.gpr 8] [])) #v[3819]
    (.letOp (n := 3869) (.out 0x123097 (rolR32Effect 0x123097 3 2 21) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3867]
    (.letOp (n := 3870) (.exec 0x123097 (fun s => s.RIP = 0x123097) (rolR32Effect 0x123097 3 2 21) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3867]
    (.letOp (n := 3871) (.out 0x12309a (xorR32R32Effect 0x12309a 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3869, 3865]
    (.letOp (n := 3872) (.exec 0x12309a (fun s => s.RIP = 0x12309a) (xorR32R32Effect 0x12309a 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3869, 3865]
    (.letOp (n := 3873) (.out 0x12309c (movR32R32Effect 0x12309c 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[3819]
    (.letOp (n := 3874) (.exec 0x12309c (fun s => s.RIP = 0x12309c) (movR32R32Effect 0x12309c 3 0 8) (Reg.operands [.gpr 8] [])) #v[3819]
    (.letOp (n := 3875) (.out 0x12309f (rolR32Effect 0x12309f 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3873]
    (.letOp (n := 3876) (.exec 0x12309f (fun s => s.RIP = 0x12309f) (rolR32Effect 0x12309f 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3873]
    (b_l121930_98))))))))))))))))))))))))))))))))))))))

def bytes_l121930_97 : List UInt8 :=
  [0xC1, 0xC6, 0x0E, 0x31, 0xD6, 0x89, 0xEA, 0xC1, 0xEA, 0x03, 0x31, 0xF2, 0x44, 0x01, 0x3C, 0x24,
    0x44, 0x01, 0xFA, 0x89, 0x54, 0x24, 0x08, 0x44, 0x89, 0xFA, 0xC1, 0xEA, 0x0A, 0x31, 0xC2, 0x8B,
    0x5C, 0x24, 0x78, 0x01, 0xD3, 0x44, 0x89, 0xC0, 0xC1, 0xC0, 0x1A, 0x44, 0x89, 0xC2, 0xC1, 0xC2,
    0x15, 0x31, 0xC2, 0x44, 0x89, 0xC0, 0xC1, 0xC0, 0x07] ++ bytes_l121930_98

theorem code_l121930_97 : ∀ x ∈ codeRange 0x123069 bytes_l121930_97, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23069 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_98

def b_l121930_96 : Block Op Label signature Reg.count 3799 :=
  .letOp (n := 3799) (.out 0x123036 (movR32R32Effect 0x123036 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[3727]
    (.letOp (n := 3800) (.exec 0x123036 (fun s => s.RIP = 0x123036) (movR32R32Effect 0x123036 3 2 14) (Reg.operands [.gpr 14] [])) #v[3727]
    (.letOp (n := 3801) (.out 0x123039 (rolR32Effect 0x123039 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3799]
    (.letOp (n := 3802) (.exec 0x123039 (fun s => s.RIP = 0x123039) (rolR32Effect 0x123039 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3799]
    (.letOp (n := 3803) (.out 0x12303c (xorR32R32Effect 0x12303c 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[3801, 3797]
    (.letOp (n := 3804) (.exec 0x12303c (fun s => s.RIP = 0x12303c) (xorR32R32Effect 0x12303c 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[3801, 3797]
    (.letOp (n := 3805) (.out 0x12303e (movR32R32Effect 0x12303e 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[3617]
    (.letOp (n := 3806) (.exec 0x12303e (fun s => s.RIP = 0x12303e) (movR32R32Effect 0x12303e 3 6 10) (Reg.operands [.gpr 10] [])) #v[3617]
    (.letOp (n := 3807) (.out 0x123041 (andR32R32Effect 0x123041 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[3805, 3507]
    (.letOp (n := 3808) (.exec 0x123041 (fun s => s.RIP = 0x123041) (andR32R32Effect 0x123041 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[3805, 3507]
    (.letOp (n := 3809) (.out 0x123043 (movR32R32Effect 0x123043 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 10] []) (.reg (.gpr 7))) #v[3617]
    (.letOp (n := 3810) (.exec 0x123043 (fun s => s.RIP = 0x123043) (movR32R32Effect 0x123043 3 7 10) (Reg.operands [.gpr 10] [])) #v[3617]
    (.letOp (n := 3811) (.out 0x123046 (xorR32R32Effect 0x123046 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[3809, 3507]
    (.letOp (n := 3812) (.exec 0x123046 (fun s => s.RIP = 0x123046) (xorR32R32Effect 0x123046 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[3809, 3507]
    (.letOp (n := 3813) (.out 0x123048 (andR32R32Effect 0x123048 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[3811, 3727]
    (.letOp (n := 3814) (.exec 0x123048 (fun s => s.RIP = 0x123048) (andR32R32Effect 0x123048 3 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[3811, 3727]
    (.letOp (n := 3815) (.out 0x12304b (xorR32R32Effect 0x12304b 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[3813, 3807]
    (.letOp (n := 3816) (.exec 0x12304b (fun s => s.RIP = 0x12304b) (xorR32R32Effect 0x12304b 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[3813, 3807]
    (.letOp (n := 3817) (.out 0x12304d (addR32R32Effect 0x12304d 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[3815, 3803]
    (.letOp (n := 3818) (.exec 0x12304d (fun s => s.RIP = 0x12304d) (addR32R32Effect 0x12304d 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[3815, 3803]
    (.letOp (n := 3819) (.out 0x12304f (addR32R32Effect 0x12304f 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[3397, 3787]
    (.letOp (n := 3820) (.exec 0x12304f (fun s => s.RIP = 0x12304f) (addR32R32Effect 0x12304f 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[3397, 3787]
    (.letOp (n := 3821) (.out 0x123052 (addR32R32Effect 0x123052 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[3817, 3787]
    (.letOp (n := 3822) (.exec 0x123052 (fun s => s.RIP = 0x123052) (addR32R32Effect 0x123052 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[3817, 3787]
    (.letOp (n := 3823) (.out 0x123054 (movR32R32Effect 0x123054 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[3653]
    (.letOp (n := 3824) (.exec 0x123054 (fun s => s.RIP = 0x123054) (movR32R32Effect 0x123054 3 2 15) (Reg.operands [.gpr 15] [])) #v[3653]
    (.letOp (n := 3825) (.out 0x123057 (rolR32Effect 0x123057 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3823]
    (.letOp (n := 3826) (.exec 0x123057 (fun s => s.RIP = 0x123057) (rolR32Effect 0x123057 3 2 15) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3823]
    (.letOp (n := 3827) (.out 0x12305a (movR32R32Effect 0x12305a 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[3653]
    (.letOp (n := 3828) (.exec 0x12305a (fun s => s.RIP = 0x12305a) (movR32R32Effect 0x12305a 3 0 15) (Reg.operands [.gpr 15] [])) #v[3653]
    (.letOp (n := 3829) (.out 0x12305d (rolR32Effect 0x12305d 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3827]
    (.letOp (n := 3830) (.exec 0x12305d (fun s => s.RIP = 0x12305d) (rolR32Effect 0x12305d 3 0 13) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3827]
    (.letOp (n := 3831) (.out 0x123060 (xorR32R32Effect 0x123060 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3829, 3825]
    (.letOp (n := 3832) (.exec 0x123060 (fun s => s.RIP = 0x123060) (xorR32R32Effect 0x123060 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3829, 3825]
    (.letOp (n := 3833) (.out 0x123062 (movR32R32Effect 0x123062 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[3763]
    (.letOp (n := 3834) (.exec 0x123062 (fun s => s.RIP = 0x123062) (movR32R32Effect 0x123062 2 2 5) (Reg.operands [.gpr 5] [])) #v[3763]
    (.letOp (n := 3835) (.out 0x123064 (rolR32Effect 0x123064 3 2 25) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3833]
    (.letOp (n := 3836) (.exec 0x123064 (fun s => s.RIP = 0x123064) (rolR32Effect 0x123064 3 2 25) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3833]
    (.letOp (n := 3837) (.out 0x123067 (movR32R32Effect 0x123067 2 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[3763]
    (.letOp (n := 3838) (.exec 0x123067 (fun s => s.RIP = 0x123067) (movR32R32Effect 0x123067 2 6 5) (Reg.operands [.gpr 5] [])) #v[3763]
    (b_l121930_97))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_96 : List UInt8 :=
  [0x44, 0x89, 0xF2, 0xC1, 0xC2, 0x0A, 0x31, 0xF2, 0x44, 0x89, 0xD6, 0x21, 0xCE, 0x44, 0x89, 0xD7,
    0x31, 0xCF, 0x44, 0x21, 0xF7, 0x31, 0xF7, 0x01, 0xD7, 0x41, 0x01, 0xC0, 0x01, 0xC7, 0x44, 0x89,
    0xFA, 0xC1, 0xC2, 0x0F, 0x44, 0x89, 0xF8, 0xC1, 0xC0, 0x0D, 0x31, 0xD0, 0x89, 0xEA, 0xC1, 0xC2,
    0x19, 0x89, 0xEE] ++ bytes_l121930_97

theorem code_l121930_96 : ∀ x ∈ codeRange 0x123036 bytes_l121930_96, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23036 51 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_97

def b_l121930_95 : Block Op Label signature Reg.count 3759 :=
  .letOp (n := 3759) (.out 0x122ffa (rolR32Effect 0x122ffa 3 0 21) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3757]
    (.letOp (n := 3760) (.exec 0x122ffa (fun s => s.RIP = 0x122ffa) (rolR32Effect 0x122ffa 3 0 21) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3757]
    (.letOp (n := 3761) (.out 0x122ffd (movR32M32LowEffect 0x122ffd 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 3762) (.exec 0x122ffd (LoadPre 0x122ffd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x122ffd + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x122ffd 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3763) (.out 0x123001 (addR32R32Effect 0x123001 2 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[3761, 3755]
    (.letOp (n := 3764) (.exec 0x123001 (fun s => s.RIP = 0x123001) (addR32R32Effect 0x123001 2 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[3761, 3755]
    (.letOp (n := 3765) (.out 0x123003 (movR32R32Effect 0x123003 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[3721]
    (.letOp (n := 3766) (.exec 0x123003 (fun s => s.RIP = 0x123003) (movR32R32Effect 0x123003 3 2 13) (Reg.operands [.gpr 13] [])) #v[3721]
    (.letOp (n := 3767) (.out 0x123006 (rolR32Effect 0x123006 3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3765]
    (.letOp (n := 3768) (.exec 0x123006 (fun s => s.RIP = 0x123006) (rolR32Effect 0x123006 3 2 7) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3765]
    (.letOp (n := 3769) (.out 0x123009 (xorR32R32Effect 0x123009 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[3759, 3753]
    (.letOp (n := 3770) (.exec 0x123009 (fun s => s.RIP = 0x123009) (xorR32R32Effect 0x123009 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[3759, 3753]
    (.letOp (n := 3771) (.out 0x12300b (xorR32R32Effect 0x12300b 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3767, 3769]
    (.letOp (n := 3772) (.exec 0x12300b (fun s => s.RIP = 0x12300b) (xorR32R32Effect 0x12300b 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3767, 3769]
    (.letOp (n := 3773) (.out 0x12300d (movR32R32Effect 0x12300d 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[3611]
    (.letOp (n := 3774) (.exec 0x12300d (fun s => s.RIP = 0x12300d) (movR32R32Effect 0x12300d 3 0 11) (Reg.operands [.gpr 11] [])) #v[3611]
    (.letOp (n := 3775) (.out 0x123010 (xorR32R32Effect 0x123010 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[3773, 3501]
    (.letOp (n := 3776) (.exec 0x123010 (fun s => s.RIP = 0x123010) (xorR32R32Effect 0x123010 3 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[3773, 3501]
    (.letOp (n := 3777) (.out 0x123013 (andR32R32Effect 0x123013 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[3775, 3721]
    (.letOp (n := 3778) (.exec 0x123013 (fun s => s.RIP = 0x123013) (andR32R32Effect 0x123013 3 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[3775, 3721]
    (.letOp (n := 3779) (.out 0x123016 (xorR32R32Effect 0x123016 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[3777, 3501]
    (.letOp (n := 3780) (.exec 0x123016 (fun s => s.RIP = 0x123016) (xorR32R32Effect 0x123016 3 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[3777, 3501]
    (.letOp (n := 3781) (.out 0x123019 (addR32R32Effect 0x123019 3 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[3395, 3763]
    (.letOp (n := 3782) (.exec 0x123019 (fun s => s.RIP = 0x123019) (addR32R32Effect 0x123019 3 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[3395, 3763]
    (.letOp (n := 3783) (.out 0x12301c (addR32R32Effect 0x12301c 3 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[3781, 3779]
    (.letOp (n := 3784) (.exec 0x12301c (fun s => s.RIP = 0x12301c) (addR32R32Effect 0x12301c 3 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[3781, 3779]
    (.letOp (n := 3785) (.out 0x12301f (leaR32Effect 0x12301f 4 0 (.sib 2 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 12] []) (.reg (.gpr 0))) #v[3771, 3783]
    (.letOp (n := 3786) (.exec 0x12301f (fun s => s.RIP = 0x12301f) (leaR32Effect 0x12301f 4 0 (.sib 2 (some 12) 0 .none)) (Reg.operands [.gpr 2, .gpr 12] [])) #v[3771, 3783]
    (.letOp (n := 3787) (.out 0x123023 (addEaxImm32Effect 0x123023 0x53380d13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[3785]
    (.letOp (n := 3788) (.exec 0x123023 (fun s => s.RIP = 0x123023) (addEaxImm32Effect 0x123023 0x53380d13) (Reg.operands [.gpr 0] [])) #v[3785]
    (.letOp (n := 3789) (.out 0x123028 (movR32R32Effect 0x123028 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[3727]
    (.letOp (n := 3790) (.exec 0x123028 (fun s => s.RIP = 0x123028) (movR32R32Effect 0x123028 3 2 14) (Reg.operands [.gpr 14] [])) #v[3727]
    (.letOp (n := 3791) (.out 0x12302b (rolR32Effect 0x12302b 3 2 30) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3789]
    (.letOp (n := 3792) (.exec 0x12302b (fun s => s.RIP = 0x12302b) (rolR32Effect 0x12302b 3 2 30) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3789]
    (.letOp (n := 3793) (.out 0x12302e (movR32R32Effect 0x12302e 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[3727]
    (.letOp (n := 3794) (.exec 0x12302e (fun s => s.RIP = 0x12302e) (movR32R32Effect 0x12302e 3 6 14) (Reg.operands [.gpr 14] [])) #v[3727]
    (.letOp (n := 3795) (.out 0x123031 (rolR32Effect 0x123031 3 6 19) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3793]
    (.letOp (n := 3796) (.exec 0x123031 (fun s => s.RIP = 0x123031) (rolR32Effect 0x123031 3 6 19) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3793]
    (.letOp (n := 3797) (.out 0x123034 (xorR32R32Effect 0x123034 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[3795, 3791]
    (.letOp (n := 3798) (.exec 0x123034 (fun s => s.RIP = 0x123034) (xorR32R32Effect 0x123034 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[3795, 3791]
    (b_l121930_96))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_95 : List UInt8 :=
  [0xC1, 0xC0, 0x15, 0x8B, 0x6C, 0x24, 0x50, 0x01, 0xD5, 0x44, 0x89, 0xEA, 0xC1, 0xC2, 0x07, 0x31,
    0xF0, 0x31, 0xC2, 0x44, 0x89, 0xD8, 0x44, 0x31, 0xC8, 0x44, 0x21, 0xE8, 0x44, 0x31, 0xC8, 0x41,
    0x01, 0xEC, 0x41, 0x01, 0xC4, 0x42, 0x8D, 0x04, 0x22, 0x05, 0x13, 0x0D, 0x38, 0x53, 0x44, 0x89,
    0xF2, 0xC1, 0xC2, 0x1E, 0x44, 0x89, 0xF6, 0xC1, 0xC6, 0x13, 0x31, 0xD6] ++ bytes_l121930_96

theorem code_l121930_95 : ∀ x ∈ codeRange 0x122ffa bytes_l121930_95, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22ffa 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_96

def b_l121930_94 : Block Op Label signature Reg.count 3721 :=
  .letOp (n := 3721) (.out 0x122fc2 (addR32R32Effect 0x122fc2 3 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[3303, 3681]
    (.letOp (n := 3722) (.exec 0x122fc2 (fun s => s.RIP = 0x122fc2) (addR32R32Effect 0x122fc2 3 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[3303, 3681]
    (.letOp (n := 3723) (.out 0x122fc5 (movR32R32Effect 0x122fc5 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[3653]
    (.letOp (n := 3724) (.exec 0x122fc5 (fun s => s.RIP = 0x122fc5) (movR32R32Effect 0x122fc5 3 7 15) (Reg.operands [.gpr 15] [])) #v[3653]
    (.letOp (n := 3725) (.out 0x122fc8 (rolR32Effect 0x122fc8 3 7 25) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3723]
    (.letOp (n := 3726) (.exec 0x122fc8 (fun s => s.RIP = 0x122fc8) (rolR32Effect 0x122fc8 3 7 25) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3723]
    (.letOp (n := 3727) (.out 0x122fcb (addR32R32Effect 0x122fcb 3 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[3715, 3681]
    (.letOp (n := 3728) (.exec 0x122fcb (fun s => s.RIP = 0x122fcb) (addR32R32Effect 0x122fcb 3 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[3715, 3681]
    (.letOp (n := 3729) (.out 0x122fce (movR32R32Effect 0x122fce 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[3653]
    (.letOp (n := 3730) (.exec 0x122fce (fun s => s.RIP = 0x122fce) (movR32R32Effect 0x122fce 3 2 15) (Reg.operands [.gpr 15] [])) #v[3653]
    (.letOp (n := 3731) (.out 0x122fd1 (rolR32Effect 0x122fd1 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3729]
    (.letOp (n := 3732) (.exec 0x122fd1 (fun s => s.RIP = 0x122fd1) (rolR32Effect 0x122fd1 3 2 14) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3729]
    (.letOp (n := 3733) (.out 0x122fd4 (xorR32R32Effect 0x122fd4 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[3719, 3713]
    (.letOp (n := 3734) (.exec 0x122fd4 (fun s => s.RIP = 0x122fd4) (xorR32R32Effect 0x122fd4 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[3719, 3713]
    (.letOp (n := 3735) (.out 0x122fd6 (xorR32R32Effect 0x122fd6 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[3731, 3725]
    (.letOp (n := 3736) (.exec 0x122fd6 (fun s => s.RIP = 0x122fd6) (xorR32R32Effect 0x122fd6 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[3731, 3725]
    (.letOp (n := 3737) (.out 0x122fd8 (movR32R32Effect 0x122fd8 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[3653]
    (.letOp (n := 3738) (.exec 0x122fd8 (fun s => s.RIP = 0x122fd8) (movR32R32Effect 0x122fd8 3 6 15) (Reg.operands [.gpr 15] [])) #v[3653]
    (.letOp (n := 3739) (.out 0x122fdb (shrR32Effect 0x122fdb 3 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3737]
    (.letOp (n := 3740) (.exec 0x122fdb (fun s => s.RIP = 0x122fdb) (shrR32Effect 0x122fdb 3 6 3) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3737]
    (.letOp (n := 3741) (.out 0x122fde (xorR32R32Effect 0x122fde 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[3739, 3735]
    (.letOp (n := 3742) (.exec 0x122fde (fun s => s.RIP = 0x122fde) (xorR32R32Effect 0x122fde 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[3739, 3735]
    (.letOp (n := 3743) (.exec 0x122fe0 (StorePre 0x122fe0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x122fe0 + BitVec.ofNat 64 4)) 4) (addMREffect 0x122fe0 4 32 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[3543, 4]
    (.letOp (n := 3744) (.out 0x122fe4 (addR32R32Effect 0x122fe4 2 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[3741, 3543]
    (.letOp (n := 3745) (.exec 0x122fe4 (fun s => s.RIP = 0x122fe4) (addR32R32Effect 0x122fe4 2 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[3741, 3543]
    (.letOp (n := 3746) (.exec 0x122fe6 (StorePre 0x122fe6 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x122fe6 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x122fe6 6 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[3744, 4]
    (.letOp (n := 3747) (.out 0x122fea (movR32R32Effect 0x122fea 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[3543]
    (.letOp (n := 3748) (.exec 0x122fea (fun s => s.RIP = 0x122fea) (movR32R32Effect 0x122fea 2 2 5) (Reg.operands [.gpr 5] [])) #v[3543]
    (.letOp (n := 3749) (.out 0x122fec (shrR32Effect 0x122fec 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3747]
    (.letOp (n := 3750) (.exec 0x122fec (fun s => s.RIP = 0x122fec) (shrR32Effect 0x122fec 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3747]
    (.letOp (n := 3751) (.out 0x122fef (movR32R32Effect 0x122fef 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[3721]
    (.letOp (n := 3752) (.exec 0x122fef (fun s => s.RIP = 0x122fef) (movR32R32Effect 0x122fef 3 6 13) (Reg.operands [.gpr 13] [])) #v[3721]
    (.letOp (n := 3753) (.out 0x122ff2 (rolR32Effect 0x122ff2 3 6 26) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3751]
    (.letOp (n := 3754) (.exec 0x122ff2 (fun s => s.RIP = 0x122ff2) (rolR32Effect 0x122ff2 3 6 26) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3751]
    (.letOp (n := 3755) (.out 0x122ff5 (xorR32R32Effect 0x122ff5 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3749, 3733]
    (.letOp (n := 3756) (.exec 0x122ff5 (fun s => s.RIP = 0x122ff5) (xorR32R32Effect 0x122ff5 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3749, 3733]
    (.letOp (n := 3757) (.out 0x122ff7 (movR32R32Effect 0x122ff7 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[3721]
    (.letOp (n := 3758) (.exec 0x122ff7 (fun s => s.RIP = 0x122ff7) (movR32R32Effect 0x122ff7 3 0 13) (Reg.operands [.gpr 13] [])) #v[3721]
    (b_l121930_95))))))))))))))))))))))))))))))))))))))

def bytes_l121930_94 : List UInt8 :=
  [0x41, 0x01, 0xD5, 0x44, 0x89, 0xFF, 0xC1, 0xC7, 0x19, 0x41, 0x01, 0xD6, 0x44, 0x89, 0xFA, 0xC1,
    0xC2, 0x0E, 0x31, 0xF0, 0x31, 0xFA, 0x44, 0x89, 0xFE, 0xC1, 0xEE, 0x03, 0x31, 0xD6, 0x01, 0x6C,
    0x24, 0x70, 0x01, 0xEE, 0x89, 0x74, 0x24, 0x0C, 0x89, 0xEA, 0xC1, 0xEA, 0x0A, 0x44, 0x89, 0xEE,
    0xC1, 0xC6, 0x1A, 0x31, 0xC2, 0x44, 0x89, 0xE8] ++ bytes_l121930_95

theorem code_l121930_94 : ∀ x ∈ codeRange 0x122fc2 bytes_l121930_94, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22fc2 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_95

def b_l121930_93 : Block Op Label signature Reg.count 3681 :=
  .letOp (n := 3681) (.out 0x122f88 (addR32Imm32Effect 0x122f88 6 2 0x4d2c6dfc) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[3679]
    (.letOp (n := 3682) (.exec 0x122f88 (fun s => s.RIP = 0x122f88) (addR32Imm32Effect 0x122f88 6 2 0x4d2c6dfc) (Reg.operands [.gpr 2] [])) #v[3679]
    (.letOp (n := 3683) (.out 0x122f8e (movR32R32Effect 0x122f8e 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[3617]
    (.letOp (n := 3684) (.exec 0x122f8e (fun s => s.RIP = 0x122f8e) (movR32R32Effect 0x122f8e 3 0 10) (Reg.operands [.gpr 10] [])) #v[3617]
    (.letOp (n := 3685) (.out 0x122f91 (rolR32Effect 0x122f91 3 0 30) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3683]
    (.letOp (n := 3686) (.exec 0x122f91 (fun s => s.RIP = 0x122f91) (rolR32Effect 0x122f91 3 0 30) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3683]
    (.letOp (n := 3687) (.out 0x122f94 (movR32R32Effect 0x122f94 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[3617]
    (.letOp (n := 3688) (.exec 0x122f94 (fun s => s.RIP = 0x122f94) (movR32R32Effect 0x122f94 3 6 10) (Reg.operands [.gpr 10] [])) #v[3617]
    (.letOp (n := 3689) (.out 0x122f97 (rolR32Effect 0x122f97 3 6 19) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3687]
    (.letOp (n := 3690) (.exec 0x122f97 (fun s => s.RIP = 0x122f97) (rolR32Effect 0x122f97 3 6 19) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3687]
    (.letOp (n := 3691) (.out 0x122f9a (xorR32R32Effect 0x122f9a 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[3689, 3685]
    (.letOp (n := 3692) (.exec 0x122f9a (fun s => s.RIP = 0x122f9a) (xorR32R32Effect 0x122f9a 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[3689, 3685]
    (.letOp (n := 3693) (.out 0x122f9c (movR32R32Effect 0x122f9c 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[3617]
    (.letOp (n := 3694) (.exec 0x122f9c (fun s => s.RIP = 0x122f9c) (movR32R32Effect 0x122f9c 3 0 10) (Reg.operands [.gpr 10] [])) #v[3617]
    (.letOp (n := 3695) (.out 0x122f9f (rolR32Effect 0x122f9f 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3693]
    (.letOp (n := 3696) (.exec 0x122f9f (fun s => s.RIP = 0x122f9f) (rolR32Effect 0x122f9f 3 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3693]
    (.letOp (n := 3697) (.out 0x122fa2 (xorR32R32Effect 0x122fa2 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[3695, 3691]
    (.letOp (n := 3698) (.exec 0x122fa2 (fun s => s.RIP = 0x122fa2) (xorR32R32Effect 0x122fa2 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[3695, 3691]
    (.letOp (n := 3699) (.out 0x122fa4 (movR32R32Effect 0x122fa4 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[3507]
    (.letOp (n := 3700) (.exec 0x122fa4 (fun s => s.RIP = 0x122fa4) (movR32R32Effect 0x122fa4 2 6 1) (Reg.operands [.gpr 1] [])) #v[3507]
    (.letOp (n := 3701) (.out 0x122fa6 (andR32R32Effect 0x122fa6 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[3699, 3397]
    (.letOp (n := 3702) (.exec 0x122fa6 (fun s => s.RIP = 0x122fa6) (andR32R32Effect 0x122fa6 3 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[3699, 3397]
    (.letOp (n := 3703) (.out 0x122fa9 (movR32R32Effect 0x122fa9 3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[3507]
    (.letOp (n := 3704) (.exec 0x122fa9 (fun s => s.RIP = 0x122fa9) (movR32R32Effect 0x122fa9 3 14 1) (Reg.operands [.gpr 1] [])) #v[3507]
    (.letOp (n := 3705) (.out 0x122fac (xorR32R32Effect 0x122fac 3 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[3703, 3397]
    (.letOp (n := 3706) (.exec 0x122fac (fun s => s.RIP = 0x122fac) (xorR32R32Effect 0x122fac 3 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[3703, 3397]
    (.letOp (n := 3707) (.out 0x122faf (andR32R32Effect 0x122faf 3 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10] []) (.reg (.gpr 14))) #v[3705, 3617]
    (.letOp (n := 3708) (.exec 0x122faf (fun s => s.RIP = 0x122faf) (andR32R32Effect 0x122faf 3 14 10) (Reg.operands [.gpr 14, .gpr 10] [])) #v[3705, 3617]
    (.letOp (n := 3709) (.out 0x122fb2 (xorR32R32Effect 0x122fb2 3 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[3707, 3701]
    (.letOp (n := 3710) (.exec 0x122fb2 (fun s => s.RIP = 0x122fb2) (xorR32R32Effect 0x122fb2 3 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[3707, 3701]
    (.letOp (n := 3711) (.out 0x122fb5 (movR32R32Effect 0x122fb5 2 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[3543]
    (.letOp (n := 3712) (.exec 0x122fb5 (fun s => s.RIP = 0x122fb5) (movR32R32Effect 0x122fb5 2 6 5) (Reg.operands [.gpr 5] [])) #v[3543]
    (.letOp (n := 3713) (.out 0x122fb7 (rolR32Effect 0x122fb7 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3711]
    (.letOp (n := 3714) (.exec 0x122fb7 (fun s => s.RIP = 0x122fb7) (rolR32Effect 0x122fb7 3 6 15) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3711]
    (.letOp (n := 3715) (.out 0x122fba (addR32R32Effect 0x122fba 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[3709, 3697]
    (.letOp (n := 3716) (.exec 0x122fba (fun s => s.RIP = 0x122fba) (addR32R32Effect 0x122fba 3 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[3709, 3697]
    (.letOp (n := 3717) (.out 0x122fbd (movR32R32Effect 0x122fbd 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[3543]
    (.letOp (n := 3718) (.exec 0x122fbd (fun s => s.RIP = 0x122fbd) (movR32R32Effect 0x122fbd 2 0 5) (Reg.operands [.gpr 5] [])) #v[3543]
    (.letOp (n := 3719) (.out 0x122fbf (rolR32Effect 0x122fbf 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3717]
    (.letOp (n := 3720) (.exec 0x122fbf (fun s => s.RIP = 0x122fbf) (rolR32Effect 0x122fbf 3 0 13) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3717]
    (b_l121930_94))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_93 : List UInt8 :=
  [0x81, 0xC2, 0xFC, 0x6D, 0x2C, 0x4D, 0x44, 0x89, 0xD0, 0xC1, 0xC0, 0x1E, 0x44, 0x89, 0xD6, 0xC1,
    0xC6, 0x13, 0x31, 0xC6, 0x44, 0x89, 0xD0, 0xC1, 0xC0, 0x0A, 0x31, 0xF0, 0x89, 0xCE, 0x44, 0x21,
    0xC6, 0x41, 0x89, 0xCE, 0x45, 0x31, 0xC6, 0x45, 0x21, 0xD6, 0x41, 0x31, 0xF6, 0x89, 0xEE, 0xC1,
    0xC6, 0x0F, 0x41, 0x01, 0xC6, 0x89, 0xE8, 0xC1, 0xC0, 0x0D] ++ bytes_l121930_94

theorem code_l121930_93 : ∀ x ∈ codeRange 0x122f88 bytes_l121930_93, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22f88 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_94

def b_l121930_92 : Block Op Label signature Reg.count 3641 :=
  .letOp (n := 3641) (.out 0x122f4e (movR32R32Effect 0x122f4e 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[3437]
    (.letOp (n := 3642) (.exec 0x122f4e (fun s => s.RIP = 0x122f4e) (movR32R32Effect 0x122f4e 3 2 15) (Reg.operands [.gpr 15] [])) #v[3437]
    (.letOp (n := 3643) (.out 0x122f51 (shrR32Effect 0x122f51 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3641]
    (.letOp (n := 3644) (.exec 0x122f51 (fun s => s.RIP = 0x122f51) (shrR32Effect 0x122f51 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3641]
    (.letOp (n := 3645) (.out 0x122f54 (xorR32R32Effect 0x122f54 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3643, 3623]
    (.letOp (n := 3646) (.exec 0x122f54 (fun s => s.RIP = 0x122f54) (xorR32R32Effect 0x122f54 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3643, 3623]
    (.letOp (n := 3647) (.out 0x122f56 (movR32R32Effect 0x122f56 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[3611]
    (.letOp (n := 3648) (.exec 0x122f56 (fun s => s.RIP = 0x122f56) (movR32R32Effect 0x122f56 3 0 11) (Reg.operands [.gpr 11] [])) #v[3611]
    (.letOp (n := 3649) (.out 0x122f59 (rolR32Effect 0x122f59 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3647]
    (.letOp (n := 3650) (.exec 0x122f59 (fun s => s.RIP = 0x122f59) (rolR32Effect 0x122f59 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3647]
    (.letOp (n := 3651) (.out 0x122f5c (movR32M32Effect 0x122f5c 15 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 3652) (.exec 0x122f5c (LoadPre 0x122f5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x122f5c + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x122f5c 15 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3653) (.out 0x122f61 (addR32R32Effect 0x122f61 3 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[3651, 3645]
    (.letOp (n := 3654) (.exec 0x122f61 (fun s => s.RIP = 0x122f61) (addR32R32Effect 0x122f61 3 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[3651, 3645]
    (.letOp (n := 3655) (.out 0x122f64 (movR32R32Effect 0x122f64 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11] []) (.reg (.gpr 2))) #v[3611]
    (.letOp (n := 3656) (.exec 0x122f64 (fun s => s.RIP = 0x122f64) (movR32R32Effect 0x122f64 3 2 11) (Reg.operands [.gpr 11] [])) #v[3611]
    (.letOp (n := 3657) (.out 0x122f67 (rolR32Effect 0x122f67 3 2 21) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3655]
    (.letOp (n := 3658) (.exec 0x122f67 (fun s => s.RIP = 0x122f67) (rolR32Effect 0x122f67 3 2 21) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3655]
    (.letOp (n := 3659) (.out 0x122f6a (xorR32R32Effect 0x122f6a 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3657, 3649]
    (.letOp (n := 3660) (.exec 0x122f6a (fun s => s.RIP = 0x122f6a) (xorR32R32Effect 0x122f6a 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3657, 3649]
    (.letOp (n := 3661) (.out 0x122f6c (movR32R32Effect 0x122f6c 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[3611]
    (.letOp (n := 3662) (.exec 0x122f6c (fun s => s.RIP = 0x122f6c) (movR32R32Effect 0x122f6c 3 0 11) (Reg.operands [.gpr 11] [])) #v[3611]
    (.letOp (n := 3663) (.out 0x122f6f (rolR32Effect 0x122f6f 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3661]
    (.letOp (n := 3664) (.exec 0x122f6f (fun s => s.RIP = 0x122f6f) (rolR32Effect 0x122f6f 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3661]
    (.letOp (n := 3665) (.out 0x122f72 (xorR32R32Effect 0x122f72 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3663, 3659]
    (.letOp (n := 3666) (.exec 0x122f72 (fun s => s.RIP = 0x122f72) (xorR32R32Effect 0x122f72 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3663, 3659]
    (.letOp (n := 3667) (.out 0x122f74 (movR32R32Effect 0x122f74 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[3501]
    (.letOp (n := 3668) (.exec 0x122f74 (fun s => s.RIP = 0x122f74) (movR32R32Effect 0x122f74 3 2 9) (Reg.operands [.gpr 9] [])) #v[3501]
    (.letOp (n := 3669) (.out 0x122f77 (xorR32R32Effect 0x122f77 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[3667, 3395]
    (.letOp (n := 3670) (.exec 0x122f77 (fun s => s.RIP = 0x122f77) (xorR32R32Effect 0x122f77 3 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[3667, 3395]
    (.letOp (n := 3671) (.out 0x122f7a (andR32R32Effect 0x122f7a 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[3669, 3611]
    (.letOp (n := 3672) (.exec 0x122f7a (fun s => s.RIP = 0x122f7a) (andR32R32Effect 0x122f7a 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[3669, 3611]
    (.letOp (n := 3673) (.out 0x122f7d (xorR32R32Effect 0x122f7d 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[3671, 3395]
    (.letOp (n := 3674) (.exec 0x122f7d (fun s => s.RIP = 0x122f7d) (xorR32R32Effect 0x122f7d 3 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[3671, 3395]
    (.letOp (n := 3675) (.out 0x122f80 (addR32R32Effect 0x122f80 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[3297, 3653]
    (.letOp (n := 3676) (.exec 0x122f80 (fun s => s.RIP = 0x122f80) (addR32R32Effect 0x122f80 3 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[3297, 3653]
    (.letOp (n := 3677) (.out 0x122f83 (addR32R32Effect 0x122f83 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[3675, 3673]
    (.letOp (n := 3678) (.exec 0x122f83 (fun s => s.RIP = 0x122f83) (addR32R32Effect 0x122f83 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[3675, 3673]
    (.letOp (n := 3679) (.out 0x122f85 (leaR32Effect 0x122f85 3 2 (.sib 0 (some 6) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 6] []) (.reg (.gpr 2))) #v[3665, 3677]
    (.letOp (n := 3680) (.exec 0x122f85 (fun s => s.RIP = 0x122f85) (leaR32Effect 0x122f85 3 2 (.sib 0 (some 6) 0 .none)) (Reg.operands [.gpr 0, .gpr 6] [])) #v[3665, 3677]
    (b_l121930_93))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_92 : List UInt8 :=
  [0x44, 0x89, 0xFA, 0xC1, 0xEA, 0x0A, 0x31, 0xC2, 0x44, 0x89, 0xD8, 0xC1, 0xC0, 0x1A, 0x44, 0x8B,
    0x7C, 0x24, 0x38, 0x41, 0x01, 0xD7, 0x44, 0x89, 0xDA, 0xC1, 0xC2, 0x15, 0x31, 0xC2, 0x44, 0x89,
    0xD8, 0xC1, 0xC0, 0x07, 0x31, 0xD0, 0x44, 0x89, 0xCA, 0x44, 0x31, 0xE2, 0x44, 0x21, 0xDA, 0x44,
    0x31, 0xE2, 0x44, 0x01, 0xFE, 0x01, 0xD6, 0x8D, 0x14, 0x30] ++ bytes_l121930_93

theorem code_l121930_92 : ∀ x ∈ codeRange 0x122f4e bytes_l121930_92, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22f4e 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_93

def b_l121930_91 : Block Op Label signature Reg.count 3603 :=
  .letOp (n := 3603) (.out 0x122f14 (xorR32R32Effect 0x122f14 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[3601, 3595]
    (.letOp (n := 3604) (.exec 0x122f14 (fun s => s.RIP = 0x122f14) (xorR32R32Effect 0x122f14 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[3601, 3595]
    (.letOp (n := 3605) (.out 0x122f17 (addR32R32Effect 0x122f17 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[3603, 3591]
    (.letOp (n := 3606) (.exec 0x122f17 (fun s => s.RIP = 0x122f17) (addR32R32Effect 0x122f17 3 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[3603, 3591]
    (.letOp (n := 3607) (.out 0x122f1a (movR32R32Effect 0x122f1a 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[3437]
    (.letOp (n := 3608) (.exec 0x122f1a (fun s => s.RIP = 0x122f1a) (movR32R32Effect 0x122f1a 3 2 15) (Reg.operands [.gpr 15] [])) #v[3437]
    (.letOp (n := 3609) (.out 0x122f1d (rolR32Effect 0x122f1d 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3607]
    (.letOp (n := 3610) (.exec 0x122f1d (fun s => s.RIP = 0x122f1d) (rolR32Effect 0x122f1d 3 2 15) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3607]
    (.letOp (n := 3611) (.out 0x122f20 (addR32R32Effect 0x122f20 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[3193, 3583]
    (.letOp (n := 3612) (.exec 0x122f20 (fun s => s.RIP = 0x122f20) (addR32R32Effect 0x122f20 3 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[3193, 3583]
    (.letOp (n := 3613) (.out 0x122f23 (movR32R32Effect 0x122f23 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[3437]
    (.letOp (n := 3614) (.exec 0x122f23 (fun s => s.RIP = 0x122f23) (movR32R32Effect 0x122f23 3 0 15) (Reg.operands [.gpr 15] [])) #v[3437]
    (.letOp (n := 3615) (.out 0x122f26 (rolR32Effect 0x122f26 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3613]
    (.letOp (n := 3616) (.exec 0x122f26 (fun s => s.RIP = 0x122f26) (rolR32Effect 0x122f26 3 0 13) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3613]
    (.letOp (n := 3617) (.out 0x122f29 (addR32R32Effect 0x122f29 3 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[3605, 3583]
    (.letOp (n := 3618) (.exec 0x122f29 (fun s => s.RIP = 0x122f29) (addR32R32Effect 0x122f29 3 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[3605, 3583]
    (.letOp (n := 3619) (.out 0x122f2c (movR32R32Effect 0x122f2c 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[3543]
    (.letOp (n := 3620) (.exec 0x122f2c (fun s => s.RIP = 0x122f2c) (movR32R32Effect 0x122f2c 2 7 5) (Reg.operands [.gpr 5] [])) #v[3543]
    (.letOp (n := 3621) (.out 0x122f2e (rolR32Effect 0x122f2e 3 7 25) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3619]
    (.letOp (n := 3622) (.exec 0x122f2e (fun s => s.RIP = 0x122f2e) (rolR32Effect 0x122f2e 3 7 25) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3619]
    (.letOp (n := 3623) (.out 0x122f31 (xorR32R32Effect 0x122f31 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3615, 3609]
    (.letOp (n := 3624) (.exec 0x122f31 (fun s => s.RIP = 0x122f31) (xorR32R32Effect 0x122f31 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3615, 3609]
    (.letOp (n := 3625) (.out 0x122f33 (movR32R32Effect 0x122f33 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[3543]
    (.letOp (n := 3626) (.exec 0x122f33 (fun s => s.RIP = 0x122f33) (movR32R32Effect 0x122f33 2 2 5) (Reg.operands [.gpr 5] [])) #v[3543]
    (.letOp (n := 3627) (.out 0x122f35 (rolR32Effect 0x122f35 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3625]
    (.letOp (n := 3628) (.exec 0x122f35 (fun s => s.RIP = 0x122f35) (rolR32Effect 0x122f35 3 2 14) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3625]
    (.letOp (n := 3629) (.out 0x122f38 (xorR32R32Effect 0x122f38 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[3627, 3621]
    (.letOp (n := 3630) (.exec 0x122f38 (fun s => s.RIP = 0x122f38) (xorR32R32Effect 0x122f38 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[3627, 3621]
    (.letOp (n := 3631) (.out 0x122f3a (movR32R32Effect 0x122f3a 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[3543]
    (.letOp (n := 3632) (.exec 0x122f3a (fun s => s.RIP = 0x122f3a) (movR32R32Effect 0x122f3a 2 7 5) (Reg.operands [.gpr 5] [])) #v[3543]
    (.letOp (n := 3633) (.out 0x122f3c (shrR32Effect 0x122f3c 3 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3631]
    (.letOp (n := 3634) (.exec 0x122f3c (fun s => s.RIP = 0x122f3c) (shrR32Effect 0x122f3c 3 7 3) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3631]
    (.letOp (n := 3635) (.out 0x122f3f (xorR32R32Effect 0x122f3f 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[3633, 3629]
    (.letOp (n := 3636) (.exec 0x122f3f (fun s => s.RIP = 0x122f3f) (xorR32R32Effect 0x122f3f 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[3633, 3629]
    (.letOp (n := 3637) (.exec 0x122f41 (StorePre 0x122f41 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x122f41 + BitVec.ofNat 64 5)) 4) (addMREffect 0x122f41 5 32 15 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[3437, 4]
    (.letOp (n := 3638) (.out 0x122f46 (addR32R32Effect 0x122f46 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[3635, 3437]
    (.letOp (n := 3639) (.exec 0x122f46 (fun s => s.RIP = 0x122f46) (addR32R32Effect 0x122f46 3 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[3635, 3437]
    (.letOp (n := 3640) (.exec 0x122f49 (StorePre 0x122f49 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x122f49 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x122f49 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[3638, 4]
    (b_l121930_92))))))))))))))))))))))))))))))))))))))

def bytes_l121930_91 : List UInt8 :=
  [0x41, 0x31, 0xD2, 0x41, 0x01, 0xC2, 0x44, 0x89, 0xFA, 0xC1, 0xC2, 0x0F, 0x41, 0x01, 0xDB, 0x44,
    0x89, 0xF8, 0xC1, 0xC0, 0x0D, 0x41, 0x01, 0xDA, 0x89, 0xEF, 0xC1, 0xC7, 0x19, 0x31, 0xD0, 0x89,
    0xEA, 0xC1, 0xC2, 0x0E, 0x31, 0xFA, 0x89, 0xEF, 0xC1, 0xEF, 0x03, 0x31, 0xD7, 0x44, 0x01, 0x7C,
    0x24, 0x48, 0x44, 0x01, 0xFF, 0x48, 0x89, 0x7C, 0x24, 0x28] ++ bytes_l121930_92

theorem code_l121930_91 : ∀ x ∈ codeRange 0x122f14 bytes_l121930_91, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22f14 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_92

def b_l121930_90 : Block Op Label signature Reg.count 3563 :=
  .letOp (n := 3563) (.out 0x122edb (xorR32R32Effect 0x122edb 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[3561, 3297]
    (.letOp (n := 3564) (.exec 0x122edb (fun s => s.RIP = 0x122edb) (xorR32R32Effect 0x122edb 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[3561, 3297]
    (.letOp (n := 3565) (.out 0x122edd (andR32R32Effect 0x122edd 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[3563, 3501]
    (.letOp (n := 3566) (.exec 0x122edd (fun s => s.RIP = 0x122edd) (andR32R32Effect 0x122edd 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[3563, 3501]
    (.letOp (n := 3567) (.out 0x122ee0 (xorR32R32Effect 0x122ee0 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[3565, 3297]
    (.letOp (n := 3568) (.exec 0x122ee0 (fun s => s.RIP = 0x122ee0) (xorR32R32Effect 0x122ee0 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[3565, 3297]
    (.letOp (n := 3569) (.out 0x122ee2 (addR32R32Effect 0x122ee2 3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[3187, 3543]
    (.letOp (n := 3570) (.exec 0x122ee2 (fun s => s.RIP = 0x122ee2) (addR32R32Effect 0x122ee2 3 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[3187, 3543]
    (.letOp (n := 3571) (.out 0x122ee5 (movR32R32Effect 0x122ee5 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[3507]
    (.letOp (n := 3572) (.exec 0x122ee5 (fun s => s.RIP = 0x122ee5) (movR32R32Effect 0x122ee5 2 7 1) (Reg.operands [.gpr 1] [])) #v[3507]
    (.letOp (n := 3573) (.out 0x122ee7 (rolR32Effect 0x122ee7 3 7 30) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3571]
    (.letOp (n := 3574) (.exec 0x122ee7 (fun s => s.RIP = 0x122ee7) (rolR32Effect 0x122ee7 3 7 30) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3571]
    (.letOp (n := 3575) (.out 0x122eea (addR32R32Effect 0x122eea 3 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[3569, 3567]
    (.letOp (n := 3576) (.exec 0x122eea (fun s => s.RIP = 0x122eea) (addR32R32Effect 0x122eea 3 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[3569, 3567]
    (.letOp (n := 3577) (.out 0x122eed (movR32R32Effect 0x122eed 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[3507]
    (.letOp (n := 3578) (.exec 0x122eed (fun s => s.RIP = 0x122eed) (movR32R32Effect 0x122eed 2 2 1) (Reg.operands [.gpr 1] [])) #v[3507]
    (.letOp (n := 3579) (.out 0x122eef (rolR32Effect 0x122eef 3 2 19) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3577]
    (.letOp (n := 3580) (.exec 0x122eef (fun s => s.RIP = 0x122eef) (rolR32Effect 0x122eef 3 2 19) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3577]
    (.letOp (n := 3581) (.out 0x122ef2 (leaR32Effect 0x122ef2 4 3 (.sib 0 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0, .gpr 14] []) (.reg (.gpr 3))) #v[3559, 3575]
    (.letOp (n := 3582) (.exec 0x122ef2 (fun s => s.RIP = 0x122ef2) (leaR32Effect 0x122ef2 4 3 (.sib 0 (some 14) 0 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[3559, 3575]
    (.letOp (n := 3583) (.out 0x122ef6 (addR32Imm32Effect 0x122ef6 6 3 0x2e1b2138) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3581]
    (.letOp (n := 3584) (.exec 0x122ef6 (fun s => s.RIP = 0x122ef6) (addR32Imm32Effect 0x122ef6 6 3 0x2e1b2138) (Reg.operands [.gpr 3] [])) #v[3581]
    (.letOp (n := 3585) (.out 0x122efc (movR32R32Effect 0x122efc 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[3507]
    (.letOp (n := 3586) (.exec 0x122efc (fun s => s.RIP = 0x122efc) (movR32R32Effect 0x122efc 2 0 1) (Reg.operands [.gpr 1] [])) #v[3507]
    (.letOp (n := 3587) (.out 0x122efe (rolR32Effect 0x122efe 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3585]
    (.letOp (n := 3588) (.exec 0x122efe (fun s => s.RIP = 0x122efe) (rolR32Effect 0x122efe 3 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3585]
    (.letOp (n := 3589) (.out 0x122f01 (xorR32R32Effect 0x122f01 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[3579, 3573]
    (.letOp (n := 3590) (.exec 0x122f01 (fun s => s.RIP = 0x122f01) (xorR32R32Effect 0x122f01 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[3579, 3573]
    (.letOp (n := 3591) (.out 0x122f03 (xorR32R32Effect 0x122f03 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3587, 3589]
    (.letOp (n := 3592) (.exec 0x122f03 (fun s => s.RIP = 0x122f03) (xorR32R32Effect 0x122f03 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3587, 3589]
    (.letOp (n := 3593) (.out 0x122f05 (movR32R32Effect 0x122f05 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[3397]
    (.letOp (n := 3594) (.exec 0x122f05 (fun s => s.RIP = 0x122f05) (movR32R32Effect 0x122f05 3 2 8) (Reg.operands [.gpr 8] [])) #v[3397]
    (.letOp (n := 3595) (.out 0x122f08 (andR32R32Effect 0x122f08 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[3593, 3303]
    (.letOp (n := 3596) (.exec 0x122f08 (fun s => s.RIP = 0x122f08) (andR32R32Effect 0x122f08 3 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[3593, 3303]
    (.letOp (n := 3597) (.out 0x122f0b (movR32R32Effect 0x122f0b 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[3397]
    (.letOp (n := 3598) (.exec 0x122f0b (fun s => s.RIP = 0x122f0b) (movR32R32Effect 0x122f0b 3 10 8) (Reg.operands [.gpr 8] [])) #v[3397]
    (.letOp (n := 3599) (.out 0x122f0e (xorR32R32Effect 0x122f0e 3 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[3597, 3303]
    (.letOp (n := 3600) (.exec 0x122f0e (fun s => s.RIP = 0x122f0e) (xorR32R32Effect 0x122f0e 3 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[3597, 3303]
    (.letOp (n := 3601) (.out 0x122f11 (andR32R32Effect 0x122f11 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[3599, 3507]
    (.letOp (n := 3602) (.exec 0x122f11 (fun s => s.RIP = 0x122f11) (andR32R32Effect 0x122f11 3 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[3599, 3507]
    (b_l121930_91))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_90 : List UInt8 :=
  [0x31, 0xF2, 0x44, 0x21, 0xCA, 0x31, 0xF2, 0x41, 0x01, 0xEE, 0x89, 0xCF, 0xC1, 0xC7, 0x1E, 0x41,
    0x01, 0xD6, 0x89, 0xCA, 0xC1, 0xC2, 0x13, 0x42, 0x8D, 0x1C, 0x30, 0x81, 0xC3, 0x38, 0x21, 0x1B,
    0x2E, 0x89, 0xC8, 0xC1, 0xC0, 0x0A, 0x31, 0xFA, 0x31, 0xD0, 0x44, 0x89, 0xC2, 0x44, 0x21, 0xEA,
    0x45, 0x89, 0xC2, 0x45, 0x31, 0xEA, 0x41, 0x21, 0xCA] ++ bytes_l121930_91

theorem code_l121930_90 : ∀ x ∈ codeRange 0x122edb bytes_l121930_90, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22edb 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_91

def b_l121930_89 : Block Op Label signature Reg.count 3525 :=
  .letOp (n := 3525) (.out 0x122ea0 (movR32R32Effect 0x122ea0 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[3437]
    (.letOp (n := 3526) (.exec 0x122ea0 (fun s => s.RIP = 0x122ea0) (movR32R32Effect 0x122ea0 3 2 15) (Reg.operands [.gpr 15] [])) #v[3437]
    (.letOp (n := 3527) (.out 0x122ea3 (shrR32Effect 0x122ea3 3 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3525]
    (.letOp (n := 3528) (.exec 0x122ea3 (fun s => s.RIP = 0x122ea3) (shrR32Effect 0x122ea3 3 2 3) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3525]
    (.letOp (n := 3529) (.out 0x122ea6 (xorR32R32Effect 0x122ea6 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[3527, 3523]
    (.letOp (n := 3530) (.exec 0x122ea6 (fun s => s.RIP = 0x122ea6) (xorR32R32Effect 0x122ea6 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[3527, 3523]
    (.letOp (n := 3531) (.exec 0x122ea8 (StorePre 0x122ea8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x122ea8 + BitVec.ofNat 64 5)) 4) (addMREffect 0x122ea8 5 32 10 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[3337, 4]
    (.letOp (n := 3532) (.out 0x122ead (addR32R32Effect 0x122ead 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[3529, 3337]
    (.letOp (n := 3533) (.exec 0x122ead (fun s => s.RIP = 0x122ead) (addR32R32Effect 0x122ead 3 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[3529, 3337]
    (.letOp (n := 3534) (.exec 0x122eb0 (StorePre 0x122eb0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x122eb0 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x122eb0 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3532, 4]
    (.letOp (n := 3535) (.out 0x122eb4 (movR32R32Effect 0x122eb4 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[3337]
    (.letOp (n := 3536) (.exec 0x122eb4 (fun s => s.RIP = 0x122eb4) (movR32R32Effect 0x122eb4 3 2 10) (Reg.operands [.gpr 10] [])) #v[3337]
    (.letOp (n := 3537) (.out 0x122eb7 (shrR32Effect 0x122eb7 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3535]
    (.letOp (n := 3538) (.exec 0x122eb7 (fun s => s.RIP = 0x122eb7) (shrR32Effect 0x122eb7 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3535]
    (.letOp (n := 3539) (.out 0x122eba (xorR32R32Effect 0x122eba 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3537, 3513]
    (.letOp (n := 3540) (.exec 0x122eba (fun s => s.RIP = 0x122eba) (xorR32R32Effect 0x122eba 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3537, 3513]
    (.letOp (n := 3541) (.out 0x122ebc (movR32M32LowEffect 0x122ebc 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 3542) (.exec 0x122ebc (LoadPre 0x122ebc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x122ebc + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x122ebc 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3543) (.out 0x122ec0 (addR32R32Effect 0x122ec0 2 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[3541, 3539]
    (.letOp (n := 3544) (.exec 0x122ec0 (fun s => s.RIP = 0x122ec0) (addR32R32Effect 0x122ec0 2 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[3541, 3539]
    (.letOp (n := 3545) (.out 0x122ec2 (movR32R32Effect 0x122ec2 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[3501]
    (.letOp (n := 3546) (.exec 0x122ec2 (fun s => s.RIP = 0x122ec2) (movR32R32Effect 0x122ec2 3 0 9) (Reg.operands [.gpr 9] [])) #v[3501]
    (.letOp (n := 3547) (.out 0x122ec5 (rolR32Effect 0x122ec5 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3545]
    (.letOp (n := 3548) (.exec 0x122ec5 (fun s => s.RIP = 0x122ec5) (rolR32Effect 0x122ec5 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3545]
    (.letOp (n := 3549) (.out 0x122ec8 (movR32R32Effect 0x122ec8 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[3501]
    (.letOp (n := 3550) (.exec 0x122ec8 (fun s => s.RIP = 0x122ec8) (movR32R32Effect 0x122ec8 3 2 9) (Reg.operands [.gpr 9] [])) #v[3501]
    (.letOp (n := 3551) (.out 0x122ecb (rolR32Effect 0x122ecb 3 2 21) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3549]
    (.letOp (n := 3552) (.exec 0x122ecb (fun s => s.RIP = 0x122ecb) (rolR32Effect 0x122ecb 3 2 21) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3549]
    (.letOp (n := 3553) (.out 0x122ece (xorR32R32Effect 0x122ece 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3551, 3547]
    (.letOp (n := 3554) (.exec 0x122ece (fun s => s.RIP = 0x122ece) (xorR32R32Effect 0x122ece 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3551, 3547]
    (.letOp (n := 3555) (.out 0x122ed0 (movR32R32Effect 0x122ed0 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[3501]
    (.letOp (n := 3556) (.exec 0x122ed0 (fun s => s.RIP = 0x122ed0) (movR32R32Effect 0x122ed0 3 0 9) (Reg.operands [.gpr 9] [])) #v[3501]
    (.letOp (n := 3557) (.out 0x122ed3 (rolR32Effect 0x122ed3 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3555]
    (.letOp (n := 3558) (.exec 0x122ed3 (fun s => s.RIP = 0x122ed3) (rolR32Effect 0x122ed3 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3555]
    (.letOp (n := 3559) (.out 0x122ed6 (xorR32R32Effect 0x122ed6 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3557, 3553]
    (.letOp (n := 3560) (.exec 0x122ed6 (fun s => s.RIP = 0x122ed6) (xorR32R32Effect 0x122ed6 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3557, 3553]
    (.letOp (n := 3561) (.out 0x122ed8 (movR32R32Effect 0x122ed8 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[3395]
    (.letOp (n := 3562) (.exec 0x122ed8 (fun s => s.RIP = 0x122ed8) (movR32R32Effect 0x122ed8 3 2 12) (Reg.operands [.gpr 12] [])) #v[3395]
    (b_l121930_90))))))))))))))))))))))))))))))))))))))

def bytes_l121930_89 : List UInt8 :=
  [0x44, 0x89, 0xFA, 0xC1, 0xEA, 0x03, 0x31, 0xFA, 0x44, 0x01, 0x54, 0x24, 0x14, 0x44, 0x01, 0xD2,
    0x89, 0x54, 0x24, 0x40, 0x44, 0x89, 0xD2, 0xC1, 0xEA, 0x0A, 0x31, 0xC2, 0x8B, 0x6C, 0x24, 0x08,
    0x01, 0xD5, 0x44, 0x89, 0xC8, 0xC1, 0xC0, 0x1A, 0x44, 0x89, 0xCA, 0xC1, 0xC2, 0x15, 0x31, 0xC2,
    0x44, 0x89, 0xC8, 0xC1, 0xC0, 0x07, 0x31, 0xD0, 0x44, 0x89, 0xE2] ++ bytes_l121930_90

theorem code_l121930_89 : ∀ x ∈ codeRange 0x122ea0 bytes_l121930_89, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22ea0 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_90

def b_l121930_88 : Block Op Label signature Reg.count 3485 :=
  .letOp (n := 3485) (.out 0x122e6a (xorR32R32Effect 0x122e6a 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[3483, 3479]
    (.letOp (n := 3486) (.exec 0x122e6a (fun s => s.RIP = 0x122e6a) (xorR32R32Effect 0x122e6a 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[3483, 3479]
    (.letOp (n := 3487) (.out 0x122e6c (movR32R32Effect 0x122e6c 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[3303]
    (.letOp (n := 3488) (.exec 0x122e6c (fun s => s.RIP = 0x122e6c) (movR32R32Effect 0x122e6c 3 7 13) (Reg.operands [.gpr 13] [])) #v[3303]
    (.letOp (n := 3489) (.out 0x122e6f (andR32R32Effect 0x122e6f 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[3487, 3193]
    (.letOp (n := 3490) (.exec 0x122e6f (fun s => s.RIP = 0x122e6f) (andR32R32Effect 0x122e6f 3 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[3487, 3193]
    (.letOp (n := 3491) (.out 0x122e72 (movR32R32Effect 0x122e72 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[3303]
    (.letOp (n := 3492) (.exec 0x122e72 (fun s => s.RIP = 0x122e72) (movR32R32Effect 0x122e72 3 1 13) (Reg.operands [.gpr 13] [])) #v[3303]
    (.letOp (n := 3493) (.out 0x122e75 (xorR32R32Effect 0x122e75 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[3491, 3193]
    (.letOp (n := 3494) (.exec 0x122e75 (fun s => s.RIP = 0x122e75) (xorR32R32Effect 0x122e75 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[3491, 3193]
    (.letOp (n := 3495) (.out 0x122e78 (andR32R32Effect 0x122e78 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[3493, 3397]
    (.letOp (n := 3496) (.exec 0x122e78 (fun s => s.RIP = 0x122e78) (andR32R32Effect 0x122e78 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[3493, 3397]
    (.letOp (n := 3497) (.out 0x122e7b (xorR32R32Effect 0x122e7b 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[3495, 3489]
    (.letOp (n := 3498) (.exec 0x122e7b (fun s => s.RIP = 0x122e7b) (xorR32R32Effect 0x122e7b 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[3495, 3489]
    (.letOp (n := 3499) (.out 0x122e7d (addR32R32Effect 0x122e7d 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[3497, 3485]
    (.letOp (n := 3500) (.exec 0x122e7d (fun s => s.RIP = 0x122e7d) (addR32R32Effect 0x122e7d 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[3497, 3485]
    (.letOp (n := 3501) (.out 0x122e7f (addR32R32Effect 0x122e7f 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[3081, 3473]
    (.letOp (n := 3502) (.exec 0x122e7f (fun s => s.RIP = 0x122e7f) (addR32R32Effect 0x122e7f 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[3081, 3473]
    (.letOp (n := 3503) (.out 0x122e82 (movR32R32Effect 0x122e82 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[3337]
    (.letOp (n := 3504) (.exec 0x122e82 (fun s => s.RIP = 0x122e82) (movR32R32Effect 0x122e82 3 2 10) (Reg.operands [.gpr 10] [])) #v[3337]
    (.letOp (n := 3505) (.out 0x122e85 (rolR32Effect 0x122e85 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3503]
    (.letOp (n := 3506) (.exec 0x122e85 (fun s => s.RIP = 0x122e85) (rolR32Effect 0x122e85 3 2 15) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3503]
    (.letOp (n := 3507) (.out 0x122e88 (addR32R32Effect 0x122e88 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[3499, 3473]
    (.letOp (n := 3508) (.exec 0x122e88 (fun s => s.RIP = 0x122e88) (addR32R32Effect 0x122e88 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[3499, 3473]
    (.letOp (n := 3509) (.out 0x122e8a (movR32R32Effect 0x122e8a 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[3337]
    (.letOp (n := 3510) (.exec 0x122e8a (fun s => s.RIP = 0x122e8a) (movR32R32Effect 0x122e8a 3 0 10) (Reg.operands [.gpr 10] [])) #v[3337]
    (.letOp (n := 3511) (.out 0x122e8d (rolR32Effect 0x122e8d 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3509]
    (.letOp (n := 3512) (.exec 0x122e8d (fun s => s.RIP = 0x122e8d) (rolR32Effect 0x122e8d 3 0 13) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3509]
    (.letOp (n := 3513) (.out 0x122e90 (xorR32R32Effect 0x122e90 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3511, 3505]
    (.letOp (n := 3514) (.exec 0x122e90 (fun s => s.RIP = 0x122e90) (xorR32R32Effect 0x122e90 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3511, 3505]
    (.letOp (n := 3515) (.out 0x122e92 (movR32R32Effect 0x122e92 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[3437]
    (.letOp (n := 3516) (.exec 0x122e92 (fun s => s.RIP = 0x122e92) (movR32R32Effect 0x122e92 3 2 15) (Reg.operands [.gpr 15] [])) #v[3437]
    (.letOp (n := 3517) (.out 0x122e95 (rolR32Effect 0x122e95 3 2 25) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3515]
    (.letOp (n := 3518) (.exec 0x122e95 (fun s => s.RIP = 0x122e95) (rolR32Effect 0x122e95 3 2 25) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3515]
    (.letOp (n := 3519) (.out 0x122e98 (movR32R32Effect 0x122e98 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[3437]
    (.letOp (n := 3520) (.exec 0x122e98 (fun s => s.RIP = 0x122e98) (movR32R32Effect 0x122e98 3 7 15) (Reg.operands [.gpr 15] [])) #v[3437]
    (.letOp (n := 3521) (.out 0x122e9b (rolR32Effect 0x122e9b 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3519]
    (.letOp (n := 3522) (.exec 0x122e9b (fun s => s.RIP = 0x122e9b) (rolR32Effect 0x122e9b 3 7 14) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3519]
    (.letOp (n := 3523) (.out 0x122e9e (xorR32R32Effect 0x122e9e 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[3521, 3517]
    (.letOp (n := 3524) (.exec 0x122e9e (fun s => s.RIP = 0x122e9e) (xorR32R32Effect 0x122e9e 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[3521, 3517]
    (b_l121930_89))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_88 : List UInt8 :=
  [0x31, 0xCA, 0x44, 0x89, 0xEF, 0x44, 0x21, 0xDF, 0x44, 0x89, 0xE9, 0x44, 0x31, 0xD9, 0x44, 0x21,
    0xC1, 0x31, 0xF9, 0x01, 0xD1, 0x41, 0x01, 0xC1, 0x44, 0x89, 0xD2, 0xC1, 0xC2, 0x0F, 0x01, 0xC1,
    0x44, 0x89, 0xD0, 0xC1, 0xC0, 0x0D, 0x31, 0xD0, 0x44, 0x89, 0xFA, 0xC1, 0xC2, 0x19, 0x44, 0x89,
    0xFF, 0xC1, 0xC7, 0x0E, 0x31, 0xD7] ++ bytes_l121930_89

theorem code_l121930_88 : ∀ x ∈ codeRange 0x122e6a bytes_l121930_88, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22e6a 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_89

def b_l121930_87 : Block Op Label signature Reg.count 3445 :=
  .letOp (n := 3445) (.out 0x122e32 (rolR32Effect 0x122e32 3 2 21) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3443]
    (.letOp (n := 3446) (.exec 0x122e32 (fun s => s.RIP = 0x122e32) (rolR32Effect 0x122e32 3 2 21) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3443]
    (.letOp (n := 3447) (.out 0x122e35 (xorR32R32Effect 0x122e35 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[3445, 3441]
    (.letOp (n := 3448) (.exec 0x122e35 (fun s => s.RIP = 0x122e35) (xorR32R32Effect 0x122e35 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[3445, 3441]
    (.letOp (n := 3449) (.out 0x122e37 (movR32R32Effect 0x122e37 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[3395]
    (.letOp (n := 3450) (.exec 0x122e37 (fun s => s.RIP = 0x122e37) (movR32R32Effect 0x122e37 3 1 12) (Reg.operands [.gpr 12] [])) #v[3395]
    (.letOp (n := 3451) (.out 0x122e3a (rolR32Effect 0x122e3a 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3449]
    (.letOp (n := 3452) (.exec 0x122e3a (fun s => s.RIP = 0x122e3a) (rolR32Effect 0x122e3a 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3449]
    (.letOp (n := 3453) (.out 0x122e3d (xorR32R32Effect 0x122e3d 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[3451, 3447]
    (.letOp (n := 3454) (.exec 0x122e3d (fun s => s.RIP = 0x122e3d) (xorR32R32Effect 0x122e3d 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[3451, 3447]
    (.letOp (n := 3455) (.out 0x122e3f (movR32R32Effect 0x122e3f 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[3297]
    (.letOp (n := 3456) (.exec 0x122e3f (fun s => s.RIP = 0x122e3f) (movR32R32Effect 0x122e3f 2 2 6) (Reg.operands [.gpr 6] [])) #v[3297]
    (.letOp (n := 3457) (.out 0x122e41 (xorR32R32Effect 0x122e41 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[3455, 3187]
    (.letOp (n := 3458) (.exec 0x122e41 (fun s => s.RIP = 0x122e41) (xorR32R32Effect 0x122e41 3 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[3455, 3187]
    (.letOp (n := 3459) (.out 0x122e44 (andR32R32Effect 0x122e44 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[3457, 3395]
    (.letOp (n := 3460) (.exec 0x122e44 (fun s => s.RIP = 0x122e44) (andR32R32Effect 0x122e44 3 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[3457, 3395]
    (.letOp (n := 3461) (.out 0x122e47 (xorR32R32Effect 0x122e47 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[3459, 3187]
    (.letOp (n := 3462) (.exec 0x122e47 (fun s => s.RIP = 0x122e47) (xorR32R32Effect 0x122e47 3 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[3459, 3187]
    (.letOp (n := 3463) (.out 0x122e4a (addR32R32Effect 0x122e4a 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[3355, 3437]
    (.letOp (n := 3464) (.exec 0x122e4a (fun s => s.RIP = 0x122e4a) (addR32R32Effect 0x122e4a 3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[3355, 3437]
    (.letOp (n := 3465) (.out 0x122e4d (addR32R32Effect 0x122e4d 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3463, 3461]
    (.letOp (n := 3466) (.exec 0x122e4d (fun s => s.RIP = 0x122e4d) (addR32R32Effect 0x122e4d 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3463, 3461]
    (.letOp (n := 3467) (.out 0x122e4f (movR32R32Effect 0x122e4f 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[3397]
    (.letOp (n := 3468) (.exec 0x122e4f (fun s => s.RIP = 0x122e4f) (movR32R32Effect 0x122e4f 3 2 8) (Reg.operands [.gpr 8] [])) #v[3397]
    (.letOp (n := 3469) (.out 0x122e52 (rolR32Effect 0x122e52 3 2 30) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3467]
    (.letOp (n := 3470) (.exec 0x122e52 (fun s => s.RIP = 0x122e52) (rolR32Effect 0x122e52 3 2 30) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3467]
    (.letOp (n := 3471) (.out 0x122e55 (addR32R32Effect 0x122e55 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3465, 3453]
    (.letOp (n := 3472) (.exec 0x122e55 (fun s => s.RIP = 0x122e55) (addR32R32Effect 0x122e55 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3465, 3453]
    (.letOp (n := 3473) (.out 0x122e57 (addEaxImm32Effect 0x122e57 0x27b70a85) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[3471]
    (.letOp (n := 3474) (.exec 0x122e57 (fun s => s.RIP = 0x122e57) (addEaxImm32Effect 0x122e57 0x27b70a85) (Reg.operands [.gpr 0] [])) #v[3471]
    (.letOp (n := 3475) (.out 0x122e5c (movR32R32Effect 0x122e5c 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[3397]
    (.letOp (n := 3476) (.exec 0x122e5c (fun s => s.RIP = 0x122e5c) (movR32R32Effect 0x122e5c 3 1 8) (Reg.operands [.gpr 8] [])) #v[3397]
    (.letOp (n := 3477) (.out 0x122e5f (rolR32Effect 0x122e5f 3 1 19) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3475]
    (.letOp (n := 3478) (.exec 0x122e5f (fun s => s.RIP = 0x122e5f) (rolR32Effect 0x122e5f 3 1 19) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3475]
    (.letOp (n := 3479) (.out 0x122e62 (xorR32R32Effect 0x122e62 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[3477, 3469]
    (.letOp (n := 3480) (.exec 0x122e62 (fun s => s.RIP = 0x122e62) (xorR32R32Effect 0x122e62 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[3477, 3469]
    (.letOp (n := 3481) (.out 0x122e64 (movR32R32Effect 0x122e64 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[3397]
    (.letOp (n := 3482) (.exec 0x122e64 (fun s => s.RIP = 0x122e64) (movR32R32Effect 0x122e64 3 2 8) (Reg.operands [.gpr 8] [])) #v[3397]
    (.letOp (n := 3483) (.out 0x122e67 (rolR32Effect 0x122e67 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3481]
    (.letOp (n := 3484) (.exec 0x122e67 (fun s => s.RIP = 0x122e67) (rolR32Effect 0x122e67 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3481]
    (b_l121930_88))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_87 : List UInt8 :=
  [0xC1, 0xC2, 0x15, 0x31, 0xCA, 0x44, 0x89, 0xE1, 0xC1, 0xC1, 0x07, 0x31, 0xD1, 0x89, 0xF2, 0x44,
    0x31, 0xF2, 0x44, 0x21, 0xE2, 0x44, 0x31, 0xF2, 0x44, 0x01, 0xF8, 0x01, 0xD0, 0x44, 0x89, 0xC2,
    0xC1, 0xC2, 0x1E, 0x01, 0xC8, 0x05, 0x85, 0x0A, 0xB7, 0x27, 0x44, 0x89, 0xC1, 0xC1, 0xC1, 0x13,
    0x31, 0xD1, 0x44, 0x89, 0xC2, 0xC1, 0xC2, 0x0A] ++ bytes_l121930_88

theorem code_l121930_87 : ∀ x ∈ codeRange 0x122e32 bytes_l121930_87, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22e32 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_88

def b_l121930_86 : Block Op Label signature Reg.count 3407 :=
  .letOp (n := 3407) (.out 0x122df8 (xorR32R32Effect 0x122df8 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[3405, 3401]
    (.letOp (n := 3408) (.exec 0x122df8 (fun s => s.RIP = 0x122df8) (xorR32R32Effect 0x122df8 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[3405, 3401]
    (.letOp (n := 3409) (.out 0x122dfa (movR32R32Effect 0x122dfa 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[3337]
    (.letOp (n := 3410) (.exec 0x122dfa (fun s => s.RIP = 0x122dfa) (movR32R32Effect 0x122dfa 3 2 10) (Reg.operands [.gpr 10] [])) #v[3337]
    (.letOp (n := 3411) (.out 0x122dfd (rolR32Effect 0x122dfd 3 2 25) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3409]
    (.letOp (n := 3412) (.exec 0x122dfd (fun s => s.RIP = 0x122dfd) (rolR32Effect 0x122dfd 3 2 25) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3409]
    (.letOp (n := 3413) (.out 0x122e00 (movR32R32Effect 0x122e00 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 10] []) (.reg (.gpr 7))) #v[3337]
    (.letOp (n := 3414) (.exec 0x122e00 (fun s => s.RIP = 0x122e00) (movR32R32Effect 0x122e00 3 7 10) (Reg.operands [.gpr 10] [])) #v[3337]
    (.letOp (n := 3415) (.out 0x122e03 (rolR32Effect 0x122e03 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3413]
    (.letOp (n := 3416) (.exec 0x122e03 (fun s => s.RIP = 0x122e03) (rolR32Effect 0x122e03 3 7 14) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3413]
    (.letOp (n := 3417) (.out 0x122e06 (xorR32R32Effect 0x122e06 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[3415, 3411]
    (.letOp (n := 3418) (.exec 0x122e06 (fun s => s.RIP = 0x122e06) (xorR32R32Effect 0x122e06 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[3415, 3411]
    (.letOp (n := 3419) (.out 0x122e08 (movR32R32Effect 0x122e08 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[3337]
    (.letOp (n := 3420) (.exec 0x122e08 (fun s => s.RIP = 0x122e08) (movR32R32Effect 0x122e08 3 2 10) (Reg.operands [.gpr 10] [])) #v[3337]
    (.letOp (n := 3421) (.out 0x122e0b (shrR32Effect 0x122e0b 3 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3419]
    (.letOp (n := 3422) (.exec 0x122e0b (fun s => s.RIP = 0x122e0b) (shrR32Effect 0x122e0b 3 2 3) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3419]
    (.letOp (n := 3423) (.out 0x122e0e (xorR32R32Effect 0x122e0e 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[3421, 3417]
    (.letOp (n := 3424) (.exec 0x122e0e (fun s => s.RIP = 0x122e0e) (xorR32R32Effect 0x122e0e 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[3421, 3417]
    (.letOp (n := 3425) (.exec 0x122e10 (StorePre 0x122e10 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x122e10 + BitVec.ofNat 64 4)) 4) (addMREffect 0x122e10 4 32 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[3229, 4]
    (.letOp (n := 3426) (.out 0x122e14 (addR32R32Effect 0x122e14 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[3423, 3229]
    (.letOp (n := 3427) (.exec 0x122e14 (fun s => s.RIP = 0x122e14) (addR32R32Effect 0x122e14 2 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[3423, 3229]
    (.letOp (n := 3428) (.exec 0x122e16 (StorePre 0x122e16 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x122e16 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x122e16 2 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3426, 4]
    (.letOp (n := 3429) (.out 0x122e1a (movR32R32Effect 0x122e1a 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[3229]
    (.letOp (n := 3430) (.exec 0x122e1a (fun s => s.RIP = 0x122e1a) (movR32R32Effect 0x122e1a 2 2 5) (Reg.operands [.gpr 5] [])) #v[3229]
    (.letOp (n := 3431) (.out 0x122e1c (shrR32Effect 0x122e1c 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3429]
    (.letOp (n := 3432) (.exec 0x122e1c (fun s => s.RIP = 0x122e1c) (shrR32Effect 0x122e1c 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3429]
    (.letOp (n := 3433) (.out 0x122e1f (xorR32R32Effect 0x122e1f 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[3431, 3407]
    (.letOp (n := 3434) (.exec 0x122e1f (fun s => s.RIP = 0x122e1f) (xorR32R32Effect 0x122e1f 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[3431, 3407]
    (.letOp (n := 3435) (.out 0x122e21 (movR32M32Effect 0x122e21 15 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 3436) (.exec 0x122e21 (LoadPre 0x122e21 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x122e21 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x122e21 15 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3437) (.out 0x122e26 (addR32R32Effect 0x122e26 3 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[3435, 3433]
    (.letOp (n := 3438) (.exec 0x122e26 (fun s => s.RIP = 0x122e26) (addR32R32Effect 0x122e26 3 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[3435, 3433]
    (.letOp (n := 3439) (.out 0x122e29 (movR32R32Effect 0x122e29 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[3395]
    (.letOp (n := 3440) (.exec 0x122e29 (fun s => s.RIP = 0x122e29) (movR32R32Effect 0x122e29 3 1 12) (Reg.operands [.gpr 12] [])) #v[3395]
    (.letOp (n := 3441) (.out 0x122e2c (rolR32Effect 0x122e2c 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3439]
    (.letOp (n := 3442) (.exec 0x122e2c (fun s => s.RIP = 0x122e2c) (rolR32Effect 0x122e2c 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3439]
    (.letOp (n := 3443) (.out 0x122e2f (movR32R32Effect 0x122e2f 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[3395]
    (.letOp (n := 3444) (.exec 0x122e2f (fun s => s.RIP = 0x122e2f) (movR32R32Effect 0x122e2f 3 2 12) (Reg.operands [.gpr 12] [])) #v[3395]
    (b_l121930_87))))))))))))))))))))))))))))))))))))))

def bytes_l121930_86 : List UInt8 :=
  [0x31, 0xD1, 0x44, 0x89, 0xD2, 0xC1, 0xC2, 0x19, 0x44, 0x89, 0xD7, 0xC1, 0xC7, 0x0E, 0x31, 0xD7,
    0x44, 0x89, 0xD2, 0xC1, 0xEA, 0x03, 0x31, 0xFA, 0x01, 0x6C, 0x24, 0x68, 0x01, 0xEA, 0x89, 0x54,
    0x24, 0x04, 0x89, 0xEA, 0xC1, 0xEA, 0x0A, 0x31, 0xCA, 0x44, 0x8B, 0x7C, 0x24, 0x0C, 0x41, 0x01,
    0xD7, 0x44, 0x89, 0xE1, 0xC1, 0xC1, 0x1A, 0x44, 0x89, 0xE2] ++ bytes_l121930_87

theorem code_l121930_86 : ∀ x ∈ codeRange 0x122df8 bytes_l121930_86, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22df8 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_87

def b_l121930_85 : Block Op Label signature Reg.count 3367 :=
  .letOp (n := 3367) (.out 0x122dc0 (rolR32Effect 0x122dc0 3 2 30) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3365]
    (.letOp (n := 3368) (.exec 0x122dc0 (fun s => s.RIP = 0x122dc0) (rolR32Effect 0x122dc0 3 2 30) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3365]
    (.letOp (n := 3369) (.out 0x122dc3 (movR32R32Effect 0x122dc3 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[3303]
    (.letOp (n := 3370) (.exec 0x122dc3 (fun s => s.RIP = 0x122dc3) (movR32R32Effect 0x122dc3 3 7 13) (Reg.operands [.gpr 13] [])) #v[3303]
    (.letOp (n := 3371) (.out 0x122dc6 (rolR32Effect 0x122dc6 3 7 19) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3369]
    (.letOp (n := 3372) (.exec 0x122dc6 (fun s => s.RIP = 0x122dc6) (rolR32Effect 0x122dc6 3 7 19) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3369]
    (.letOp (n := 3373) (.out 0x122dc9 (xorR32R32Effect 0x122dc9 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[3371, 3367]
    (.letOp (n := 3374) (.exec 0x122dc9 (fun s => s.RIP = 0x122dc9) (xorR32R32Effect 0x122dc9 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[3371, 3367]
    (.letOp (n := 3375) (.out 0x122dcb (movR32R32Effect 0x122dcb 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[3303]
    (.letOp (n := 3376) (.exec 0x122dcb (fun s => s.RIP = 0x122dcb) (movR32R32Effect 0x122dcb 3 2 13) (Reg.operands [.gpr 13] [])) #v[3303]
    (.letOp (n := 3377) (.out 0x122dce (rolR32Effect 0x122dce 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3375]
    (.letOp (n := 3378) (.exec 0x122dce (fun s => s.RIP = 0x122dce) (rolR32Effect 0x122dce 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3375]
    (.letOp (n := 3379) (.out 0x122dd1 (xorR32R32Effect 0x122dd1 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[3377, 3373]
    (.letOp (n := 3380) (.exec 0x122dd1 (fun s => s.RIP = 0x122dd1) (xorR32R32Effect 0x122dd1 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[3377, 3373]
    (.letOp (n := 3381) (.out 0x122dd3 (movR32R32Effect 0x122dd3 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 11] []) (.reg (.gpr 7))) #v[3193]
    (.letOp (n := 3382) (.exec 0x122dd3 (fun s => s.RIP = 0x122dd3) (movR32R32Effect 0x122dd3 3 7 11) (Reg.operands [.gpr 11] [])) #v[3193]
    (.letOp (n := 3383) (.out 0x122dd6 (andR32R32Effect 0x122dd6 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[3381, 3081]
    (.letOp (n := 3384) (.exec 0x122dd6 (fun s => s.RIP = 0x122dd6) (andR32R32Effect 0x122dd6 3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[3381, 3081]
    (.letOp (n := 3385) (.out 0x122dd9 (movR32R32Effect 0x122dd9 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[3193]
    (.letOp (n := 3386) (.exec 0x122dd9 (fun s => s.RIP = 0x122dd9) (movR32R32Effect 0x122dd9 3 8 11) (Reg.operands [.gpr 11] [])) #v[3193]
    (.letOp (n := 3387) (.out 0x122ddc (xorR32R32Effect 0x122ddc 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[3385, 3081]
    (.letOp (n := 3388) (.exec 0x122ddc (fun s => s.RIP = 0x122ddc) (xorR32R32Effect 0x122ddc 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[3385, 3081]
    (.letOp (n := 3389) (.out 0x122ddf (andR32R32Effect 0x122ddf 3 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[3387, 3303]
    (.letOp (n := 3390) (.exec 0x122ddf (fun s => s.RIP = 0x122ddf) (andR32R32Effect 0x122ddf 3 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[3387, 3303]
    (.letOp (n := 3391) (.out 0x122de2 (xorR32R32Effect 0x122de2 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[3389, 3383]
    (.letOp (n := 3392) (.exec 0x122de2 (fun s => s.RIP = 0x122de2) (xorR32R32Effect 0x122de2 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[3389, 3383]
    (.letOp (n := 3393) (.out 0x122de5 (addR32R32Effect 0x122de5 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[3391, 3379]
    (.letOp (n := 3394) (.exec 0x122de5 (fun s => s.RIP = 0x122de5) (addR32R32Effect 0x122de5 3 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[3391, 3379]
    (.letOp (n := 3395) (.out 0x122de8 (addR32R32Effect 0x122de8 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[2971, 3363]
    (.letOp (n := 3396) (.exec 0x122de8 (fun s => s.RIP = 0x122de8) (addR32R32Effect 0x122de8 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[2971, 3363]
    (.letOp (n := 3397) (.out 0x122deb (addR32R32Effect 0x122deb 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[3393, 3363]
    (.letOp (n := 3398) (.exec 0x122deb (fun s => s.RIP = 0x122deb) (addR32R32Effect 0x122deb 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[3393, 3363]
    (.letOp (n := 3399) (.out 0x122dee (movR32R32Effect 0x122dee 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[3229]
    (.letOp (n := 3400) (.exec 0x122dee (fun s => s.RIP = 0x122dee) (movR32R32Effect 0x122dee 2 2 5) (Reg.operands [.gpr 5] [])) #v[3229]
    (.letOp (n := 3401) (.out 0x122df0 (rolR32Effect 0x122df0 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3399]
    (.letOp (n := 3402) (.exec 0x122df0 (fun s => s.RIP = 0x122df0) (rolR32Effect 0x122df0 3 2 15) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3399]
    (.letOp (n := 3403) (.out 0x122df3 (movR32R32Effect 0x122df3 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[3229]
    (.letOp (n := 3404) (.exec 0x122df3 (fun s => s.RIP = 0x122df3) (movR32R32Effect 0x122df3 2 1 5) (Reg.operands [.gpr 5] [])) #v[3229]
    (.letOp (n := 3405) (.out 0x122df5 (rolR32Effect 0x122df5 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3403]
    (.letOp (n := 3406) (.exec 0x122df5 (fun s => s.RIP = 0x122df5) (rolR32Effect 0x122df5 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3403]
    (b_l121930_86))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_85 : List UInt8 :=
  [0xC1, 0xC2, 0x1E, 0x44, 0x89, 0xEF, 0xC1, 0xC7, 0x13, 0x31, 0xD7, 0x44, 0x89, 0xEA, 0xC1, 0xC2,
    0x0A, 0x31, 0xFA, 0x44, 0x89, 0xDF, 0x44, 0x21, 0xCF, 0x45, 0x89, 0xD8, 0x45, 0x31, 0xC8, 0x45,
    0x21, 0xE8, 0x41, 0x31, 0xF8, 0x41, 0x01, 0xD0, 0x41, 0x01, 0xCC, 0x41, 0x01, 0xC8, 0x89, 0xEA,
    0xC1, 0xC2, 0x0F, 0x89, 0xE9, 0xC1, 0xC1, 0x0D] ++ bytes_l121930_86

theorem code_l121930_85 : ∀ x ∈ codeRange 0x122dc0 bytes_l121930_85, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22dc0 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_86

def b_l121930_84 : Block Op Label signature Reg.count 3327 :=
  .letOp (n := 3327) (.out 0x122d81 (rolR32Effect 0x122d81 3 7 26) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3325]
    (.letOp (n := 3328) (.exec 0x122d81 (fun s => s.RIP = 0x122d81) (rolR32Effect 0x122d81 3 7 26) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3325]
    (.letOp (n := 3329) (.out 0x122d84 (xorR32R32Effect 0x122d84 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3323, 3309]
    (.letOp (n := 3330) (.exec 0x122d84 (fun s => s.RIP = 0x122d84) (xorR32R32Effect 0x122d84 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3323, 3309]
    (.letOp (n := 3331) (.out 0x122d86 (movR32R32Effect 0x122d86 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[3297]
    (.letOp (n := 3332) (.exec 0x122d86 (fun s => s.RIP = 0x122d86) (movR32R32Effect 0x122d86 2 1 6) (Reg.operands [.gpr 6] [])) #v[3297]
    (.letOp (n := 3333) (.out 0x122d88 (rolR32Effect 0x122d88 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3331]
    (.letOp (n := 3334) (.exec 0x122d88 (fun s => s.RIP = 0x122d88) (rolR32Effect 0x122d88 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3331]
    (.letOp (n := 3335) (.out 0x122d8b (movR32M32Effect 0x122d8b 10 (.sib 4 none 0 (.d32 0x8c))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 3336) (.exec 0x122d8b (LoadPre 0x122d8b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x122d8b + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x122d8b 10 (.sib 4 none 0 (.d32 0x8c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3337) (.out 0x122d93 (addR32R32Effect 0x122d93 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[3335, 3329]
    (.letOp (n := 3338) (.exec 0x122d93 (fun s => s.RIP = 0x122d93) (addR32R32Effect 0x122d93 3 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[3335, 3329]
    (.letOp (n := 3339) (.out 0x122d96 (movR32R32Effect 0x122d96 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[3297]
    (.letOp (n := 3340) (.exec 0x122d96 (fun s => s.RIP = 0x122d96) (movR32R32Effect 0x122d96 2 2 6) (Reg.operands [.gpr 6] [])) #v[3297]
    (.letOp (n := 3341) (.out 0x122d98 (rolR32Effect 0x122d98 3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3339]
    (.letOp (n := 3342) (.exec 0x122d98 (fun s => s.RIP = 0x122d98) (rolR32Effect 0x122d98 3 2 7) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3339]
    (.letOp (n := 3343) (.out 0x122d9b (xorR32R32Effect 0x122d9b 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[3333, 3327]
    (.letOp (n := 3344) (.exec 0x122d9b (fun s => s.RIP = 0x122d9b) (xorR32R32Effect 0x122d9b 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[3333, 3327]
    (.letOp (n := 3345) (.out 0x122d9d (xorR32R32Effect 0x122d9d 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[3341, 3343]
    (.letOp (n := 3346) (.exec 0x122d9d (fun s => s.RIP = 0x122d9d) (xorR32R32Effect 0x122d9d 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[3341, 3343]
    (.letOp (n := 3347) (.out 0x122d9f (movR32R32Effect 0x122d9f 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[3187]
    (.letOp (n := 3348) (.exec 0x122d9f (fun s => s.RIP = 0x122d9f) (movR32R32Effect 0x122d9f 3 1 14) (Reg.operands [.gpr 14] [])) #v[3187]
    (.letOp (n := 3349) (.out 0x122da2 (xorR32R32Effect 0x122da2 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[3347, 3075]
    (.letOp (n := 3350) (.exec 0x122da2 (fun s => s.RIP = 0x122da2) (xorR32R32Effect 0x122da2 3 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[3347, 3075]
    (.letOp (n := 3351) (.out 0x122da5 (andR32R32Effect 0x122da5 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[3349, 3297]
    (.letOp (n := 3352) (.exec 0x122da5 (fun s => s.RIP = 0x122da5) (andR32R32Effect 0x122da5 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[3349, 3297]
    (.letOp (n := 3353) (.out 0x122da7 (xorR32R32Effect 0x122da7 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[3351, 3075]
    (.letOp (n := 3354) (.exec 0x122da7 (fun s => s.RIP = 0x122da7) (xorR32R32Effect 0x122da7 3 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[3351, 3075]
    (.letOp (n := 3355) (.out 0x122daa (movR64R64Effect 0x122daa 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[3075]
    (.letOp (n := 3356) (.exec 0x122daa (fun s => s.RIP = 0x122daa) (movR64R64Effect 0x122daa 0 15) (Reg.operands [.gpr 15] [])) #v[3075]
    (.letOp (n := 3357) (.out 0x122dad (addR32R32Effect 0x122dad 3 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[2969, 3337]
    (.letOp (n := 3358) (.exec 0x122dad (fun s => s.RIP = 0x122dad) (addR32R32Effect 0x122dad 3 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[2969, 3337]
    (.letOp (n := 3359) (.out 0x122db0 (addR32R32Effect 0x122db0 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[3357, 3353]
    (.letOp (n := 3360) (.exec 0x122db0 (fun s => s.RIP = 0x122db0) (addR32R32Effect 0x122db0 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[3357, 3353]
    (.letOp (n := 3361) (.out 0x122db3 (leaR32Effect 0x122db3 4 1 (.sib 2 (some 8) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 8] []) (.reg (.gpr 1))) #v[3345, 3359]
    (.letOp (n := 3362) (.exec 0x122db3 (fun s => s.RIP = 0x122db3) (leaR32Effect 0x122db3 4 1 (.sib 2 (some 8) 0 .none)) (Reg.operands [.gpr 2, .gpr 8] [])) #v[3345, 3359]
    (.letOp (n := 3363) (.out 0x122db7 (addR32Imm32Effect 0x122db7 6 1 0x14292967) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[3361]
    (.letOp (n := 3364) (.exec 0x122db7 (fun s => s.RIP = 0x122db7) (addR32Imm32Effect 0x122db7 6 1 0x14292967) (Reg.operands [.gpr 1] [])) #v[3361]
    (.letOp (n := 3365) (.out 0x122dbd (movR32R32Effect 0x122dbd 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[3303]
    (.letOp (n := 3366) (.exec 0x122dbd (fun s => s.RIP = 0x122dbd) (movR32R32Effect 0x122dbd 3 2 13) (Reg.operands [.gpr 13] [])) #v[3303]
    (b_l121930_85))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_84 : List UInt8 :=
  [0xC1, 0xC7, 0x1A, 0x31, 0xC8, 0x89, 0xF1, 0xC1, 0xC1, 0x15, 0x44, 0x8B, 0x94, 0x24, 0x8C, 0x00,
    0x00, 0x00, 0x41, 0x01, 0xC2, 0x89, 0xF2, 0xC1, 0xC2, 0x07, 0x31, 0xF9, 0x31, 0xCA, 0x44, 0x89,
    0xF1, 0x44, 0x31, 0xF9, 0x21, 0xF1, 0x44, 0x31, 0xF9, 0x4C, 0x89, 0xF8, 0x45, 0x01, 0xD0, 0x41,
    0x01, 0xC8, 0x42, 0x8D, 0x0C, 0x02, 0x81, 0xC1, 0x67, 0x29, 0x29, 0x14, 0x44, 0x89, 0xEA] ++ bytes_l121930_85

theorem code_l121930_84 : ∀ x ∈ codeRange 0x122d81 bytes_l121930_84, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22d81 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_85

def b_l121930_83 : Block Op Label signature Reg.count 3289 :=
  .letOp (n := 3289) (.out 0x122d4a (rolR32Effect 0x122d4a 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3287]
    (.letOp (n := 3290) (.exec 0x122d4a (fun s => s.RIP = 0x122d4a) (rolR32Effect 0x122d4a 3 7 15) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3287]
    (.letOp (n := 3291) (.out 0x122d4d (addR32R32Effect 0x122d4d 3 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[3285, 3273]
    (.letOp (n := 3292) (.exec 0x122d4d (fun s => s.RIP = 0x122d4d) (addR32R32Effect 0x122d4d 3 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[3285, 3273]
    (.letOp (n := 3293) (.out 0x122d50 (movR32R32Effect 0x122d50 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[3117]
    (.letOp (n := 3294) (.exec 0x122d50 (fun s => s.RIP = 0x122d50) (movR32R32Effect 0x122d50 2 1 0) (Reg.operands [.gpr 0] [])) #v[3117]
    (.letOp (n := 3295) (.out 0x122d52 (rolR32Effect 0x122d52 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3293]
    (.letOp (n := 3296) (.exec 0x122d52 (fun s => s.RIP = 0x122d52) (rolR32Effect 0x122d52 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3293]
    (.letOp (n := 3297) (.out 0x122d55 (addR32R32Effect 0x122d55 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[2877, 3257]
    (.letOp (n := 3298) (.exec 0x122d55 (fun s => s.RIP = 0x122d55) (addR32R32Effect 0x122d55 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[2877, 3257]
    (.letOp (n := 3299) (.out 0x122d57 (movR32R32Effect 0x122d57 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 5] []) (.reg (.gpr 10))) #v[3229]
    (.letOp (n := 3300) (.exec 0x122d57 (fun s => s.RIP = 0x122d57) (movR32R32Effect 0x122d57 3 10 5) (Reg.operands [.gpr 5] [])) #v[3229]
    (.letOp (n := 3301) (.out 0x122d5a (rolR32Effect 0x122d5a 4 10 25) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[3299]
    (.letOp (n := 3302) (.exec 0x122d5a (fun s => s.RIP = 0x122d5a) (rolR32Effect 0x122d5a 4 10 25) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3299]
    (.letOp (n := 3303) (.out 0x122d5e (addR32R32Effect 0x122d5e 3 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[3291, 3257]
    (.letOp (n := 3304) (.exec 0x122d5e (fun s => s.RIP = 0x122d5e) (addR32R32Effect 0x122d5e 3 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[3291, 3257]
    (.letOp (n := 3305) (.out 0x122d61 (movR32R32Effect 0x122d61 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[3229]
    (.letOp (n := 3306) (.exec 0x122d61 (fun s => s.RIP = 0x122d61) (movR32R32Effect 0x122d61 2 2 5) (Reg.operands [.gpr 5] [])) #v[3229]
    (.letOp (n := 3307) (.out 0x122d63 (rolR32Effect 0x122d63 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3305]
    (.letOp (n := 3308) (.exec 0x122d63 (fun s => s.RIP = 0x122d63) (rolR32Effect 0x122d63 3 2 14) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3305]
    (.letOp (n := 3309) (.out 0x122d66 (xorR32R32Effect 0x122d66 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[3295, 3289]
    (.letOp (n := 3310) (.exec 0x122d66 (fun s => s.RIP = 0x122d66) (xorR32R32Effect 0x122d66 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[3295, 3289]
    (.letOp (n := 3311) (.out 0x122d68 (xorR32R32Effect 0x122d68 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[3307, 3301]
    (.letOp (n := 3312) (.exec 0x122d68 (fun s => s.RIP = 0x122d68) (xorR32R32Effect 0x122d68 3 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[3307, 3301]
    (.letOp (n := 3313) (.out 0x122d6b (movR32R32Effect 0x122d6b 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[3229]
    (.letOp (n := 3314) (.exec 0x122d6b (fun s => s.RIP = 0x122d6b) (movR32R32Effect 0x122d6b 2 7 5) (Reg.operands [.gpr 5] [])) #v[3229]
    (.letOp (n := 3315) (.out 0x122d6d (shrR32Effect 0x122d6d 3 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3313]
    (.letOp (n := 3316) (.exec 0x122d6d (fun s => s.RIP = 0x122d6d) (shrR32Effect 0x122d6d 3 7 3) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3313]
    (.letOp (n := 3317) (.out 0x122d70 (xorR32R32Effect 0x122d70 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[3315, 3311]
    (.letOp (n := 3318) (.exec 0x122d70 (fun s => s.RIP = 0x122d70) (xorR32R32Effect 0x122d70 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[3315, 3311]
    (.letOp (n := 3319) (.exec 0x122d72 (StorePre 0x122d72 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x122d72 + BitVec.ofNat 64 4)) 4) (addMREffect 0x122d72 4 32 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[3117, 4]
    (.letOp (n := 3320) (.out 0x122d76 (addR32R32Effect 0x122d76 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[3317, 3117]
    (.letOp (n := 3321) (.exec 0x122d76 (fun s => s.RIP = 0x122d76) (addR32R32Effect 0x122d76 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[3317, 3117]
    (.letOp (n := 3322) (.exec 0x122d78 (StorePre 0x122d78 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x122d78 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x122d78 7 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[3320, 4]
    (.letOp (n := 3323) (.out 0x122d7c (shrR32Effect 0x122d7c 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[3117]
    (.letOp (n := 3324) (.exec 0x122d7c (fun s => s.RIP = 0x122d7c) (shrR32Effect 0x122d7c 3 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3117]
    (.letOp (n := 3325) (.out 0x122d7f (movR32R32Effect 0x122d7f 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[3297]
    (.letOp (n := 3326) (.exec 0x122d7f (fun s => s.RIP = 0x122d7f) (movR32R32Effect 0x122d7f 2 7 6) (Reg.operands [.gpr 6] [])) #v[3297]
    (b_l121930_84))))))))))))))))))))))))))))))))))))))

def bytes_l121930_83 : List UInt8 :=
  [0xC1, 0xC7, 0x0F, 0x41, 0x01, 0xCD, 0x89, 0xC1, 0xC1, 0xC1, 0x0D, 0x01, 0xD6, 0x41, 0x89, 0xEA,
    0x41, 0xC1, 0xC2, 0x19, 0x41, 0x01, 0xD5, 0x89, 0xEA, 0xC1, 0xC2, 0x0E, 0x31, 0xF9, 0x44, 0x31,
    0xD2, 0x89, 0xEF, 0xC1, 0xEF, 0x03, 0x31, 0xD7, 0x01, 0x44, 0x24, 0x78, 0x01, 0xC7, 0x89, 0x7C,
    0x24, 0x24, 0xC1, 0xE8, 0x0A, 0x89, 0xF7] ++ bytes_l121930_84

theorem code_l121930_83 : ∀ x ∈ codeRange 0x122d4a bytes_l121930_83, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22d4a 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_84

def b_l121930_82 : Block Op Label signature Reg.count 3249 :=
  .letOp (n := 3249) (.out 0x122d10 (xorR32R32Effect 0x122d10 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[3247, 2969]
    (.letOp (n := 3250) (.exec 0x122d10 (fun s => s.RIP = 0x122d10) (xorR32R32Effect 0x122d10 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[3247, 2969]
    (.letOp (n := 3251) (.out 0x122d13 (addR32R32Effect 0x122d13 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[2871, 3229]
    (.letOp (n := 3252) (.exec 0x122d13 (fun s => s.RIP = 0x122d13) (addR32R32Effect 0x122d13 2 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[2871, 3229]
    (.letOp (n := 3253) (.out 0x122d15 (addR32R32Effect 0x122d15 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[3251, 3249]
    (.letOp (n := 3254) (.exec 0x122d15 (fun s => s.RIP = 0x122d15) (addR32R32Effect 0x122d15 2 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[3251, 3249]
    (.letOp (n := 3255) (.out 0x122d17 (leaR32Effect 0x122d17 3 2 (.sib 1 (some 3) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 3] []) (.reg (.gpr 2))) #v[3241, 3253]
    (.letOp (n := 3256) (.exec 0x122d17 (fun s => s.RIP = 0x122d17) (leaR32Effect 0x122d17 3 2 (.sib 1 (some 3) 0 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[3241, 3253]
    (.letOp (n := 3257) (.out 0x122d1a (addR32Imm32Effect 0x122d1a 6 2 0x6ca6351) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[3255]
    (.letOp (n := 3258) (.exec 0x122d1a (fun s => s.RIP = 0x122d1a) (addR32Imm32Effect 0x122d1a 6 2 0x6ca6351) (Reg.operands [.gpr 2] [])) #v[3255]
    (.letOp (n := 3259) (.out 0x122d20 (movR32R32Effect 0x122d20 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11] []) (.reg (.gpr 1))) #v[3193]
    (.letOp (n := 3260) (.exec 0x122d20 (fun s => s.RIP = 0x122d20) (movR32R32Effect 0x122d20 3 1 11) (Reg.operands [.gpr 11] [])) #v[3193]
    (.letOp (n := 3261) (.out 0x122d23 (rolR32Effect 0x122d23 3 1 30) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3259]
    (.letOp (n := 3262) (.exec 0x122d23 (fun s => s.RIP = 0x122d23) (rolR32Effect 0x122d23 3 1 30) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3259]
    (.letOp (n := 3263) (.out 0x122d26 (movR32R32Effect 0x122d26 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 11] []) (.reg (.gpr 7))) #v[3193]
    (.letOp (n := 3264) (.exec 0x122d26 (fun s => s.RIP = 0x122d26) (movR32R32Effect 0x122d26 3 7 11) (Reg.operands [.gpr 11] [])) #v[3193]
    (.letOp (n := 3265) (.out 0x122d29 (rolR32Effect 0x122d29 3 7 19) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3263]
    (.letOp (n := 3266) (.exec 0x122d29 (fun s => s.RIP = 0x122d29) (rolR32Effect 0x122d29 3 7 19) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3263]
    (.letOp (n := 3267) (.out 0x122d2c (xorR32R32Effect 0x122d2c 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[3265, 3261]
    (.letOp (n := 3268) (.exec 0x122d2c (fun s => s.RIP = 0x122d2c) (xorR32R32Effect 0x122d2c 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[3265, 3261]
    (.letOp (n := 3269) (.out 0x122d2e (movR32R32Effect 0x122d2e 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11] []) (.reg (.gpr 1))) #v[3193]
    (.letOp (n := 3270) (.exec 0x122d2e (fun s => s.RIP = 0x122d2e) (movR32R32Effect 0x122d2e 3 1 11) (Reg.operands [.gpr 11] [])) #v[3193]
    (.letOp (n := 3271) (.out 0x122d31 (rolR32Effect 0x122d31 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3269]
    (.letOp (n := 3272) (.exec 0x122d31 (fun s => s.RIP = 0x122d31) (rolR32Effect 0x122d31 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3269]
    (.letOp (n := 3273) (.out 0x122d34 (xorR32R32Effect 0x122d34 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[3271, 3267]
    (.letOp (n := 3274) (.exec 0x122d34 (fun s => s.RIP = 0x122d34) (xorR32R32Effect 0x122d34 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[3271, 3267]
    (.letOp (n := 3275) (.out 0x122d36 (movR32R32Effect 0x122d36 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[3081]
    (.letOp (n := 3276) (.exec 0x122d36 (fun s => s.RIP = 0x122d36) (movR32R32Effect 0x122d36 3 7 9) (Reg.operands [.gpr 9] [])) #v[3081]
    (.letOp (n := 3277) (.out 0x122d39 (andR32R32Effect 0x122d39 3 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[3275, 2971]
    (.letOp (n := 3278) (.exec 0x122d39 (fun s => s.RIP = 0x122d39) (andR32R32Effect 0x122d39 3 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[3275, 2971]
    (.letOp (n := 3279) (.out 0x122d3c (movR32R32Effect 0x122d3c 3 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[3081]
    (.letOp (n := 3280) (.exec 0x122d3c (fun s => s.RIP = 0x122d3c) (movR32R32Effect 0x122d3c 3 13 9) (Reg.operands [.gpr 9] [])) #v[3081]
    (.letOp (n := 3281) (.out 0x122d3f (xorR32R32Effect 0x122d3f 3 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[3279, 2971]
    (.letOp (n := 3282) (.exec 0x122d3f (fun s => s.RIP = 0x122d3f) (xorR32R32Effect 0x122d3f 3 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[3279, 2971]
    (.letOp (n := 3283) (.out 0x122d42 (andR32R32Effect 0x122d42 3 13 11) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 11] []) (.reg (.gpr 13))) #v[3281, 3193]
    (.letOp (n := 3284) (.exec 0x122d42 (fun s => s.RIP = 0x122d42) (andR32R32Effect 0x122d42 3 13 11) (Reg.operands [.gpr 13, .gpr 11] [])) #v[3281, 3193]
    (.letOp (n := 3285) (.out 0x122d45 (xorR32R32Effect 0x122d45 3 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 7] []) (.reg (.gpr 13))) #v[3283, 3277]
    (.letOp (n := 3286) (.exec 0x122d45 (fun s => s.RIP = 0x122d45) (xorR32R32Effect 0x122d45 3 13 7) (Reg.operands [.gpr 13, .gpr 7] [])) #v[3283, 3277]
    (.letOp (n := 3287) (.out 0x122d48 (movR32R32Effect 0x122d48 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[3117]
    (.letOp (n := 3288) (.exec 0x122d48 (fun s => s.RIP = 0x122d48) (movR32R32Effect 0x122d48 2 7 0) (Reg.operands [.gpr 0] [])) #v[3117]
    (b_l121930_83))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_82 : List UInt8 :=
  [0x44, 0x31, 0xC2, 0x01, 0xEB, 0x01, 0xD3, 0x8D, 0x14, 0x19, 0x81, 0xC2, 0x51, 0x63, 0xCA, 0x06,
    0x44, 0x89, 0xD9, 0xC1, 0xC1, 0x1E, 0x44, 0x89, 0xDF, 0xC1, 0xC7, 0x13, 0x31, 0xCF, 0x44, 0x89,
    0xD9, 0xC1, 0xC1, 0x0A, 0x31, 0xF9, 0x44, 0x89, 0xCF, 0x44, 0x21, 0xE7, 0x45, 0x89, 0xCD, 0x45,
    0x31, 0xE5, 0x45, 0x21, 0xDD, 0x41, 0x31, 0xFD, 0x89, 0xC7] ++ bytes_l121930_83

theorem code_l121930_82 : ∀ x ∈ codeRange 0x122d10 bytes_l121930_82, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22d10 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_83

def b_l121930_81 : Block Op Label signature Reg.count 3211 :=
  .letOp (n := 3211) (.out 0x122cd8 (xorR32R32Effect 0x122cd8 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[3209, 3205]
    (.letOp (n := 3212) (.exec 0x122cd8 (fun s => s.RIP = 0x122cd8) (xorR32R32Effect 0x122cd8 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[3209, 3205]
    (.letOp (n := 3213) (.exec 0x122cda (StorePre 0x122cda 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x122cda + BitVec.ofNat 64 4)) 4) (addMREffect 0x122cda 4 32 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[3011, 4]
    (.letOp (n := 3214) (.out 0x122cde (addR32R32Effect 0x122cde 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[3211, 3011]
    (.letOp (n := 3215) (.exec 0x122cde (fun s => s.RIP = 0x122cde) (addR32R32Effect 0x122cde 2 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[3211, 3011]
    (.letOp (n := 3216) (.exec 0x122ce0 (StorePre 0x122ce0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x122ce0 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x122ce0 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[3214, 4]
    (.letOp (n := 3217) (.out 0x122ce4 (movR32R32Effect 0x122ce4 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[3011]
    (.letOp (n := 3218) (.exec 0x122ce4 (fun s => s.RIP = 0x122ce4) (movR32R32Effect 0x122ce4 2 2 5) (Reg.operands [.gpr 5] [])) #v[3011]
    (.letOp (n := 3219) (.out 0x122ce6 (shrR32Effect 0x122ce6 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3217]
    (.letOp (n := 3220) (.exec 0x122ce6 (fun s => s.RIP = 0x122ce6) (shrR32Effect 0x122ce6 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3217]
    (.letOp (n := 3221) (.out 0x122ce9 (xorR32R32Effect 0x122ce9 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[3219, 3199]
    (.letOp (n := 3222) (.exec 0x122ce9 (fun s => s.RIP = 0x122ce9) (xorR32R32Effect 0x122ce9 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[3219, 3199]
    (.letOp (n := 3223) (.out 0x122ceb (movR32R32Effect 0x122ceb 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[3187]
    (.letOp (n := 3224) (.exec 0x122ceb (fun s => s.RIP = 0x122ceb) (movR32R32Effect 0x122ceb 3 1 14) (Reg.operands [.gpr 14] [])) #v[3187]
    (.letOp (n := 3225) (.out 0x122cee (rolR32Effect 0x122cee 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3223]
    (.letOp (n := 3226) (.exec 0x122cee (fun s => s.RIP = 0x122cee) (rolR32Effect 0x122cee 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3223]
    (.letOp (n := 3227) (.out 0x122cf1 (movR32M32LowEffect 0x122cf1 5 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 3228) (.exec 0x122cf1 (LoadPre 0x122cf1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x122cf1 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x122cf1 5 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3229) (.out 0x122cf5 (addR32R32Effect 0x122cf5 2 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[3227, 3221]
    (.letOp (n := 3230) (.exec 0x122cf5 (fun s => s.RIP = 0x122cf5) (addR32R32Effect 0x122cf5 2 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[3227, 3221]
    (.letOp (n := 3231) (.out 0x122cf7 (movR32R32Effect 0x122cf7 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[3187]
    (.letOp (n := 3232) (.exec 0x122cf7 (fun s => s.RIP = 0x122cf7) (movR32R32Effect 0x122cf7 3 2 14) (Reg.operands [.gpr 14] [])) #v[3187]
    (.letOp (n := 3233) (.out 0x122cfa (rolR32Effect 0x122cfa 3 2 21) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3231]
    (.letOp (n := 3234) (.exec 0x122cfa (fun s => s.RIP = 0x122cfa) (rolR32Effect 0x122cfa 3 2 21) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3231]
    (.letOp (n := 3235) (.out 0x122cfd (xorR32R32Effect 0x122cfd 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[3233, 3225]
    (.letOp (n := 3236) (.exec 0x122cfd (fun s => s.RIP = 0x122cfd) (xorR32R32Effect 0x122cfd 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[3233, 3225]
    (.letOp (n := 3237) (.out 0x122cff (movR32R32Effect 0x122cff 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[3187]
    (.letOp (n := 3238) (.exec 0x122cff (fun s => s.RIP = 0x122cff) (movR32R32Effect 0x122cff 3 1 14) (Reg.operands [.gpr 14] [])) #v[3187]
    (.letOp (n := 3239) (.out 0x122d02 (rolR32Effect 0x122d02 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3237]
    (.letOp (n := 3240) (.exec 0x122d02 (fun s => s.RIP = 0x122d02) (rolR32Effect 0x122d02 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3237]
    (.letOp (n := 3241) (.out 0x122d05 (xorR32R32Effect 0x122d05 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[3239, 3235]
    (.letOp (n := 3242) (.exec 0x122d05 (fun s => s.RIP = 0x122d05) (xorR32R32Effect 0x122d05 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[3239, 3235]
    (.letOp (n := 3243) (.out 0x122d07 (movR32R32Effect 0x122d07 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[3075]
    (.letOp (n := 3244) (.exec 0x122d07 (fun s => s.RIP = 0x122d07) (movR32R32Effect 0x122d07 3 2 15) (Reg.operands [.gpr 15] [])) #v[3075]
    (.letOp (n := 3245) (.out 0x122d0a (xorR32R32Effect 0x122d0a 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[3243, 2969]
    (.letOp (n := 3246) (.exec 0x122d0a (fun s => s.RIP = 0x122d0a) (xorR32R32Effect 0x122d0a 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[3243, 2969]
    (.letOp (n := 3247) (.out 0x122d0d (andR32R32Effect 0x122d0d 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[3245, 3187]
    (.letOp (n := 3248) (.exec 0x122d0d (fun s => s.RIP = 0x122d0d) (andR32R32Effect 0x122d0d 3 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[3245, 3187]
    (b_l121930_82))))))))))))))))))))))))))))))))))))))

def bytes_l121930_81 : List UInt8 :=
  [0x31, 0xD7, 0x01, 0x6C, 0x24, 0x50, 0x01, 0xEF, 0x89, 0x7C, 0x24, 0x10, 0x89, 0xEA, 0xC1, 0xEA,
    0x0A, 0x31, 0xCA, 0x44, 0x89, 0xF1, 0xC1, 0xC1, 0x1A, 0x8B, 0x6C, 0x24, 0x04, 0x01, 0xD5, 0x44,
    0x89, 0xF2, 0xC1, 0xC2, 0x15, 0x31, 0xCA, 0x44, 0x89, 0xF1, 0xC1, 0xC1, 0x07, 0x31, 0xD1, 0x44,
    0x89, 0xFA, 0x44, 0x31, 0xC2, 0x44, 0x21, 0xF2] ++ bytes_l121930_82

theorem code_l121930_81 : ∀ x ∈ codeRange 0x122cd8 bytes_l121930_81, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22cd8 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_82

def b_l121930_80 : Block Op Label signature Reg.count 3171 :=
  .letOp (n := 3171) (.out 0x122ca4 (andR32R32Effect 0x122ca4 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[3169, 2877]
    (.letOp (n := 3172) (.exec 0x122ca4 (fun s => s.RIP = 0x122ca4) (andR32R32Effect 0x122ca4 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[3169, 2877]
    (.letOp (n := 3173) (.out 0x122ca6 (movR32R32Effect 0x122ca6 3 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 12] []) (.reg (.gpr 11))) #v[2971]
    (.letOp (n := 3174) (.exec 0x122ca6 (fun s => s.RIP = 0x122ca6) (movR32R32Effect 0x122ca6 3 11 12) (Reg.operands [.gpr 12] [])) #v[2971]
    (.letOp (n := 3175) (.out 0x122ca9 (xorR32R32Effect 0x122ca9 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[3173, 2877]
    (.letOp (n := 3176) (.exec 0x122ca9 (fun s => s.RIP = 0x122ca9) (xorR32R32Effect 0x122ca9 3 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[3173, 2877]
    (.letOp (n := 3177) (.out 0x122cac (andR32R32Effect 0x122cac 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[3175, 3081]
    (.letOp (n := 3178) (.exec 0x122cac (fun s => s.RIP = 0x122cac) (andR32R32Effect 0x122cac 3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[3175, 3081]
    (.letOp (n := 3179) (.out 0x122caf (xorR32R32Effect 0x122caf 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[3177, 3171]
    (.letOp (n := 3180) (.exec 0x122caf (fun s => s.RIP = 0x122caf) (xorR32R32Effect 0x122caf 3 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[3177, 3171]
    (.letOp (n := 3181) (.out 0x122cb2 (addR32R32Effect 0x122cb2 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[3179, 3167]
    (.letOp (n := 3182) (.exec 0x122cb2 (fun s => s.RIP = 0x122cb2) (addR32R32Effect 0x122cb2 3 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[3179, 3167]
    (.letOp (n := 3183) (.out 0x122cb5 (movR32R32Effect 0x122cb5 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[3011]
    (.letOp (n := 3184) (.exec 0x122cb5 (fun s => s.RIP = 0x122cb5) (movR32R32Effect 0x122cb5 2 2 5) (Reg.operands [.gpr 5] [])) #v[3011]
    (.letOp (n := 3185) (.out 0x122cb7 (rolR32Effect 0x122cb7 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3183]
    (.letOp (n := 3186) (.exec 0x122cb7 (fun s => s.RIP = 0x122cb7) (rolR32Effect 0x122cb7 3 2 15) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3183]
    (.letOp (n := 3187) (.out 0x122cba (addR32R32Effect 0x122cba 3 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[2767, 3159]
    (.letOp (n := 3188) (.exec 0x122cba (fun s => s.RIP = 0x122cba) (addR32R32Effect 0x122cba 3 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[2767, 3159]
    (.letOp (n := 3189) (.out 0x122cbd (movR32R32Effect 0x122cbd 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[3011]
    (.letOp (n := 3190) (.exec 0x122cbd (fun s => s.RIP = 0x122cbd) (movR32R32Effect 0x122cbd 2 1 5) (Reg.operands [.gpr 5] [])) #v[3011]
    (.letOp (n := 3191) (.out 0x122cbf (rolR32Effect 0x122cbf 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3189]
    (.letOp (n := 3192) (.exec 0x122cbf (fun s => s.RIP = 0x122cbf) (rolR32Effect 0x122cbf 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3189]
    (.letOp (n := 3193) (.out 0x122cc2 (addR32R32Effect 0x122cc2 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[3181, 3159]
    (.letOp (n := 3194) (.exec 0x122cc2 (fun s => s.RIP = 0x122cc2) (addR32R32Effect 0x122cc2 3 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[3181, 3159]
    (.letOp (n := 3195) (.out 0x122cc5 (movR32R32Effect 0x122cc5 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[3117]
    (.letOp (n := 3196) (.exec 0x122cc5 (fun s => s.RIP = 0x122cc5) (movR32R32Effect 0x122cc5 2 7 0) (Reg.operands [.gpr 0] [])) #v[3117]
    (.letOp (n := 3197) (.out 0x122cc7 (rolR32Effect 0x122cc7 3 7 25) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3195]
    (.letOp (n := 3198) (.exec 0x122cc7 (fun s => s.RIP = 0x122cc7) (rolR32Effect 0x122cc7 3 7 25) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3195]
    (.letOp (n := 3199) (.out 0x122cca (xorR32R32Effect 0x122cca 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[3191, 3185]
    (.letOp (n := 3200) (.exec 0x122cca (fun s => s.RIP = 0x122cca) (xorR32R32Effect 0x122cca 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[3191, 3185]
    (.letOp (n := 3201) (.out 0x122ccc (movR32R32Effect 0x122ccc 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[3117]
    (.letOp (n := 3202) (.exec 0x122ccc (fun s => s.RIP = 0x122ccc) (movR32R32Effect 0x122ccc 2 2 0) (Reg.operands [.gpr 0] [])) #v[3117]
    (.letOp (n := 3203) (.out 0x122cce (rolR32Effect 0x122cce 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3201]
    (.letOp (n := 3204) (.exec 0x122cce (fun s => s.RIP = 0x122cce) (rolR32Effect 0x122cce 3 2 14) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3201]
    (.letOp (n := 3205) (.out 0x122cd1 (xorR32R32Effect 0x122cd1 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[3203, 3197]
    (.letOp (n := 3206) (.exec 0x122cd1 (fun s => s.RIP = 0x122cd1) (xorR32R32Effect 0x122cd1 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[3203, 3197]
    (.letOp (n := 3207) (.out 0x122cd3 (movR32R32Effect 0x122cd3 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[3117]
    (.letOp (n := 3208) (.exec 0x122cd3 (fun s => s.RIP = 0x122cd3) (movR32R32Effect 0x122cd3 2 7 0) (Reg.operands [.gpr 0] [])) #v[3117]
    (.letOp (n := 3209) (.out 0x122cd5 (shrR32Effect 0x122cd5 3 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[3207]
    (.letOp (n := 3210) (.exec 0x122cd5 (fun s => s.RIP = 0x122cd5) (shrR32Effect 0x122cd5 3 7 3) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3207]
    (b_l121930_81))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_80 : List UInt8 :=
  [0x21, 0xF2, 0x45, 0x89, 0xE3, 0x41, 0x31, 0xF3, 0x45, 0x21, 0xCB, 0x41, 0x31, 0xD3, 0x41, 0x01,
    0xCB, 0x89, 0xEA, 0xC1, 0xC2, 0x0F, 0x41, 0x01, 0xFE, 0x89, 0xE9, 0xC1, 0xC1, 0x0D, 0x41, 0x01,
    0xFB, 0x89, 0xC7, 0xC1, 0xC7, 0x19, 0x31, 0xD1, 0x89, 0xC2, 0xC1, 0xC2, 0x0E, 0x31, 0xFA, 0x89,
    0xC7, 0xC1, 0xEF, 0x03] ++ bytes_l121930_81

theorem code_l121930_80 : ∀ x ∈ codeRange 0x122ca4 bytes_l121930_80, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22ca4 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_81

def b_l121930_79 : Block Op Label signature Reg.count 3131 :=
  .letOp (n := 3131) (.out 0x122c6b (movR32R32Effect 0x122c6b 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[3119]
    (.letOp (n := 3132) (.exec 0x122c6b (fun s => s.RIP = 0x122c6b) (movR32R32Effect 0x122c6b 3 1 10) (Reg.operands [.gpr 10] [])) #v[3119]
    (.letOp (n := 3133) (.out 0x122c6e (rolR32Effect 0x122c6e 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3131]
    (.letOp (n := 3134) (.exec 0x122c6e (fun s => s.RIP = 0x122c6e) (rolR32Effect 0x122c6e 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3131]
    (.letOp (n := 3135) (.out 0x122c71 (xorR32R32Effect 0x122c71 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[3133, 3129]
    (.letOp (n := 3136) (.exec 0x122c71 (fun s => s.RIP = 0x122c71) (xorR32R32Effect 0x122c71 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[3133, 3129]
    (.letOp (n := 3137) (.out 0x122c73 (movR32R32Effect 0x122c73 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[2969]
    (.letOp (n := 3138) (.exec 0x122c73 (fun s => s.RIP = 0x122c73) (movR32R32Effect 0x122c73 3 2 8) (Reg.operands [.gpr 8] [])) #v[2969]
    (.letOp (n := 3139) (.out 0x122c76 (xorR32R32Effect 0x122c76 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[3137, 2871]
    (.letOp (n := 3140) (.exec 0x122c76 (fun s => s.RIP = 0x122c76) (xorR32R32Effect 0x122c76 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[3137, 2871]
    (.letOp (n := 3141) (.out 0x122c78 (andR32R32Effect 0x122c78 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[3139, 3119]
    (.letOp (n := 3142) (.exec 0x122c78 (fun s => s.RIP = 0x122c78) (andR32R32Effect 0x122c78 3 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[3139, 3119]
    (.letOp (n := 3143) (.out 0x122c7b (xorR32R32Effect 0x122c7b 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[3141, 2871]
    (.letOp (n := 3144) (.exec 0x122c7b (fun s => s.RIP = 0x122c7b) (xorR32R32Effect 0x122c7b 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[3141, 2871]
    (.letOp (n := 3145) (.out 0x122c7d (addR32R32Effect 0x122c7d 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[2761, 3117]
    (.letOp (n := 3146) (.exec 0x122c7d (fun s => s.RIP = 0x122c7d) (addR32R32Effect 0x122c7d 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2761, 3117]
    (.letOp (n := 3147) (.out 0x122c7f (movR32R32Effect 0x122c7f 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[3081]
    (.letOp (n := 3148) (.exec 0x122c7f (fun s => s.RIP = 0x122c7f) (movR32R32Effect 0x122c7f 3 10 9) (Reg.operands [.gpr 9] [])) #v[3081]
    (.letOp (n := 3149) (.out 0x122c82 (rolR32Effect 0x122c82 4 10 30) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[3147]
    (.letOp (n := 3150) (.exec 0x122c82 (fun s => s.RIP = 0x122c82) (rolR32Effect 0x122c82 4 10 30) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3147]
    (.letOp (n := 3151) (.out 0x122c86 (addR32R32Effect 0x122c86 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[3145, 3143]
    (.letOp (n := 3152) (.exec 0x122c86 (fun s => s.RIP = 0x122c86) (addR32R32Effect 0x122c86 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[3145, 3143]
    (.letOp (n := 3153) (.out 0x122c88 (movR32R32Effect 0x122c88 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[3081]
    (.letOp (n := 3154) (.exec 0x122c88 (fun s => s.RIP = 0x122c88) (movR32R32Effect 0x122c88 3 2 9) (Reg.operands [.gpr 9] [])) #v[3081]
    (.letOp (n := 3155) (.out 0x122c8b (rolR32Effect 0x122c8b 3 2 19) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3153]
    (.letOp (n := 3156) (.exec 0x122c8b (fun s => s.RIP = 0x122c8b) (rolR32Effect 0x122c8b 3 2 19) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3153]
    (.letOp (n := 3157) (.out 0x122c8e (addR32R32Effect 0x122c8e 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[3151, 3135]
    (.letOp (n := 3158) (.exec 0x122c8e (fun s => s.RIP = 0x122c8e) (addR32R32Effect 0x122c8e 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[3151, 3135]
    (.letOp (n := 3159) (.out 0x122c90 (addR32Imm32Effect 0x122c90 6 7 0xd5a79147) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[3157]
    (.letOp (n := 3160) (.exec 0x122c90 (fun s => s.RIP = 0x122c90) (addR32Imm32Effect 0x122c90 6 7 0xd5a79147) (Reg.operands [.gpr 7] [])) #v[3157]
    (.letOp (n := 3161) (.out 0x122c96 (movR32R32Effect 0x122c96 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[3081]
    (.letOp (n := 3162) (.exec 0x122c96 (fun s => s.RIP = 0x122c96) (movR32R32Effect 0x122c96 3 1 9) (Reg.operands [.gpr 9] [])) #v[3081]
    (.letOp (n := 3163) (.out 0x122c99 (rolR32Effect 0x122c99 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3161]
    (.letOp (n := 3164) (.exec 0x122c99 (fun s => s.RIP = 0x122c99) (rolR32Effect 0x122c99 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3161]
    (.letOp (n := 3165) (.out 0x122c9c (xorR32R32Effect 0x122c9c 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[3155, 3149]
    (.letOp (n := 3166) (.exec 0x122c9c (fun s => s.RIP = 0x122c9c) (xorR32R32Effect 0x122c9c 3 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[3155, 3149]
    (.letOp (n := 3167) (.out 0x122c9f (xorR32R32Effect 0x122c9f 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[3163, 3165]
    (.letOp (n := 3168) (.exec 0x122c9f (fun s => s.RIP = 0x122c9f) (xorR32R32Effect 0x122c9f 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[3163, 3165]
    (.letOp (n := 3169) (.out 0x122ca1 (movR32R32Effect 0x122ca1 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[2971]
    (.letOp (n := 3170) (.exec 0x122ca1 (fun s => s.RIP = 0x122ca1) (movR32R32Effect 0x122ca1 3 2 12) (Reg.operands [.gpr 12] [])) #v[2971]
    (b_l121930_80))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_79 : List UInt8 :=
  [0x44, 0x89, 0xD1, 0xC1, 0xC1, 0x07, 0x31, 0xD1, 0x44, 0x89, 0xC2, 0x31, 0xDA, 0x44, 0x21, 0xD2,
    0x31, 0xDA, 0x01, 0xC7, 0x45, 0x89, 0xCA, 0x41, 0xC1, 0xC2, 0x1E, 0x01, 0xD7, 0x44, 0x89, 0xCA,
    0xC1, 0xC2, 0x13, 0x01, 0xCF, 0x81, 0xC7, 0x47, 0x91, 0xA7, 0xD5, 0x44, 0x89, 0xC9, 0xC1, 0xC1,
    0x0A, 0x44, 0x31, 0xD2, 0x31, 0xD1, 0x44, 0x89, 0xE2] ++ bytes_l121930_80

theorem code_l121930_79 : ∀ x ∈ codeRange 0x122c6b bytes_l121930_79, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22c6b 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_80

def b_l121930_78 : Block Op Label signature Reg.count 3093 :=
  .letOp (n := 3093) (.out 0x122c31 (movR32R32Effect 0x122c31 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 5] []) (.reg (.gpr 10))) #v[3011]
    (.letOp (n := 3094) (.exec 0x122c31 (fun s => s.RIP = 0x122c31) (movR32R32Effect 0x122c31 3 10 5) (Reg.operands [.gpr 5] [])) #v[3011]
    (.letOp (n := 3095) (.out 0x122c34 (rolR32Effect 0x122c34 4 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[3093]
    (.letOp (n := 3096) (.exec 0x122c34 (fun s => s.RIP = 0x122c34) (rolR32Effect 0x122c34 4 10 14) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3093]
    (.letOp (n := 3097) (.out 0x122c38 (xorR32R32Effect 0x122c38 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[3095, 3091]
    (.letOp (n := 3098) (.exec 0x122c38 (fun s => s.RIP = 0x122c38) (xorR32R32Effect 0x122c38 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[3095, 3091]
    (.letOp (n := 3099) (.out 0x122c3b (movR32R32Effect 0x122c3b 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[3011]
    (.letOp (n := 3100) (.exec 0x122c3b (fun s => s.RIP = 0x122c3b) (movR32R32Effect 0x122c3b 2 2 5) (Reg.operands [.gpr 5] [])) #v[3011]
    (.letOp (n := 3101) (.out 0x122c3d (shrR32Effect 0x122c3d 3 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3099]
    (.letOp (n := 3102) (.exec 0x122c3d (fun s => s.RIP = 0x122c3d) (shrR32Effect 0x122c3d 3 2 3) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3099]
    (.letOp (n := 3103) (.out 0x122c40 (xorR32R32Effect 0x122c40 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[3101, 3097]
    (.letOp (n := 3104) (.exec 0x122c40 (fun s => s.RIP = 0x122c40) (xorR32R32Effect 0x122c40 3 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[3101, 3097]
    (.letOp (n := 3105) (.exec 0x122c43 (StorePre 0x122c43 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x122c43 + BitVec.ofNat 64 4)) 4) (addMREffect 0x122c43 4 32 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2913, 4]
    (.letOp (n := 3106) (.out 0x122c47 (addR32R32Effect 0x122c47 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[3103, 2913]
    (.letOp (n := 3107) (.exec 0x122c47 (fun s => s.RIP = 0x122c47) (addR32R32Effect 0x122c47 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[3103, 2913]
    (.letOp (n := 3108) (.exec 0x122c49 (StorePre 0x122c49 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x122c49 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x122c49 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[3106, 4]
    (.letOp (n := 3109) (.out 0x122c4d (movR32R32Effect 0x122c4d 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[2913]
    (.letOp (n := 3110) (.exec 0x122c4d (fun s => s.RIP = 0x122c4d) (movR32R32Effect 0x122c4d 2 2 0) (Reg.operands [.gpr 0] [])) #v[2913]
    (.letOp (n := 3111) (.out 0x122c4f (shrR32Effect 0x122c4f 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3109]
    (.letOp (n := 3112) (.exec 0x122c4f (fun s => s.RIP = 0x122c4f) (shrR32Effect 0x122c4f 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3109]
    (.letOp (n := 3113) (.out 0x122c52 (xorR32R32Effect 0x122c52 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[3111, 3087]
    (.letOp (n := 3114) (.exec 0x122c52 (fun s => s.RIP = 0x122c52) (xorR32R32Effect 0x122c52 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[3111, 3087]
    (.letOp (n := 3115) (.out 0x122c54 (movR32M32LowEffect 0x122c54 0 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 3116) (.exec 0x122c54 (LoadPre 0x122c54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x122c54 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x122c54 0 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3117) (.out 0x122c58 (addR32R32Effect 0x122c58 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3115, 3113]
    (.letOp (n := 3118) (.exec 0x122c58 (fun s => s.RIP = 0x122c58) (addR32R32Effect 0x122c58 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3115, 3113]
    (.letOp (n := 3119) (.out 0x122c5a (movR64R64Effect 0x122c5a 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 15] []) (.reg (.gpr 10))) #v[3075]
    (.letOp (n := 3120) (.exec 0x122c5a (fun s => s.RIP = 0x122c5a) (movR64R64Effect 0x122c5a 10 15) (Reg.operands [.gpr 15] [])) #v[3075]
    (.letOp (n := 3121) (.out 0x122c5d (movR32R32Effect 0x122c5d 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[3119]
    (.letOp (n := 3122) (.exec 0x122c5d (fun s => s.RIP = 0x122c5d) (movR32R32Effect 0x122c5d 3 1 10) (Reg.operands [.gpr 10] [])) #v[3119]
    (.letOp (n := 3123) (.out 0x122c60 (rolR32Effect 0x122c60 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3121]
    (.letOp (n := 3124) (.exec 0x122c60 (fun s => s.RIP = 0x122c60) (rolR32Effect 0x122c60 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3121]
    (.letOp (n := 3125) (.out 0x122c63 (movR32R32Effect 0x122c63 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[3119]
    (.letOp (n := 3126) (.exec 0x122c63 (fun s => s.RIP = 0x122c63) (movR32R32Effect 0x122c63 3 2 10) (Reg.operands [.gpr 10] [])) #v[3119]
    (.letOp (n := 3127) (.out 0x122c66 (rolR32Effect 0x122c66 3 2 21) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3125]
    (.letOp (n := 3128) (.exec 0x122c66 (fun s => s.RIP = 0x122c66) (rolR32Effect 0x122c66 3 2 21) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3125]
    (.letOp (n := 3129) (.out 0x122c69 (xorR32R32Effect 0x122c69 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[3127, 3123]
    (.letOp (n := 3130) (.exec 0x122c69 (fun s => s.RIP = 0x122c69) (xorR32R32Effect 0x122c69 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[3127, 3123]
    (b_l121930_79))))))))))))))))))))))))))))))))))))))

def bytes_l121930_78 : List UInt8 :=
  [0x41, 0x89, 0xEA, 0x41, 0xC1, 0xC2, 0x0E, 0x41, 0x31, 0xD2, 0x89, 0xEA, 0xC1, 0xEA, 0x03, 0x44,
    0x31, 0xD2, 0x01, 0x44, 0x24, 0x38, 0x01, 0xC2, 0x89, 0x54, 0x24, 0x58, 0x89, 0xC2, 0xC1, 0xEA,
    0x0A, 0x31, 0xCA, 0x8B, 0x44, 0x24, 0x24, 0x01, 0xD0, 0x4D, 0x89, 0xFA, 0x44, 0x89, 0xD1, 0xC1,
    0xC1, 0x1A, 0x44, 0x89, 0xD2, 0xC1, 0xC2, 0x15, 0x31, 0xCA] ++ bytes_l121930_79

theorem code_l121930_78 : ∀ x ∈ codeRange 0x122c31 bytes_l121930_78, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22c31 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_79

def b_l121930_77 : Block Op Label signature Reg.count 3053 :=
  .letOp (n := 3053) (.out 0x122bf9 (xorR32R32Effect 0x122bf9 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[3051, 3043]
    (.letOp (n := 3054) (.exec 0x122bf9 (fun s => s.RIP = 0x122bf9) (xorR32R32Effect 0x122bf9 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[3051, 3043]
    (.letOp (n := 3055) (.out 0x122bfc (movR32R32Effect 0x122bfc 3 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 12] []) (.reg (.gpr 10))) #v[2971]
    (.letOp (n := 3056) (.exec 0x122bfc (fun s => s.RIP = 0x122bfc) (movR32R32Effect 0x122bfc 3 10 12) (Reg.operands [.gpr 12] [])) #v[2971]
    (.letOp (n := 3057) (.out 0x122bff (rolR32Effect 0x122bff 4 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[3055]
    (.letOp (n := 3058) (.exec 0x122bff (fun s => s.RIP = 0x122bff) (rolR32Effect 0x122bff 4 10 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3055]
    (.letOp (n := 3059) (.out 0x122c03 (xorR32R32Effect 0x122c03 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[3057, 3053]
    (.letOp (n := 3060) (.exec 0x122c03 (fun s => s.RIP = 0x122c03) (xorR32R32Effect 0x122c03 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[3057, 3053]
    (.letOp (n := 3061) (.out 0x122c06 (movR32R32Effect 0x122c06 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[2877]
    (.letOp (n := 3062) (.exec 0x122c06 (fun s => s.RIP = 0x122c06) (movR32R32Effect 0x122c06 2 2 6) (Reg.operands [.gpr 6] [])) #v[2877]
    (.letOp (n := 3063) (.out 0x122c08 (andR32R32Effect 0x122c08 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[3061, 2767]
    (.letOp (n := 3064) (.exec 0x122c08 (fun s => s.RIP = 0x122c08) (andR32R32Effect 0x122c08 3 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[3061, 2767]
    (.letOp (n := 3065) (.out 0x122c0b (movR32R32Effect 0x122c0b 3 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[2877]
    (.letOp (n := 3066) (.exec 0x122c0b (fun s => s.RIP = 0x122c0b) (movR32R32Effect 0x122c0b 3 9 6) (Reg.operands [.gpr 6] [])) #v[2877]
    (.letOp (n := 3067) (.out 0x122c0e (xorR32R32Effect 0x122c0e 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[3065, 2767]
    (.letOp (n := 3068) (.exec 0x122c0e (fun s => s.RIP = 0x122c0e) (xorR32R32Effect 0x122c0e 3 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[3065, 2767]
    (.letOp (n := 3069) (.out 0x122c11 (andR32R32Effect 0x122c11 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[3067, 2971]
    (.letOp (n := 3070) (.exec 0x122c11 (fun s => s.RIP = 0x122c11) (andR32R32Effect 0x122c11 3 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[3067, 2971]
    (.letOp (n := 3071) (.out 0x122c14 (xorR32R32Effect 0x122c14 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[3069, 3063]
    (.letOp (n := 3072) (.exec 0x122c14 (fun s => s.RIP = 0x122c14) (xorR32R32Effect 0x122c14 3 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[3069, 3063]
    (.letOp (n := 3073) (.out 0x122c17 (addR32R32Effect 0x122c17 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[3071, 3059]
    (.letOp (n := 3074) (.exec 0x122c17 (fun s => s.RIP = 0x122c17) (addR32R32Effect 0x122c17 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[3071, 3059]
    (.letOp (n := 3075) (.out 0x122c1a (addR32R32Effect 0x122c1a 3 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[2847, 3047]
    (.letOp (n := 3076) (.exec 0x122c1a (fun s => s.RIP = 0x122c1a) (addR32R32Effect 0x122c1a 3 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[2847, 3047]
    (.letOp (n := 3077) (.out 0x122c1d (movR32R32Effect 0x122c1d 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[2913]
    (.letOp (n := 3078) (.exec 0x122c1d (fun s => s.RIP = 0x122c1d) (movR32R32Effect 0x122c1d 2 2 0) (Reg.operands [.gpr 0] [])) #v[2913]
    (.letOp (n := 3079) (.out 0x122c1f (rolR32Effect 0x122c1f 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3077]
    (.letOp (n := 3080) (.exec 0x122c1f (fun s => s.RIP = 0x122c1f) (rolR32Effect 0x122c1f 3 2 15) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3077]
    (.letOp (n := 3081) (.out 0x122c22 (addR32R32Effect 0x122c22 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[3073, 3047]
    (.letOp (n := 3082) (.exec 0x122c22 (fun s => s.RIP = 0x122c22) (addR32R32Effect 0x122c22 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[3073, 3047]
    (.letOp (n := 3083) (.out 0x122c25 (movR32R32Effect 0x122c25 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[2913]
    (.letOp (n := 3084) (.exec 0x122c25 (fun s => s.RIP = 0x122c25) (movR32R32Effect 0x122c25 2 1 0) (Reg.operands [.gpr 0] [])) #v[2913]
    (.letOp (n := 3085) (.out 0x122c27 (rolR32Effect 0x122c27 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3083]
    (.letOp (n := 3086) (.exec 0x122c27 (fun s => s.RIP = 0x122c27) (rolR32Effect 0x122c27 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3083]
    (.letOp (n := 3087) (.out 0x122c2a (xorR32R32Effect 0x122c2a 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[3085, 3079]
    (.letOp (n := 3088) (.exec 0x122c2a (fun s => s.RIP = 0x122c2a) (xorR32R32Effect 0x122c2a 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[3085, 3079]
    (.letOp (n := 3089) (.out 0x122c2c (movR32R32Effect 0x122c2c 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[3011]
    (.letOp (n := 3090) (.exec 0x122c2c (fun s => s.RIP = 0x122c2c) (movR32R32Effect 0x122c2c 2 2 5) (Reg.operands [.gpr 5] [])) #v[3011]
    (.letOp (n := 3091) (.out 0x122c2e (rolR32Effect 0x122c2e 3 2 25) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3089]
    (.letOp (n := 3092) (.exec 0x122c2e (fun s => s.RIP = 0x122c2e) (rolR32Effect 0x122c2e 3 2 25) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3089]
    (b_l121930_78))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_77 : List UInt8 :=
  [0x44, 0x31, 0xCA, 0x45, 0x89, 0xE2, 0x41, 0xC1, 0xC2, 0x0A, 0x41, 0x31, 0xD2, 0x89, 0xF2, 0x44,
    0x21, 0xF2, 0x41, 0x89, 0xF1, 0x45, 0x31, 0xF1, 0x45, 0x21, 0xE1, 0x41, 0x31, 0xD1, 0x45, 0x01,
    0xD1, 0x41, 0x01, 0xCF, 0x89, 0xC2, 0xC1, 0xC2, 0x0F, 0x41, 0x01, 0xC9, 0x89, 0xC1, 0xC1, 0xC1,
    0x0D, 0x31, 0xD1, 0x89, 0xEA, 0xC1, 0xC2, 0x19] ++ bytes_l121930_78

theorem code_l121930_77 : ∀ x ∈ codeRange 0x122bf9 bytes_l121930_77, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22bf9 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_78

def b_l121930_76 : Block Op Label signature Reg.count 3013 :=
  .letOp (n := 3013) (.out 0x122bb8 (movR32R32Effect 0x122bb8 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[2969]
    (.letOp (n := 3014) (.exec 0x122bb8 (fun s => s.RIP = 0x122bb8) (movR32R32Effect 0x122bb8 3 1 8) (Reg.operands [.gpr 8] [])) #v[2969]
    (.letOp (n := 3015) (.out 0x122bbb (rolR32Effect 0x122bbb 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3013]
    (.letOp (n := 3016) (.exec 0x122bbb (fun s => s.RIP = 0x122bbb) (rolR32Effect 0x122bbb 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3013]
    (.letOp (n := 3017) (.out 0x122bbe (movR32R32Effect 0x122bbe 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[2969]
    (.letOp (n := 3018) (.exec 0x122bbe (fun s => s.RIP = 0x122bbe) (movR32R32Effect 0x122bbe 3 9 8) (Reg.operands [.gpr 8] [])) #v[2969]
    (.letOp (n := 3019) (.out 0x122bc1 (rolR32Effect 0x122bc1 4 9 21) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[3017]
    (.letOp (n := 3020) (.exec 0x122bc1 (fun s => s.RIP = 0x122bc1) (rolR32Effect 0x122bc1 4 9 21) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3017]
    (.letOp (n := 3021) (.out 0x122bc5 (xorR32R32Effect 0x122bc5 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[3019, 3015]
    (.letOp (n := 3022) (.exec 0x122bc5 (fun s => s.RIP = 0x122bc5) (xorR32R32Effect 0x122bc5 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[3019, 3015]
    (.letOp (n := 3023) (.out 0x122bc8 (movR32R32Effect 0x122bc8 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[2969]
    (.letOp (n := 3024) (.exec 0x122bc8 (fun s => s.RIP = 0x122bc8) (movR32R32Effect 0x122bc8 3 1 8) (Reg.operands [.gpr 8] [])) #v[2969]
    (.letOp (n := 3025) (.out 0x122bcb (rolR32Effect 0x122bcb 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[3023]
    (.letOp (n := 3026) (.exec 0x122bcb (fun s => s.RIP = 0x122bcb) (rolR32Effect 0x122bcb 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3023]
    (.letOp (n := 3027) (.out 0x122bce (xorR32R32Effect 0x122bce 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[3025, 3021]
    (.letOp (n := 3028) (.exec 0x122bce (fun s => s.RIP = 0x122bce) (xorR32R32Effect 0x122bce 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[3025, 3021]
    (.letOp (n := 3029) (.out 0x122bd1 (movR32R32Effect 0x122bd1 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[2871]
    (.letOp (n := 3030) (.exec 0x122bd1 (fun s => s.RIP = 0x122bd1) (movR32R32Effect 0x122bd1 3 9 3) (Reg.operands [.gpr 3] [])) #v[2871]
    (.letOp (n := 3031) (.out 0x122bd4 (xorR32R32Effect 0x122bd4 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[3029, 2761]
    (.letOp (n := 3032) (.exec 0x122bd4 (fun s => s.RIP = 0x122bd4) (xorR32R32Effect 0x122bd4 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[3029, 2761]
    (.letOp (n := 3033) (.out 0x122bd7 (andR32R32Effect 0x122bd7 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[3031, 2969]
    (.letOp (n := 3034) (.exec 0x122bd7 (fun s => s.RIP = 0x122bd7) (andR32R32Effect 0x122bd7 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[3031, 2969]
    (.letOp (n := 3035) (.out 0x122bda (xorR32R32Effect 0x122bda 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[3033, 2761]
    (.letOp (n := 3036) (.exec 0x122bda (fun s => s.RIP = 0x122bda) (xorR32R32Effect 0x122bda 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[3033, 2761]
    (.letOp (n := 3037) (.out 0x122bdd (addR32R32Effect 0x122bdd 3 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[2650, 3011]
    (.letOp (n := 3038) (.exec 0x122bdd (fun s => s.RIP = 0x122bdd) (addR32R32Effect 0x122bdd 3 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[2650, 3011]
    (.letOp (n := 3039) (.out 0x122be0 (addR32R32Effect 0x122be0 3 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[3037, 3035]
    (.letOp (n := 3040) (.exec 0x122be0 (fun s => s.RIP = 0x122be0) (addR32R32Effect 0x122be0 3 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[3037, 3035]
    (.letOp (n := 3041) (.out 0x122be3 (movR32R32Effect 0x122be3 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 12] []) (.reg (.gpr 9))) #v[2971]
    (.letOp (n := 3042) (.exec 0x122be3 (fun s => s.RIP = 0x122be3) (movR32R32Effect 0x122be3 3 9 12) (Reg.operands [.gpr 12] [])) #v[2971]
    (.letOp (n := 3043) (.out 0x122be6 (rolR32Effect 0x122be6 4 9 30) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[3041]
    (.letOp (n := 3044) (.exec 0x122be6 (fun s => s.RIP = 0x122be6) (rolR32Effect 0x122be6 4 9 30) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3041]
    (.letOp (n := 3045) (.out 0x122bea (addR32R32Effect 0x122bea 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[3027, 3039]
    (.letOp (n := 3046) (.exec 0x122bea (fun s => s.RIP = 0x122bea) (addR32R32Effect 0x122bea 3 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[3027, 3039]
    (.letOp (n := 3047) (.out 0x122bed (addR32Imm32Effect 0x122bed 6 1 0xc6e00bf3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[3045]
    (.letOp (n := 3048) (.exec 0x122bed (fun s => s.RIP = 0x122bed) (addR32Imm32Effect 0x122bed 6 1 0xc6e00bf3) (Reg.operands [.gpr 1] [])) #v[3045]
    (.letOp (n := 3049) (.out 0x122bf3 (movR32R32Effect 0x122bf3 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[2971]
    (.letOp (n := 3050) (.exec 0x122bf3 (fun s => s.RIP = 0x122bf3) (movR32R32Effect 0x122bf3 3 2 12) (Reg.operands [.gpr 12] [])) #v[2971]
    (.letOp (n := 3051) (.out 0x122bf6 (rolR32Effect 0x122bf6 3 2 19) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3049]
    (.letOp (n := 3052) (.exec 0x122bf6 (fun s => s.RIP = 0x122bf6) (rolR32Effect 0x122bf6 3 2 19) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3049]
    (b_l121930_77))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_76 : List UInt8 :=
  [0x44, 0x89, 0xC1, 0xC1, 0xC1, 0x1A, 0x45, 0x89, 0xC1, 0x41, 0xC1, 0xC1, 0x15, 0x41, 0x31, 0xC9,
    0x44, 0x89, 0xC1, 0xC1, 0xC1, 0x07, 0x44, 0x31, 0xC9, 0x41, 0x89, 0xD9, 0x41, 0x31, 0xF9, 0x45,
    0x21, 0xC1, 0x41, 0x31, 0xF9, 0x41, 0x01, 0xED, 0x45, 0x01, 0xCD, 0x45, 0x89, 0xE1, 0x41, 0xC1,
    0xC1, 0x1E, 0x44, 0x01, 0xE9, 0x81, 0xC1, 0xF3, 0x0B, 0xE0, 0xC6, 0x44, 0x89, 0xE2, 0xC1, 0xC2,
    0x13] ++ bytes_l121930_77

theorem code_l121930_76 : ∀ x ∈ codeRange 0x122bb8 bytes_l121930_76, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22bb8 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_77

def b_l121930_75 : Block Op Label signature Reg.count 2975 :=
  .letOp (n := 2975) (.out 0x122b71 (rolR32Effect 0x122b71 4 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2973]
    (.letOp (n := 2976) (.exec 0x122b71 (fun s => s.RIP = 0x122b71) (rolR32Effect 0x122b71 4 9 15) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2973]
    (.letOp (n := 2977) (.out 0x122b75 (movR32R32Effect 0x122b75 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[2801]
    (.letOp (n := 2978) (.exec 0x122b75 (fun s => s.RIP = 0x122b75) (movR32R32Effect 0x122b75 2 1 5) (Reg.operands [.gpr 5] [])) #v[2801]
    (.letOp (n := 2979) (.out 0x122b77 (rolR32Effect 0x122b77 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2977]
    (.letOp (n := 2980) (.exec 0x122b77 (fun s => s.RIP = 0x122b77) (rolR32Effect 0x122b77 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2977]
    (.letOp (n := 2981) (.out 0x122b7a (xorR32R32Effect 0x122b7a 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[2979, 2975]
    (.letOp (n := 2982) (.exec 0x122b7a (fun s => s.RIP = 0x122b7a) (xorR32R32Effect 0x122b7a 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[2979, 2975]
    (.letOp (n := 2983) (.out 0x122b7d (movR32R32Effect 0x122b7d 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[2913]
    (.letOp (n := 2984) (.exec 0x122b7d (fun s => s.RIP = 0x122b7d) (movR32R32Effect 0x122b7d 3 9 0) (Reg.operands [.gpr 0] [])) #v[2913]
    (.letOp (n := 2985) (.out 0x122b80 (rolR32Effect 0x122b80 4 9 25) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2983]
    (.letOp (n := 2986) (.exec 0x122b80 (fun s => s.RIP = 0x122b80) (rolR32Effect 0x122b80 4 9 25) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2983]
    (.letOp (n := 2987) (.out 0x122b84 (movR32R32Effect 0x122b84 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2913]
    (.letOp (n := 2988) (.exec 0x122b84 (fun s => s.RIP = 0x122b84) (movR32R32Effect 0x122b84 3 10 0) (Reg.operands [.gpr 0] [])) #v[2913]
    (.letOp (n := 2989) (.out 0x122b87 (rolR32Effect 0x122b87 4 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2987]
    (.letOp (n := 2990) (.exec 0x122b87 (fun s => s.RIP = 0x122b87) (rolR32Effect 0x122b87 4 10 14) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2987]
    (.letOp (n := 2991) (.out 0x122b8b (xorR32R32Effect 0x122b8b 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[2989, 2985]
    (.letOp (n := 2992) (.exec 0x122b8b (fun s => s.RIP = 0x122b8b) (xorR32R32Effect 0x122b8b 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[2989, 2985]
    (.letOp (n := 2993) (.out 0x122b8e (movR32R32Effect 0x122b8e 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[2913]
    (.letOp (n := 2994) (.exec 0x122b8e (fun s => s.RIP = 0x122b8e) (movR32R32Effect 0x122b8e 3 9 0) (Reg.operands [.gpr 0] [])) #v[2913]
    (.letOp (n := 2995) (.out 0x122b91 (shrR32Effect 0x122b91 4 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2993]
    (.letOp (n := 2996) (.exec 0x122b91 (fun s => s.RIP = 0x122b91) (shrR32Effect 0x122b91 4 9 3) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2993]
    (.letOp (n := 2997) (.out 0x122b95 (xorR32R32Effect 0x122b95 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[2995, 2991]
    (.letOp (n := 2998) (.exec 0x122b95 (fun s => s.RIP = 0x122b95) (xorR32R32Effect 0x122b95 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[2995, 2991]
    (.letOp (n := 2999) (.exec 0x122b98 (StorePre 0x122b98 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x122b98 + BitVec.ofNat 64 4)) 4) (addMREffect 0x122b98 4 32 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[2801, 4]
    (.letOp (n := 3000) (.out 0x122b9c (addR32R32Effect 0x122b9c 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[2997, 2801]
    (.letOp (n := 3001) (.exec 0x122b9c (fun s => s.RIP = 0x122b9c) (addR32R32Effect 0x122b9c 3 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[2997, 2801]
    (.letOp (n := 3002) (.exec 0x122b9f (StorePre 0x122b9f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x122b9f + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x122b9f 9 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[3000, 4]
    (.letOp (n := 3003) (.out 0x122ba7 (movR32R32Effect 0x122ba7 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[2801]
    (.letOp (n := 3004) (.exec 0x122ba7 (fun s => s.RIP = 0x122ba7) (movR32R32Effect 0x122ba7 3 9 5) (Reg.operands [.gpr 5] [])) #v[2801]
    (.letOp (n := 3005) (.out 0x122baa (shrR32Effect 0x122baa 4 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[3003]
    (.letOp (n := 3006) (.exec 0x122baa (fun s => s.RIP = 0x122baa) (shrR32Effect 0x122baa 4 9 10) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3003]
    (.letOp (n := 3007) (.out 0x122bae (xorR32R32Effect 0x122bae 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[3005, 2981]
    (.letOp (n := 3008) (.exec 0x122bae (fun s => s.RIP = 0x122bae) (xorR32R32Effect 0x122bae 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[3005, 2981]
    (.letOp (n := 3009) (.out 0x122bb1 (movR32M32LowEffect 0x122bb1 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 3010) (.exec 0x122bb1 (LoadPre 0x122bb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x122bb1 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x122bb1 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3011) (.out 0x122bb5 (addR32R32Effect 0x122bb5 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[3009, 3007]
    (.letOp (n := 3012) (.exec 0x122bb5 (fun s => s.RIP = 0x122bb5) (addR32R32Effect 0x122bb5 3 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[3009, 3007]
    (b_l121930_76))))))))))))))))))))))))))))))))))))))

def bytes_l121930_75 : List UInt8 :=
  [0x41, 0xC1, 0xC1, 0x0F, 0x89, 0xE9, 0xC1, 0xC1, 0x0D, 0x44, 0x31, 0xC9, 0x41, 0x89, 0xC1, 0x41,
    0xC1, 0xC1, 0x19, 0x41, 0x89, 0xC2, 0x41, 0xC1, 0xC2, 0x0E, 0x45, 0x31, 0xCA, 0x41, 0x89, 0xC1,
    0x41, 0xC1, 0xE9, 0x03, 0x45, 0x31, 0xD1, 0x01, 0x6C, 0x24, 0x08, 0x41, 0x01, 0xE9, 0x44, 0x89,
    0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x41, 0x89, 0xE9, 0x41, 0xC1, 0xE9, 0x0A, 0x41, 0x31, 0xC9,
    0x8B, 0x6C, 0x24, 0x10, 0x44, 0x01, 0xCD] ++ bytes_l121930_76

theorem code_l121930_75 : ∀ x ∈ codeRange 0x122b71 bytes_l121930_75, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22b71 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_76

def b_l121930_74 : Block Op Label signature Reg.count 2935 :=
  .letOp (n := 2935) (.out 0x122b2e (leaR32Effect 0x122b2e 4 1 (.sib 9 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9, .gpr 12] []) (.reg (.gpr 1))) #v[2921, 2933]
    (.letOp (n := 2936) (.exec 0x122b2e (fun s => s.RIP = 0x122b2e) (leaR32Effect 0x122b2e 4 1 (.sib 9 (some 12) 0 .none)) (Reg.operands [.gpr 9, .gpr 12] [])) #v[2921, 2933]
    (.letOp (n := 2937) (.out 0x122b32 (addR32Imm32Effect 0x122b32 6 1 0xbf597fc7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[2935]
    (.letOp (n := 2938) (.exec 0x122b32 (fun s => s.RIP = 0x122b32) (addR32Imm32Effect 0x122b32 6 1 0xbf597fc7) (Reg.operands [.gpr 1] [])) #v[2935]
    (.letOp (n := 2939) (.out 0x122b38 (movR32R32Effect 0x122b38 3 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[2877]
    (.letOp (n := 2940) (.exec 0x122b38 (fun s => s.RIP = 0x122b38) (movR32R32Effect 0x122b38 3 9 6) (Reg.operands [.gpr 6] [])) #v[2877]
    (.letOp (n := 2941) (.out 0x122b3b (rolR32Effect 0x122b3b 4 9 30) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2939]
    (.letOp (n := 2942) (.exec 0x122b3b (fun s => s.RIP = 0x122b3b) (rolR32Effect 0x122b3b 4 9 30) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2939]
    (.letOp (n := 2943) (.out 0x122b3f (movR32R32Effect 0x122b3f 3 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[2877]
    (.letOp (n := 2944) (.exec 0x122b3f (fun s => s.RIP = 0x122b3f) (movR32R32Effect 0x122b3f 3 10 6) (Reg.operands [.gpr 6] [])) #v[2877]
    (.letOp (n := 2945) (.out 0x122b42 (rolR32Effect 0x122b42 4 10 19) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2943]
    (.letOp (n := 2946) (.exec 0x122b42 (fun s => s.RIP = 0x122b42) (rolR32Effect 0x122b42 4 10 19) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2943]
    (.letOp (n := 2947) (.out 0x122b46 (xorR32R32Effect 0x122b46 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[2945, 2941]
    (.letOp (n := 2948) (.exec 0x122b46 (fun s => s.RIP = 0x122b46) (xorR32R32Effect 0x122b46 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[2945, 2941]
    (.letOp (n := 2949) (.out 0x122b49 (movR32R32Effect 0x122b49 3 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[2877]
    (.letOp (n := 2950) (.exec 0x122b49 (fun s => s.RIP = 0x122b49) (movR32R32Effect 0x122b49 3 9 6) (Reg.operands [.gpr 6] [])) #v[2877]
    (.letOp (n := 2951) (.out 0x122b4c (rolR32Effect 0x122b4c 4 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2949]
    (.letOp (n := 2952) (.exec 0x122b4c (fun s => s.RIP = 0x122b4c) (rolR32Effect 0x122b4c 4 9 10) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2949]
    (.letOp (n := 2953) (.out 0x122b50 (xorR32R32Effect 0x122b50 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[2951, 2947]
    (.letOp (n := 2954) (.exec 0x122b50 (fun s => s.RIP = 0x122b50) (xorR32R32Effect 0x122b50 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[2951, 2947]
    (.letOp (n := 2955) (.out 0x122b53 (movR32R32Effect 0x122b53 3 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[2767]
    (.letOp (n := 2956) (.exec 0x122b53 (fun s => s.RIP = 0x122b53) (movR32R32Effect 0x122b53 3 10 14) (Reg.operands [.gpr 14] [])) #v[2767]
    (.letOp (n := 2957) (.out 0x122b56 (andR32R32Effect 0x122b56 3 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15] []) (.reg (.gpr 10))) #v[2955, 2847]
    (.letOp (n := 2958) (.exec 0x122b56 (fun s => s.RIP = 0x122b56) (andR32R32Effect 0x122b56 3 10 15) (Reg.operands [.gpr 10, .gpr 15] [])) #v[2955, 2847]
    (.letOp (n := 2959) (.out 0x122b59 (movR32R32Effect 0x122b59 3 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[2767]
    (.letOp (n := 2960) (.exec 0x122b59 (fun s => s.RIP = 0x122b59) (movR32R32Effect 0x122b59 3 12 14) (Reg.operands [.gpr 14] [])) #v[2767]
    (.letOp (n := 2961) (.out 0x122b5c (xorR32R32Effect 0x122b5c 3 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[2959, 2847]
    (.letOp (n := 2962) (.exec 0x122b5c (fun s => s.RIP = 0x122b5c) (xorR32R32Effect 0x122b5c 3 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[2959, 2847]
    (.letOp (n := 2963) (.out 0x122b5f (andR32R32Effect 0x122b5f 3 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[2961, 2877]
    (.letOp (n := 2964) (.exec 0x122b5f (fun s => s.RIP = 0x122b5f) (andR32R32Effect 0x122b5f 3 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[2961, 2877]
    (.letOp (n := 2965) (.out 0x122b62 (xorR32R32Effect 0x122b62 3 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[2963, 2957]
    (.letOp (n := 2966) (.exec 0x122b62 (fun s => s.RIP = 0x122b62) (xorR32R32Effect 0x122b62 3 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[2963, 2957]
    (.letOp (n := 2967) (.out 0x122b65 (addR32R32Effect 0x122b65 3 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 9] []) (.reg (.gpr 12))) #v[2965, 2953]
    (.letOp (n := 2968) (.exec 0x122b65 (fun s => s.RIP = 0x122b65) (addR32R32Effect 0x122b65 3 12 9) (Reg.operands [.gpr 12, .gpr 9] [])) #v[2965, 2953]
    (.letOp (n := 2969) (.out 0x122b68 (addR32R32Effect 0x122b68 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[2546, 2937]
    (.letOp (n := 2970) (.exec 0x122b68 (fun s => s.RIP = 0x122b68) (addR32R32Effect 0x122b68 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[2546, 2937]
    (.letOp (n := 2971) (.out 0x122b6b (addR32R32Effect 0x122b6b 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[2967, 2937]
    (.letOp (n := 2972) (.exec 0x122b6b (fun s => s.RIP = 0x122b6b) (addR32R32Effect 0x122b6b 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[2967, 2937]
    (.letOp (n := 2973) (.out 0x122b6e (movR32R32Effect 0x122b6e 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[2801]
    (.letOp (n := 2974) (.exec 0x122b6e (fun s => s.RIP = 0x122b6e) (movR32R32Effect 0x122b6e 3 9 5) (Reg.operands [.gpr 5] [])) #v[2801]
    (b_l121930_75))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_74 : List UInt8 :=
  [0x43, 0x8D, 0x0C, 0x21, 0x81, 0xC1, 0xC7, 0x7F, 0x59, 0xBF, 0x41, 0x89, 0xF1, 0x41, 0xC1, 0xC1,
    0x1E, 0x41, 0x89, 0xF2, 0x41, 0xC1, 0xC2, 0x13, 0x45, 0x31, 0xCA, 0x41, 0x89, 0xF1, 0x41, 0xC1,
    0xC1, 0x0A, 0x45, 0x31, 0xD1, 0x45, 0x89, 0xF2, 0x45, 0x21, 0xFA, 0x45, 0x89, 0xF4, 0x45, 0x31,
    0xFC, 0x41, 0x21, 0xF4, 0x45, 0x31, 0xD4, 0x45, 0x01, 0xCC, 0x41, 0x01, 0xC8, 0x41, 0x01, 0xCC,
    0x41, 0x89, 0xE9] ++ bytes_l121930_75

theorem code_l121930_74 : ∀ x ∈ codeRange 0x122b2e bytes_l121930_74, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22b2e 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_75

def b_l121930_73 : Block Op Label signature Reg.count 2896 :=
  .letOp (n := 2896) (.exec 0x122af0 (StorePre 0x122af0 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x122af0 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x122af0 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[2894, 4]
    (.letOp (n := 2897) (.out 0x122af4 (movR32R32Effect 0x122af4 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[2692]
    (.letOp (n := 2898) (.exec 0x122af4 (fun s => s.RIP = 0x122af4) (movR32R32Effect 0x122af4 3 9 0) (Reg.operands [.gpr 0] [])) #v[2692]
    (.letOp (n := 2899) (.out 0x122af7 (shrR32Effect 0x122af7 4 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2897]
    (.letOp (n := 2900) (.exec 0x122af7 (fun s => s.RIP = 0x122af7) (shrR32Effect 0x122af7 4 9 10) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2897]
    (.letOp (n := 2901) (.out 0x122afb (movR32R32Effect 0x122afb 3 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 3] []) (.reg (.gpr 10))) #v[2871]
    (.letOp (n := 2902) (.exec 0x122afb (fun s => s.RIP = 0x122afb) (movR32R32Effect 0x122afb 3 10 3) (Reg.operands [.gpr 3] [])) #v[2871]
    (.letOp (n := 2903) (.out 0x122afe (rolR32Effect 0x122afe 4 10 26) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2901]
    (.letOp (n := 2904) (.exec 0x122afe (fun s => s.RIP = 0x122afe) (rolR32Effect 0x122afe 4 10 26) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2901]
    (.letOp (n := 2905) (.out 0x122b02 (xorR32R32Effect 0x122b02 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[2899, 2883]
    (.letOp (n := 2906) (.exec 0x122b02 (fun s => s.RIP = 0x122b02) (xorR32R32Effect 0x122b02 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[2899, 2883]
    (.letOp (n := 2907) (.out 0x122b05 (movR32R32Effect 0x122b05 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[2871]
    (.letOp (n := 2908) (.exec 0x122b05 (fun s => s.RIP = 0x122b05) (movR32R32Effect 0x122b05 2 1 3) (Reg.operands [.gpr 3] [])) #v[2871]
    (.letOp (n := 2909) (.out 0x122b07 (rolR32Effect 0x122b07 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2907]
    (.letOp (n := 2910) (.exec 0x122b07 (fun s => s.RIP = 0x122b07) (rolR32Effect 0x122b07 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2907]
    (.letOp (n := 2911) (.out 0x122b0a (movR32M32LowEffect 0x122b0a 0 (.sib 4 none 0 (.d8 0x64))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2912) (.exec 0x122b0a (LoadPre 0x122b0a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x122b0a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x122b0a 0 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2913) (.out 0x122b0e (addR32R32Effect 0x122b0e 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[2911, 2905]
    (.letOp (n := 2914) (.exec 0x122b0e (fun s => s.RIP = 0x122b0e) (addR32R32Effect 0x122b0e 3 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[2911, 2905]
    (.letOp (n := 2915) (.out 0x122b11 (movR32R32Effect 0x122b11 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[2871]
    (.letOp (n := 2916) (.exec 0x122b11 (fun s => s.RIP = 0x122b11) (movR32R32Effect 0x122b11 3 9 3) (Reg.operands [.gpr 3] [])) #v[2871]
    (.letOp (n := 2917) (.out 0x122b14 (rolR32Effect 0x122b14 4 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2915]
    (.letOp (n := 2918) (.exec 0x122b14 (fun s => s.RIP = 0x122b14) (rolR32Effect 0x122b14 4 9 7) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2915]
    (.letOp (n := 2919) (.out 0x122b18 (xorR32R32Effect 0x122b18 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[2909, 2903]
    (.letOp (n := 2920) (.exec 0x122b18 (fun s => s.RIP = 0x122b18) (xorR32R32Effect 0x122b18 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[2909, 2903]
    (.letOp (n := 2921) (.out 0x122b1b (xorR32R32Effect 0x122b1b 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[2917, 2919]
    (.letOp (n := 2922) (.exec 0x122b1b (fun s => s.RIP = 0x122b1b) (xorR32R32Effect 0x122b1b 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[2917, 2919]
    (.letOp (n := 2923) (.out 0x122b1e (movR32R32Effect 0x122b1e 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[2761]
    (.letOp (n := 2924) (.exec 0x122b1e (fun s => s.RIP = 0x122b1e) (movR32R32Effect 0x122b1e 2 1 7) (Reg.operands [.gpr 7] [])) #v[2761]
    (.letOp (n := 2925) (.out 0x122b20 (xorR32R32Effect 0x122b20 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[2923, 2650]
    (.letOp (n := 2926) (.exec 0x122b20 (fun s => s.RIP = 0x122b20) (xorR32R32Effect 0x122b20 3 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[2923, 2650]
    (.letOp (n := 2927) (.out 0x122b23 (andR32R32Effect 0x122b23 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[2925, 2871]
    (.letOp (n := 2928) (.exec 0x122b23 (fun s => s.RIP = 0x122b23) (andR32R32Effect 0x122b23 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[2925, 2871]
    (.letOp (n := 2929) (.out 0x122b25 (xorR32R32Effect 0x122b25 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[2927, 2650]
    (.letOp (n := 2930) (.exec 0x122b25 (fun s => s.RIP = 0x122b25) (xorR32R32Effect 0x122b25 3 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[2927, 2650]
    (.letOp (n := 2931) (.out 0x122b28 (addR32R32Effect 0x122b28 3 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[2544, 2913]
    (.letOp (n := 2932) (.exec 0x122b28 (fun s => s.RIP = 0x122b28) (addR32R32Effect 0x122b28 3 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[2544, 2913]
    (.letOp (n := 2933) (.out 0x122b2b (addR32R32Effect 0x122b2b 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[2931, 2929]
    (.letOp (n := 2934) (.exec 0x122b2b (fun s => s.RIP = 0x122b2b) (addR32R32Effect 0x122b2b 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[2931, 2929]
    (b_l121930_74)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_73 : List UInt8 :=
  [0x44, 0x89, 0x14, 0x24, 0x41, 0x89, 0xC1, 0x41, 0xC1, 0xE9, 0x0A, 0x41, 0x89, 0xDA, 0x41, 0xC1,
    0xC2, 0x1A, 0x41, 0x31, 0xC9, 0x89, 0xD9, 0xC1, 0xC1, 0x15, 0x8B, 0x44, 0x24, 0x64, 0x44, 0x01,
    0xC8, 0x41, 0x89, 0xD9, 0x41, 0xC1, 0xC1, 0x07, 0x44, 0x31, 0xD1, 0x41, 0x31, 0xC9, 0x89, 0xF9,
    0x44, 0x31, 0xE9, 0x21, 0xD9, 0x44, 0x31, 0xE9, 0x41, 0x01, 0xC4, 0x41, 0x01, 0xCC] ++ bytes_l121930_74

theorem code_l121930_73 : ∀ x ∈ codeRange 0x122af0 bytes_l121930_73, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22af0 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_74

def b_l121930_72 : Block Op Label signature Reg.count 2857 :=
  .letOp (n := 2857) (.out 0x122ab1 (andR32R32Effect 0x122ab1 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[2855, 2767]
    (.letOp (n := 2858) (.exec 0x122ab1 (fun s => s.RIP = 0x122ab1) (andR32R32Effect 0x122ab1 3 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[2855, 2767]
    (.letOp (n := 2859) (.out 0x122ab4 (xorR32R32Effect 0x122ab4 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[2857, 2851]
    (.letOp (n := 2860) (.exec 0x122ab4 (fun s => s.RIP = 0x122ab4) (xorR32R32Effect 0x122ab4 3 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[2857, 2851]
    (.letOp (n := 2861) (.out 0x122ab7 (movR32R32Effect 0x122ab7 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2692]
    (.letOp (n := 2862) (.exec 0x122ab7 (fun s => s.RIP = 0x122ab7) (movR32R32Effect 0x122ab7 3 10 0) (Reg.operands [.gpr 0] [])) #v[2692]
    (.letOp (n := 2863) (.out 0x122aba (rolR32Effect 0x122aba 4 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2861]
    (.letOp (n := 2864) (.exec 0x122aba (fun s => s.RIP = 0x122aba) (rolR32Effect 0x122aba 4 10 15) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2861]
    (.letOp (n := 2865) (.out 0x122abe (addR32R32Effect 0x122abe 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[2859, 2845]
    (.letOp (n := 2866) (.exec 0x122abe (fun s => s.RIP = 0x122abe) (addR32R32Effect 0x122abe 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[2859, 2845]
    (.letOp (n := 2867) (.out 0x122ac0 (movR32R32Effect 0x122ac0 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[2692]
    (.letOp (n := 2868) (.exec 0x122ac0 (fun s => s.RIP = 0x122ac0) (movR32R32Effect 0x122ac0 2 1 0) (Reg.operands [.gpr 0] [])) #v[2692]
    (.letOp (n := 2869) (.out 0x122ac2 (rolR32Effect 0x122ac2 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2867]
    (.letOp (n := 2870) (.exec 0x122ac2 (fun s => s.RIP = 0x122ac2) (rolR32Effect 0x122ac2 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2867]
    (.letOp (n := 2871) (.out 0x122ac5 (addR32R32Effect 0x122ac5 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[2454, 2829]
    (.letOp (n := 2872) (.exec 0x122ac5 (fun s => s.RIP = 0x122ac5) (addR32R32Effect 0x122ac5 3 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[2454, 2829]
    (.letOp (n := 2873) (.out 0x122ac8 (movR32R32Effect 0x122ac8 3 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 5] []) (.reg (.gpr 11))) #v[2801]
    (.letOp (n := 2874) (.exec 0x122ac8 (fun s => s.RIP = 0x122ac8) (movR32R32Effect 0x122ac8 3 11 5) (Reg.operands [.gpr 5] [])) #v[2801]
    (.letOp (n := 2875) (.out 0x122acb (rolR32Effect 0x122acb 4 11 25) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[2873]
    (.letOp (n := 2876) (.exec 0x122acb (fun s => s.RIP = 0x122acb) (rolR32Effect 0x122acb 4 11 25) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2873]
    (.letOp (n := 2877) (.out 0x122acf (addR32R32Effect 0x122acf 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[2865, 2829]
    (.letOp (n := 2878) (.exec 0x122acf (fun s => s.RIP = 0x122acf) (addR32R32Effect 0x122acf 3 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[2865, 2829]
    (.letOp (n := 2879) (.out 0x122ad2 (movR32R32Effect 0x122ad2 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[2801]
    (.letOp (n := 2880) (.exec 0x122ad2 (fun s => s.RIP = 0x122ad2) (movR32R32Effect 0x122ad2 3 9 5) (Reg.operands [.gpr 5] [])) #v[2801]
    (.letOp (n := 2881) (.out 0x122ad5 (rolR32Effect 0x122ad5 4 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2879]
    (.letOp (n := 2882) (.exec 0x122ad5 (fun s => s.RIP = 0x122ad5) (rolR32Effect 0x122ad5 4 9 14) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2879]
    (.letOp (n := 2883) (.out 0x122ad9 (xorR32R32Effect 0x122ad9 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[2869, 2863]
    (.letOp (n := 2884) (.exec 0x122ad9 (fun s => s.RIP = 0x122ad9) (xorR32R32Effect 0x122ad9 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[2869, 2863]
    (.letOp (n := 2885) (.out 0x122adc (xorR32R32Effect 0x122adc 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[2881, 2875]
    (.letOp (n := 2886) (.exec 0x122adc (fun s => s.RIP = 0x122adc) (xorR32R32Effect 0x122adc 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[2881, 2875]
    (.letOp (n := 2887) (.out 0x122adf (movR32R32Effect 0x122adf 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 5] []) (.reg (.gpr 10))) #v[2801]
    (.letOp (n := 2888) (.exec 0x122adf (fun s => s.RIP = 0x122adf) (movR32R32Effect 0x122adf 3 10 5) (Reg.operands [.gpr 5] [])) #v[2801]
    (.letOp (n := 2889) (.out 0x122ae2 (shrR32Effect 0x122ae2 4 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2887]
    (.letOp (n := 2890) (.exec 0x122ae2 (fun s => s.RIP = 0x122ae2) (shrR32Effect 0x122ae2 4 10 3) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2887]
    (.letOp (n := 2891) (.out 0x122ae6 (xorR32R32Effect 0x122ae6 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[2889, 2885]
    (.letOp (n := 2892) (.exec 0x122ae6 (fun s => s.RIP = 0x122ae6) (xorR32R32Effect 0x122ae6 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[2889, 2885]
    (.letOp (n := 2893) (.exec 0x122ae9 (StorePre 0x122ae9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x122ae9 + BitVec.ofNat 64 4)) 4) (addMREffect 0x122ae9 4 32 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2692, 4]
    (.letOp (n := 2894) (.out 0x122aed (addR32R32Effect 0x122aed 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[2891, 2692]
    (.letOp (n := 2895) (.exec 0x122aed (fun s => s.RIP = 0x122aed) (addR32R32Effect 0x122aed 3 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2891, 2692]
    (b_l121930_73)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_72 : List UInt8 :=
  [0x44, 0x21, 0xF6, 0x44, 0x31, 0xD6, 0x41, 0x89, 0xC2, 0x41, 0xC1, 0xC2, 0x0F, 0x01, 0xCE, 0x89,
    0xC1, 0xC1, 0xC1, 0x0D, 0x44, 0x01, 0xCB, 0x41, 0x89, 0xEB, 0x41, 0xC1, 0xC3, 0x19, 0x44, 0x01,
    0xCE, 0x41, 0x89, 0xE9, 0x41, 0xC1, 0xC1, 0x0E, 0x44, 0x31, 0xD1, 0x45, 0x31, 0xD9, 0x41, 0x89,
    0xEA, 0x41, 0xC1, 0xEA, 0x03, 0x45, 0x31, 0xCA, 0x01, 0x44, 0x24, 0x0C, 0x41, 0x01, 0xC2] ++ bytes_l121930_73

theorem code_l121930_72 : ∀ x ∈ codeRange 0x122ab1 bytes_l121930_72, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22ab1 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_73

def b_l121930_71 : Block Op Label signature Reg.count 2817 :=
  .letOp (n := 2817) (.out 0x122a70 (xorR32R32Effect 0x122a70 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[2815, 2544]
    (.letOp (n := 2818) (.exec 0x122a70 (fun s => s.RIP = 0x122a70) (xorR32R32Effect 0x122a70 3 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[2815, 2544]
    (.letOp (n := 2819) (.out 0x122a73 (andR32R32Effect 0x122a73 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[2817, 2761]
    (.letOp (n := 2820) (.exec 0x122a73 (fun s => s.RIP = 0x122a73) (andR32R32Effect 0x122a73 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[2817, 2761]
    (.letOp (n := 2821) (.out 0x122a76 (xorR32R32Effect 0x122a76 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[2819, 2544]
    (.letOp (n := 2822) (.exec 0x122a76 (fun s => s.RIP = 0x122a76) (xorR32R32Effect 0x122a76 3 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[2819, 2544]
    (.letOp (n := 2823) (.out 0x122a79 (addR32R32Effect 0x122a79 3 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 5] []) (.reg (.gpr 15))) #v[2448, 2801]
    (.letOp (n := 2824) (.exec 0x122a79 (fun s => s.RIP = 0x122a79) (addR32R32Effect 0x122a79 3 15 5) (Reg.operands [.gpr 15, .gpr 5] [])) #v[2448, 2801]
    (.letOp (n := 2825) (.out 0x122a7c (addR32R32Effect 0x122a7c 3 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9] []) (.reg (.gpr 15))) #v[2823, 2821]
    (.letOp (n := 2826) (.exec 0x122a7c (fun s => s.RIP = 0x122a7c) (addR32R32Effect 0x122a7c 3 15 9) (Reg.operands [.gpr 15, .gpr 9] [])) #v[2823, 2821]
    (.letOp (n := 2827) (.out 0x122a7f (leaR32Effect 0x122a7f 4 9 (.sib 1 (some 15) 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1, .gpr 15] []) (.reg (.gpr 9))) #v[2813, 2825]
    (.letOp (n := 2828) (.exec 0x122a7f (fun s => s.RIP = 0x122a7f) (leaR32Effect 0x122a7f 4 9 (.sib 1 (some 15) 0 .none)) (Reg.operands [.gpr 1, .gpr 15] [])) #v[2813, 2825]
    (.letOp (n := 2829) (.out 0x122a83 (addR32Imm32Effect 0x122a83 7 9 0xb00327c8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[2827]
    (.letOp (n := 2830) (.exec 0x122a83 (fun s => s.RIP = 0x122a83) (addR32Imm32Effect 0x122a83 7 9 0xb00327c8) (Reg.operands [.gpr 9] [])) #v[2827]
    (.letOp (n := 2831) (.out 0x122a8a (movR32R32Effect 0x122a8a 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[2767]
    (.letOp (n := 2832) (.exec 0x122a8a (fun s => s.RIP = 0x122a8a) (movR32R32Effect 0x122a8a 3 1 14) (Reg.operands [.gpr 14] [])) #v[2767]
    (.letOp (n := 2833) (.out 0x122a8d (rolR32Effect 0x122a8d 3 1 30) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2831]
    (.letOp (n := 2834) (.exec 0x122a8d (fun s => s.RIP = 0x122a8d) (rolR32Effect 0x122a8d 3 1 30) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2831]
    (.letOp (n := 2835) (.out 0x122a90 (movR32R32Effect 0x122a90 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[2767]
    (.letOp (n := 2836) (.exec 0x122a90 (fun s => s.RIP = 0x122a90) (movR32R32Effect 0x122a90 3 6 14) (Reg.operands [.gpr 14] [])) #v[2767]
    (.letOp (n := 2837) (.out 0x122a93 (rolR32Effect 0x122a93 3 6 19) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[2835]
    (.letOp (n := 2838) (.exec 0x122a93 (fun s => s.RIP = 0x122a93) (rolR32Effect 0x122a93 3 6 19) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2835]
    (.letOp (n := 2839) (.out 0x122a96 (xorR32R32Effect 0x122a96 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[2837, 2833]
    (.letOp (n := 2840) (.exec 0x122a96 (fun s => s.RIP = 0x122a96) (xorR32R32Effect 0x122a96 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[2837, 2833]
    (.letOp (n := 2841) (.out 0x122a98 (movR32R32Effect 0x122a98 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[2767]
    (.letOp (n := 2842) (.exec 0x122a98 (fun s => s.RIP = 0x122a98) (movR32R32Effect 0x122a98 3 1 14) (Reg.operands [.gpr 14] [])) #v[2767]
    (.letOp (n := 2843) (.out 0x122a9b (rolR32Effect 0x122a9b 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2841]
    (.letOp (n := 2844) (.exec 0x122a9b (fun s => s.RIP = 0x122a9b) (rolR32Effect 0x122a9b 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2841]
    (.letOp (n := 2845) (.out 0x122a9e (xorR32R32Effect 0x122a9e 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[2843, 2839]
    (.letOp (n := 2846) (.exec 0x122a9e (fun s => s.RIP = 0x122a9e) (xorR32R32Effect 0x122a9e 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[2843, 2839]
    (.letOp (n := 2847) (.out 0x122aa0 (movR64M64Effect 0x122aa0 15 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 2848) (.exec 0x122aa0 (LoadPre 0x122aa0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x122aa0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x122aa0 15 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2849) (.out 0x122aa5 (movR32R32Effect 0x122aa5 3 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 15] []) (.reg (.gpr 10))) #v[2847]
    (.letOp (n := 2850) (.exec 0x122aa5 (fun s => s.RIP = 0x122aa5) (movR32R32Effect 0x122aa5 3 10 15) (Reg.operands [.gpr 15] [])) #v[2847]
    (.letOp (n := 2851) (.out 0x122aa8 (andR32R32Effect 0x122aa8 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[2849, 2546]
    (.letOp (n := 2852) (.exec 0x122aa8 (fun s => s.RIP = 0x122aa8) (andR32R32Effect 0x122aa8 3 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[2849, 2546]
    (.letOp (n := 2853) (.out 0x122aab (movR32R32Effect 0x122aab 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[2847]
    (.letOp (n := 2854) (.exec 0x122aab (fun s => s.RIP = 0x122aab) (movR32R32Effect 0x122aab 3 6 15) (Reg.operands [.gpr 15] [])) #v[2847]
    (.letOp (n := 2855) (.out 0x122aae (xorR32R32Effect 0x122aae 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[2853, 2546]
    (.letOp (n := 2856) (.exec 0x122aae (fun s => s.RIP = 0x122aae) (xorR32R32Effect 0x122aae 3 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[2853, 2546]
    (b_l121930_72))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_71 : List UInt8 :=
  [0x45, 0x31, 0xE1, 0x41, 0x21, 0xF9, 0x45, 0x31, 0xE1, 0x41, 0x01, 0xEF, 0x45, 0x01, 0xCF, 0x46,
    0x8D, 0x0C, 0x39, 0x41, 0x81, 0xC1, 0xC8, 0x27, 0x03, 0xB0, 0x44, 0x89, 0xF1, 0xC1, 0xC1, 0x1E,
    0x44, 0x89, 0xF6, 0xC1, 0xC6, 0x13, 0x31, 0xCE, 0x44, 0x89, 0xF1, 0xC1, 0xC1, 0x0A, 0x31, 0xF1,
    0x4C, 0x8B, 0x7C, 0x24, 0x28, 0x45, 0x89, 0xFA, 0x45, 0x21, 0xC2, 0x44, 0x89, 0xFE, 0x44, 0x31,
    0xC6] ++ bytes_l121930_72

theorem code_l121930_71 : ∀ x ∈ codeRange 0x122a70 bytes_l121930_71, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22a70 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_72

def b_l121930_70 : Block Op Label signature Reg.count 2779 :=
  .letOp (n := 2779) (.out 0x122a2c (xorR32R32Effect 0x122a2c 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[2777, 2771]
    (.letOp (n := 2780) (.exec 0x122a2c (fun s => s.RIP = 0x122a2c) (xorR32R32Effect 0x122a2c 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[2777, 2771]
    (.letOp (n := 2781) (.out 0x122a2f (movR32R32Effect 0x122a2f 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[2692]
    (.letOp (n := 2782) (.exec 0x122a2f (fun s => s.RIP = 0x122a2f) (movR32R32Effect 0x122a2f 3 9 0) (Reg.operands [.gpr 0] [])) #v[2692]
    (.letOp (n := 2783) (.out 0x122a32 (shrR32Effect 0x122a32 4 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2781]
    (.letOp (n := 2784) (.exec 0x122a32 (fun s => s.RIP = 0x122a32) (shrR32Effect 0x122a32 4 9 3) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2781]
    (.letOp (n := 2785) (.out 0x122a36 (xorR32R32Effect 0x122a36 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[2783, 2779]
    (.letOp (n := 2786) (.exec 0x122a36 (fun s => s.RIP = 0x122a36) (xorR32R32Effect 0x122a36 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[2783, 2779]
    (.letOp (n := 2787) (.exec 0x122a39 (StorePre 0x122a39 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x122a39 + BitVec.ofNat 64 7)) 4) (addMREffect 0x122a39 7 32 2 (.sib 4 none 0 (.d32 0x8c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2586, 4]
    (.letOp (n := 2788) (.out 0x122a40 (addR32R32Effect 0x122a40 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[2785, 2586]
    (.letOp (n := 2789) (.exec 0x122a40 (fun s => s.RIP = 0x122a40) (addR32R32Effect 0x122a40 3 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[2785, 2586]
    (.letOp (n := 2790) (.exec 0x122a43 (StorePre 0x122a43 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x122a43 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x122a43 9 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[2788, 4]
    (.letOp (n := 2791) (.out 0x122a48 (shrR32Effect 0x122a48 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2586]
    (.letOp (n := 2792) (.exec 0x122a48 (fun s => s.RIP = 0x122a48) (shrR32Effect 0x122a48 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2586]
    (.letOp (n := 2793) (.out 0x122a4b (xorR32R32Effect 0x122a4b 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[2791, 2773]
    (.letOp (n := 2794) (.exec 0x122a4b (fun s => s.RIP = 0x122a4b) (xorR32R32Effect 0x122a4b 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2791, 2773]
    (.letOp (n := 2795) (.out 0x122a4d (movR32R32Effect 0x122a4d 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[2761]
    (.letOp (n := 2796) (.exec 0x122a4d (fun s => s.RIP = 0x122a4d) (movR32R32Effect 0x122a4d 2 1 7) (Reg.operands [.gpr 7] [])) #v[2761]
    (.letOp (n := 2797) (.out 0x122a4f (rolR32Effect 0x122a4f 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2795]
    (.letOp (n := 2798) (.exec 0x122a4f (fun s => s.RIP = 0x122a4f) (rolR32Effect 0x122a4f 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2795]
    (.letOp (n := 2799) (.out 0x122a52 (movR32M32LowEffect 0x122a52 5 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 2800) (.exec 0x122a52 (LoadPre 0x122a52 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x122a52 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x122a52 5 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2801) (.out 0x122a59 (addR32R32Effect 0x122a59 2 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[2799, 2793]
    (.letOp (n := 2802) (.exec 0x122a59 (fun s => s.RIP = 0x122a59) (addR32R32Effect 0x122a59 2 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[2799, 2793]
    (.letOp (n := 2803) (.out 0x122a5b (movR32R32Effect 0x122a5b 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[2761]
    (.letOp (n := 2804) (.exec 0x122a5b (fun s => s.RIP = 0x122a5b) (movR32R32Effect 0x122a5b 3 9 7) (Reg.operands [.gpr 7] [])) #v[2761]
    (.letOp (n := 2805) (.out 0x122a5e (rolR32Effect 0x122a5e 4 9 21) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2803]
    (.letOp (n := 2806) (.exec 0x122a5e (fun s => s.RIP = 0x122a5e) (rolR32Effect 0x122a5e 4 9 21) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2803]
    (.letOp (n := 2807) (.out 0x122a62 (xorR32R32Effect 0x122a62 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[2805, 2797]
    (.letOp (n := 2808) (.exec 0x122a62 (fun s => s.RIP = 0x122a62) (xorR32R32Effect 0x122a62 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[2805, 2797]
    (.letOp (n := 2809) (.out 0x122a65 (movR32R32Effect 0x122a65 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[2761]
    (.letOp (n := 2810) (.exec 0x122a65 (fun s => s.RIP = 0x122a65) (movR32R32Effect 0x122a65 2 1 7) (Reg.operands [.gpr 7] [])) #v[2761]
    (.letOp (n := 2811) (.out 0x122a67 (rolR32Effect 0x122a67 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2809]
    (.letOp (n := 2812) (.exec 0x122a67 (fun s => s.RIP = 0x122a67) (rolR32Effect 0x122a67 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2809]
    (.letOp (n := 2813) (.out 0x122a6a (xorR32R32Effect 0x122a6a 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[2811, 2807]
    (.letOp (n := 2814) (.exec 0x122a6a (fun s => s.RIP = 0x122a6a) (xorR32R32Effect 0x122a6a 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[2811, 2807]
    (.letOp (n := 2815) (.out 0x122a6d (movR32R32Effect 0x122a6d 3 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 13] []) (.reg (.gpr 9))) #v[2650]
    (.letOp (n := 2816) (.exec 0x122a6d (fun s => s.RIP = 0x122a6d) (movR32R32Effect 0x122a6d 3 9 13) (Reg.operands [.gpr 13] [])) #v[2650]
    (b_l121930_71))))))))))))))))))))))))))))))))))))))

def bytes_l121930_70 : List UInt8 :=
  [0x45, 0x31, 0xDA, 0x41, 0x89, 0xC1, 0x41, 0xC1, 0xE9, 0x03, 0x45, 0x31, 0xD1, 0x01, 0x94, 0x24,
    0x8C, 0x00, 0x00, 0x00, 0x41, 0x01, 0xD1, 0x44, 0x89, 0x4C, 0x24, 0x70, 0xC1, 0xEA, 0x0A, 0x31,
    0xCA, 0x89, 0xF9, 0xC1, 0xC1, 0x1A, 0x8B, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x01, 0xD5, 0x41,
    0x89, 0xF9, 0x41, 0xC1, 0xC1, 0x15, 0x41, 0x31, 0xC9, 0x89, 0xF9, 0xC1, 0xC1, 0x07, 0x44, 0x31,
    0xC9, 0x45, 0x89, 0xE9] ++ bytes_l121930_71

theorem code_l121930_70 : ∀ x ∈ codeRange 0x122a2c bytes_l121930_70, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22a2c 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_71

def b_l121930_69 : Block Op Label signature Reg.count 2739 :=
  .letOp (n := 2739) (.out 0x1229ef (xorR32R32Effect 0x1229ef 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[2728, 2722]
    (.letOp (n := 2740) (.exec 0x1229ef (fun s => s.RIP = 0x1229ef) (xorR32R32Effect 0x1229ef 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[2728, 2722]
    (.letOp (n := 2741) (.out 0x1229f2 (xorR32R32Effect 0x1229f2 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[2737, 2739]
    (.letOp (n := 2742) (.exec 0x1229f2 (fun s => s.RIP = 0x1229f2) (xorR32R32Effect 0x1229f2 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[2737, 2739]
    (.letOp (n := 2743) (.out 0x1229f5 (movR32R32Effect 0x1229f5 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[2546]
    (.letOp (n := 2744) (.exec 0x1229f5 (fun s => s.RIP = 0x1229f5) (movR32R32Effect 0x1229f5 3 10 8) (Reg.operands [.gpr 8] [])) #v[2546]
    (.letOp (n := 2745) (.out 0x1229f8 (andR32R32Effect 0x1229f8 3 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[2743, 2454]
    (.letOp (n := 2746) (.exec 0x1229f8 (fun s => s.RIP = 0x1229f8) (andR32R32Effect 0x1229f8 3 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[2743, 2454]
    (.letOp (n := 2747) (.out 0x1229fb (movR32R32Effect 0x1229fb 3 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[2546]
    (.letOp (n := 2748) (.exec 0x1229fb (fun s => s.RIP = 0x1229fb) (movR32R32Effect 0x1229fb 3 14 8) (Reg.operands [.gpr 8] [])) #v[2546]
    (.letOp (n := 2749) (.out 0x1229fe (xorR32R32Effect 0x1229fe 3 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[2747, 2454]
    (.letOp (n := 2750) (.exec 0x1229fe (fun s => s.RIP = 0x1229fe) (xorR32R32Effect 0x1229fe 3 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[2747, 2454]
    (.letOp (n := 2751) (.out 0x122a01 (andR32R32Effect 0x122a01 3 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[2749, 2658]
    (.letOp (n := 2752) (.exec 0x122a01 (fun s => s.RIP = 0x122a01) (andR32R32Effect 0x122a01 3 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[2749, 2658]
    (.letOp (n := 2753) (.out 0x122a04 (xorR32R32Effect 0x122a04 3 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10] []) (.reg (.gpr 14))) #v[2751, 2745]
    (.letOp (n := 2754) (.exec 0x122a04 (fun s => s.RIP = 0x122a04) (xorR32R32Effect 0x122a04 3 14 10) (Reg.operands [.gpr 14, .gpr 10] [])) #v[2751, 2745]
    (.letOp (n := 2755) (.out 0x122a07 (addR32R32Effect 0x122a07 3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[2753, 2741]
    (.letOp (n := 2756) (.exec 0x122a07 (fun s => s.RIP = 0x122a07) (addR32R32Effect 0x122a07 3 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[2753, 2741]
    (.letOp (n := 2757) (.out 0x122a0a (movR32R32Effect 0x122a0a 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[2586]
    (.letOp (n := 2758) (.exec 0x122a0a (fun s => s.RIP = 0x122a0a) (movR32R32Effect 0x122a0a 3 10 2) (Reg.operands [.gpr 2] [])) #v[2586]
    (.letOp (n := 2759) (.out 0x122a0d (rolR32Effect 0x122a0d 4 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2757]
    (.letOp (n := 2760) (.exec 0x122a0d (fun s => s.RIP = 0x122a0d) (rolR32Effect 0x122a0d 4 10 15) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2757]
    (.letOp (n := 2761) (.out 0x122a11 (addR32R32Effect 0x122a11 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[2316, 2732]
    (.letOp (n := 2762) (.exec 0x122a11 (fun s => s.RIP = 0x122a11) (addR32R32Effect 0x122a11 2 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[2316, 2732]
    (.letOp (n := 2763) (.out 0x122a13 (movR32R32Effect 0x122a13 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2586]
    (.letOp (n := 2764) (.exec 0x122a13 (fun s => s.RIP = 0x122a13) (movR32R32Effect 0x122a13 2 1 2) (Reg.operands [.gpr 2] [])) #v[2586]
    (.letOp (n := 2765) (.out 0x122a15 (rolR32Effect 0x122a15 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2763]
    (.letOp (n := 2766) (.exec 0x122a15 (fun s => s.RIP = 0x122a15) (rolR32Effect 0x122a15 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2763]
    (.letOp (n := 2767) (.out 0x122a18 (addR32R32Effect 0x122a18 3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[2755, 2732]
    (.letOp (n := 2768) (.exec 0x122a18 (fun s => s.RIP = 0x122a18) (addR32R32Effect 0x122a18 3 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[2755, 2732]
    (.letOp (n := 2769) (.out 0x122a1b (movR32R32Effect 0x122a1b 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[2692]
    (.letOp (n := 2770) (.exec 0x122a1b (fun s => s.RIP = 0x122a1b) (movR32R32Effect 0x122a1b 3 11 0) (Reg.operands [.gpr 0] [])) #v[2692]
    (.letOp (n := 2771) (.out 0x122a1e (rolR32Effect 0x122a1e 4 11 25) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[2769]
    (.letOp (n := 2772) (.exec 0x122a1e (fun s => s.RIP = 0x122a1e) (rolR32Effect 0x122a1e 4 11 25) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2769]
    (.letOp (n := 2773) (.out 0x122a22 (xorR32R32Effect 0x122a22 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[2765, 2759]
    (.letOp (n := 2774) (.exec 0x122a22 (fun s => s.RIP = 0x122a22) (xorR32R32Effect 0x122a22 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[2765, 2759]
    (.letOp (n := 2775) (.out 0x122a25 (movR32R32Effect 0x122a25 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[2692]
    (.letOp (n := 2776) (.exec 0x122a25 (fun s => s.RIP = 0x122a25) (movR32R32Effect 0x122a25 3 10 0) (Reg.operands [.gpr 0] [])) #v[2692]
    (.letOp (n := 2777) (.out 0x122a28 (rolR32Effect 0x122a28 4 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2775]
    (.letOp (n := 2778) (.exec 0x122a28 (fun s => s.RIP = 0x122a28) (rolR32Effect 0x122a28 4 10 14) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2775]
    (b_l121930_70))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_69 : List UInt8 :=
  [0x45, 0x31, 0xDA, 0x44, 0x31, 0xD1, 0x45, 0x89, 0xC2, 0x41, 0x21, 0xDA, 0x45, 0x89, 0xC6, 0x41,
    0x31, 0xDE, 0x41, 0x21, 0xF6, 0x45, 0x31, 0xD6, 0x41, 0x01, 0xCE, 0x41, 0x89, 0xD2, 0x41, 0xC1,
    0xC2, 0x0F, 0x01, 0xEF, 0x89, 0xD1, 0xC1, 0xC1, 0x0D, 0x41, 0x01, 0xEE, 0x41, 0x89, 0xC3, 0x41,
    0xC1, 0xC3, 0x19, 0x44, 0x31, 0xD1, 0x41, 0x89, 0xC2, 0x41, 0xC1, 0xC2, 0x0E] ++ bytes_l121930_70

theorem code_l121930_69 : ∀ x ∈ codeRange 0x1229ef bytes_l121930_69, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x229ef 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_70

def b_l121930_68 : Block Op Label signature Reg.count 2700 :=
  .letOp (n := 2700) (.out 0x1229ab (rolR32Effect 0x1229ab 4 10 21) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2698]
    (.letOp (n := 2701) (.exec 0x1229ab (fun s => s.RIP = 0x1229ab) (rolR32Effect 0x1229ab 4 10 21) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2698]
    (.letOp (n := 2702) (.out 0x1229af (xorR32R32Effect 0x1229af 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[2700, 2696]
    (.letOp (n := 2703) (.exec 0x1229af (fun s => s.RIP = 0x1229af) (xorR32R32Effect 0x1229af 3 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[2700, 2696]
    (.letOp (n := 2704) (.out 0x1229b2 (movR32R32Effect 0x1229b2 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[2650]
    (.letOp (n := 2705) (.exec 0x1229b2 (fun s => s.RIP = 0x1229b2) (movR32R32Effect 0x1229b2 3 1 13) (Reg.operands [.gpr 13] [])) #v[2650]
    (.letOp (n := 2706) (.out 0x1229b5 (rolR32Effect 0x1229b5 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2704]
    (.letOp (n := 2707) (.exec 0x1229b5 (fun s => s.RIP = 0x1229b5) (rolR32Effect 0x1229b5 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2704]
    (.letOp (n := 2708) (.out 0x1229b8 (xorR32R32Effect 0x1229b8 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[2706, 2702]
    (.letOp (n := 2709) (.exec 0x1229b8 (fun s => s.RIP = 0x1229b8) (xorR32R32Effect 0x1229b8 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[2706, 2702]
    (.letOp (n := 2710) (.out 0x1229bb (movR32R32Effect 0x1229bb 3 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 12] []) (.reg (.gpr 10))) #v[2544]
    (.letOp (n := 2711) (.exec 0x1229bb (fun s => s.RIP = 0x1229bb) (movR32R32Effect 0x1229bb 3 10 12) (Reg.operands [.gpr 12] [])) #v[2544]
    (.letOp (n := 2712) (.out 0x1229be (xorR32R32Effect 0x1229be 3 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15] []) (.reg (.gpr 10))) #v[2710, 2448]
    (.letOp (n := 2713) (.exec 0x1229be (fun s => s.RIP = 0x1229be) (xorR32R32Effect 0x1229be 3 10 15) (Reg.operands [.gpr 10, .gpr 15] [])) #v[2710, 2448]
    (.letOp (n := 2714) (.out 0x1229c1 (andR32R32Effect 0x1229c1 3 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[2712, 2650]
    (.letOp (n := 2715) (.exec 0x1229c1 (fun s => s.RIP = 0x1229c1) (andR32R32Effect 0x1229c1 3 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[2712, 2650]
    (.letOp (n := 2716) (.out 0x1229c4 (xorR32R32Effect 0x1229c4 3 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15] []) (.reg (.gpr 10))) #v[2714, 2448]
    (.letOp (n := 2717) (.exec 0x1229c4 (fun s => s.RIP = 0x1229c4) (xorR32R32Effect 0x1229c4 3 10 15) (Reg.operands [.gpr 10, .gpr 15] [])) #v[2714, 2448]
    (.letOp (n := 2718) (.out 0x1229c7 (addR32R32Effect 0x1229c7 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[2314, 2692]
    (.letOp (n := 2719) (.exec 0x1229c7 (fun s => s.RIP = 0x1229c7) (addR32R32Effect 0x1229c7 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[2314, 2692]
    (.letOp (n := 2720) (.out 0x1229ca (movR32R32Effect 0x1229ca 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[2658]
    (.letOp (n := 2721) (.exec 0x1229ca (fun s => s.RIP = 0x1229ca) (movR32R32Effect 0x1229ca 3 11 6) (Reg.operands [.gpr 6] [])) #v[2658]
    (.letOp (n := 2722) (.out 0x1229cd (rolR32Effect 0x1229cd 4 11 30) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[2720]
    (.letOp (n := 2723) (.exec 0x1229cd (fun s => s.RIP = 0x1229cd) (rolR32Effect 0x1229cd 4 11 30) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2720]
    (.letOp (n := 2724) (.out 0x1229d1 (addR32R32Effect 0x1229d1 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[2718, 2716]
    (.letOp (n := 2725) (.exec 0x1229d1 (fun s => s.RIP = 0x1229d1) (addR32R32Effect 0x1229d1 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[2718, 2716]
    (.letOp (n := 2726) (.out 0x1229d4 (movR32R32Effect 0x1229d4 3 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[2658]
    (.letOp (n := 2727) (.exec 0x1229d4 (fun s => s.RIP = 0x1229d4) (movR32R32Effect 0x1229d4 3 10 6) (Reg.operands [.gpr 6] [])) #v[2658]
    (.letOp (n := 2728) (.out 0x1229d7 (rolR32Effect 0x1229d7 4 10 19) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2726]
    (.letOp (n := 2729) (.exec 0x1229d7 (fun s => s.RIP = 0x1229d7) (rolR32Effect 0x1229d7 4 10 19) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2726]
    (.letOp (n := 2730) (.out 0x1229db (leaR32Effect 0x1229db 4 5 (.sib 1 (some 9) 0 .none)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1, .gpr 9] []) (.reg (.gpr 5))) #v[2708, 2724]
    (.letOp (n := 2731) (.exec 0x1229db (fun s => s.RIP = 0x1229db) (leaR32Effect 0x1229db 4 5 (.sib 1 (some 9) 0 .none)) (Reg.operands [.gpr 1, .gpr 9] [])) #v[2708, 2724]
    (.letOp (n := 2732) (.out 0x1229df (addR32Imm32Effect 0x1229df 6 5 0xa831c66d) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[2730]
    (.letOp (n := 2733) (.exec 0x1229df (fun s => s.RIP = 0x1229df) (addR32Imm32Effect 0x1229df 6 5 0xa831c66d) (Reg.operands [.gpr 5] [])) #v[2730]
    (.letOp (n := 2734) (.out 0x1229e5 (movR32R32Effect 0x1229e5 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[2658]
    (.letOp (n := 2735) (.exec 0x1229e5 (fun s => s.RIP = 0x1229e5) (movR32R32Effect 0x1229e5 2 1 6) (Reg.operands [.gpr 6] [])) #v[2658]
    (.letOp (n := 2736) (.exec 0x1229e7 (StorePre 0x1229e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1229e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1229e7 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[2658, 4]
    (.letOp (n := 2737) (.out 0x1229ec (rolR32Effect 0x1229ec 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2734]
    (.letOp (n := 2738) (.exec 0x1229ec (fun s => s.RIP = 0x1229ec) (rolR32Effect 0x1229ec 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2734]
    (b_l121930_69)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_68 : List UInt8 :=
  [0x41, 0xC1, 0xC2, 0x15, 0x41, 0x31, 0xCA, 0x44, 0x89, 0xE9, 0xC1, 0xC1, 0x07, 0x44, 0x31, 0xD1,
    0x45, 0x89, 0xE2, 0x45, 0x31, 0xFA, 0x45, 0x21, 0xEA, 0x45, 0x31, 0xFA, 0x41, 0x01, 0xC1, 0x41,
    0x89, 0xF3, 0x41, 0xC1, 0xC3, 0x1E, 0x45, 0x01, 0xD1, 0x41, 0x89, 0xF2, 0x41, 0xC1, 0xC2, 0x13,
    0x42, 0x8D, 0x2C, 0x09, 0x81, 0xC5, 0x6D, 0xC6, 0x31, 0xA8, 0x89, 0xF1, 0x48, 0x89, 0x74, 0x24,
    0x28, 0xC1, 0xC1, 0x0A] ++ bytes_l121930_69

theorem code_l121930_68 : ∀ x ∈ codeRange 0x1229ab bytes_l121930_68, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x229ab 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_69

def b_l121930_67 : Block Op Label signature Reg.count 2662 :=
  .letOp (n := 2662) (.out 0x122967 (rolR32Effect 0x122967 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2660]
    (.letOp (n := 2663) (.exec 0x122967 (fun s => s.RIP = 0x122967) (rolR32Effect 0x122967 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2660]
    (.letOp (n := 2664) (.out 0x12296a (xorR32R32Effect 0x12296a 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[2662, 2654]
    (.letOp (n := 2665) (.exec 0x12296a (fun s => s.RIP = 0x12296a) (xorR32R32Effect 0x12296a 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[2662, 2654]
    (.letOp (n := 2666) (.out 0x12296d (movR32R32Effect 0x12296d 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[2586]
    (.letOp (n := 2667) (.exec 0x12296d (fun s => s.RIP = 0x12296d) (movR32R32Effect 0x12296d 3 10 2) (Reg.operands [.gpr 2] [])) #v[2586]
    (.letOp (n := 2668) (.out 0x122970 (rolR32Effect 0x122970 4 10 25) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2666]
    (.letOp (n := 2669) (.exec 0x122970 (fun s => s.RIP = 0x122970) (rolR32Effect 0x122970 4 10 25) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2666]
    (.letOp (n := 2670) (.out 0x122974 (movR32R32Effect 0x122974 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2586]
    (.letOp (n := 2671) (.exec 0x122974 (fun s => s.RIP = 0x122974) (movR32R32Effect 0x122974 3 11 2) (Reg.operands [.gpr 2] [])) #v[2586]
    (.letOp (n := 2672) (.out 0x122977 (rolR32Effect 0x122977 4 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[2670]
    (.letOp (n := 2673) (.exec 0x122977 (fun s => s.RIP = 0x122977) (rolR32Effect 0x122977 4 11 14) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2670]
    (.letOp (n := 2674) (.out 0x12297b (xorR32R32Effect 0x12297b 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[2672, 2668]
    (.letOp (n := 2675) (.exec 0x12297b (fun s => s.RIP = 0x12297b) (xorR32R32Effect 0x12297b 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[2672, 2668]
    (.letOp (n := 2676) (.out 0x12297e (movR32R32Effect 0x12297e 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[2586]
    (.letOp (n := 2677) (.exec 0x12297e (fun s => s.RIP = 0x12297e) (movR32R32Effect 0x12297e 3 10 2) (Reg.operands [.gpr 2] [])) #v[2586]
    (.letOp (n := 2678) (.out 0x122981 (shrR32Effect 0x122981 4 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2676]
    (.letOp (n := 2679) (.exec 0x122981 (fun s => s.RIP = 0x122981) (shrR32Effect 0x122981 4 10 3) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2676]
    (.letOp (n := 2680) (.out 0x122985 (xorR32R32Effect 0x122985 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[2678, 2674]
    (.letOp (n := 2681) (.exec 0x122985 (fun s => s.RIP = 0x122985) (xorR32R32Effect 0x122985 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[2678, 2674]
    (.letOp (n := 2682) (.exec 0x122988 (StorePre 0x122988 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x122988 + BitVec.ofNat 64 5)) 4) (addMREffect 0x122988 5 32 14 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[2488, 4]
    (.letOp (n := 2683) (.out 0x12298d (addR32R32Effect 0x12298d 3 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[2680, 2488]
    (.letOp (n := 2684) (.exec 0x12298d (fun s => s.RIP = 0x12298d) (addR32R32Effect 0x12298d 3 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[2680, 2488]
    (.letOp (n := 2685) (.exec 0x122990 (StorePre 0x122990 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x122990 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x122990 10 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[2683, 4]
    (.letOp (n := 2686) (.out 0x122995 (shrR32Effect 0x122995 4 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[2488]
    (.letOp (n := 2687) (.exec 0x122995 (fun s => s.RIP = 0x122995) (shrR32Effect 0x122995 4 14 10) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2488]
    (.letOp (n := 2688) (.out 0x122999 (xorR32R32Effect 0x122999 3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[2686, 2664]
    (.letOp (n := 2689) (.exec 0x122999 (fun s => s.RIP = 0x122999) (xorR32R32Effect 0x122999 3 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[2686, 2664]
    (.letOp (n := 2690) (.out 0x12299c (movR32M32LowEffect 0x12299c 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2691) (.exec 0x12299c (LoadPre 0x12299c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12299c + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12299c 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2692) (.out 0x12299f (addR32R32Effect 0x12299f 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[2690, 2688]
    (.letOp (n := 2693) (.exec 0x12299f (fun s => s.RIP = 0x12299f) (addR32R32Effect 0x12299f 3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[2690, 2688]
    (.letOp (n := 2694) (.out 0x1229a2 (movR32R32Effect 0x1229a2 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[2650]
    (.letOp (n := 2695) (.exec 0x1229a2 (fun s => s.RIP = 0x1229a2) (movR32R32Effect 0x1229a2 3 1 13) (Reg.operands [.gpr 13] [])) #v[2650]
    (.letOp (n := 2696) (.out 0x1229a5 (rolR32Effect 0x1229a5 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2694]
    (.letOp (n := 2697) (.exec 0x1229a5 (fun s => s.RIP = 0x1229a5) (rolR32Effect 0x1229a5 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2694]
    (.letOp (n := 2698) (.out 0x1229a8 (movR32R32Effect 0x1229a8 3 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 13] []) (.reg (.gpr 10))) #v[2650]
    (.letOp (n := 2699) (.exec 0x1229a8 (fun s => s.RIP = 0x1229a8) (movR32R32Effect 0x1229a8 3 10 13) (Reg.operands [.gpr 13] [])) #v[2650]
    (b_l121930_68))))))))))))))))))))))))))))))))))))))

def bytes_l121930_67 : List UInt8 :=
  [0xC1, 0xC1, 0x0D, 0x44, 0x31, 0xD9, 0x41, 0x89, 0xD2, 0x41, 0xC1, 0xC2, 0x19, 0x41, 0x89, 0xD3,
    0x41, 0xC1, 0xC3, 0x0E, 0x45, 0x31, 0xD3, 0x41, 0x89, 0xD2, 0x41, 0xC1, 0xEA, 0x03, 0x45, 0x31,
    0xDA, 0x44, 0x01, 0x74, 0x24, 0x04, 0x45, 0x01, 0xF2, 0x44, 0x89, 0x54, 0x24, 0x48, 0x41, 0xC1,
    0xEE, 0x0A, 0x41, 0x31, 0xCE, 0x8B, 0x04, 0x24, 0x44, 0x01, 0xF0, 0x44, 0x89, 0xE9, 0xC1, 0xC1,
    0x1A, 0x45, 0x89, 0xEA] ++ bytes_l121930_68

theorem code_l121930_67 : ∀ x ∈ codeRange 0x122967 bytes_l121930_67, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22967 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_68

def b_l121930_66 : Block Op Label signature Reg.count 2622 :=
  .letOp (n := 2622) (.out 0x12292b (addR32Imm32Effect 0x12292b 7 10 0x983e5152) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[2620]
    (.letOp (n := 2623) (.exec 0x12292b (fun s => s.RIP = 0x12292b) (addR32Imm32Effect 0x12292b 7 10 0x983e5152) (Reg.operands [.gpr 10] [])) #v[2620]
    (.letOp (n := 2624) (.out 0x122932 (movR32R32Effect 0x122932 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2546]
    (.letOp (n := 2625) (.exec 0x122932 (fun s => s.RIP = 0x122932) (movR32R32Effect 0x122932 3 0 8) (Reg.operands [.gpr 8] [])) #v[2546]
    (.letOp (n := 2626) (.out 0x122935 (rolR32Effect 0x122935 3 0 19) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2624]
    (.letOp (n := 2627) (.exec 0x122935 (fun s => s.RIP = 0x122935) (rolR32Effect 0x122935 3 0 19) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2624]
    (.letOp (n := 2628) (.out 0x122938 (xorR32R32Effect 0x122938 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2626, 2618]
    (.letOp (n := 2629) (.exec 0x122938 (fun s => s.RIP = 0x122938) (xorR32R32Effect 0x122938 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2626, 2618]
    (.letOp (n := 2630) (.out 0x12293a (movR32R32Effect 0x12293a 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[2546]
    (.letOp (n := 2631) (.exec 0x12293a (fun s => s.RIP = 0x12293a) (movR32R32Effect 0x12293a 3 1 8) (Reg.operands [.gpr 8] [])) #v[2546]
    (.letOp (n := 2632) (.out 0x12293d (rolR32Effect 0x12293d 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2630]
    (.letOp (n := 2633) (.exec 0x12293d (fun s => s.RIP = 0x12293d) (rolR32Effect 0x12293d 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2630]
    (.letOp (n := 2634) (.out 0x122940 (xorR32R32Effect 0x122940 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2632, 2628]
    (.letOp (n := 2635) (.exec 0x122940 (fun s => s.RIP = 0x122940) (xorR32R32Effect 0x122940 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2632, 2628]
    (.letOp (n := 2636) (.out 0x122942 (movR32R32Effect 0x122942 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[2454]
    (.letOp (n := 2637) (.exec 0x122942 (fun s => s.RIP = 0x122942) (movR32R32Effect 0x122942 3 11 3) (Reg.operands [.gpr 3] [])) #v[2454]
    (.letOp (n := 2638) (.out 0x122945 (andR32R32Effect 0x122945 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[2636, 2316]
    (.letOp (n := 2639) (.exec 0x122945 (fun s => s.RIP = 0x122945) (andR32R32Effect 0x122945 3 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[2636, 2316]
    (.letOp (n := 2640) (.out 0x122948 (movR32R32Effect 0x122948 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[2454]
    (.letOp (n := 2641) (.exec 0x122948 (fun s => s.RIP = 0x122948) (movR32R32Effect 0x122948 2 0 3) (Reg.operands [.gpr 3] [])) #v[2454]
    (.letOp (n := 2642) (.out 0x12294a (xorR32R32Effect 0x12294a 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[2640, 2316]
    (.letOp (n := 2643) (.exec 0x12294a (fun s => s.RIP = 0x12294a) (xorR32R32Effect 0x12294a 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[2640, 2316]
    (.letOp (n := 2644) (.out 0x12294c (andR32R32Effect 0x12294c 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[2642, 2546]
    (.letOp (n := 2645) (.exec 0x12294c (fun s => s.RIP = 0x12294c) (andR32R32Effect 0x12294c 3 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[2642, 2546]
    (.letOp (n := 2646) (.out 0x12294f (xorR32R32Effect 0x12294f 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[2644, 2638]
    (.letOp (n := 2647) (.exec 0x12294f (fun s => s.RIP = 0x12294f) (xorR32R32Effect 0x12294f 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[2644, 2638]
    (.letOp (n := 2648) (.out 0x122952 (addR32R32Effect 0x122952 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2646, 2634]
    (.letOp (n := 2649) (.exec 0x122952 (fun s => s.RIP = 0x122952) (addR32R32Effect 0x122952 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2646, 2634]
    (.letOp (n := 2650) (.out 0x122954 (addR32R32Effect 0x122954 3 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[2194, 2622]
    (.letOp (n := 2651) (.exec 0x122954 (fun s => s.RIP = 0x122954) (addR32R32Effect 0x122954 3 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[2194, 2622]
    (.letOp (n := 2652) (.out 0x122957 (movR32R32Effect 0x122957 3 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 14] []) (.reg (.gpr 11))) #v[2488]
    (.letOp (n := 2653) (.exec 0x122957 (fun s => s.RIP = 0x122957) (movR32R32Effect 0x122957 3 11 14) (Reg.operands [.gpr 14] [])) #v[2488]
    (.letOp (n := 2654) (.out 0x12295a (rolR32Effect 0x12295a 4 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[2652]
    (.letOp (n := 2655) (.exec 0x12295a (fun s => s.RIP = 0x12295a) (rolR32Effect 0x12295a 4 11 15) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2652]
    (.letOp (n := 2656) (.out 0x12295e (addR32R32Effect 0x12295e 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[2648, 2622]
    (.letOp (n := 2657) (.exec 0x12295e (fun s => s.RIP = 0x12295e) (addR32R32Effect 0x12295e 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[2648, 2622]
    (.letOp (n := 2658) (.out 0x122961 (movR64R64Effect 0x122961 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[2656]
    (.letOp (n := 2659) (.exec 0x122961 (fun s => s.RIP = 0x122961) (movR64R64Effect 0x122961 6 0) (Reg.operands [.gpr 0] [])) #v[2656]
    (.letOp (n := 2660) (.out 0x122964 (movR32R32Effect 0x122964 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[2488]
    (.letOp (n := 2661) (.exec 0x122964 (fun s => s.RIP = 0x122964) (movR32R32Effect 0x122964 3 1 14) (Reg.operands [.gpr 14] [])) #v[2488]
    (b_l121930_67))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_66 : List UInt8 :=
  [0x41, 0x81, 0xC2, 0x52, 0x51, 0x3E, 0x98, 0x44, 0x89, 0xC0, 0xC1, 0xC0, 0x13, 0x31, 0xC8, 0x44,
    0x89, 0xC1, 0xC1, 0xC1, 0x0A, 0x31, 0xC1, 0x41, 0x89, 0xDB, 0x41, 0x21, 0xFB, 0x89, 0xD8, 0x31,
    0xF8, 0x44, 0x21, 0xC0, 0x44, 0x31, 0xD8, 0x01, 0xC8, 0x45, 0x01, 0xD5, 0x45, 0x89, 0xF3, 0x41,
    0xC1, 0xC3, 0x0F, 0x44, 0x01, 0xD0, 0x48, 0x89, 0xC6, 0x44, 0x89, 0xF1] ++ bytes_l121930_67

theorem code_l121930_66 : ∀ x ∈ codeRange 0x12292b bytes_l121930_66, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2292b 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_67

def b_l121930_65 : Block Op Label signature Reg.count 2582 :=
  .letOp (n := 2582) (.out 0x1228f3 (xorR32R32Effect 0x1228f3 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2580, 2556]
    (.letOp (n := 2583) (.exec 0x1228f3 (fun s => s.RIP = 0x1228f3) (xorR32R32Effect 0x1228f3 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2580, 2556]
    (.letOp (n := 2584) (.out 0x1228f5 (movR32M32LowEffect 0x1228f5 2 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 2585) (.exec 0x1228f5 (LoadPre 0x1228f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1228f5 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1228f5 2 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2586) (.out 0x1228f9 (addR32R32Effect 0x1228f9 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[2584, 2582]
    (.letOp (n := 2587) (.exec 0x1228f9 (fun s => s.RIP = 0x1228f9) (addR32R32Effect 0x1228f9 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2584, 2582]
    (.letOp (n := 2588) (.out 0x1228fb (movR32R32Effect 0x1228fb 3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[2544]
    (.letOp (n := 2589) (.exec 0x1228fb (fun s => s.RIP = 0x1228fb) (movR32R32Effect 0x1228fb 3 0 12) (Reg.operands [.gpr 12] [])) #v[2544]
    (.letOp (n := 2590) (.out 0x1228fe (rolR32Effect 0x1228fe 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2588]
    (.letOp (n := 2591) (.exec 0x1228fe (fun s => s.RIP = 0x1228fe) (rolR32Effect 0x1228fe 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2588]
    (.letOp (n := 2592) (.out 0x122901 (movR32R32Effect 0x122901 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[2544]
    (.letOp (n := 2593) (.exec 0x122901 (fun s => s.RIP = 0x122901) (movR32R32Effect 0x122901 3 1 12) (Reg.operands [.gpr 12] [])) #v[2544]
    (.letOp (n := 2594) (.out 0x122904 (rolR32Effect 0x122904 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2592]
    (.letOp (n := 2595) (.exec 0x122904 (fun s => s.RIP = 0x122904) (rolR32Effect 0x122904 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2592]
    (.letOp (n := 2596) (.out 0x122907 (xorR32R32Effect 0x122907 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2594, 2590]
    (.letOp (n := 2597) (.exec 0x122907 (fun s => s.RIP = 0x122907) (xorR32R32Effect 0x122907 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2594, 2590]
    (.letOp (n := 2598) (.out 0x122909 (movR32R32Effect 0x122909 3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[2544]
    (.letOp (n := 2599) (.exec 0x122909 (fun s => s.RIP = 0x122909) (movR32R32Effect 0x122909 3 0 12) (Reg.operands [.gpr 12] [])) #v[2544]
    (.letOp (n := 2600) (.out 0x12290c (rolR32Effect 0x12290c 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2598]
    (.letOp (n := 2601) (.exec 0x12290c (fun s => s.RIP = 0x12290c) (rolR32Effect 0x12290c 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2598]
    (.letOp (n := 2602) (.out 0x12290f (xorR32R32Effect 0x12290f 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2600, 2596]
    (.letOp (n := 2603) (.exec 0x12290f (fun s => s.RIP = 0x12290f) (xorR32R32Effect 0x12290f 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2600, 2596]
    (.letOp (n := 2604) (.out 0x122911 (movR32R32Effect 0x122911 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[2448]
    (.letOp (n := 2605) (.exec 0x122911 (fun s => s.RIP = 0x122911) (movR32R32Effect 0x122911 3 1 15) (Reg.operands [.gpr 15] [])) #v[2448]
    (.letOp (n := 2606) (.out 0x122914 (xorR32R32Effect 0x122914 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[2604, 2314]
    (.letOp (n := 2607) (.exec 0x122914 (fun s => s.RIP = 0x122914) (xorR32R32Effect 0x122914 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[2604, 2314]
    (.letOp (n := 2608) (.out 0x122917 (andR32R32Effect 0x122917 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[2606, 2544]
    (.letOp (n := 2609) (.exec 0x122917 (fun s => s.RIP = 0x122917) (andR32R32Effect 0x122917 3 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[2606, 2544]
    (.letOp (n := 2610) (.out 0x12291a (xorR32R32Effect 0x12291a 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[2608, 2314]
    (.letOp (n := 2611) (.exec 0x12291a (fun s => s.RIP = 0x12291a) (xorR32R32Effect 0x12291a 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[2608, 2314]
    (.letOp (n := 2612) (.out 0x12291d (addR32R32Effect 0x12291d 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[2248, 2586]
    (.letOp (n := 2613) (.exec 0x12291d (fun s => s.RIP = 0x12291d) (addR32R32Effect 0x12291d 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[2248, 2586]
    (.letOp (n := 2614) (.out 0x12291f (addR32R32Effect 0x12291f 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[2612, 2610]
    (.letOp (n := 2615) (.exec 0x12291f (fun s => s.RIP = 0x12291f) (addR32R32Effect 0x12291f 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[2612, 2610]
    (.letOp (n := 2616) (.out 0x122921 (movR32R32Effect 0x122921 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[2546]
    (.letOp (n := 2617) (.exec 0x122921 (fun s => s.RIP = 0x122921) (movR32R32Effect 0x122921 3 1 8) (Reg.operands [.gpr 8] [])) #v[2546]
    (.letOp (n := 2618) (.out 0x122924 (rolR32Effect 0x122924 3 1 30) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2616]
    (.letOp (n := 2619) (.exec 0x122924 (fun s => s.RIP = 0x122924) (rolR32Effect 0x122924 3 1 30) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2616]
    (.letOp (n := 2620) (.out 0x122927 (leaR32Effect 0x122927 4 10 (.sib 0 (some 6) 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0, .gpr 6] []) (.reg (.gpr 10))) #v[2602, 2614]
    (.letOp (n := 2621) (.exec 0x122927 (fun s => s.RIP = 0x122927) (leaR32Effect 0x122927 4 10 (.sib 0 (some 6) 0 .none)) (Reg.operands [.gpr 0, .gpr 6] [])) #v[2602, 2614]
    (b_l121930_66))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_65 : List UInt8 :=
  [0x31, 0xC1, 0x8B, 0x54, 0x24, 0x34, 0x01, 0xCA, 0x44, 0x89, 0xE0, 0xC1, 0xC0, 0x1A, 0x44, 0x89,
    0xE1, 0xC1, 0xC1, 0x15, 0x31, 0xC1, 0x44, 0x89, 0xE0, 0xC1, 0xC0, 0x07, 0x31, 0xC8, 0x44, 0x89,
    0xF9, 0x44, 0x31, 0xC9, 0x44, 0x21, 0xE1, 0x44, 0x31, 0xC9, 0x01, 0xD6, 0x01, 0xCE, 0x44, 0x89,
    0xC1, 0xC1, 0xC1, 0x1E, 0x44, 0x8D, 0x14, 0x30] ++ bytes_l121930_66

theorem code_l121930_65 : ∀ x ∈ codeRange 0x1228f3 bytes_l121930_65, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x228f3 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_66

def b_l121930_64 : Block Op Label signature Reg.count 2544 :=
  .letOp (n := 2544) (.out 0x1228b9 (addR32R32Effect 0x1228b9 3 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[2066, 2512]
    (.letOp (n := 2545) (.exec 0x1228b9 (fun s => s.RIP = 0x1228b9) (addR32R32Effect 0x1228b9 3 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[2066, 2512]
    (.letOp (n := 2546) (.out 0x1228bc (addR32R32Effect 0x1228bc 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[2542, 2512]
    (.letOp (n := 2547) (.exec 0x1228bc (fun s => s.RIP = 0x1228bc) (addR32R32Effect 0x1228bc 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[2542, 2512]
    (.letOp (n := 2548) (.out 0x1228bf (movR32R32Effect 0x1228bf 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[2380]
    (.letOp (n := 2549) (.exec 0x1228bf (fun s => s.RIP = 0x1228bf) (movR32R32Effect 0x1228bf 2 1 5) (Reg.operands [.gpr 5] [])) #v[2380]
    (.letOp (n := 2550) (.out 0x1228c1 (rolR32Effect 0x1228c1 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2548]
    (.letOp (n := 2551) (.exec 0x1228c1 (fun s => s.RIP = 0x1228c1) (rolR32Effect 0x1228c1 3 1 15) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2548]
    (.letOp (n := 2552) (.out 0x1228c4 (movR32R32Effect 0x1228c4 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[2380]
    (.letOp (n := 2553) (.exec 0x1228c4 (fun s => s.RIP = 0x1228c4) (movR32R32Effect 0x1228c4 2 0 5) (Reg.operands [.gpr 5] [])) #v[2380]
    (.letOp (n := 2554) (.out 0x1228c6 (rolR32Effect 0x1228c6 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2552]
    (.letOp (n := 2555) (.exec 0x1228c6 (fun s => s.RIP = 0x1228c6) (rolR32Effect 0x1228c6 3 0 13) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2552]
    (.letOp (n := 2556) (.out 0x1228c9 (xorR32R32Effect 0x1228c9 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2554, 2550]
    (.letOp (n := 2557) (.exec 0x1228c9 (fun s => s.RIP = 0x1228c9) (xorR32R32Effect 0x1228c9 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2554, 2550]
    (.letOp (n := 2558) (.out 0x1228cb (movR32R32Effect 0x1228cb 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[2488]
    (.letOp (n := 2559) (.exec 0x1228cb (fun s => s.RIP = 0x1228cb) (movR32R32Effect 0x1228cb 3 1 14) (Reg.operands [.gpr 14] [])) #v[2488]
    (.letOp (n := 2560) (.out 0x1228ce (rolR32Effect 0x1228ce 3 1 25) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2558]
    (.letOp (n := 2561) (.exec 0x1228ce (fun s => s.RIP = 0x1228ce) (rolR32Effect 0x1228ce 3 1 25) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2558]
    (.letOp (n := 2562) (.out 0x1228d1 (movR32R32Effect 0x1228d1 3 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[2488]
    (.letOp (n := 2563) (.exec 0x1228d1 (fun s => s.RIP = 0x1228d1) (movR32R32Effect 0x1228d1 3 10 14) (Reg.operands [.gpr 14] [])) #v[2488]
    (.letOp (n := 2564) (.out 0x1228d4 (rolR32Effect 0x1228d4 4 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2562]
    (.letOp (n := 2565) (.exec 0x1228d4 (fun s => s.RIP = 0x1228d4) (rolR32Effect 0x1228d4 4 10 14) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2562]
    (.letOp (n := 2566) (.out 0x1228d8 (xorR32R32Effect 0x1228d8 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[2564, 2560]
    (.letOp (n := 2567) (.exec 0x1228d8 (fun s => s.RIP = 0x1228d8) (xorR32R32Effect 0x1228d8 3 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[2564, 2560]
    (.letOp (n := 2568) (.out 0x1228db (movR32R32Effect 0x1228db 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[2488]
    (.letOp (n := 2569) (.exec 0x1228db (fun s => s.RIP = 0x1228db) (movR32R32Effect 0x1228db 3 1 14) (Reg.operands [.gpr 14] [])) #v[2488]
    (.letOp (n := 2570) (.out 0x1228de (shrR32Effect 0x1228de 3 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2568]
    (.letOp (n := 2571) (.exec 0x1228de (fun s => s.RIP = 0x1228de) (shrR32Effect 0x1228de 3 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2568]
    (.letOp (n := 2572) (.out 0x1228e1 (xorR32R32Effect 0x1228e1 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[2570, 2566]
    (.letOp (n := 2573) (.exec 0x1228e1 (fun s => s.RIP = 0x1228e1) (xorR32R32Effect 0x1228e1 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[2570, 2566]
    (.letOp (n := 2574) (.exec 0x1228e4 (StorePre 0x1228e4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1228e4 + BitVec.ofNat 64 4)) 4) (addMREffect 0x1228e4 4 32 5 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[2380, 4]
    (.letOp (n := 2575) (.out 0x1228e8 (addR32R32Effect 0x1228e8 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[2572, 2380]
    (.letOp (n := 2576) (.exec 0x1228e8 (fun s => s.RIP = 0x1228e8) (addR32R32Effect 0x1228e8 2 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[2572, 2380]
    (.letOp (n := 2577) (.exec 0x1228ea (StorePre 0x1228ea 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1228ea + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1228ea 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2575, 4]
    (.letOp (n := 2578) (.out 0x1228ee (movR32R32Effect 0x1228ee 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[2380]
    (.letOp (n := 2579) (.exec 0x1228ee (fun s => s.RIP = 0x1228ee) (movR32R32Effect 0x1228ee 2 1 5) (Reg.operands [.gpr 5] [])) #v[2380]
    (.letOp (n := 2580) (.out 0x1228f0 (shrR32Effect 0x1228f0 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2578]
    (.letOp (n := 2581) (.exec 0x1228f0 (fun s => s.RIP = 0x1228f0) (shrR32Effect 0x1228f0 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2578]
    (b_l121930_65))))))))))))))))))))))))))))))))))))))

def bytes_l121930_64 : List UInt8 :=
  [0x41, 0x01, 0xC4, 0x41, 0x01, 0xC0, 0x89, 0xE9, 0xC1, 0xC1, 0x0F, 0x89, 0xE8, 0xC1, 0xC0, 0x0D,
    0x31, 0xC8, 0x44, 0x89, 0xF1, 0xC1, 0xC1, 0x19, 0x45, 0x89, 0xF2, 0x41, 0xC1, 0xC2, 0x0E, 0x41,
    0x31, 0xCA, 0x44, 0x89, 0xF1, 0xC1, 0xE9, 0x03, 0x44, 0x31, 0xD1, 0x01, 0x6C, 0x24, 0x24, 0x01,
    0xE9, 0x89, 0x4C, 0x24, 0x14, 0x89, 0xE9, 0xC1, 0xE9, 0x0A] ++ bytes_l121930_65

theorem code_l121930_64 : ∀ x ∈ codeRange 0x1228b9 bytes_l121930_64, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x228b9 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_65

def b_l121930_63 : Block Op Label signature Reg.count 2504 :=
  .letOp (n := 2504) (.out 0x12287c (xorR32R32Effect 0x12287c 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[2502, 2248]
    (.letOp (n := 2505) (.exec 0x12287c (fun s => s.RIP = 0x12287c) (xorR32R32Effect 0x12287c 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[2502, 2248]
    (.letOp (n := 2506) (.out 0x12287e (addR32R32Effect 0x12287e 3 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[2124, 2488]
    (.letOp (n := 2507) (.exec 0x12287e (fun s => s.RIP = 0x12287e) (addR32R32Effect 0x12287e 3 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[2124, 2488]
    (.letOp (n := 2508) (.out 0x122881 (addR32R32Effect 0x122881 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[2506, 2504]
    (.letOp (n := 2509) (.exec 0x122881 (fun s => s.RIP = 0x122881) (addR32R32Effect 0x122881 3 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2506, 2504]
    (.letOp (n := 2510) (.out 0x122884 (leaR32Effect 0x122884 4 0 (.sib 1 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 10] []) (.reg (.gpr 0))) #v[2496, 2508]
    (.letOp (n := 2511) (.exec 0x122884 (fun s => s.RIP = 0x122884) (leaR32Effect 0x122884 4 0 (.sib 1 (some 10) 0 .none)) (Reg.operands [.gpr 1, .gpr 10] [])) #v[2496, 2508]
    (.letOp (n := 2512) (.out 0x122888 (addEaxImm32Effect 0x122888 0x76f988da) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2510]
    (.letOp (n := 2513) (.exec 0x122888 (fun s => s.RIP = 0x122888) (addEaxImm32Effect 0x122888 0x76f988da) (Reg.operands [.gpr 0] [])) #v[2510]
    (.letOp (n := 2514) (.out 0x12288d (movR32R32Effect 0x12288d 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[2454]
    (.letOp (n := 2515) (.exec 0x12288d (fun s => s.RIP = 0x12288d) (movR32R32Effect 0x12288d 2 1 3) (Reg.operands [.gpr 3] [])) #v[2454]
    (.letOp (n := 2516) (.out 0x12288f (rolR32Effect 0x12288f 3 1 30) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2514]
    (.letOp (n := 2517) (.exec 0x12288f (fun s => s.RIP = 0x12288f) (rolR32Effect 0x12288f 3 1 30) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2514]
    (.letOp (n := 2518) (.out 0x122892 (movR32R32Effect 0x122892 3 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[2454]
    (.letOp (n := 2519) (.exec 0x122892 (fun s => s.RIP = 0x122892) (movR32R32Effect 0x122892 3 8 3) (Reg.operands [.gpr 3] [])) #v[2454]
    (.letOp (n := 2520) (.out 0x122895 (rolR32Effect 0x122895 4 8 19) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2518]
    (.letOp (n := 2521) (.exec 0x122895 (fun s => s.RIP = 0x122895) (rolR32Effect 0x122895 4 8 19) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2518]
    (.letOp (n := 2522) (.out 0x122899 (xorR32R32Effect 0x122899 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[2520, 2516]
    (.letOp (n := 2523) (.exec 0x122899 (fun s => s.RIP = 0x122899) (xorR32R32Effect 0x122899 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[2520, 2516]
    (.letOp (n := 2524) (.out 0x12289c (movR32R32Effect 0x12289c 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[2454]
    (.letOp (n := 2525) (.exec 0x12289c (fun s => s.RIP = 0x12289c) (movR32R32Effect 0x12289c 2 1 3) (Reg.operands [.gpr 3] [])) #v[2454]
    (.letOp (n := 2526) (.out 0x12289e (rolR32Effect 0x12289e 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2524]
    (.letOp (n := 2527) (.exec 0x12289e (fun s => s.RIP = 0x12289e) (rolR32Effect 0x12289e 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2524]
    (.letOp (n := 2528) (.out 0x1228a1 (xorR32R32Effect 0x1228a1 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[2526, 2522]
    (.letOp (n := 2529) (.exec 0x1228a1 (fun s => s.RIP = 0x1228a1) (xorR32R32Effect 0x1228a1 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[2526, 2522]
    (.letOp (n := 2530) (.out 0x1228a4 (movR32R32Effect 0x1228a4 3 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[2316]
    (.letOp (n := 2531) (.exec 0x1228a4 (fun s => s.RIP = 0x1228a4) (movR32R32Effect 0x1228a4 3 10 7) (Reg.operands [.gpr 7] [])) #v[2316]
    (.letOp (n := 2532) (.out 0x1228a7 (andR32R32Effect 0x1228a7 3 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[2530, 2194]
    (.letOp (n := 2533) (.exec 0x1228a7 (fun s => s.RIP = 0x1228a7) (andR32R32Effect 0x1228a7 3 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[2530, 2194]
    (.letOp (n := 2534) (.out 0x1228aa (movR32R32Effect 0x1228aa 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[2316]
    (.letOp (n := 2535) (.exec 0x1228aa (fun s => s.RIP = 0x1228aa) (movR32R32Effect 0x1228aa 3 8 7) (Reg.operands [.gpr 7] [])) #v[2316]
    (.letOp (n := 2536) (.out 0x1228ad (xorR32R32Effect 0x1228ad 3 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[2534, 2194]
    (.letOp (n := 2537) (.exec 0x1228ad (fun s => s.RIP = 0x1228ad) (xorR32R32Effect 0x1228ad 3 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[2534, 2194]
    (.letOp (n := 2538) (.out 0x1228b0 (andR32R32Effect 0x1228b0 3 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[2536, 2454]
    (.letOp (n := 2539) (.exec 0x1228b0 (fun s => s.RIP = 0x1228b0) (andR32R32Effect 0x1228b0 3 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[2536, 2454]
    (.letOp (n := 2540) (.out 0x1228b3 (xorR32R32Effect 0x1228b3 3 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[2538, 2532]
    (.letOp (n := 2541) (.exec 0x1228b3 (fun s => s.RIP = 0x1228b3) (xorR32R32Effect 0x1228b3 3 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[2538, 2532]
    (.letOp (n := 2542) (.out 0x1228b6 (addR32R32Effect 0x1228b6 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[2540, 2528]
    (.letOp (n := 2543) (.exec 0x1228b6 (fun s => s.RIP = 0x1228b6) (addR32R32Effect 0x1228b6 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[2540, 2528]
    (b_l121930_64))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_63 : List UInt8 :=
  [0x31, 0xF0, 0x45, 0x01, 0xF2, 0x41, 0x01, 0xC2, 0x42, 0x8D, 0x04, 0x11, 0x05, 0xDA, 0x88, 0xF9,
    0x76, 0x89, 0xD9, 0xC1, 0xC1, 0x1E, 0x41, 0x89, 0xD8, 0x41, 0xC1, 0xC0, 0x13, 0x41, 0x31, 0xC8,
    0x89, 0xD9, 0xC1, 0xC1, 0x0A, 0x44, 0x31, 0xC1, 0x41, 0x89, 0xFA, 0x45, 0x21, 0xEA, 0x41, 0x89,
    0xF8, 0x45, 0x31, 0xE8, 0x41, 0x21, 0xD8, 0x45, 0x31, 0xD0, 0x41, 0x01, 0xC8] ++ bytes_l121930_64

theorem code_l121930_63 : ∀ x ∈ codeRange 0x12287c bytes_l121930_63, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2287c 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_64

def b_l121930_62 : Block Op Label signature Reg.count 2466 :=
  .letOp (n := 2466) (.out 0x12283c (shrR32Effect 0x12283c 4 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2464]
    (.letOp (n := 2467) (.exec 0x12283c (fun s => s.RIP = 0x12283c) (shrR32Effect 0x12283c 4 8 3) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2464]
    (.letOp (n := 2468) (.out 0x122840 (xorR32R32Effect 0x122840 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[2466, 2462]
    (.letOp (n := 2469) (.exec 0x122840 (fun s => s.RIP = 0x122840) (xorR32R32Effect 0x122840 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[2466, 2462]
    (.letOp (n := 2470) (.exec 0x122843 (StorePre 0x122843 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x122843 + BitVec.ofNat 64 4)) 4) (addMREffect 0x122843 4 32 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2254, 4]
    (.letOp (n := 2471) (.out 0x122847 (addR32R32Effect 0x122847 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[2468, 2254]
    (.letOp (n := 2472) (.exec 0x122847 (fun s => s.RIP = 0x122847) (addR32R32Effect 0x122847 3 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[2468, 2254]
    (.letOp (n := 2473) (.exec 0x12284a (StorePre 0x12284a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x12284a + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x12284a 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[2471, 4]
    (.letOp (n := 2474) (.out 0x12284f (shrR32Effect 0x12284f 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2254]
    (.letOp (n := 2475) (.exec 0x12284f (fun s => s.RIP = 0x12284f) (shrR32Effect 0x12284f 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2254]
    (.letOp (n := 2476) (.out 0x122852 (movR32R32Effect 0x122852 3 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[2448]
    (.letOp (n := 2477) (.exec 0x122852 (fun s => s.RIP = 0x122852) (movR32R32Effect 0x122852 3 8 15) (Reg.operands [.gpr 15] [])) #v[2448]
    (.letOp (n := 2478) (.out 0x122855 (rolR32Effect 0x122855 4 8 26) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2476]
    (.letOp (n := 2479) (.exec 0x122855 (fun s => s.RIP = 0x122855) (rolR32Effect 0x122855 4 8 26) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2476]
    (.letOp (n := 2480) (.out 0x122859 (xorR32R32Effect 0x122859 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2474, 2460]
    (.letOp (n := 2481) (.exec 0x122859 (fun s => s.RIP = 0x122859) (xorR32R32Effect 0x122859 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2474, 2460]
    (.letOp (n := 2482) (.out 0x12285b (movR32R32Effect 0x12285b 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[2448]
    (.letOp (n := 2483) (.exec 0x12285b (fun s => s.RIP = 0x12285b) (movR32R32Effect 0x12285b 3 0 15) (Reg.operands [.gpr 15] [])) #v[2448]
    (.letOp (n := 2484) (.out 0x12285e (rolR32Effect 0x12285e 3 0 21) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2482]
    (.letOp (n := 2485) (.exec 0x12285e (fun s => s.RIP = 0x12285e) (rolR32Effect 0x12285e 3 0 21) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2482]
    (.letOp (n := 2486) (.out 0x122861 (movR32M32Effect 0x122861 14 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 2487) (.exec 0x122861 (LoadPre 0x122861 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x122861 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x122861 14 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2488) (.out 0x122866 (addR32R32Effect 0x122866 3 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[2486, 2480]
    (.letOp (n := 2489) (.exec 0x122866 (fun s => s.RIP = 0x122866) (addR32R32Effect 0x122866 3 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[2486, 2480]
    (.letOp (n := 2490) (.out 0x122869 (movR32R32Effect 0x122869 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[2448]
    (.letOp (n := 2491) (.exec 0x122869 (fun s => s.RIP = 0x122869) (movR32R32Effect 0x122869 3 1 15) (Reg.operands [.gpr 15] [])) #v[2448]
    (.letOp (n := 2492) (.out 0x12286c (rolR32Effect 0x12286c 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2490]
    (.letOp (n := 2493) (.exec 0x12286c (fun s => s.RIP = 0x12286c) (rolR32Effect 0x12286c 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2490]
    (.letOp (n := 2494) (.out 0x12286f (xorR32R32Effect 0x12286f 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[2484, 2478]
    (.letOp (n := 2495) (.exec 0x12286f (fun s => s.RIP = 0x12286f) (xorR32R32Effect 0x12286f 3 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[2484, 2478]
    (.letOp (n := 2496) (.out 0x122872 (xorR32R32Effect 0x122872 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2492, 2494]
    (.letOp (n := 2497) (.exec 0x122872 (fun s => s.RIP = 0x122872) (xorR32R32Effect 0x122872 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2492, 2494]
    (.letOp (n := 2498) (.out 0x122874 (movR32R32Effect 0x122874 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2314]
    (.letOp (n := 2499) (.exec 0x122874 (fun s => s.RIP = 0x122874) (movR32R32Effect 0x122874 3 0 9) (Reg.operands [.gpr 9] [])) #v[2314]
    (.letOp (n := 2500) (.out 0x122877 (xorR32R32Effect 0x122877 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[2498, 2248]
    (.letOp (n := 2501) (.exec 0x122877 (fun s => s.RIP = 0x122877) (xorR32R32Effect 0x122877 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[2498, 2248]
    (.letOp (n := 2502) (.out 0x122879 (andR32R32Effect 0x122879 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[2500, 2448]
    (.letOp (n := 2503) (.exec 0x122879 (fun s => s.RIP = 0x122879) (andR32R32Effect 0x122879 3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[2500, 2448]
    (b_l121930_63))))))))))))))))))))))))))))))))))))))

def bytes_l121930_62 : List UInt8 :=
  [0x41, 0xC1, 0xE8, 0x03, 0x41, 0x31, 0xC8, 0x01, 0x54, 0x24, 0x10, 0x41, 0x01, 0xD0, 0x44, 0x89,
    0x44, 0x24, 0x68, 0xC1, 0xEA, 0x0A, 0x45, 0x89, 0xF8, 0x41, 0xC1, 0xC0, 0x1A, 0x31, 0xC2, 0x44,
    0x89, 0xF8, 0xC1, 0xC0, 0x15, 0x44, 0x8B, 0x74, 0x24, 0x60, 0x41, 0x01, 0xD6, 0x44, 0x89, 0xF9,
    0xC1, 0xC1, 0x07, 0x44, 0x31, 0xC0, 0x31, 0xC1, 0x44, 0x89, 0xC8, 0x31, 0xF0, 0x44, 0x21, 0xF8] ++ bytes_l121930_63

theorem code_l121930_62 : ∀ x ∈ codeRange 0x12283c bytes_l121930_62, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2283c 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_63

def b_l121930_61 : Block Op Label signature Reg.count 2426 :=
  .letOp (n := 2426) (.out 0x122803 (movR32R32Effect 0x122803 3 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 13] []) (.reg (.gpr 8))) #v[2194]
    (.letOp (n := 2427) (.exec 0x122803 (fun s => s.RIP = 0x122803) (movR32R32Effect 0x122803 3 8 13) (Reg.operands [.gpr 13] [])) #v[2194]
    (.letOp (n := 2428) (.out 0x122806 (andR32R32Effect 0x122806 3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[2426, 2066]
    (.letOp (n := 2429) (.exec 0x122806 (fun s => s.RIP = 0x122806) (andR32R32Effect 0x122806 3 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[2426, 2066]
    (.letOp (n := 2430) (.out 0x122809 (movR32R32Effect 0x122809 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 13] []) (.reg (.gpr 3))) #v[2194]
    (.letOp (n := 2431) (.exec 0x122809 (fun s => s.RIP = 0x122809) (movR32R32Effect 0x122809 3 3 13) (Reg.operands [.gpr 13] [])) #v[2194]
    (.letOp (n := 2432) (.out 0x12280c (xorR32R32Effect 0x12280c 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[2430, 2066]
    (.letOp (n := 2433) (.exec 0x12280c (fun s => s.RIP = 0x12280c) (xorR32R32Effect 0x12280c 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[2430, 2066]
    (.letOp (n := 2434) (.out 0x12280f (andR32R32Effect 0x12280f 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[2432, 2316]
    (.letOp (n := 2435) (.exec 0x12280f (fun s => s.RIP = 0x12280f) (andR32R32Effect 0x12280f 2 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[2432, 2316]
    (.letOp (n := 2436) (.out 0x122811 (xorR32R32Effect 0x122811 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[2434, 2428]
    (.letOp (n := 2437) (.exec 0x122811 (fun s => s.RIP = 0x122811) (xorR32R32Effect 0x122811 3 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[2434, 2428]
    (.letOp (n := 2438) (.out 0x122814 (movR32R32Effect 0x122814 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2254]
    (.letOp (n := 2439) (.exec 0x122814 (fun s => s.RIP = 0x122814) (movR32R32Effect 0x122814 3 8 2) (Reg.operands [.gpr 2] [])) #v[2254]
    (.letOp (n := 2440) (.out 0x122817 (rolR32Effect 0x122817 4 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2438]
    (.letOp (n := 2441) (.exec 0x122817 (fun s => s.RIP = 0x122817) (rolR32Effect 0x122817 4 8 15) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2438]
    (.letOp (n := 2442) (.out 0x12281b (addR32R32Effect 0x12281b 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[2436, 2424]
    (.letOp (n := 2443) (.exec 0x12281b (fun s => s.RIP = 0x12281b) (addR32R32Effect 0x12281b 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[2436, 2424]
    (.letOp (n := 2444) (.out 0x12281d (movR32R32Effect 0x12281d 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2254]
    (.letOp (n := 2445) (.exec 0x12281d (fun s => s.RIP = 0x12281d) (movR32R32Effect 0x12281d 2 0 2) (Reg.operands [.gpr 2] [])) #v[2254]
    (.letOp (n := 2446) (.out 0x12281f (rolR32Effect 0x12281f 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2444]
    (.letOp (n := 2447) (.exec 0x12281f (fun s => s.RIP = 0x12281f) (rolR32Effect 0x12281f 3 0 13) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2444]
    (.letOp (n := 2448) (.out 0x122822 (addR32R32Effect 0x122822 3 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[2024, 2408]
    (.letOp (n := 2449) (.exec 0x122822 (fun s => s.RIP = 0x122822) (addR32R32Effect 0x122822 3 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[2024, 2408]
    (.letOp (n := 2450) (.out 0x122825 (movR32R32Effect 0x122825 3 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 5] []) (.reg (.gpr 11))) #v[2380]
    (.letOp (n := 2451) (.exec 0x122825 (fun s => s.RIP = 0x122825) (movR32R32Effect 0x122825 3 11 5) (Reg.operands [.gpr 5] [])) #v[2380]
    (.letOp (n := 2452) (.out 0x122828 (rolR32Effect 0x122828 4 11 25) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[2450]
    (.letOp (n := 2453) (.exec 0x122828 (fun s => s.RIP = 0x122828) (rolR32Effect 0x122828 4 11 25) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2450]
    (.letOp (n := 2454) (.out 0x12282c (addR32R32Effect 0x12282c 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[2442, 2408]
    (.letOp (n := 2455) (.exec 0x12282c (fun s => s.RIP = 0x12282c) (addR32R32Effect 0x12282c 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[2442, 2408]
    (.letOp (n := 2456) (.out 0x12282e (movR32R32Effect 0x12282e 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[2380]
    (.letOp (n := 2457) (.exec 0x12282e (fun s => s.RIP = 0x12282e) (movR32R32Effect 0x12282e 2 1 5) (Reg.operands [.gpr 5] [])) #v[2380]
    (.letOp (n := 2458) (.out 0x122830 (rolR32Effect 0x122830 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2456]
    (.letOp (n := 2459) (.exec 0x122830 (fun s => s.RIP = 0x122830) (rolR32Effect 0x122830 3 1 14) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2456]
    (.letOp (n := 2460) (.out 0x122833 (xorR32R32Effect 0x122833 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[2446, 2440]
    (.letOp (n := 2461) (.exec 0x122833 (fun s => s.RIP = 0x122833) (xorR32R32Effect 0x122833 3 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[2446, 2440]
    (.letOp (n := 2462) (.out 0x122836 (xorR32R32Effect 0x122836 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[2458, 2452]
    (.letOp (n := 2463) (.exec 0x122836 (fun s => s.RIP = 0x122836) (xorR32R32Effect 0x122836 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[2458, 2452]
    (.letOp (n := 2464) (.out 0x122839 (movR32R32Effect 0x122839 3 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[2380]
    (.letOp (n := 2465) (.exec 0x122839 (fun s => s.RIP = 0x122839) (movR32R32Effect 0x122839 3 8 5) (Reg.operands [.gpr 5] [])) #v[2380]
    (b_l121930_62))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_61 : List UInt8 :=
  [0x45, 0x89, 0xE8, 0x45, 0x21, 0xE0, 0x44, 0x89, 0xEB, 0x44, 0x31, 0xE3, 0x21, 0xFB, 0x44, 0x31,
    0xC3, 0x41, 0x89, 0xD0, 0x41, 0xC1, 0xC0, 0x0F, 0x01, 0xC3, 0x89, 0xD0, 0xC1, 0xC0, 0x0D, 0x41,
    0x01, 0xCF, 0x41, 0x89, 0xEB, 0x41, 0xC1, 0xC3, 0x19, 0x01, 0xCB, 0x89, 0xE9, 0xC1, 0xC1, 0x0E,
    0x44, 0x31, 0xC0, 0x44, 0x31, 0xD9, 0x41, 0x89, 0xE8] ++ bytes_l121930_62

theorem code_l121930_61 : ∀ x ∈ codeRange 0x122803 bytes_l121930_61, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22803 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_62

def b_l121930_60 : Block Op Label signature Reg.count 2386 :=
  .letOp (n := 2386) (.out 0x1227c7 (xorR32R32Effect 0x1227c7 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2384, 2378]
    (.letOp (n := 2387) (.exec 0x1227c7 (fun s => s.RIP = 0x1227c7) (xorR32R32Effect 0x1227c7 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2384, 2378]
    (.letOp (n := 2388) (.out 0x1227c9 (movR32R32Effect 0x1227c9 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2314]
    (.letOp (n := 2389) (.exec 0x1227c9 (fun s => s.RIP = 0x1227c9) (movR32R32Effect 0x1227c9 3 0 9) (Reg.operands [.gpr 9] [])) #v[2314]
    (.letOp (n := 2390) (.out 0x1227cc (rolR32Effect 0x1227cc 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2388]
    (.letOp (n := 2391) (.exec 0x1227cc (fun s => s.RIP = 0x1227cc) (rolR32Effect 0x1227cc 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2388]
    (.letOp (n := 2392) (.out 0x1227cf (xorR32R32Effect 0x1227cf 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2390, 2386]
    (.letOp (n := 2393) (.exec 0x1227cf (fun s => s.RIP = 0x1227cf) (xorR32R32Effect 0x1227cf 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2390, 2386]
    (.letOp (n := 2394) (.out 0x1227d1 (movR32R32Effect 0x1227d1 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[2248]
    (.letOp (n := 2395) (.exec 0x1227d1 (fun s => s.RIP = 0x1227d1) (movR32R32Effect 0x1227d1 2 1 6) (Reg.operands [.gpr 6] [])) #v[2248]
    (.letOp (n := 2396) (.out 0x1227d3 (xorR32R32Effect 0x1227d3 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[2394, 2124]
    (.letOp (n := 2397) (.exec 0x1227d3 (fun s => s.RIP = 0x1227d3) (xorR32R32Effect 0x1227d3 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[2394, 2124]
    (.letOp (n := 2398) (.out 0x1227d6 (andR32R32Effect 0x1227d6 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[2396, 2314]
    (.letOp (n := 2399) (.exec 0x1227d6 (fun s => s.RIP = 0x1227d6) (andR32R32Effect 0x1227d6 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[2396, 2314]
    (.letOp (n := 2400) (.out 0x1227d9 (xorR32R32Effect 0x1227d9 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[2398, 2124]
    (.letOp (n := 2401) (.exec 0x1227d9 (fun s => s.RIP = 0x1227d9) (xorR32R32Effect 0x1227d9 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[2398, 2124]
    (.letOp (n := 2402) (.out 0x1227dc (addR32R32Effect 0x1227dc 3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[1932, 2380]
    (.letOp (n := 2403) (.exec 0x1227dc (fun s => s.RIP = 0x1227dc) (addR32R32Effect 0x1227dc 3 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[1932, 2380]
    (.letOp (n := 2404) (.out 0x1227df (addR32R32Effect 0x1227df 3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[2402, 2400]
    (.letOp (n := 2405) (.exec 0x1227df (fun s => s.RIP = 0x1227df) (addR32R32Effect 0x1227df 3 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[2402, 2400]
    (.letOp (n := 2406) (.out 0x1227e2 (leaR32Effect 0x1227e2 4 1 (.sib 0 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0, .gpr 14] []) (.reg (.gpr 1))) #v[2392, 2404]
    (.letOp (n := 2407) (.exec 0x1227e2 (fun s => s.RIP = 0x1227e2) (leaR32Effect 0x1227e2 4 1 (.sib 0 (some 14) 0 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[2392, 2404]
    (.letOp (n := 2408) (.out 0x1227e6 (addR32Imm32Effect 0x1227e6 6 1 0x5cb0a9dc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[2406]
    (.letOp (n := 2409) (.exec 0x1227e6 (fun s => s.RIP = 0x1227e6) (addR32Imm32Effect 0x1227e6 6 1 0x5cb0a9dc) (Reg.operands [.gpr 1] [])) #v[2406]
    (.letOp (n := 2410) (.out 0x1227ec (movR32R32Effect 0x1227ec 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[2316]
    (.letOp (n := 2411) (.exec 0x1227ec (fun s => s.RIP = 0x1227ec) (movR32R32Effect 0x1227ec 2 0 7) (Reg.operands [.gpr 7] [])) #v[2316]
    (.letOp (n := 2412) (.out 0x1227ee (rolR32Effect 0x1227ee 3 0 30) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2410]
    (.letOp (n := 2413) (.exec 0x1227ee (fun s => s.RIP = 0x1227ee) (rolR32Effect 0x1227ee 3 0 30) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2410]
    (.letOp (n := 2414) (.out 0x1227f1 (movR32R32Effect 0x1227f1 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[2316]
    (.letOp (n := 2415) (.exec 0x1227f1 (fun s => s.RIP = 0x1227f1) (movR32R32Effect 0x1227f1 3 8 7) (Reg.operands [.gpr 7] [])) #v[2316]
    (.letOp (n := 2416) (.out 0x1227f4 (rolR32Effect 0x1227f4 4 8 19) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2414]
    (.letOp (n := 2417) (.exec 0x1227f4 (fun s => s.RIP = 0x1227f4) (rolR32Effect 0x1227f4 4 8 19) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2414]
    (.letOp (n := 2418) (.out 0x1227f8 (xorR32R32Effect 0x1227f8 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[2416, 2412]
    (.letOp (n := 2419) (.exec 0x1227f8 (fun s => s.RIP = 0x1227f8) (xorR32R32Effect 0x1227f8 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[2416, 2412]
    (.letOp (n := 2420) (.out 0x1227fb (movR32R32Effect 0x1227fb 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[2316]
    (.letOp (n := 2421) (.exec 0x1227fb (fun s => s.RIP = 0x1227fb) (movR32R32Effect 0x1227fb 2 0 7) (Reg.operands [.gpr 7] [])) #v[2316]
    (.letOp (n := 2422) (.out 0x1227fd (rolR32Effect 0x1227fd 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2420]
    (.letOp (n := 2423) (.exec 0x1227fd (fun s => s.RIP = 0x1227fd) (rolR32Effect 0x1227fd 3 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2420]
    (.letOp (n := 2424) (.out 0x122800 (xorR32R32Effect 0x122800 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[2422, 2418]
    (.letOp (n := 2425) (.exec 0x122800 (fun s => s.RIP = 0x122800) (xorR32R32Effect 0x122800 3 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[2422, 2418]
    (b_l121930_61))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_60 : List UInt8 :=
  [0x31, 0xC1, 0x44, 0x89, 0xC8, 0xC1, 0xC0, 0x07, 0x31, 0xC8, 0x89, 0xF1, 0x44, 0x31, 0xD1, 0x44,
    0x21, 0xC9, 0x44, 0x31, 0xD1, 0x41, 0x01, 0xEE, 0x41, 0x01, 0xCE, 0x42, 0x8D, 0x0C, 0x30, 0x81,
    0xC1, 0xDC, 0xA9, 0xB0, 0x5C, 0x89, 0xF8, 0xC1, 0xC0, 0x1E, 0x41, 0x89, 0xF8, 0x41, 0xC1, 0xC0,
    0x13, 0x41, 0x31, 0xC0, 0x89, 0xF8, 0xC1, 0xC0, 0x0A, 0x44, 0x31, 0xC0] ++ bytes_l121930_61

theorem code_l121930_60 : ∀ x ∈ codeRange 0x1227c7 bytes_l121930_60, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x227c7 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_61

def b_l121930_59 : Block Op Label signature Reg.count 2348 :=
  .letOp (n := 2348) (.out 0x122786 (rolR32Effect 0x122786 4 8 25) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2346]
    (.letOp (n := 2349) (.exec 0x122786 (fun s => s.RIP = 0x122786) (rolR32Effect 0x122786 4 8 25) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2346]
    (.letOp (n := 2350) (.out 0x12278a (movR32R32Effect 0x12278a 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2254]
    (.letOp (n := 2351) (.exec 0x12278a (fun s => s.RIP = 0x12278a) (movR32R32Effect 0x12278a 2 3 2) (Reg.operands [.gpr 2] [])) #v[2254]
    (.letOp (n := 2352) (.out 0x12278c (rolR32Effect 0x12278c 3 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[2350]
    (.letOp (n := 2353) (.exec 0x12278c (fun s => s.RIP = 0x12278c) (rolR32Effect 0x12278c 3 3 14) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2350]
    (.letOp (n := 2354) (.out 0x12278f (xorR32R32Effect 0x12278f 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[2352, 2348]
    (.letOp (n := 2355) (.exec 0x12278f (fun s => s.RIP = 0x12278f) (xorR32R32Effect 0x12278f 3 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[2352, 2348]
    (.letOp (n := 2356) (.out 0x122792 (movR32R32Effect 0x122792 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2254]
    (.letOp (n := 2357) (.exec 0x122792 (fun s => s.RIP = 0x122792) (movR32R32Effect 0x122792 3 8 2) (Reg.operands [.gpr 2] [])) #v[2254]
    (.letOp (n := 2358) (.out 0x122795 (shrR32Effect 0x122795 4 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2356]
    (.letOp (n := 2359) (.exec 0x122795 (fun s => s.RIP = 0x122795) (shrR32Effect 0x122795 4 8 3) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2356]
    (.letOp (n := 2360) (.out 0x122799 (xorR32R32Effect 0x122799 3 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[2358, 2354]
    (.letOp (n := 2361) (.exec 0x122799 (fun s => s.RIP = 0x122799) (xorR32R32Effect 0x122799 3 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[2358, 2354]
    (.letOp (n := 2362) (.exec 0x12279c (StorePre 0x12279c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x12279c + BitVec.ofNat 64 4)) 4) (addMREffect 0x12279c 4 32 5 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[2122, 4]
    (.letOp (n := 2363) (.out 0x1227a0 (addR32R32Effect 0x1227a0 3 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[2360, 2122]
    (.letOp (n := 2364) (.exec 0x1227a0 (fun s => s.RIP = 0x1227a0) (addR32R32Effect 0x1227a0 3 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[2360, 2122]
    (.letOp (n := 2365) (.exec 0x1227a3 (StorePre 0x1227a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1227a3 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1227a3 8 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[2363, 4]
    (.letOp (n := 2366) (.out 0x1227a8 (movR32R32Effect 0x1227a8 3 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[2122]
    (.letOp (n := 2367) (.exec 0x1227a8 (fun s => s.RIP = 0x1227a8) (movR32R32Effect 0x1227a8 3 8 5) (Reg.operands [.gpr 5] [])) #v[2122]
    (.letOp (n := 2368) (.out 0x1227ab (shrR32Effect 0x1227ab 4 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2366]
    (.letOp (n := 2369) (.exec 0x1227ab (fun s => s.RIP = 0x1227ab) (shrR32Effect 0x1227ab 4 8 10) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2366]
    (.letOp (n := 2370) (.out 0x1227af (xorR32R32Effect 0x1227af 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[2368, 2344]
    (.letOp (n := 2371) (.exec 0x1227af (fun s => s.RIP = 0x1227af) (xorR32R32Effect 0x1227af 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[2368, 2344]
    (.letOp (n := 2372) (.out 0x1227b2 (movR32M32LowEffect 0x1227b2 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 2373) (.exec 0x1227b2 (LoadPre 0x1227b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1227b2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1227b2 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2374) (.out 0x1227b6 (addR32R32Effect 0x1227b6 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[2372, 2338]
    (.letOp (n := 2375) (.exec 0x1227b6 (fun s => s.RIP = 0x1227b6) (addR32R32Effect 0x1227b6 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[2372, 2338]
    (.letOp (n := 2376) (.out 0x1227b8 (movR32R32Effect 0x1227b8 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[2314]
    (.letOp (n := 2377) (.exec 0x1227b8 (fun s => s.RIP = 0x1227b8) (movR32R32Effect 0x1227b8 3 0 9) (Reg.operands [.gpr 9] [])) #v[2314]
    (.letOp (n := 2378) (.out 0x1227bb (rolR32Effect 0x1227bb 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2376]
    (.letOp (n := 2379) (.exec 0x1227bb (fun s => s.RIP = 0x1227bb) (rolR32Effect 0x1227bb 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2376]
    (.letOp (n := 2380) (.out 0x1227be (addR32R32Effect 0x1227be 3 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[2374, 2370]
    (.letOp (n := 2381) (.exec 0x1227be (fun s => s.RIP = 0x1227be) (addR32R32Effect 0x1227be 3 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[2374, 2370]
    (.letOp (n := 2382) (.out 0x1227c1 (movR32R32Effect 0x1227c1 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[2314]
    (.letOp (n := 2383) (.exec 0x1227c1 (fun s => s.RIP = 0x1227c1) (movR32R32Effect 0x1227c1 3 1 9) (Reg.operands [.gpr 9] [])) #v[2314]
    (.letOp (n := 2384) (.out 0x1227c4 (rolR32Effect 0x1227c4 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2382]
    (.letOp (n := 2385) (.exec 0x1227c4 (fun s => s.RIP = 0x1227c4) (rolR32Effect 0x1227c4 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2382]
    (b_l121930_60))))))))))))))))))))))))))))))))))))))

def bytes_l121930_59 : List UInt8 :=
  [0x41, 0xC1, 0xC0, 0x19, 0x89, 0xD3, 0xC1, 0xC3, 0x0E, 0x44, 0x31, 0xC3, 0x41, 0x89, 0xD0, 0x41,
    0xC1, 0xE8, 0x03, 0x41, 0x31, 0xD8, 0x01, 0x6C, 0x24, 0x64, 0x41, 0x01, 0xE8, 0x44, 0x89, 0x44,
    0x24, 0x78, 0x41, 0x89, 0xE8, 0x41, 0xC1, 0xE8, 0x0A, 0x41, 0x31, 0xC8, 0x8B, 0x6C, 0x24, 0x28,
    0x01, 0xC5, 0x44, 0x89, 0xC8, 0xC1, 0xC0, 0x1A, 0x44, 0x01, 0xC5, 0x44, 0x89, 0xC9, 0xC1, 0xC1,
    0x15] ++ bytes_l121930_60

theorem code_l121930_59 : ∀ x ∈ codeRange 0x122786 bytes_l121930_59, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22786 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_60

def b_l121930_58 : Block Op Label signature Reg.count 2308 :=
  .letOp (n := 2308) (.out 0x12274c (andR32R32Effect 0x12274c 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[2306, 2194]
    (.letOp (n := 2309) (.exec 0x12274c (fun s => s.RIP = 0x12274c) (andR32R32Effect 0x12274c 3 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[2306, 2194]
    (.letOp (n := 2310) (.out 0x12274f (xorR32R32Effect 0x12274f 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[2308, 2302]
    (.letOp (n := 2311) (.exec 0x12274f (fun s => s.RIP = 0x12274f) (xorR32R32Effect 0x12274f 3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[2308, 2302]
    (.letOp (n := 2312) (.out 0x122752 (addR32R32Effect 0x122752 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[2310, 2298]
    (.letOp (n := 2313) (.exec 0x122752 (fun s => s.RIP = 0x122752) (addR32R32Effect 0x122752 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[2310, 2298]
    (.letOp (n := 2314) (.out 0x122754 (addR32R32Effect 0x122754 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[1894, 2282]
    (.letOp (n := 2315) (.exec 0x122754 (fun s => s.RIP = 0x122754) (addR32R32Effect 0x122754 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1894, 2282]
    (.letOp (n := 2316) (.out 0x122757 (addR32R32Effect 0x122757 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[2312, 2282]
    (.letOp (n := 2317) (.exec 0x122757 (fun s => s.RIP = 0x122757) (addR32R32Effect 0x122757 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[2312, 2282]
    (.letOp (n := 2318) (.out 0x122759 (movR32M32Effect 0x122759 8 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 2319) (.exec 0x122759 (LoadPre 0x122759 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x122759 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x122759 8 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2320) (.out 0x12275e (movR32R32Effect 0x12275e 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2318]
    (.letOp (n := 2321) (.exec 0x12275e (fun s => s.RIP = 0x12275e) (movR32R32Effect 0x12275e 3 0 8) (Reg.operands [.gpr 8] [])) #v[2318]
    (.letOp (n := 2322) (.out 0x122761 (rolR32Effect 0x122761 3 0 25) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2320]
    (.letOp (n := 2323) (.exec 0x122761 (fun s => s.RIP = 0x122761) (rolR32Effect 0x122761 3 0 25) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2320]
    (.letOp (n := 2324) (.out 0x122764 (movR32R32Effect 0x122764 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[2318]
    (.letOp (n := 2325) (.exec 0x122764 (fun s => s.RIP = 0x122764) (movR32R32Effect 0x122764 3 1 8) (Reg.operands [.gpr 8] [])) #v[2318]
    (.letOp (n := 2326) (.out 0x122767 (rolR32Effect 0x122767 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2324]
    (.letOp (n := 2327) (.exec 0x122767 (fun s => s.RIP = 0x122767) (rolR32Effect 0x122767 3 1 14) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2324]
    (.letOp (n := 2328) (.out 0x12276a (xorR32R32Effect 0x12276a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2326, 2322]
    (.letOp (n := 2329) (.exec 0x12276a (fun s => s.RIP = 0x12276a) (xorR32R32Effect 0x12276a 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2326, 2322]
    (.letOp (n := 2330) (.out 0x12276c (movR32R32Effect 0x12276c 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[2318]
    (.letOp (n := 2331) (.exec 0x12276c (fun s => s.RIP = 0x12276c) (movR32R32Effect 0x12276c 3 0 8) (Reg.operands [.gpr 8] [])) #v[2318]
    (.letOp (n := 2332) (.out 0x12276f (shrR32Effect 0x12276f 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2330]
    (.letOp (n := 2333) (.exec 0x12276f (fun s => s.RIP = 0x12276f) (shrR32Effect 0x12276f 3 0 3) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2330]
    (.letOp (n := 2334) (.out 0x122772 (movR32R32Effect 0x122772 3 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[2122]
    (.letOp (n := 2335) (.exec 0x122772 (fun s => s.RIP = 0x122772) (movR32R32Effect 0x122772 3 8 5) (Reg.operands [.gpr 5] [])) #v[2122]
    (.letOp (n := 2336) (.out 0x122775 (rolR32Effect 0x122775 4 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[2334]
    (.letOp (n := 2337) (.exec 0x122775 (fun s => s.RIP = 0x122775) (rolR32Effect 0x122775 4 8 15) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2334]
    (.letOp (n := 2338) (.out 0x122779 (xorR32R32Effect 0x122779 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2332, 2328]
    (.letOp (n := 2339) (.exec 0x122779 (fun s => s.RIP = 0x122779) (xorR32R32Effect 0x122779 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2332, 2328]
    (.letOp (n := 2340) (.out 0x12277b (movR32R32Effect 0x12277b 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[2122]
    (.letOp (n := 2341) (.exec 0x12277b (fun s => s.RIP = 0x12277b) (movR32R32Effect 0x12277b 2 1 5) (Reg.operands [.gpr 5] [])) #v[2122]
    (.letOp (n := 2342) (.out 0x12277d (rolR32Effect 0x12277d 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2340]
    (.letOp (n := 2343) (.exec 0x12277d (fun s => s.RIP = 0x12277d) (rolR32Effect 0x12277d 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2340]
    (.letOp (n := 2344) (.out 0x122780 (xorR32R32Effect 0x122780 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[2342, 2336]
    (.letOp (n := 2345) (.exec 0x122780 (fun s => s.RIP = 0x122780) (xorR32R32Effect 0x122780 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[2342, 2336]
    (.letOp (n := 2346) (.out 0x122783 (movR32R32Effect 0x122783 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2254]
    (.letOp (n := 2347) (.exec 0x122783 (fun s => s.RIP = 0x122783) (movR32R32Effect 0x122783 3 8 2) (Reg.operands [.gpr 2] [])) #v[2254]
    (b_l121930_59))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_58 : List UInt8 :=
  [0x44, 0x21, 0xEF, 0x44, 0x31, 0xC7, 0x01, 0xCF, 0x41, 0x01, 0xC1, 0x01, 0xC7, 0x44, 0x8B, 0x44,
    0x24, 0x14, 0x44, 0x89, 0xC0, 0xC1, 0xC0, 0x19, 0x44, 0x89, 0xC1, 0xC1, 0xC1, 0x0E, 0x31, 0xC1,
    0x44, 0x89, 0xC0, 0xC1, 0xE8, 0x03, 0x41, 0x89, 0xE8, 0x41, 0xC1, 0xC0, 0x0F, 0x31, 0xC8, 0x89,
    0xE9, 0xC1, 0xC1, 0x0D, 0x44, 0x31, 0xC1, 0x41, 0x89, 0xD0] ++ bytes_l121930_59

theorem code_l121930_58 : ∀ x ∈ codeRange 0x12274c bytes_l121930_58, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2274c 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_59

def b_l121930_57 : Block Op Label signature Reg.count 2268 :=
  .letOp (n := 2268) (.out 0x122711 (movR32R32Effect 0x122711 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[2124]
    (.letOp (n := 2269) (.exec 0x122711 (fun s => s.RIP = 0x122711) (movR32R32Effect 0x122711 3 1 10) (Reg.operands [.gpr 10] [])) #v[2124]
    (.letOp (n := 2270) (.out 0x122714 (xorR32R32Effect 0x122714 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[2268, 1932]
    (.letOp (n := 2271) (.exec 0x122714 (fun s => s.RIP = 0x122714) (xorR32R32Effect 0x122714 3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[2268, 1932]
    (.letOp (n := 2272) (.out 0x122717 (andR32R32Effect 0x122717 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[2270, 2248]
    (.letOp (n := 2273) (.exec 0x122717 (fun s => s.RIP = 0x122717) (andR32R32Effect 0x122717 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[2270, 2248]
    (.letOp (n := 2274) (.out 0x122719 (xorR32R32Effect 0x122719 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[2272, 1932]
    (.letOp (n := 2275) (.exec 0x122719 (fun s => s.RIP = 0x122719) (xorR32R32Effect 0x122719 3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[2272, 1932]
    (.letOp (n := 2276) (.out 0x12271c (addR32R32Effect 0x12271c 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[1850, 2254]
    (.letOp (n := 2277) (.exec 0x12271c (fun s => s.RIP = 0x12271c) (addR32R32Effect 0x12271c 3 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[1850, 2254]
    (.letOp (n := 2278) (.out 0x12271f (addR32R32Effect 0x12271f 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[2276, 2274]
    (.letOp (n := 2279) (.exec 0x12271f (fun s => s.RIP = 0x12271f) (addR32R32Effect 0x12271f 3 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[2276, 2274]
    (.letOp (n := 2280) (.out 0x122722 (addR32R32Effect 0x122722 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[2266, 2278]
    (.letOp (n := 2281) (.exec 0x122722 (fun s => s.RIP = 0x122722) (addR32R32Effect 0x122722 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[2266, 2278]
    (.letOp (n := 2282) (.out 0x122725 (addEaxImm32Effect 0x122725 0x4a7484aa) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2280]
    (.letOp (n := 2283) (.exec 0x122725 (fun s => s.RIP = 0x122725) (addEaxImm32Effect 0x122725 0x4a7484aa) (Reg.operands [.gpr 0] [])) #v[2280]
    (.letOp (n := 2284) (.out 0x12272a (movR32R32Effect 0x12272a 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[2194]
    (.letOp (n := 2285) (.exec 0x12272a (fun s => s.RIP = 0x12272a) (movR32R32Effect 0x12272a 3 1 13) (Reg.operands [.gpr 13] [])) #v[2194]
    (.letOp (n := 2286) (.out 0x12272d (rolR32Effect 0x12272d 3 1 30) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2284]
    (.letOp (n := 2287) (.exec 0x12272d (fun s => s.RIP = 0x12272d) (rolR32Effect 0x12272d 3 1 30) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2284]
    (.letOp (n := 2288) (.out 0x122730 (movR32R32Effect 0x122730 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[2194]
    (.letOp (n := 2289) (.exec 0x122730 (fun s => s.RIP = 0x122730) (movR32R32Effect 0x122730 3 7 13) (Reg.operands [.gpr 13] [])) #v[2194]
    (.letOp (n := 2290) (.out 0x122733 (rolR32Effect 0x122733 3 7 19) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[2288]
    (.letOp (n := 2291) (.exec 0x122733 (fun s => s.RIP = 0x122733) (rolR32Effect 0x122733 3 7 19) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2288]
    (.letOp (n := 2292) (.out 0x122736 (xorR32R32Effect 0x122736 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[2290, 2286]
    (.letOp (n := 2293) (.exec 0x122736 (fun s => s.RIP = 0x122736) (xorR32R32Effect 0x122736 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[2290, 2286]
    (.letOp (n := 2294) (.out 0x122738 (movR32R32Effect 0x122738 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[2194]
    (.letOp (n := 2295) (.exec 0x122738 (fun s => s.RIP = 0x122738) (movR32R32Effect 0x122738 3 1 13) (Reg.operands [.gpr 13] [])) #v[2194]
    (.letOp (n := 2296) (.out 0x12273b (rolR32Effect 0x12273b 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2294]
    (.letOp (n := 2297) (.exec 0x12273b (fun s => s.RIP = 0x12273b) (rolR32Effect 0x12273b 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2294]
    (.letOp (n := 2298) (.out 0x12273e (xorR32R32Effect 0x12273e 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[2296, 2292]
    (.letOp (n := 2299) (.exec 0x12273e (fun s => s.RIP = 0x12273e) (xorR32R32Effect 0x12273e 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[2296, 2292]
    (.letOp (n := 2300) (.out 0x122740 (movR32R32Effect 0x122740 3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[2066]
    (.letOp (n := 2301) (.exec 0x122740 (fun s => s.RIP = 0x122740) (movR32R32Effect 0x122740 3 8 12) (Reg.operands [.gpr 12] [])) #v[2066]
    (.letOp (n := 2302) (.out 0x122743 (andR32R32Effect 0x122743 3 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[2300, 2024]
    (.letOp (n := 2303) (.exec 0x122743 (fun s => s.RIP = 0x122743) (andR32R32Effect 0x122743 3 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[2300, 2024]
    (.letOp (n := 2304) (.out 0x122746 (movR32R32Effect 0x122746 3 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[2066]
    (.letOp (n := 2305) (.exec 0x122746 (fun s => s.RIP = 0x122746) (movR32R32Effect 0x122746 3 7 12) (Reg.operands [.gpr 12] [])) #v[2066]
    (.letOp (n := 2306) (.out 0x122749 (xorR32R32Effect 0x122749 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[2304, 2024]
    (.letOp (n := 2307) (.exec 0x122749 (fun s => s.RIP = 0x122749) (xorR32R32Effect 0x122749 3 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[2304, 2024]
    (b_l121930_58))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_57 : List UInt8 :=
  [0x44, 0x89, 0xD1, 0x44, 0x31, 0xF1, 0x21, 0xF1, 0x44, 0x31, 0xF1, 0x41, 0x01, 0xD3, 0x41, 0x01,
    0xCB, 0x44, 0x01, 0xD8, 0x05, 0xAA, 0x84, 0x74, 0x4A, 0x44, 0x89, 0xE9, 0xC1, 0xC1, 0x1E, 0x44,
    0x89, 0xEF, 0xC1, 0xC7, 0x13, 0x31, 0xCF, 0x44, 0x89, 0xE9, 0xC1, 0xC1, 0x0A, 0x31, 0xF9, 0x45,
    0x89, 0xE0, 0x45, 0x21, 0xF8, 0x44, 0x89, 0xE7, 0x44, 0x31, 0xFF] ++ bytes_l121930_58

theorem code_l121930_57 : ∀ x ∈ codeRange 0x122711 bytes_l121930_57, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22711 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_58

def b_l121930_56 : Block Op Label signature Reg.count 2230 :=
  .letOp (n := 2230) (.out 0x1226d7 (shrR32Effect 0x1226d7 3 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2228]
    (.letOp (n := 2231) (.exec 0x1226d7 (fun s => s.RIP = 0x1226d7) (shrR32Effect 0x1226d7 3 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2228]
    (.letOp (n := 2232) (.out 0x1226da (xorR32R32Effect 0x1226da 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[2230, 2226]
    (.letOp (n := 2233) (.exec 0x1226da (fun s => s.RIP = 0x1226da) (xorR32R32Effect 0x1226da 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[2230, 2226]
    (.letOp (n := 2234) (.exec 0x1226dc (StorePre 0x1226dc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1226dc + BitVec.ofNat 64 8)) 4) (addMREffect 0x1226dc 8 32 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1990, 4]
    (.letOp (n := 2235) (.out 0x1226e4 (addR32R32Effect 0x1226e4 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[2232, 1990]
    (.letOp (n := 2236) (.exec 0x1226e4 (fun s => s.RIP = 0x1226e4) (addR32R32Effect 0x1226e4 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[2232, 1990]
    (.letOp (n := 2237) (.exec 0x1226e7 (StorePre 0x1226e7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1226e7 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1226e7 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2235, 4]
    (.letOp (n := 2238) (.out 0x1226eb (movR32R32Effect 0x1226eb 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[1990]
    (.letOp (n := 2239) (.exec 0x1226eb (fun s => s.RIP = 0x1226eb) (movR32R32Effect 0x1226eb 3 1 8) (Reg.operands [.gpr 8] [])) #v[1990]
    (.letOp (n := 2240) (.out 0x1226ee (shrR32Effect 0x1226ee 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2238]
    (.letOp (n := 2241) (.exec 0x1226ee (fun s => s.RIP = 0x1226ee) (shrR32Effect 0x1226ee 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2238]
    (.letOp (n := 2242) (.out 0x1226f1 (xorR32R32Effect 0x1226f1 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2240, 2216]
    (.letOp (n := 2243) (.exec 0x1226f1 (fun s => s.RIP = 0x1226f1) (xorR32R32Effect 0x1226f1 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2240, 2216]
    (.letOp (n := 2244) (.out 0x1226f3 (movR32M32LowEffect 0x1226f3 2 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 2245) (.exec 0x1226f3 (LoadPre 0x1226f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1226f3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1226f3 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2246) (.out 0x1226f7 (addR32R32Effect 0x1226f7 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[2244, 2210]
    (.letOp (n := 2247) (.exec 0x1226f7 (fun s => s.RIP = 0x1226f7) (addR32R32Effect 0x1226f7 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2244, 2210]
    (.letOp (n := 2248) (.out 0x1226f9 (movR64R64Effect 0x1226f9 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[2188]
    (.letOp (n := 2249) (.exec 0x1226f9 (fun s => s.RIP = 0x1226f9) (movR64R64Effect 0x1226f9 6 3) (Reg.operands [.gpr 3] [])) #v[2188]
    (.letOp (n := 2250) (.out 0x1226fc (movR32R32Effect 0x1226fc 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2248]
    (.letOp (n := 2251) (.exec 0x1226fc (fun s => s.RIP = 0x1226fc) (movR32R32Effect 0x1226fc 2 0 6) (Reg.operands [.gpr 6] [])) #v[2248]
    (.letOp (n := 2252) (.out 0x1226fe (rolR32Effect 0x1226fe 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2250]
    (.letOp (n := 2253) (.exec 0x1226fe (fun s => s.RIP = 0x1226fe) (rolR32Effect 0x1226fe 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2250]
    (.letOp (n := 2254) (.out 0x122701 (addR32R32Effect 0x122701 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[2246, 2242]
    (.letOp (n := 2255) (.exec 0x122701 (fun s => s.RIP = 0x122701) (addR32R32Effect 0x122701 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2246, 2242]
    (.letOp (n := 2256) (.out 0x122703 (movR32R32Effect 0x122703 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[2248]
    (.letOp (n := 2257) (.exec 0x122703 (fun s => s.RIP = 0x122703) (movR32R32Effect 0x122703 2 1 6) (Reg.operands [.gpr 6] [])) #v[2248]
    (.letOp (n := 2258) (.out 0x122705 (rolR32Effect 0x122705 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2256]
    (.letOp (n := 2259) (.exec 0x122705 (fun s => s.RIP = 0x122705) (rolR32Effect 0x122705 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2256]
    (.letOp (n := 2260) (.out 0x122708 (xorR32R32Effect 0x122708 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2258, 2252]
    (.letOp (n := 2261) (.exec 0x122708 (fun s => s.RIP = 0x122708) (xorR32R32Effect 0x122708 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2258, 2252]
    (.letOp (n := 2262) (.out 0x12270a (movR32R32Effect 0x12270a 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2248]
    (.letOp (n := 2263) (.exec 0x12270a (fun s => s.RIP = 0x12270a) (movR32R32Effect 0x12270a 2 0 6) (Reg.operands [.gpr 6] [])) #v[2248]
    (.letOp (n := 2264) (.out 0x12270c (rolR32Effect 0x12270c 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2262]
    (.letOp (n := 2265) (.exec 0x12270c (fun s => s.RIP = 0x12270c) (rolR32Effect 0x12270c 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2262]
    (.letOp (n := 2266) (.out 0x12270f (xorR32R32Effect 0x12270f 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2264, 2260]
    (.letOp (n := 2267) (.exec 0x12270f (fun s => s.RIP = 0x12270f) (xorR32R32Effect 0x12270f 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2264, 2260]
    (b_l121930_57))))))))))))))))))))))))))))))))))))))

def bytes_l121930_56 : List UInt8 :=
  [0xC1, 0xE9, 0x03, 0x31, 0xF9, 0x44, 0x01, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x44, 0x01, 0xC1,
    0x89, 0x4C, 0x24, 0x50, 0x44, 0x89, 0xC1, 0xC1, 0xE9, 0x0A, 0x31, 0xC1, 0x8B, 0x54, 0x24, 0x40,
    0x01, 0xF2, 0x48, 0x89, 0xDE, 0x89, 0xF0, 0xC1, 0xC0, 0x1A, 0x01, 0xCA, 0x89, 0xF1, 0xC1, 0xC1,
    0x15, 0x31, 0xC1, 0x89, 0xF0, 0xC1, 0xC0, 0x07, 0x31, 0xC8] ++ bytes_l121930_57

theorem code_l121930_56 : ∀ x ∈ codeRange 0x1226d7 bytes_l121930_56, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x226d7 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_57

def b_l121930_55 : Block Op Label signature Reg.count 2190 :=
  .letOp (n := 2190) (.out 0x122696 (movR32M32LowEffect 0x122696 1 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 2191) (.exec 0x122696 (LoadPre 0x122696 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x122696 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x122696 1 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2192) (.out 0x12269d (rolR32Effect 0x12269d 3 1 25) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2190]
    (.letOp (n := 2193) (.exec 0x12269d (fun s => s.RIP = 0x12269d) (rolR32Effect 0x12269d 3 1 25) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2190]
    (.letOp (n := 2194) (.out 0x1226a0 (addR32R32Effect 0x1226a0 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[2186, 2164]
    (.letOp (n := 2195) (.exec 0x1226a0 (fun s => s.RIP = 0x1226a0) (addR32R32Effect 0x1226a0 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2186, 2164]
    (.letOp (n := 2196) (.out 0x1226a3 (movR32M32LowEffect 0x1226a3 0 (.sib 4 none 0 (.d32 0xac))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2197) (.exec 0x1226a3 (LoadPre 0x1226a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x1226a3 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1226a3 0 (.sib 4 none 0 (.d32 0xac))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2198) (.out 0x1226aa (rolR32Effect 0x1226aa 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2196]
    (.letOp (n := 2199) (.exec 0x1226aa (fun s => s.RIP = 0x1226aa) (rolR32Effect 0x1226aa 3 0 14) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2196]
    (.letOp (n := 2200) (.out 0x1226ad (xorR32R32Effect 0x1226ad 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2198, 2192]
    (.letOp (n := 2201) (.exec 0x1226ad (fun s => s.RIP = 0x1226ad) (xorR32R32Effect 0x1226ad 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2198, 2192]
    (.letOp (n := 2202) (.out 0x1226af (movR32M32LowEffect 0x1226af 6 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 2203) (.exec 0x1226af (LoadPre 0x1226af (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1226af + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1226af 6 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2204) (.out 0x1226b6 (shrR32Effect 0x1226b6 3 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[2202]
    (.letOp (n := 2205) (.exec 0x1226b6 (fun s => s.RIP = 0x1226b6) (shrR32Effect 0x1226b6 3 6 3) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2202]
    (.letOp (n := 2206) (.out 0x1226b9 (movR32R32Effect 0x1226b9 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[1990]
    (.letOp (n := 2207) (.exec 0x1226b9 (fun s => s.RIP = 0x1226b9) (movR32R32Effect 0x1226b9 3 1 8) (Reg.operands [.gpr 8] [])) #v[1990]
    (.letOp (n := 2208) (.out 0x1226bc (rolR32Effect 0x1226bc 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2206]
    (.letOp (n := 2209) (.exec 0x1226bc (fun s => s.RIP = 0x1226bc) (rolR32Effect 0x1226bc 3 1 15) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2206]
    (.letOp (n := 2210) (.out 0x1226bf (xorR32R32Effect 0x1226bf 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[2204, 2200]
    (.letOp (n := 2211) (.exec 0x1226bf (fun s => s.RIP = 0x1226bf) (xorR32R32Effect 0x1226bf 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[2204, 2200]
    (.letOp (n := 2212) (.out 0x1226c1 (movR32R32Effect 0x1226c1 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[1990]
    (.letOp (n := 2213) (.exec 0x1226c1 (fun s => s.RIP = 0x1226c1) (movR32R32Effect 0x1226c1 3 0 8) (Reg.operands [.gpr 8] [])) #v[1990]
    (.letOp (n := 2214) (.out 0x1226c4 (rolR32Effect 0x1226c4 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2212]
    (.letOp (n := 2215) (.exec 0x1226c4 (fun s => s.RIP = 0x1226c4) (rolR32Effect 0x1226c4 3 0 13) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2212]
    (.letOp (n := 2216) (.out 0x1226c7 (xorR32R32Effect 0x1226c7 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2214, 2208]
    (.letOp (n := 2217) (.exec 0x1226c7 (fun s => s.RIP = 0x1226c7) (xorR32R32Effect 0x1226c7 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2214, 2208]
    (.letOp (n := 2218) (.out 0x1226c9 (movR32R32Effect 0x1226c9 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[2122]
    (.letOp (n := 2219) (.exec 0x1226c9 (fun s => s.RIP = 0x1226c9) (movR32R32Effect 0x1226c9 2 1 5) (Reg.operands [.gpr 5] [])) #v[2122]
    (.letOp (n := 2220) (.out 0x1226cb (rolR32Effect 0x1226cb 3 1 25) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2218]
    (.letOp (n := 2221) (.exec 0x1226cb (fun s => s.RIP = 0x1226cb) (rolR32Effect 0x1226cb 3 1 25) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2218]
    (.letOp (n := 2222) (.out 0x1226ce (movR32R32Effect 0x1226ce 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[2122]
    (.letOp (n := 2223) (.exec 0x1226ce (fun s => s.RIP = 0x1226ce) (movR32R32Effect 0x1226ce 2 7 5) (Reg.operands [.gpr 5] [])) #v[2122]
    (.letOp (n := 2224) (.out 0x1226d0 (rolR32Effect 0x1226d0 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[2222]
    (.letOp (n := 2225) (.exec 0x1226d0 (fun s => s.RIP = 0x1226d0) (rolR32Effect 0x1226d0 3 7 14) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2222]
    (.letOp (n := 2226) (.out 0x1226d3 (xorR32R32Effect 0x1226d3 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[2224, 2220]
    (.letOp (n := 2227) (.exec 0x1226d3 (fun s => s.RIP = 0x1226d3) (xorR32R32Effect 0x1226d3 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[2224, 2220]
    (.letOp (n := 2228) (.out 0x1226d5 (movR32R32Effect 0x1226d5 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[2122]
    (.letOp (n := 2229) (.exec 0x1226d5 (fun s => s.RIP = 0x1226d5) (movR32R32Effect 0x1226d5 2 1 5) (Reg.operands [.gpr 5] [])) #v[2122]
    (b_l121930_56))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_55 : List UInt8 :=
  [0x8B, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0xC1, 0xC1, 0x19, 0x41, 0x01, 0xC5, 0x8B, 0x84, 0x24,
    0xAC, 0x00, 0x00, 0x00, 0xC1, 0xC0, 0x0E, 0x31, 0xC8, 0x8B, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0xC1, 0xEE, 0x03, 0x44, 0x89, 0xC1, 0xC1, 0xC1, 0x0F, 0x31, 0xC6, 0x44, 0x89, 0xC0, 0xC1, 0xC0,
    0x0D, 0x31, 0xC8, 0x89, 0xE9, 0xC1, 0xC1, 0x19, 0x89, 0xEF, 0xC1, 0xC7, 0x0E, 0x31, 0xCF, 0x89,
    0xE9] ++ bytes_l121930_56

theorem code_l121930_55 : ∀ x ∈ codeRange 0x122696 bytes_l121930_55, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22696 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_56

def b_l121930_54 : Block Op Label signature Reg.count 2150 :=
  .letOp (n := 2150) (.out 0x12265e (addR32R32Effect 0x12265e 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[2016, 2122]
    (.letOp (n := 2151) (.exec 0x12265e (fun s => s.RIP = 0x12265e) (addR32R32Effect 0x12265e 2 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[2016, 2122]
    (.letOp (n := 2152) (.out 0x122660 (movR32R32Effect 0x122660 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[2066]
    (.letOp (n := 2153) (.exec 0x122660 (fun s => s.RIP = 0x122660) (movR32R32Effect 0x122660 3 2 12) (Reg.operands [.gpr 12] [])) #v[2066]
    (.letOp (n := 2154) (.out 0x122663 (rolR32Effect 0x122663 3 2 30) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2152]
    (.letOp (n := 2155) (.exec 0x122663 (fun s => s.RIP = 0x122663) (rolR32Effect 0x122663 3 2 30) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2152]
    (.letOp (n := 2156) (.out 0x122666 (addR32R32Effect 0x122666 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[2150, 2148]
    (.letOp (n := 2157) (.exec 0x122666 (fun s => s.RIP = 0x122666) (addR32R32Effect 0x122666 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[2150, 2148]
    (.letOp (n := 2158) (.out 0x122668 (movR32R32Effect 0x122668 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[2066]
    (.letOp (n := 2159) (.exec 0x122668 (fun s => s.RIP = 0x122668) (movR32R32Effect 0x122668 3 1 12) (Reg.operands [.gpr 12] [])) #v[2066]
    (.letOp (n := 2160) (.out 0x12266b (rolR32Effect 0x12266b 3 1 19) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2158]
    (.letOp (n := 2161) (.exec 0x12266b (fun s => s.RIP = 0x12266b) (rolR32Effect 0x12266b 3 1 19) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2158]
    (.letOp (n := 2162) (.out 0x12266e (addR32R32Effect 0x12266e 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[2140, 2156]
    (.letOp (n := 2163) (.exec 0x12266e (fun s => s.RIP = 0x12266e) (addR32R32Effect 0x12266e 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[2140, 2156]
    (.letOp (n := 2164) (.out 0x122670 (addEaxImm32Effect 0x122670 0x2de92c6f) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2162]
    (.letOp (n := 2165) (.exec 0x122670 (fun s => s.RIP = 0x122670) (addEaxImm32Effect 0x122670 0x2de92c6f) (Reg.operands [.gpr 0] [])) #v[2162]
    (.letOp (n := 2166) (.out 0x122675 (movR32R32Effect 0x122675 3 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[2066]
    (.letOp (n := 2167) (.exec 0x122675 (fun s => s.RIP = 0x122675) (movR32R32Effect 0x122675 3 7 12) (Reg.operands [.gpr 12] [])) #v[2066]
    (.letOp (n := 2168) (.out 0x122678 (rolR32Effect 0x122678 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[2166]
    (.letOp (n := 2169) (.exec 0x122678 (fun s => s.RIP = 0x122678) (rolR32Effect 0x122678 3 7 10) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2166]
    (.letOp (n := 2170) (.out 0x12267b (xorR32R32Effect 0x12267b 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[2160, 2154]
    (.letOp (n := 2171) (.exec 0x12267b (fun s => s.RIP = 0x12267b) (xorR32R32Effect 0x12267b 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[2160, 2154]
    (.letOp (n := 2172) (.out 0x12267d (xorR32R32Effect 0x12267d 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[2168, 2170]
    (.letOp (n := 2173) (.exec 0x12267d (fun s => s.RIP = 0x12267d) (xorR32R32Effect 0x12267d 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[2168, 2170]
    (.letOp (n := 2174) (.out 0x12267f (movR32R32Effect 0x12267f 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[2024]
    (.letOp (n := 2175) (.exec 0x12267f (fun s => s.RIP = 0x12267f) (movR32R32Effect 0x12267f 3 1 15) (Reg.operands [.gpr 15] [])) #v[2024]
    (.letOp (n := 2176) (.out 0x122682 (andR32R32Effect 0x122682 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[2174, 1894]
    (.letOp (n := 2177) (.exec 0x122682 (fun s => s.RIP = 0x122682) (andR32R32Effect 0x122682 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[2174, 1894]
    (.letOp (n := 2178) (.out 0x122685 (movR32R32Effect 0x122685 3 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[2024]
    (.letOp (n := 2179) (.exec 0x122685 (fun s => s.RIP = 0x122685) (movR32R32Effect 0x122685 3 13 15) (Reg.operands [.gpr 15] [])) #v[2024]
    (.letOp (n := 2180) (.out 0x122688 (xorR32R32Effect 0x122688 3 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[2178, 1894]
    (.letOp (n := 2181) (.exec 0x122688 (fun s => s.RIP = 0x122688) (xorR32R32Effect 0x122688 3 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[2178, 1894]
    (.letOp (n := 2182) (.out 0x12268b (andR32R32Effect 0x12268b 3 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[2180, 2066]
    (.letOp (n := 2183) (.exec 0x12268b (fun s => s.RIP = 0x12268b) (andR32R32Effect 0x12268b 3 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[2180, 2066]
    (.letOp (n := 2184) (.out 0x12268e (xorR32R32Effect 0x12268e 3 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[2182, 2176]
    (.letOp (n := 2185) (.exec 0x12268e (fun s => s.RIP = 0x12268e) (xorR32R32Effect 0x12268e 3 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[2182, 2176]
    (.letOp (n := 2186) (.out 0x122691 (addR32R32Effect 0x122691 3 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 7] []) (.reg (.gpr 13))) #v[2184, 2172]
    (.letOp (n := 2187) (.exec 0x122691 (fun s => s.RIP = 0x122691) (addR32R32Effect 0x122691 3 13 7) (Reg.operands [.gpr 13, .gpr 7] [])) #v[2184, 2172]
    (.letOp (n := 2188) (.out 0x122694 (addR32R32Effect 0x122694 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[2048, 2164]
    (.letOp (n := 2189) (.exec 0x122694 (fun s => s.RIP = 0x122694) (addR32R32Effect 0x122694 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[2048, 2164]
    (b_l121930_55))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_54 : List UInt8 :=
  [0x01, 0xEF, 0x44, 0x89, 0xE2, 0xC1, 0xC2, 0x1E, 0x01, 0xCF, 0x44, 0x89, 0xE1, 0xC1, 0xC1, 0x13,
    0x01, 0xF8, 0x05, 0x6F, 0x2C, 0xE9, 0x2D, 0x44, 0x89, 0xE7, 0xC1, 0xC7, 0x0A, 0x31, 0xD1, 0x31,
    0xCF, 0x44, 0x89, 0xF9, 0x44, 0x21, 0xC9, 0x45, 0x89, 0xFD, 0x45, 0x31, 0xCD, 0x45, 0x21, 0xE5,
    0x41, 0x31, 0xCD, 0x41, 0x01, 0xFD, 0x01, 0xC3] ++ bytes_l121930_55

theorem code_l121930_54 : ∀ x ∈ codeRange 0x12265e bytes_l121930_54, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2265e 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_55

def b_l121930_53 : Block Op Label signature Reg.count 2111 :=
  .letOp (n := 2111) (.out 0x122627 (addR32R32Effect 0x122627 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[2108, 1968]
    (.letOp (n := 2112) (.exec 0x122627 (fun s => s.RIP = 0x122627) (addR32R32Effect 0x122627 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[2108, 1968]
    (.letOp (n := 2113) (.exec 0x122629 (StorePre 0x122629 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x122629 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x122629 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2111, 4]
    (.letOp (n := 2114) (.out 0x12262d (movR32R32Effect 0x12262d 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[1968]
    (.letOp (n := 2115) (.exec 0x12262d (fun s => s.RIP = 0x12262d) (movR32R32Effect 0x12262d 2 1 6) (Reg.operands [.gpr 6] [])) #v[1968]
    (.letOp (n := 2116) (.out 0x12262f (shrR32Effect 0x12262f 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2114]
    (.letOp (n := 2117) (.exec 0x12262f (fun s => s.RIP = 0x12262f) (shrR32Effect 0x12262f 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2114]
    (.letOp (n := 2118) (.out 0x122632 (xorR32R32Effect 0x122632 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2116, 2092]
    (.letOp (n := 2119) (.exec 0x122632 (fun s => s.RIP = 0x122632) (xorR32R32Effect 0x122632 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2116, 2092]
    (.letOp (n := 2120) (.out 0x122634 (addR32R32Effect 0x122634 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[1753, 2082]
    (.letOp (n := 2121) (.exec 0x122634 (fun s => s.RIP = 0x122634) (addR32R32Effect 0x122634 3 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[1753, 2082]
    (.letOp (n := 2122) (.out 0x122637 (addR32R32Effect 0x122637 2 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[2120, 2118]
    (.letOp (n := 2123) (.exec 0x122637 (fun s => s.RIP = 0x122637) (addR32R32Effect 0x122637 2 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[2120, 2118]
    (.letOp (n := 2124) (.out 0x122639 (movR64R64Effect 0x122639 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 13] []) (.reg (.gpr 10))) #v[2064]
    (.letOp (n := 2125) (.exec 0x122639 (fun s => s.RIP = 0x122639) (movR64R64Effect 0x122639 10 13) (Reg.operands [.gpr 13] [])) #v[2064]
    (.letOp (n := 2126) (.out 0x12263c (movR32R32Effect 0x12263c 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[2124]
    (.letOp (n := 2127) (.exec 0x12263c (fun s => s.RIP = 0x12263c) (movR32R32Effect 0x12263c 3 0 10) (Reg.operands [.gpr 10] [])) #v[2124]
    (.letOp (n := 2128) (.out 0x12263f (rolR32Effect 0x12263f 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2126]
    (.letOp (n := 2129) (.exec 0x12263f (fun s => s.RIP = 0x12263f) (rolR32Effect 0x12263f 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2126]
    (.letOp (n := 2130) (.out 0x122642 (movR32R32Effect 0x122642 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[2124]
    (.letOp (n := 2131) (.exec 0x122642 (fun s => s.RIP = 0x122642) (movR32R32Effect 0x122642 3 1 10) (Reg.operands [.gpr 10] [])) #v[2124]
    (.letOp (n := 2132) (.out 0x122645 (rolR32Effect 0x122645 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2130]
    (.letOp (n := 2133) (.exec 0x122645 (fun s => s.RIP = 0x122645) (rolR32Effect 0x122645 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2130]
    (.letOp (n := 2134) (.out 0x122648 (xorR32R32Effect 0x122648 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2132, 2128]
    (.letOp (n := 2135) (.exec 0x122648 (fun s => s.RIP = 0x122648) (xorR32R32Effect 0x122648 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2132, 2128]
    (.letOp (n := 2136) (.out 0x12264a (movR32R32Effect 0x12264a 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[2124]
    (.letOp (n := 2137) (.exec 0x12264a (fun s => s.RIP = 0x12264a) (movR32R32Effect 0x12264a 3 0 10) (Reg.operands [.gpr 10] [])) #v[2124]
    (.letOp (n := 2138) (.out 0x12264d (rolR32Effect 0x12264d 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2136]
    (.letOp (n := 2139) (.exec 0x12264d (fun s => s.RIP = 0x12264d) (rolR32Effect 0x12264d 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2136]
    (.letOp (n := 2140) (.out 0x122650 (xorR32R32Effect 0x122650 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2138, 2134]
    (.letOp (n := 2141) (.exec 0x122650 (fun s => s.RIP = 0x122650) (xorR32R32Effect 0x122650 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2138, 2134]
    (.letOp (n := 2142) (.out 0x122652 (movR32R32Effect 0x122652 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[1932]
    (.letOp (n := 2143) (.exec 0x122652 (fun s => s.RIP = 0x122652) (movR32R32Effect 0x122652 3 1 14) (Reg.operands [.gpr 14] [])) #v[1932]
    (.letOp (n := 2144) (.out 0x122655 (xorR32R32Effect 0x122655 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[2142, 1850]
    (.letOp (n := 2145) (.exec 0x122655 (fun s => s.RIP = 0x122655) (xorR32R32Effect 0x122655 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[2142, 1850]
    (.letOp (n := 2146) (.out 0x122658 (andR32R32Effect 0x122658 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[2144, 2124]
    (.letOp (n := 2147) (.exec 0x122658 (fun s => s.RIP = 0x122658) (andR32R32Effect 0x122658 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[2144, 2124]
    (.letOp (n := 2148) (.out 0x12265b (xorR32R32Effect 0x12265b 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[2146, 1850]
    (.letOp (n := 2149) (.exec 0x12265b (fun s => s.RIP = 0x12265b) (xorR32R32Effect 0x12265b 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[2146, 1850]
    (b_l121930_54)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_53 : List UInt8 :=
  [0x01, 0xF1, 0x89, 0x4C, 0x24, 0x38, 0x89, 0xF1, 0xC1, 0xE9, 0x0A, 0x31, 0xC1, 0x44, 0x01, 0xD5,
    0x01, 0xCD, 0x4D, 0x89, 0xEA, 0x44, 0x89, 0xD0, 0xC1, 0xC0, 0x1A, 0x44, 0x89, 0xD1, 0xC1, 0xC1,
    0x15, 0x31, 0xC1, 0x44, 0x89, 0xD0, 0xC1, 0xC0, 0x07, 0x31, 0xC8, 0x44, 0x89, 0xF1, 0x44, 0x31,
    0xD9, 0x44, 0x21, 0xD1, 0x44, 0x31, 0xD9] ++ bytes_l121930_54

theorem code_l121930_53 : ∀ x ∈ codeRange 0x122627 bytes_l121930_53, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22627 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_54

def b_l121930_52 : Block Op Label signature Reg.count 2072 :=
  .letOp (n := 2072) (.out 0x1225e7 (movR32M32LowEffect 0x1225e7 0 (.sib 4 none 0 (.d32 0x94))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2073) (.exec 0x1225e7 (LoadPre 0x1225e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x1225e7 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1225e7 0 (.sib 4 none 0 (.d32 0x94))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2074) (.out 0x1225ee (rolR32Effect 0x1225ee 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2072]
    (.letOp (n := 2075) (.exec 0x1225ee (fun s => s.RIP = 0x1225ee) (rolR32Effect 0x1225ee 3 0 14) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2072]
    (.letOp (n := 2076) (.out 0x1225f1 (xorR32R32Effect 0x1225f1 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2074, 2070]
    (.letOp (n := 2077) (.exec 0x1225f1 (fun s => s.RIP = 0x1225f1) (xorR32R32Effect 0x1225f1 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2074, 2070]
    (.letOp (n := 2078) (.out 0x1225f3 (movR32M32Effect 0x1225f3 10 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 2079) (.exec 0x1225f3 (LoadPre 0x1225f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1225f3 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x1225f3 10 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2080) (.out 0x1225fb (shrR32Effect 0x1225fb 4 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[2078]
    (.letOp (n := 2081) (.exec 0x1225fb (fun s => s.RIP = 0x1225fb) (shrR32Effect 0x1225fb 4 10 3) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2078]
    (.letOp (n := 2082) (.out 0x1225ff (xorR32R32Effect 0x1225ff 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[2080, 2076]
    (.letOp (n := 2083) (.exec 0x1225ff (fun s => s.RIP = 0x1225ff) (xorR32R32Effect 0x1225ff 3 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[2080, 2076]
    (.letOp (n := 2084) (.out 0x122602 (movR32R32Effect 0x122602 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[1968]
    (.letOp (n := 2085) (.exec 0x122602 (fun s => s.RIP = 0x122602) (movR32R32Effect 0x122602 2 1 6) (Reg.operands [.gpr 6] [])) #v[1968]
    (.letOp (n := 2086) (.out 0x122604 (rolR32Effect 0x122604 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2084]
    (.letOp (n := 2087) (.exec 0x122604 (fun s => s.RIP = 0x122604) (rolR32Effect 0x122604 3 1 15) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2084]
    (.letOp (n := 2088) (.out 0x122607 (movR32R32Effect 0x122607 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[1968]
    (.letOp (n := 2089) (.exec 0x122607 (fun s => s.RIP = 0x122607) (movR32R32Effect 0x122607 2 0 6) (Reg.operands [.gpr 6] [])) #v[1968]
    (.letOp (n := 2090) (.out 0x122609 (rolR32Effect 0x122609 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2088]
    (.letOp (n := 2091) (.exec 0x122609 (fun s => s.RIP = 0x122609) (rolR32Effect 0x122609 3 0 13) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2088]
    (.letOp (n := 2092) (.out 0x12260c (xorR32R32Effect 0x12260c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2090, 2086]
    (.letOp (n := 2093) (.exec 0x12260c (fun s => s.RIP = 0x12260c) (xorR32R32Effect 0x12260c 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2090, 2086]
    (.letOp (n := 2094) (.out 0x12260e (movR32R32Effect 0x12260e 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[1990]
    (.letOp (n := 2095) (.exec 0x12260e (fun s => s.RIP = 0x12260e) (movR32R32Effect 0x12260e 3 1 8) (Reg.operands [.gpr 8] [])) #v[1990]
    (.letOp (n := 2096) (.out 0x122611 (rolR32Effect 0x122611 3 1 25) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2094]
    (.letOp (n := 2097) (.exec 0x122611 (fun s => s.RIP = 0x122611) (rolR32Effect 0x122611 3 1 25) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2094]
    (.letOp (n := 2098) (.out 0x122614 (movR32R32Effect 0x122614 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[1990]
    (.letOp (n := 2099) (.exec 0x122614 (fun s => s.RIP = 0x122614) (movR32R32Effect 0x122614 3 2 8) (Reg.operands [.gpr 8] [])) #v[1990]
    (.letOp (n := 2100) (.out 0x122617 (rolR32Effect 0x122617 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2098]
    (.letOp (n := 2101) (.exec 0x122617 (fun s => s.RIP = 0x122617) (rolR32Effect 0x122617 3 2 14) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2098]
    (.letOp (n := 2102) (.out 0x12261a (xorR32R32Effect 0x12261a 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[2100, 2096]
    (.letOp (n := 2103) (.exec 0x12261a (fun s => s.RIP = 0x12261a) (xorR32R32Effect 0x12261a 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2100, 2096]
    (.letOp (n := 2104) (.out 0x12261c (movR32R32Effect 0x12261c 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[1990]
    (.letOp (n := 2105) (.exec 0x12261c (fun s => s.RIP = 0x12261c) (movR32R32Effect 0x12261c 3 1 8) (Reg.operands [.gpr 8] [])) #v[1990]
    (.letOp (n := 2106) (.out 0x12261f (shrR32Effect 0x12261f 3 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2104]
    (.letOp (n := 2107) (.exec 0x12261f (fun s => s.RIP = 0x12261f) (shrR32Effect 0x12261f 3 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2104]
    (.letOp (n := 2108) (.out 0x122622 (xorR32R32Effect 0x122622 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[2106, 2102]
    (.letOp (n := 2109) (.exec 0x122622 (fun s => s.RIP = 0x122622) (xorR32R32Effect 0x122622 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[2106, 2102]
    (.letOp (n := 2110) (.exec 0x122624 (StorePre 0x122624 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x122624 + BitVec.ofNat 64 3)) 4) (addMREffect 0x122624 3 32 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1968, 4]
    (b_l121930_53)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_52 : List UInt8 :=
  [0x8B, 0x84, 0x24, 0x94, 0x00, 0x00, 0x00, 0xC1, 0xC0, 0x0E, 0x31, 0xC8, 0x44, 0x8B, 0x94, 0x24,
    0x98, 0x00, 0x00, 0x00, 0x41, 0xC1, 0xEA, 0x03, 0x41, 0x31, 0xC2, 0x89, 0xF1, 0xC1, 0xC1, 0x0F,
    0x89, 0xF0, 0xC1, 0xC0, 0x0D, 0x31, 0xC8, 0x44, 0x89, 0xC1, 0xC1, 0xC1, 0x19, 0x44, 0x89, 0xC2,
    0xC1, 0xC2, 0x0E, 0x31, 0xCA, 0x44, 0x89, 0xC1, 0xC1, 0xE9, 0x03, 0x31, 0xD1, 0x01, 0x34, 0x24] ++ bytes_l121930_53

theorem code_l121930_52 : ∀ x ∈ codeRange 0x1225e7 bytes_l121930_52, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x225e7 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_53

def b_l121930_51 : Block Op Label signature Reg.count 2032 :=
  .letOp (n := 2032) (.out 0x1225a4 (addEaxImm32Effect 0x1225a4 0x240ca1cc) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2030]
    (.letOp (n := 2033) (.exec 0x1225a4 (fun s => s.RIP = 0x1225a4) (addEaxImm32Effect 0x1225a4 0x240ca1cc) (Reg.operands [.gpr 0] [])) #v[2030]
    (.letOp (n := 2034) (.out 0x1225a9 (movR32R32Effect 0x1225a9 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[2024]
    (.letOp (n := 2035) (.exec 0x1225a9 (fun s => s.RIP = 0x1225a9) (movR32R32Effect 0x1225a9 3 2 15) (Reg.operands [.gpr 15] [])) #v[2024]
    (.letOp (n := 2036) (.out 0x1225ac (rolR32Effect 0x1225ac 3 2 19) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2034]
    (.letOp (n := 2037) (.exec 0x1225ac (fun s => s.RIP = 0x1225ac) (rolR32Effect 0x1225ac 3 2 19) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2034]
    (.letOp (n := 2038) (.out 0x1225af (xorR32R32Effect 0x1225af 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[2036, 2028]
    (.letOp (n := 2039) (.exec 0x1225af (fun s => s.RIP = 0x1225af) (xorR32R32Effect 0x1225af 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2036, 2028]
    (.letOp (n := 2040) (.out 0x1225b1 (movR32R32Effect 0x1225b1 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[2024]
    (.letOp (n := 2041) (.exec 0x1225b1 (fun s => s.RIP = 0x1225b1) (movR32R32Effect 0x1225b1 3 1 15) (Reg.operands [.gpr 15] [])) #v[2024]
    (.letOp (n := 2042) (.out 0x1225b4 (rolR32Effect 0x1225b4 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2040]
    (.letOp (n := 2043) (.exec 0x1225b4 (fun s => s.RIP = 0x1225b4) (rolR32Effect 0x1225b4 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2040]
    (.letOp (n := 2044) (.out 0x1225b7 (xorR32R32Effect 0x1225b7 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[2042, 2038]
    (.letOp (n := 2045) (.exec 0x1225b7 (fun s => s.RIP = 0x1225b7) (xorR32R32Effect 0x1225b7 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[2042, 2038]
    (.letOp (n := 2046) (.out 0x1225b9 (movR32R32Effect 0x1225b9 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[1894]
    (.letOp (n := 2047) (.exec 0x1225b9 (fun s => s.RIP = 0x1225b9) (movR32R32Effect 0x1225b9 3 2 9) (Reg.operands [.gpr 9] [])) #v[1894]
    (.letOp (n := 2048) (.out 0x1225bc (movR64M64Effect 0x1225bc 3 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 2049) (.exec 0x1225bc (LoadPre 0x1225bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1225bc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1225bc 3 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2050) (.out 0x1225c1 (andR32R32Effect 0x1225c1 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[2046, 2048]
    (.letOp (n := 2051) (.exec 0x1225c1 (fun s => s.RIP = 0x1225c1) (andR32R32Effect 0x1225c1 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2046, 2048]
    (.letOp (n := 2052) (.out 0x1225c3 (movR32R32Effect 0x1225c3 3 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[1894]
    (.letOp (n := 2053) (.exec 0x1225c3 (fun s => s.RIP = 0x1225c3) (movR32R32Effect 0x1225c3 3 12 9) (Reg.operands [.gpr 9] [])) #v[1894]
    (.letOp (n := 2054) (.out 0x1225c6 (xorR32R32Effect 0x1225c6 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[2052, 2048]
    (.letOp (n := 2055) (.exec 0x1225c6 (fun s => s.RIP = 0x1225c6) (xorR32R32Effect 0x1225c6 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[2052, 2048]
    (.letOp (n := 2056) (.out 0x1225c9 (andR32R32Effect 0x1225c9 3 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[2054, 2024]
    (.letOp (n := 2057) (.exec 0x1225c9 (fun s => s.RIP = 0x1225c9) (andR32R32Effect 0x1225c9 3 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[2054, 2024]
    (.letOp (n := 2058) (.out 0x1225cc (xorR32R32Effect 0x1225cc 3 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[2056, 2050]
    (.letOp (n := 2059) (.exec 0x1225cc (fun s => s.RIP = 0x1225cc) (xorR32R32Effect 0x1225cc 3 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[2056, 2050]
    (.letOp (n := 2060) (.out 0x1225cf (addR32R32Effect 0x1225cf 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[2058, 2044]
    (.letOp (n := 2061) (.exec 0x1225cf (fun s => s.RIP = 0x1225cf) (addR32R32Effect 0x1225cf 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[2058, 2044]
    (.letOp (n := 2062) (.out 0x1225d2 (movR64M64Effect 0x1225d2 13 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 2063) (.exec 0x1225d2 (LoadPre 0x1225d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1225d2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1225d2 13 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2064) (.out 0x1225d7 (addR32R32Effect 0x1225d7 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[2062, 2032]
    (.letOp (n := 2065) (.exec 0x1225d7 (fun s => s.RIP = 0x1225d7) (addR32R32Effect 0x1225d7 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[2062, 2032]
    (.letOp (n := 2066) (.out 0x1225da (addR32R32Effect 0x1225da 3 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[2060, 2032]
    (.letOp (n := 2067) (.exec 0x1225da (fun s => s.RIP = 0x1225da) (addR32R32Effect 0x1225da 3 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[2060, 2032]
    (.letOp (n := 2068) (.out 0x1225dd (movR32M32LowEffect 0x1225dd 1 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 2069) (.exec 0x1225dd (LoadPre 0x1225dd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1225dd + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1225dd 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2070) (.out 0x1225e4 (rolR32Effect 0x1225e4 3 1 25) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2068]
    (.letOp (n := 2071) (.exec 0x1225e4 (fun s => s.RIP = 0x1225e4) (rolR32Effect 0x1225e4 3 1 25) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2068]
    (b_l121930_52))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_51 : List UInt8 :=
  [0x05, 0xCC, 0xA1, 0x0C, 0x24, 0x44, 0x89, 0xFA, 0xC1, 0xC2, 0x13, 0x31, 0xCA, 0x44, 0x89, 0xF9,
    0xC1, 0xC1, 0x0A, 0x31, 0xD1, 0x44, 0x89, 0xCA, 0x48, 0x8B, 0x5C, 0x24, 0x70, 0x21, 0xDA, 0x45,
    0x89, 0xCC, 0x41, 0x31, 0xDC, 0x45, 0x21, 0xFC, 0x41, 0x31, 0xD4, 0x41, 0x01, 0xCC, 0x4C, 0x8B,
    0x6C, 0x24, 0x78, 0x41, 0x01, 0xC5, 0x41, 0x01, 0xC4, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00,
    0xC1, 0xC1, 0x19] ++ bytes_l121930_52

theorem code_l121930_51 : ∀ x ∈ codeRange 0x1225a4 bytes_l121930_51, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x225a4 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_52

def b_l121930_50 : Block Op Label signature Reg.count 1992 :=
  .letOp (n := 1992) (.out 0x122569 (movR32R32Effect 0x122569 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[1932]
    (.letOp (n := 1993) (.exec 0x122569 (fun s => s.RIP = 0x122569) (movR32R32Effect 0x122569 3 0 14) (Reg.operands [.gpr 14] [])) #v[1932]
    (.letOp (n := 1994) (.out 0x12256c (rolR32Effect 0x12256c 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1992]
    (.letOp (n := 1995) (.exec 0x12256c (fun s => s.RIP = 0x12256c) (rolR32Effect 0x12256c 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1992]
    (.letOp (n := 1996) (.out 0x12256f (movR32R32Effect 0x12256f 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[1932]
    (.letOp (n := 1997) (.exec 0x12256f (fun s => s.RIP = 0x12256f) (movR32R32Effect 0x12256f 3 1 14) (Reg.operands [.gpr 14] [])) #v[1932]
    (.letOp (n := 1998) (.out 0x122572 (rolR32Effect 0x122572 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1996]
    (.letOp (n := 1999) (.exec 0x122572 (fun s => s.RIP = 0x122572) (rolR32Effect 0x122572 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1996]
    (.letOp (n := 2000) (.out 0x122575 (xorR32R32Effect 0x122575 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1998, 1994]
    (.letOp (n := 2001) (.exec 0x122575 (fun s => s.RIP = 0x122575) (xorR32R32Effect 0x122575 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1998, 1994]
    (.letOp (n := 2002) (.out 0x122577 (movR32R32Effect 0x122577 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[1932]
    (.letOp (n := 2003) (.exec 0x122577 (fun s => s.RIP = 0x122577) (movR32R32Effect 0x122577 3 0 14) (Reg.operands [.gpr 14] [])) #v[1932]
    (.letOp (n := 2004) (.out 0x12257a (rolR32Effect 0x12257a 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2002]
    (.letOp (n := 2005) (.exec 0x12257a (fun s => s.RIP = 0x12257a) (rolR32Effect 0x12257a 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2002]
    (.letOp (n := 2006) (.out 0x12257d (xorR32R32Effect 0x12257d 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2004, 2000]
    (.letOp (n := 2007) (.exec 0x12257d (fun s => s.RIP = 0x12257d) (xorR32R32Effect 0x12257d 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2004, 2000]
    (.letOp (n := 2008) (.out 0x12257f (movR32R32Effect 0x12257f 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11] []) (.reg (.gpr 1))) #v[1850]
    (.letOp (n := 2009) (.exec 0x12257f (fun s => s.RIP = 0x12257f) (movR32R32Effect 0x12257f 3 1 11) (Reg.operands [.gpr 11] [])) #v[1850]
    (.letOp (n := 2010) (.out 0x122582 (xorR32R32Effect 0x122582 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[2008, 1874]
    (.letOp (n := 2011) (.exec 0x122582 (fun s => s.RIP = 0x122582) (xorR32R32Effect 0x122582 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[2008, 1874]
    (.letOp (n := 2012) (.out 0x122584 (andR32R32Effect 0x122584 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[2010, 1932]
    (.letOp (n := 2013) (.exec 0x122584 (fun s => s.RIP = 0x122584) (andR32R32Effect 0x122584 3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[2010, 1932]
    (.letOp (n := 2014) (.out 0x122587 (xorR32R32Effect 0x122587 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[2012, 1874]
    (.letOp (n := 2015) (.exec 0x122587 (fun s => s.RIP = 0x122587) (xorR32R32Effect 0x122587 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[2012, 1874]
    (.letOp (n := 2016) (.out 0x122589 (movR64R64Effect 0x122589 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[1874]
    (.letOp (n := 2017) (.exec 0x122589 (fun s => s.RIP = 0x122589) (movR64R64Effect 0x122589 7 3) (Reg.operands [.gpr 3] [])) #v[1874]
    (.letOp (n := 2018) (.out 0x12258c (movR64M64Effect 0x12258c 2 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 2019) (.exec 0x12258c (LoadPre 0x12258c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x12258c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12258c 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2020) (.out 0x122594 (addR32R32Effect 0x122594 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[2018, 1990]
    (.letOp (n := 2021) (.exec 0x122594 (fun s => s.RIP = 0x122594) (addR32R32Effect 0x122594 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2018, 1990]
    (.letOp (n := 2022) (.out 0x122597 (addR32R32Effect 0x122597 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[2020, 2014]
    (.letOp (n := 2023) (.exec 0x122597 (fun s => s.RIP = 0x122597) (addR32R32Effect 0x122597 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2020, 2014]
    (.letOp (n := 2024) (.out 0x122599 (movR64R64Effect 0x122599 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 13] []) (.reg (.gpr 15))) #v[1938]
    (.letOp (n := 2025) (.exec 0x122599 (fun s => s.RIP = 0x122599) (movR64R64Effect 0x122599 15 13) (Reg.operands [.gpr 13] [])) #v[1938]
    (.letOp (n := 2026) (.out 0x12259c (movR32R32Effect 0x12259c 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[2024]
    (.letOp (n := 2027) (.exec 0x12259c (fun s => s.RIP = 0x12259c) (movR32R32Effect 0x12259c 3 1 15) (Reg.operands [.gpr 15] [])) #v[2024]
    (.letOp (n := 2028) (.out 0x12259f (rolR32Effect 0x12259f 3 1 30) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2026]
    (.letOp (n := 2029) (.exec 0x12259f (fun s => s.RIP = 0x12259f) (rolR32Effect 0x12259f 3 1 30) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2026]
    (.letOp (n := 2030) (.out 0x1225a2 (addR32R32Effect 0x1225a2 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[2006, 2022]
    (.letOp (n := 2031) (.exec 0x1225a2 (fun s => s.RIP = 0x1225a2) (addR32R32Effect 0x1225a2 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[2006, 2022]
    (b_l121930_51))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_50 : List UInt8 :=
  [0x44, 0x89, 0xF0, 0xC1, 0xC0, 0x1A, 0x44, 0x89, 0xF1, 0xC1, 0xC1, 0x15, 0x31, 0xC1, 0x44, 0x89,
    0xF0, 0xC1, 0xC0, 0x07, 0x31, 0xC8, 0x44, 0x89, 0xD9, 0x31, 0xD9, 0x44, 0x21, 0xF1, 0x31, 0xD9,
    0x48, 0x89, 0xDF, 0x48, 0x8B, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x44, 0x01, 0xC2, 0x01, 0xCA,
    0x4D, 0x89, 0xEF, 0x44, 0x89, 0xF9, 0xC1, 0xC1, 0x1E, 0x01, 0xD0] ++ bytes_l121930_51

theorem code_l121930_50 : ∀ x ∈ codeRange 0x122569 bytes_l121930_50, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22569 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_51

def b_l121930_49 : Block Op Label signature Reg.count 1954 :=
  .letOp (n := 1954) (.out 0x12252d (rolR32Effect 0x12252d 3 0 25) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1952]
    (.letOp (n := 1955) (.exec 0x12252d (fun s => s.RIP = 0x12252d) (rolR32Effect 0x12252d 3 0 25) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1952]
    (.letOp (n := 1956) (.out 0x122530 (xorR32R32Effect 0x122530 3 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[1950, 1944]
    (.letOp (n := 1957) (.exec 0x122530 (fun s => s.RIP = 0x122530) (xorR32R32Effect 0x122530 3 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[1950, 1944]
    (.letOp (n := 1958) (.out 0x122533 (movR32R32Effect 0x122533 3 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[1864]
    (.letOp (n := 1959) (.exec 0x122533 (fun s => s.RIP = 0x122533) (movR32R32Effect 0x122533 3 15 8) (Reg.operands [.gpr 8] [])) #v[1864]
    (.letOp (n := 1960) (.out 0x122536 (rolR32Effect 0x122536 4 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[1958]
    (.letOp (n := 1961) (.exec 0x122536 (fun s => s.RIP = 0x122536) (rolR32Effect 0x122536 4 15 14) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1958]
    (.letOp (n := 1962) (.out 0x12253a (xorR32R32Effect 0x12253a 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[1948, 1942]
    (.letOp (n := 1963) (.exec 0x12253a (fun s => s.RIP = 0x12253a) (xorR32R32Effect 0x12253a 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1948, 1942]
    (.letOp (n := 1964) (.out 0x12253c (xorR32R32Effect 0x12253c 3 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[1960, 1954]
    (.letOp (n := 1965) (.exec 0x12253c (fun s => s.RIP = 0x12253c) (xorR32R32Effect 0x12253c 3 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[1960, 1954]
    (.letOp (n := 1966) (.out 0x12253f (movR32R32Effect 0x12253f 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[1864]
    (.letOp (n := 1967) (.exec 0x12253f (fun s => s.RIP = 0x12253f) (movR32R32Effect 0x12253f 3 0 8) (Reg.operands [.gpr 8] [])) #v[1864]
    (.letOp (n := 1968) (.out 0x122542 (movR64R64Effect 0x122542 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[1864]
    (.letOp (n := 1969) (.exec 0x122542 (fun s => s.RIP = 0x122542) (movR64R64Effect 0x122542 6 8) (Reg.operands [.gpr 8] [])) #v[1864]
    (.letOp (n := 1970) (.out 0x122545 (shrR32Effect 0x122545 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1966]
    (.letOp (n := 1971) (.exec 0x122545 (fun s => s.RIP = 0x122545) (shrR32Effect 0x122545 3 0 3) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1966]
    (.letOp (n := 1972) (.out 0x122548 (xorR32R32Effect 0x122548 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[1970, 1964]
    (.letOp (n := 1973) (.exec 0x122548 (fun s => s.RIP = 0x122548) (xorR32R32Effect 0x122548 3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[1970, 1964]
    (.letOp (n := 1974) (.exec 0x12254b (StorePre 0x12254b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x12254b + BitVec.ofNat 64 4)) 4) (addMREffect 0x12254b 4 32 7 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1818, 4]
    (.letOp (n := 1975) (.out 0x12254f (addR32R32Effect 0x12254f 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[1972, 1818]
    (.letOp (n := 1976) (.exec 0x12254f (fun s => s.RIP = 0x12254f) (addR32R32Effect 0x12254f 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[1972, 1818]
    (.letOp (n := 1977) (.exec 0x122551 (StorePre 0x122551 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x122551 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x122551 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1975, 4]
    (.letOp (n := 1978) (.out 0x122555 (movR32R32Effect 0x122555 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1818]
    (.letOp (n := 1979) (.exec 0x122555 (fun s => s.RIP = 0x122555) (movR32R32Effect 0x122555 2 0 7) (Reg.operands [.gpr 7] [])) #v[1818]
    (.letOp (n := 1980) (.out 0x122557 (shrR32Effect 0x122557 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1978]
    (.letOp (n := 1981) (.exec 0x122557 (fun s => s.RIP = 0x122557) (shrR32Effect 0x122557 3 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1978]
    (.letOp (n := 1982) (.out 0x12255a (xorR32R32Effect 0x12255a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1980, 1962]
    (.letOp (n := 1983) (.exec 0x12255a (fun s => s.RIP = 0x12255a) (xorR32R32Effect 0x12255a 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1980, 1962]
    (.letOp (n := 1984) (.out 0x12255c (movR64M64Effect 0x12255c 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 1985) (.exec 0x12255c (LoadPre 0x12255c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12255c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12255c 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1986) (.out 0x122561 (addR32R32Effect 0x122561 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[1984, 1956]
    (.letOp (n := 1987) (.exec 0x122561 (fun s => s.RIP = 0x122561) (addR32R32Effect 0x122561 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[1984, 1956]
    (.letOp (n := 1988) (.out 0x122564 (addR32R32Effect 0x122564 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1986, 1982]
    (.letOp (n := 1989) (.exec 0x122564 (fun s => s.RIP = 0x122564) (addR32R32Effect 0x122564 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1986, 1982]
    (.letOp (n := 1990) (.out 0x122566 (movR64R64Effect 0x122566 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1988]
    (.letOp (n := 1991) (.exec 0x122566 (fun s => s.RIP = 0x122566) (movR64R64Effect 0x122566 8 1) (Reg.operands [.gpr 1] [])) #v[1988]
    (b_l121930_50))))))))))))))))))))))))))))))))))))))

def bytes_l121930_49 : List UInt8 :=
  [0xC1, 0xC0, 0x19, 0x45, 0x31, 0xE2, 0x45, 0x89, 0xC7, 0x41, 0xC1, 0xC7, 0x0E, 0x31, 0xD1, 0x41,
    0x31, 0xC7, 0x44, 0x89, 0xC0, 0x4C, 0x89, 0xC6, 0xC1, 0xE8, 0x03, 0x44, 0x31, 0xF8, 0x01, 0x7C,
    0x24, 0x34, 0x01, 0xF8, 0x89, 0x44, 0x24, 0x08, 0x89, 0xF8, 0xC1, 0xE8, 0x0A, 0x31, 0xC8, 0x48,
    0x8B, 0x4C, 0x24, 0x48, 0x44, 0x01, 0xD1, 0x01, 0xC1, 0x49, 0x89, 0xC8] ++ bytes_l121930_50

theorem code_l121930_49 : ∀ x ∈ codeRange 0x12252d bytes_l121930_49, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2252d 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_50

def b_l121930_48 : Block Op Label signature Reg.count 1914 :=
  .letOp (n := 1914) (.out 0x1224ea (movR32R32Effect 0x1224ea 3 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[1912]
    (.letOp (n := 1915) (.exec 0x1224ea (fun s => s.RIP = 0x1224ea) (movR32R32Effect 0x1224ea 3 15 6) (Reg.operands [.gpr 6] [])) #v[1912]
    (.letOp (n := 1916) (.out 0x1224ed (movR64M64Effect 0x1224ed 14 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 1917) (.exec 0x1224ed (LoadPre 0x1224ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1224ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1224ed 14 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1918) (.out 0x1224f2 (andR32R32Effect 0x1224f2 3 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[1914, 1916]
    (.letOp (n := 1919) (.exec 0x1224f2 (fun s => s.RIP = 0x1224f2) (andR32R32Effect 0x1224f2 3 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[1914, 1916]
    (.letOp (n := 1920) (.out 0x1224f5 (movR32R32Effect 0x1224f5 3 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[1912]
    (.letOp (n := 1921) (.exec 0x1224f5 (fun s => s.RIP = 0x1224f5) (movR32R32Effect 0x1224f5 3 13 6) (Reg.operands [.gpr 6] [])) #v[1912]
    (.letOp (n := 1922) (.out 0x1224f8 (xorR32R32Effect 0x1224f8 3 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[1920, 1916]
    (.letOp (n := 1923) (.exec 0x1224f8 (fun s => s.RIP = 0x1224f8) (xorR32R32Effect 0x1224f8 3 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[1920, 1916]
    (.letOp (n := 1924) (.out 0x1224fb (andR32R32Effect 0x1224fb 3 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[1922, 1894]
    (.letOp (n := 1925) (.exec 0x1224fb (fun s => s.RIP = 0x1224fb) (andR32R32Effect 0x1224fb 3 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[1922, 1894]
    (.letOp (n := 1926) (.out 0x1224fe (xorR32R32Effect 0x1224fe 3 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[1924, 1918]
    (.letOp (n := 1927) (.exec 0x1224fe (fun s => s.RIP = 0x1224fe) (xorR32R32Effect 0x1224fe 3 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[1924, 1918]
    (.letOp (n := 1928) (.out 0x122501 (addR32R32Effect 0x122501 3 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[1926, 1910]
    (.letOp (n := 1929) (.exec 0x122501 (fun s => s.RIP = 0x122501) (addR32R32Effect 0x122501 3 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[1926, 1910]
    (.letOp (n := 1930) (.out 0x122504 (movR64M64Effect 0x122504 14 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 1931) (.exec 0x122504 (LoadPre 0x122504 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x122504 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x122504 14 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1932) (.out 0x12250c (addR32R32Effect 0x12250c 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[1930, 1892]
    (.letOp (n := 1933) (.exec 0x12250c (fun s => s.RIP = 0x12250c) (addR32R32Effect 0x12250c 3 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1930, 1892]
    (.letOp (n := 1934) (.out 0x12250f (rolR32Effect 0x12250f 3 1 25) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1743]
    (.letOp (n := 1935) (.exec 0x12250f (fun s => s.RIP = 0x12250f) (rolR32Effect 0x12250f 3 1 25) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1743]
    (.letOp (n := 1936) (.out 0x122512 (rolR32Effect 0x122512 4 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1745]
    (.letOp (n := 1937) (.exec 0x122512 (fun s => s.RIP = 0x122512) (rolR32Effect 0x122512 4 12 14) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1745]
    (.letOp (n := 1938) (.out 0x122516 (addR32R32Effect 0x122516 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[1928, 1892]
    (.letOp (n := 1939) (.exec 0x122516 (fun s => s.RIP = 0x122516) (addR32R32Effect 0x122516 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1928, 1892]
    (.letOp (n := 1940) (.out 0x122519 (movR32R32Effect 0x122519 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[1818]
    (.letOp (n := 1941) (.exec 0x122519 (fun s => s.RIP = 0x122519) (movR32R32Effect 0x122519 2 2 7) (Reg.operands [.gpr 7] [])) #v[1818]
    (.letOp (n := 1942) (.out 0x12251b (rolR32Effect 0x12251b 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1940]
    (.letOp (n := 1943) (.exec 0x12251b (fun s => s.RIP = 0x12251b) (rolR32Effect 0x12251b 3 2 15) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1940]
    (.letOp (n := 1944) (.out 0x12251e (xorR32R32Effect 0x12251e 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[1936, 1934]
    (.letOp (n := 1945) (.exec 0x12251e (fun s => s.RIP = 0x12251e) (xorR32R32Effect 0x12251e 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[1936, 1934]
    (.letOp (n := 1946) (.out 0x122521 (movR32R32Effect 0x122521 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[1818]
    (.letOp (n := 1947) (.exec 0x122521 (fun s => s.RIP = 0x122521) (movR32R32Effect 0x122521 2 1 7) (Reg.operands [.gpr 7] [])) #v[1818]
    (.letOp (n := 1948) (.out 0x122523 (rolR32Effect 0x122523 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1946]
    (.letOp (n := 1949) (.exec 0x122523 (fun s => s.RIP = 0x122523) (rolR32Effect 0x122523 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1946]
    (.letOp (n := 1950) (.out 0x122526 (shrR32Effect 0x122526 4 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[1747]
    (.letOp (n := 1951) (.exec 0x122526 (fun s => s.RIP = 0x122526) (shrR32Effect 0x122526 4 10 3) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1747]
    (.letOp (n := 1952) (.out 0x12252a (movR32R32Effect 0x12252a 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[1864]
    (.letOp (n := 1953) (.exec 0x12252a (fun s => s.RIP = 0x12252a) (movR32R32Effect 0x12252a 3 0 8) (Reg.operands [.gpr 8] [])) #v[1864]
    (b_l121930_49))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_48 : List UInt8 :=
  [0x41, 0x89, 0xF7, 0x4C, 0x8B, 0x74, 0x24, 0x78, 0x45, 0x21, 0xF7, 0x41, 0x89, 0xF5, 0x45, 0x31,
    0xF5, 0x45, 0x21, 0xCD, 0x45, 0x31, 0xFD, 0x41, 0x01, 0xD5, 0x4C, 0x8B, 0xB4, 0x24, 0xD8, 0x00,
    0x00, 0x00, 0x41, 0x01, 0xC6, 0xC1, 0xC1, 0x19, 0x41, 0xC1, 0xC4, 0x0E, 0x41, 0x01, 0xC5, 0x89,
    0xFA, 0xC1, 0xC2, 0x0F, 0x41, 0x31, 0xCC, 0x89, 0xF9, 0xC1, 0xC1, 0x0D, 0x41, 0xC1, 0xEA, 0x03,
    0x44, 0x89, 0xC0] ++ bytes_l121930_49

theorem code_l121930_48 : ∀ x ∈ codeRange 0x1224ea bytes_l121930_48, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x224ea 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_49

def b_l121930_47 : Block Op Label signature Reg.count 1874 :=
  .letOp (n := 1874) (.out 0x12249f (movR64M64Effect 0x12249f 3 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1875) (.exec 0x12249f (LoadPre 0x12249f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x12249f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12249f 3 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1876) (.out 0x1224a7 (movR32R32Effect 0x1224a7 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[1874]
    (.letOp (n := 1877) (.exec 0x1224a7 (fun s => s.RIP = 0x1224a7) (movR32R32Effect 0x1224a7 2 0 3) (Reg.operands [.gpr 3] [])) #v[1874]
    (.letOp (n := 1878) (.out 0x1224a9 (movR64M64Effect 0x1224a9 6 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 1879) (.exec 0x1224a9 (LoadPre 0x1224a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1224a9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1224a9 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1880) (.out 0x1224b1 (xorR32R32Effect 0x1224b1 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1876, 1878]
    (.letOp (n := 1881) (.exec 0x1224b1 (fun s => s.RIP = 0x1224b1) (xorR32R32Effect 0x1224b1 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1876, 1878]
    (.letOp (n := 1882) (.out 0x1224b3 (andR32R32Effect 0x1224b3 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[1880, 1850]
    (.letOp (n := 1883) (.exec 0x1224b3 (fun s => s.RIP = 0x1224b3) (andR32R32Effect 0x1224b3 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[1880, 1850]
    (.letOp (n := 1884) (.out 0x1224b6 (xorR32R32Effect 0x1224b6 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1882, 1878]
    (.letOp (n := 1885) (.exec 0x1224b6 (fun s => s.RIP = 0x1224b6) (xorR32R32Effect 0x1224b6 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1882, 1878]
    (.letOp (n := 1886) (.out 0x1224b8 (addR32R32Effect 0x1224b8 3 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[1250, 1864]
    (.letOp (n := 1887) (.exec 0x1224b8 (fun s => s.RIP = 0x1224b8) (addR32R32Effect 0x1224b8 3 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[1250, 1864]
    (.letOp (n := 1888) (.out 0x1224bb (addR32R32Effect 0x1224bb 3 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[1886, 1884]
    (.letOp (n := 1889) (.exec 0x1224bb (fun s => s.RIP = 0x1224bb) (addR32R32Effect 0x1224bb 3 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[1886, 1884]
    (.letOp (n := 1890) (.out 0x1224be (leaR32Effect 0x1224be 4 0 (.sib 2 (some 15) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 15] []) (.reg (.gpr 0))) #v[1872, 1888]
    (.letOp (n := 1891) (.exec 0x1224be (fun s => s.RIP = 0x1224be) (leaR32Effect 0x1224be 4 0 (.sib 2 (some 15) 0 .none)) (Reg.operands [.gpr 2, .gpr 15] [])) #v[1872, 1888]
    (.letOp (n := 1892) (.out 0x1224c2 (addEaxImm32Effect 0x1224c2 0xfc19dc6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1890]
    (.letOp (n := 1893) (.exec 0x1224c2 (fun s => s.RIP = 0x1224c2) (addEaxImm32Effect 0x1224c2 0xfc19dc6) (Reg.operands [.gpr 0] [])) #v[1890]
    (.letOp (n := 1894) (.out 0x1224c7 (movR64M64Effect 0x1224c7 9 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 1895) (.exec 0x1224c7 (LoadPre 0x1224c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1224c7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1224c7 9 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1896) (.out 0x1224cf (movR32R32Effect 0x1224cf 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[1894]
    (.letOp (n := 1897) (.exec 0x1224cf (fun s => s.RIP = 0x1224cf) (movR32R32Effect 0x1224cf 3 2 9) (Reg.operands [.gpr 9] [])) #v[1894]
    (.letOp (n := 1898) (.out 0x1224d2 (rolR32Effect 0x1224d2 3 2 30) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1896]
    (.letOp (n := 1899) (.exec 0x1224d2 (fun s => s.RIP = 0x1224d2) (rolR32Effect 0x1224d2 3 2 30) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1896]
    (.letOp (n := 1900) (.out 0x1224d5 (movR32R32Effect 0x1224d5 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[1894]
    (.letOp (n := 1901) (.exec 0x1224d5 (fun s => s.RIP = 0x1224d5) (movR32R32Effect 0x1224d5 3 6 9) (Reg.operands [.gpr 9] [])) #v[1894]
    (.letOp (n := 1902) (.out 0x1224d8 (rolR32Effect 0x1224d8 3 6 19) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1900]
    (.letOp (n := 1903) (.exec 0x1224d8 (fun s => s.RIP = 0x1224d8) (rolR32Effect 0x1224d8 3 6 19) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1900]
    (.letOp (n := 1904) (.out 0x1224db (xorR32R32Effect 0x1224db 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[1902, 1898]
    (.letOp (n := 1905) (.exec 0x1224db (fun s => s.RIP = 0x1224db) (xorR32R32Effect 0x1224db 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[1902, 1898]
    (.letOp (n := 1906) (.out 0x1224dd (movR32R32Effect 0x1224dd 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[1894]
    (.letOp (n := 1907) (.exec 0x1224dd (fun s => s.RIP = 0x1224dd) (movR32R32Effect 0x1224dd 3 2 9) (Reg.operands [.gpr 9] [])) #v[1894]
    (.letOp (n := 1908) (.out 0x1224e0 (rolR32Effect 0x1224e0 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1906]
    (.letOp (n := 1909) (.exec 0x1224e0 (fun s => s.RIP = 0x1224e0) (rolR32Effect 0x1224e0 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1906]
    (.letOp (n := 1910) (.out 0x1224e3 (xorR32R32Effect 0x1224e3 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[1908, 1904]
    (.letOp (n := 1911) (.exec 0x1224e3 (fun s => s.RIP = 0x1224e3) (xorR32R32Effect 0x1224e3 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[1908, 1904]
    (.letOp (n := 1912) (.out 0x1224e5 (movR64M64Effect 0x1224e5 6 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 1913) (.exec 0x1224e5 (LoadPre 0x1224e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1224e5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1224e5 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l121930_48))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_47 : List UInt8 :=
  [0x48, 0x8B, 0x9C, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x89, 0xD8, 0x48, 0x8B, 0xB4, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x31, 0xF0, 0x44, 0x21, 0xD8, 0x31, 0xF0, 0x45, 0x01, 0xC7, 0x41, 0x01, 0xC7, 0x42,
    0x8D, 0x04, 0x3A, 0x05, 0xC6, 0x9D, 0xC1, 0x0F, 0x4C, 0x8B, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00,
    0x44, 0x89, 0xCA, 0xC1, 0xC2, 0x1E, 0x44, 0x89, 0xCE, 0xC1, 0xC6, 0x13, 0x31, 0xD6, 0x44, 0x89,
    0xCA, 0xC1, 0xC2, 0x0A, 0x31, 0xF2, 0x48, 0x8B, 0x74, 0x24, 0x70] ++ bytes_l121930_48

theorem code_l121930_47 : ∀ x ∈ codeRange 0x12249f bytes_l121930_47, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2249f 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_48

def b_l121930_46 : Block Op Label signature Reg.count 1836 :=
  .letOp (n := 1836) (.out 0x122455 (addR32M32Effect 0x122455 5 9 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[1816, 4]
    (.letOp (n := 1837) (.exec 0x122455 (LoadPre 0x122455 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x122455 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x122455 5 9 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[1816, 4]
    (.letOp (n := 1838) (.out 0x12245a (addR32R32Effect 0x12245a 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[1836, 1689]
    (.letOp (n := 1839) (.exec 0x12245a (fun s => s.RIP = 0x12245a) (addR32R32Effect 0x12245a 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[1836, 1689]
    (.letOp (n := 1840) (.exec 0x12245d (StorePre 0x12245d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12245d + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x12245d 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[1838, 4]
    (.letOp (n := 1841) (.out 0x122462 (addR32R32Effect 0x122462 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[1834, 1689]
    (.letOp (n := 1842) (.exec 0x122462 (fun s => s.RIP = 0x122462) (addR32R32Effect 0x122462 3 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[1834, 1689]
    (.letOp (n := 1843) (.exec 0x122465 (StorePre 0x122465 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x122465 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x122465 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1841, 4]
    (.letOp (n := 1844) (.out 0x122469 (movR32R32Effect 0x122469 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[1689]
    (.letOp (n := 1845) (.exec 0x122469 (fun s => s.RIP = 0x122469) (movR32R32Effect 0x122469 3 2 8) (Reg.operands [.gpr 8] [])) #v[1689]
    (.letOp (n := 1846) (.out 0x12246c (shrR32Effect 0x12246c 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1844]
    (.letOp (n := 1847) (.exec 0x12246c (fun s => s.RIP = 0x12246c) (shrR32Effect 0x12246c 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1844]
    (.letOp (n := 1848) (.out 0x12246f (xorR32M32LowEffect 0x12246f 2 (.sib 4 none 0 (.d32 0xb4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[1846, 4]
    (.letOp (n := 1849) (.exec 0x12246f (LoadPre 0x12246f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x12246f + BitVec.ofNat 64 7)) 4) (xorR32M32LowEffect 0x12246f 2 (.sib 4 none 0 (.d32 0xb4))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1846, 4]
    (.letOp (n := 1850) (.out 0x122476 (movR64M64Effect 0x122476 11 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 1851) (.exec 0x122476 (LoadPre 0x122476 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x122476 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x122476 11 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1852) (.out 0x12247b (movR32R32Effect 0x12247b 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[1850]
    (.letOp (n := 1853) (.exec 0x12247b (fun s => s.RIP = 0x12247b) (movR32R32Effect 0x12247b 3 6 11) (Reg.operands [.gpr 11] [])) #v[1850]
    (.letOp (n := 1854) (.out 0x12247e (rolR32Effect 0x12247e 3 6 26) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1852]
    (.letOp (n := 1855) (.exec 0x12247e (fun s => s.RIP = 0x12247e) (rolR32Effect 0x12247e 3 6 26) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1852]
    (.letOp (n := 1856) (.out 0x122481 (movR64R64Effect 0x122481 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[1778]
    (.letOp (n := 1857) (.exec 0x122481 (fun s => s.RIP = 0x122481) (movR64R64Effect 0x122481 8 3) (Reg.operands [.gpr 3] [])) #v[1778]
    (.letOp (n := 1858) (.out 0x122484 (addR32M32Effect 0x122484 8 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[1856, 4]
    (.letOp (n := 1859) (.exec 0x122484 (LoadPre 0x122484 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x122484 + BitVec.ofNat 64 8)) 4) (addR32M32Effect 0x122484 8 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1856, 4]
    (.letOp (n := 1860) (.out 0x12248c (movR32R32Effect 0x12248c 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[1850]
    (.letOp (n := 1861) (.exec 0x12248c (fun s => s.RIP = 0x12248c) (movR32R32Effect 0x12248c 3 0 11) (Reg.operands [.gpr 11] [])) #v[1850]
    (.letOp (n := 1862) (.out 0x12248f (rolR32Effect 0x12248f 3 0 21) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1860]
    (.letOp (n := 1863) (.exec 0x12248f (fun s => s.RIP = 0x12248f) (rolR32Effect 0x12248f 3 0 21) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1860]
    (.letOp (n := 1864) (.out 0x122492 (addR32R32Effect 0x122492 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[1858, 1848]
    (.letOp (n := 1865) (.exec 0x122492 (fun s => s.RIP = 0x122492) (addR32R32Effect 0x122492 3 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[1858, 1848]
    (.letOp (n := 1866) (.out 0x122495 (movR32R32Effect 0x122495 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11] []) (.reg (.gpr 2))) #v[1850]
    (.letOp (n := 1867) (.exec 0x122495 (fun s => s.RIP = 0x122495) (movR32R32Effect 0x122495 3 2 11) (Reg.operands [.gpr 11] [])) #v[1850]
    (.letOp (n := 1868) (.out 0x122498 (rolR32Effect 0x122498 3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1866]
    (.letOp (n := 1869) (.exec 0x122498 (fun s => s.RIP = 0x122498) (rolR32Effect 0x122498 3 2 7) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1866]
    (.letOp (n := 1870) (.out 0x12249b (xorR32R32Effect 0x12249b 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1862, 1854]
    (.letOp (n := 1871) (.exec 0x12249b (fun s => s.RIP = 0x12249b) (xorR32R32Effect 0x12249b 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1862, 1854]
    (.letOp (n := 1872) (.out 0x12249d (xorR32R32Effect 0x12249d 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1868, 1870]
    (.letOp (n := 1873) (.exec 0x12249d (fun s => s.RIP = 0x12249d) (xorR32R32Effect 0x12249d 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1868, 1870]
    (b_l121930_47))))))))))))))))))))))))))))))))))))))

def bytes_l121930_46 : List UInt8 :=
  [0x44, 0x03, 0x4C, 0x24, 0x14, 0x45, 0x01, 0xC1, 0x44, 0x89, 0x4C, 0x24, 0x60, 0x44, 0x01, 0xC0,
    0x89, 0x44, 0x24, 0x0C, 0x44, 0x89, 0xC2, 0xC1, 0xEA, 0x0A, 0x33, 0x94, 0x24, 0xB4, 0x00, 0x00,
    0x00, 0x4C, 0x8B, 0x5C, 0x24, 0x58, 0x44, 0x89, 0xDE, 0xC1, 0xC6, 0x1A, 0x49, 0x89, 0xD8, 0x44,
    0x03, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x44, 0x89, 0xD8, 0xC1, 0xC0, 0x15, 0x41, 0x01, 0xD0,
    0x44, 0x89, 0xDA, 0xC1, 0xC2, 0x07, 0x31, 0xF0, 0x31, 0xC2] ++ bytes_l121930_47

theorem code_l121930_46 : ∀ x ∈ codeRange 0x122455 bytes_l121930_46, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22455 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_47

def b_l121930_45 : Block Op Label signature Reg.count 1798 :=
  .letOp (n := 1798) (.out 0x122413 (addR32R32Effect 0x122413 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[1794, 1796]
    (.letOp (n := 1799) (.exec 0x122413 (fun s => s.RIP = 0x122413) (addR32R32Effect 0x122413 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[1794, 1796]
    (.letOp (n := 1800) (.exec 0x122416 (StorePre 0x122416 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x122416 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x122416 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[1798, 4]
    (.letOp (n := 1801) (.out 0x12241a (shrR32Effect 0x12241a 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1796]
    (.letOp (n := 1802) (.exec 0x12241a (fun s => s.RIP = 0x12241a) (shrR32Effect 0x12241a 3 0 3) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1796]
    (.letOp (n := 1803) (.out 0x12241d (xorR32M32LowEffect 0x12241d 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1801, 4]
    (.letOp (n := 1804) (.exec 0x12241d (LoadPre 0x12241d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x12241d + BitVec.ofNat 64 7)) 4) (xorR32M32LowEffect 0x12241d 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1801, 4]
    (.letOp (n := 1805) (.out 0x122424 (movR32M32LowEffect 0x122424 2 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 1806) (.exec 0x122424 (LoadPre 0x122424 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x122424 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x122424 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1807) (.out 0x122428 (addR32R32Effect 0x122428 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1803, 1805]
    (.letOp (n := 1808) (.exec 0x122428 (fun s => s.RIP = 0x122428) (addR32R32Effect 0x122428 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1803, 1805]
    (.letOp (n := 1809) (.exec 0x12242a (StorePre 0x12242a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x12242a + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x12242a 0 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1807, 4]
    (.letOp (n := 1810) (.out 0x12242e (movR32R32Effect 0x12242e 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[1805]
    (.letOp (n := 1811) (.exec 0x12242e (fun s => s.RIP = 0x12242e) (movR32R32Effect 0x12242e 2 0 2) (Reg.operands [.gpr 2] [])) #v[1805]
    (.letOp (n := 1812) (.out 0x122430 (shrR32Effect 0x122430 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1810]
    (.letOp (n := 1813) (.exec 0x122430 (fun s => s.RIP = 0x122430) (shrR32Effect 0x122430 3 0 3) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1810]
    (.letOp (n := 1814) (.out 0x122433 (xorR32M32LowEffect 0x122433 0 (.sib 4 none 0 (.d32 0xa4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[1812, 4]
    (.letOp (n := 1815) (.exec 0x122433 (LoadPre 0x122433 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x122433 + BitVec.ofNat 64 7)) 4) (xorR32M32LowEffect 0x122433 0 (.sib 4 none 0 (.d32 0xa4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1812, 4]
    (.letOp (n := 1816) (.out 0x12243a (movR32R32Effect 0x12243a 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[1814]
    (.letOp (n := 1817) (.exec 0x12243a (fun s => s.RIP = 0x12243a) (movR32R32Effect 0x12243a 3 9 0) (Reg.operands [.gpr 0] [])) #v[1814]
    (.letOp (n := 1818) (.out 0x12243d (movR64M64Effect 0x12243d 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 1819) (.exec 0x12243d (LoadPre 0x12243d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12243d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12243d 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1820) (.out 0x122442 (movR32R32Effect 0x122442 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[1818]
    (.letOp (n := 1821) (.exec 0x122442 (fun s => s.RIP = 0x122442) (movR32R32Effect 0x122442 2 2 7) (Reg.operands [.gpr 7] [])) #v[1818]
    (.letOp (n := 1822) (.out 0x122444 (rolR32Effect 0x122444 3 2 25) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1820]
    (.letOp (n := 1823) (.exec 0x122444 (fun s => s.RIP = 0x122444) (rolR32Effect 0x122444 3 2 25) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1820]
    (.letOp (n := 1824) (.out 0x122447 (movR32R32Effect 0x122447 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[1818]
    (.letOp (n := 1825) (.exec 0x122447 (fun s => s.RIP = 0x122447) (movR32R32Effect 0x122447 2 6 7) (Reg.operands [.gpr 7] [])) #v[1818]
    (.letOp (n := 1826) (.out 0x122449 (rolR32Effect 0x122449 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1824]
    (.letOp (n := 1827) (.exec 0x122449 (fun s => s.RIP = 0x122449) (rolR32Effect 0x122449 3 6 14) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1824]
    (.letOp (n := 1828) (.out 0x12244c (xorR32R32Effect 0x12244c 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[1826, 1822]
    (.letOp (n := 1829) (.exec 0x12244c (fun s => s.RIP = 0x12244c) (xorR32R32Effect 0x12244c 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[1826, 1822]
    (.letOp (n := 1830) (.out 0x12244e (movR32R32Effect 0x12244e 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1818]
    (.letOp (n := 1831) (.exec 0x12244e (fun s => s.RIP = 0x12244e) (movR32R32Effect 0x12244e 2 0 7) (Reg.operands [.gpr 7] [])) #v[1818]
    (.letOp (n := 1832) (.out 0x122450 (shrR32Effect 0x122450 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1830]
    (.letOp (n := 1833) (.exec 0x122450 (fun s => s.RIP = 0x122450) (shrR32Effect 0x122450 3 0 3) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1830]
    (.letOp (n := 1834) (.out 0x122453 (xorR32R32Effect 0x122453 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1832, 1828]
    (.letOp (n := 1835) (.exec 0x122453 (fun s => s.RIP = 0x122453) (xorR32R32Effect 0x122453 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1832, 1828]
    (b_l121930_46))))))))))))))))))))))))))))))))))))))

def bytes_l121930_45 : List UInt8 :=
  [0x41, 0x01, 0xC3, 0x44, 0x89, 0x1C, 0x24, 0xC1, 0xE8, 0x03, 0x33, 0x84, 0x24, 0xA0, 0x00, 0x00,
    0x00, 0x8B, 0x54, 0x24, 0x60, 0x01, 0xD0, 0x89, 0x44, 0x24, 0x34, 0x89, 0xD0, 0xC1, 0xE8, 0x03,
    0x33, 0x84, 0x24, 0xA4, 0x00, 0x00, 0x00, 0x41, 0x89, 0xC1, 0x48, 0x8B, 0x7C, 0x24, 0x38, 0x89,
    0xFA, 0xC1, 0xC2, 0x19, 0x89, 0xFE, 0xC1, 0xC6, 0x0E, 0x31, 0xD6, 0x89, 0xF8, 0xC1, 0xE8, 0x03,
    0x31, 0xF0] ++ bytes_l121930_46

theorem code_l121930_45 : ∀ x ∈ codeRange 0x122413 bytes_l121930_45, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22413 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_46

def b_l121930_44 : Block Op Label signature Reg.count 1762 :=
  .letOp (n := 1762) (.out 0x1223c7 (movR32M32LowEffect 0x1223c7 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 1763) (.exec 0x1223c7 (LoadPre 0x1223c7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1223c7 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1223c7 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1764) (.out 0x1223ca (addR32R32Effect 0x1223ca 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[1544, 1762]
    (.letOp (n := 1765) (.exec 0x1223ca (fun s => s.RIP = 0x1223ca) (addR32R32Effect 0x1223ca 2 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[1544, 1762]
    (.letOp (n := 1766) (.exec 0x1223cc (StorePre 0x1223cc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1223cc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1223cc 3 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1764, 4]
    (.letOp (n := 1767) (.out 0x1223d1 (addR32R32Effect 0x1223d1 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1760, 1762]
    (.letOp (n := 1768) (.exec 0x1223d1 (fun s => s.RIP = 0x1223d1) (addR32R32Effect 0x1223d1 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1760, 1762]
    (.letOp (n := 1769) (.exec 0x1223d3 (StorePre 0x1223d3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1223d3 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1223d3 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1767, 4]
    (.letOp (n := 1770) (.out 0x1223d7 (shrR32Effect 0x1223d7 3 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1762]
    (.letOp (n := 1771) (.exec 0x1223d7 (fun s => s.RIP = 0x1223d7) (shrR32Effect 0x1223d7 3 2 3) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1762]
    (.letOp (n := 1772) (.out 0x1223da (xorR32R32Effect 0x1223da 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[1770, 1669]
    (.letOp (n := 1773) (.exec 0x1223da (fun s => s.RIP = 0x1223da) (xorR32R32Effect 0x1223da 3 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[1770, 1669]
    (.letOp (n := 1774) (.out 0x1223dd (movR32M32LowEffect 0x1223dd 0 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1775) (.exec 0x1223dd (LoadPre 0x1223dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1223dd + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1223dd 0 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1776) (.out 0x1223e1 (movR64M64Effect 0x1223e1 3 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1777) (.exec 0x1223e1 (LoadPre 0x1223e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1223e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1223e1 3 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1778) (.out 0x1223e6 (addR32R32Effect 0x1223e6 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[1776, 1774]
    (.letOp (n := 1779) (.exec 0x1223e6 (fun s => s.RIP = 0x1223e6) (addR32R32Effect 0x1223e6 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1776, 1774]
    (.letOp (n := 1780) (.out 0x1223e8 (addR32R32Effect 0x1223e8 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1772, 1774]
    (.letOp (n := 1781) (.exec 0x1223e8 (fun s => s.RIP = 0x1223e8) (addR32R32Effect 0x1223e8 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1772, 1774]
    (.letOp (n := 1782) (.exec 0x1223ea (StorePre 0x1223ea 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x1223ea + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1223ea 2 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1780, 4]
    (.letOp (n := 1783) (.out 0x1223ee (shrR32Effect 0x1223ee 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1774]
    (.letOp (n := 1784) (.exec 0x1223ee (fun s => s.RIP = 0x1223ee) (shrR32Effect 0x1223ee 3 0 3) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1774]
    (.letOp (n := 1785) (.out 0x1223f1 (xorR32R32Effect 0x1223f1 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[1783, 1661]
    (.letOp (n := 1786) (.exec 0x1223f1 (fun s => s.RIP = 0x1223f1) (xorR32R32Effect 0x1223f1 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[1783, 1661]
    (.letOp (n := 1787) (.out 0x1223f4 (movR32M32Effect 0x1223f4 11 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 1788) (.exec 0x1223f4 (LoadPre 0x1223f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1223f4 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1223f4 11 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1789) (.out 0x1223f9 (addR32R32Effect 0x1223f9 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[1785, 1787]
    (.letOp (n := 1790) (.exec 0x1223f9 (fun s => s.RIP = 0x1223f9) (addR32R32Effect 0x1223f9 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[1785, 1787]
    (.letOp (n := 1791) (.exec 0x1223fc (StorePre 0x1223fc 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1223fc + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1223fc 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1789, 4]
    (.letOp (n := 1792) (.out 0x122403 (shrR32Effect 0x122403 4 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1787]
    (.letOp (n := 1793) (.exec 0x122403 (fun s => s.RIP = 0x122403) (shrR32Effect 0x122403 4 11 3) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1787]
    (.letOp (n := 1794) (.out 0x122407 (xorR32M32Effect 0x122407 11 (.sib 4 none 0 (.d32 0x9c))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4] []) (.reg (.gpr 11))) #v[1792, 4]
    (.letOp (n := 1795) (.exec 0x122407 (LoadPre 0x122407 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x122407 + BitVec.ofNat 64 8)) 4) (xorR32M32Effect 0x122407 11 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[1792, 4]
    (.letOp (n := 1796) (.out 0x12240f (movR32M32LowEffect 0x12240f 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1797) (.exec 0x12240f (LoadPre 0x12240f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12240f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12240f 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l121930_45))))))))))))))))))))))))))))))))))))

def bytes_l121930_44 : List UInt8 :=
  [0x8B, 0x14, 0x24, 0x01, 0xD3, 0x48, 0x89, 0x5C, 0x24, 0x48, 0x01, 0xD0, 0x89, 0x44, 0x24, 0x10,
    0xC1, 0xEA, 0x03, 0x44, 0x31, 0xF2, 0x8B, 0x44, 0x24, 0x34, 0x48, 0x8B, 0x5C, 0x24, 0x68, 0x01,
    0xC3, 0x01, 0xC2, 0x89, 0x54, 0x24, 0x64, 0xC1, 0xE8, 0x03, 0x44, 0x31, 0xD8, 0x44, 0x8B, 0x5C,
    0x24, 0x0C, 0x44, 0x01, 0xD8, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x41, 0xC1, 0xEB, 0x03,
    0x44, 0x33, 0x9C, 0x24, 0x9C, 0x00, 0x00, 0x00, 0x8B, 0x44, 0x24, 0x08] ++ bytes_l121930_45

theorem code_l121930_44 : ∀ x ∈ codeRange 0x1223c7 bytes_l121930_44, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x223c7 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_45

def b_l121930_43 : Block Op Label signature Reg.count 1727 :=
  .letOp (n := 1727) (.exec 0x122381 (StorePre 0x122381 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x122381 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x122381 1 (.sib 4 none 0 (.d32 0x94))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1724, 4]
    (.letOp (n := 1728) (.exec 0x122388 (StorePre 0x122388 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x122388 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x122388 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1724, 4]
    (.letOp (n := 1729) (.out 0x12238f (movR32R32Effect 0x12238f 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[1663]
    (.letOp (n := 1730) (.exec 0x12238f (fun s => s.RIP = 0x12238f) (movR32R32Effect 0x12238f 3 6 10) (Reg.operands [.gpr 10] [])) #v[1663]
    (.letOp (n := 1731) (.out 0x122392 (addR32R32Effect 0x122392 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[1724, 1663]
    (.letOp (n := 1732) (.exec 0x122392 (fun s => s.RIP = 0x122392) (addR32R32Effect 0x122392 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[1724, 1663]
    (.letOp (n := 1733) (.exec 0x122395 (StorePre 0x122395 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x122395 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x122395 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1731, 4]
    (.letOp (n := 1734) (.out 0x122399 (addR32R32Effect 0x122399 3 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[1722, 1663]
    (.letOp (n := 1735) (.exec 0x122399 (fun s => s.RIP = 0x122399) (addR32R32Effect 0x122399 3 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[1722, 1663]
    (.letOp (n := 1736) (.exec 0x12239c (StorePre 0x12239c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x12239c + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x12239c 13 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[1734, 4]
    (.letOp (n := 1737) (.out 0x1223a1 (shrR32Effect 0x1223a1 3 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1729]
    (.letOp (n := 1738) (.exec 0x1223a1 (fun s => s.RIP = 0x1223a1) (shrR32Effect 0x1223a1 3 6 3) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1729]
    (.letOp (n := 1739) (.out 0x1223a4 (xorR32R32Effect 0x1223a4 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[1737, 1681]
    (.letOp (n := 1740) (.exec 0x1223a4 (fun s => s.RIP = 0x1223a4) (xorR32R32Effect 0x1223a4 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[1737, 1681]
    (.letOp (n := 1741) (.out 0x1223a6 (movR32M32Effect 0x1223a6 9 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 1742) (.exec 0x1223a6 (LoadPre 0x1223a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1223a6 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1223a6 9 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1743) (.out 0x1223ab (movR32R32Effect 0x1223ab 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[1741]
    (.letOp (n := 1744) (.exec 0x1223ab (fun s => s.RIP = 0x1223ab) (movR32R32Effect 0x1223ab 3 1 9) (Reg.operands [.gpr 9] [])) #v[1741]
    (.letOp (n := 1745) (.out 0x1223ae (movR32R32Effect 0x1223ae 3 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[1741]
    (.letOp (n := 1746) (.exec 0x1223ae (fun s => s.RIP = 0x1223ae) (movR32R32Effect 0x1223ae 3 12 9) (Reg.operands [.gpr 9] [])) #v[1741]
    (.letOp (n := 1747) (.out 0x1223b1 (movR32R32Effect 0x1223b1 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[1741]
    (.letOp (n := 1748) (.exec 0x1223b1 (fun s => s.RIP = 0x1223b1) (movR32R32Effect 0x1223b1 3 10 9) (Reg.operands [.gpr 9] [])) #v[1741]
    (.letOp (n := 1749) (.out 0x1223b4 (movR32R32Effect 0x1223b4 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[1648]
    (.letOp (n := 1750) (.exec 0x1223b4 (fun s => s.RIP = 0x1223b4) (movR32R32Effect 0x1223b4 2 0 5) (Reg.operands [.gpr 5] [])) #v[1648]
    (.letOp (n := 1751) (.out 0x1223b6 (addR32R32Effect 0x1223b6 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[1741, 1648]
    (.letOp (n := 1752) (.exec 0x1223b6 (fun s => s.RIP = 0x1223b6) (addR32R32Effect 0x1223b6 3 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[1741, 1648]
    (.letOp (n := 1753) (.out 0x1223b9 (movR32R32Effect 0x1223b9 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[1751]
    (.letOp (n := 1754) (.exec 0x1223b9 (fun s => s.RIP = 0x1223b9) (movR32R32Effect 0x1223b9 3 5 9) (Reg.operands [.gpr 9] [])) #v[1751]
    (.letOp (n := 1755) (.out 0x1223bc (addR32R32Effect 0x1223bc 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[1739, 1749]
    (.letOp (n := 1756) (.exec 0x1223bc (fun s => s.RIP = 0x1223bc) (addR32R32Effect 0x1223bc 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[1739, 1749]
    (.letOp (n := 1757) (.exec 0x1223be (StorePre 0x1223be 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1223be + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1223be 6 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1755, 4]
    (.letOp (n := 1758) (.out 0x1223c2 (shrR32Effect 0x1223c2 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1749]
    (.letOp (n := 1759) (.exec 0x1223c2 (fun s => s.RIP = 0x1223c2) (shrR32Effect 0x1223c2 3 0 3) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1749]
    (.letOp (n := 1760) (.out 0x1223c5 (xorR32R32Effect 0x1223c5 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[1758, 1675]
    (.letOp (n := 1761) (.exec 0x1223c5 (fun s => s.RIP = 0x1223c5) (xorR32R32Effect 0x1223c5 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[1758, 1675]
    (b_l121930_44)))))))))))))))))))))))))))))))))))

def bytes_l121930_43 : List UInt8 :=
  [0x89, 0x8C, 0x24, 0x94, 0x00, 0x00, 0x00, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x44, 0x89,
    0xD6, 0x44, 0x01, 0xD1, 0x89, 0x4C, 0x24, 0x40, 0x45, 0x01, 0xD5, 0x44, 0x89, 0x6C, 0x24, 0x04,
    0xC1, 0xEE, 0x03, 0x31, 0xC6, 0x44, 0x8B, 0x4C, 0x24, 0x24, 0x44, 0x89, 0xC9, 0x45, 0x89, 0xCC,
    0x45, 0x89, 0xCA, 0x89, 0xE8, 0x41, 0x01, 0xE9, 0x44, 0x89, 0xCD, 0x01, 0xC6, 0x89, 0x74, 0x24,
    0x24, 0xC1, 0xE8, 0x03, 0x31, 0xD0] ++ bytes_l121930_44

theorem code_l121930_43 : ∀ x ∈ codeRange 0x122381 bytes_l121930_43, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22381 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_44

def b_l121930_42 : Block Op Label signature Reg.count 1693 :=
  .letOp (n := 1693) (.out 0x122330 (rolR32Effect 0x122330 3 6 25) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1691]
    (.letOp (n := 1694) (.exec 0x122330 (fun s => s.RIP = 0x122330) (rolR32Effect 0x122330 3 6 25) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1691]
    (.letOp (n := 1695) (.out 0x122333 (movR32R32Effect 0x122333 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[1689]
    (.letOp (n := 1696) (.exec 0x122333 (fun s => s.RIP = 0x122333) (movR32R32Effect 0x122333 3 7 8) (Reg.operands [.gpr 8] [])) #v[1689]
    (.letOp (n := 1697) (.out 0x122336 (rolR32Effect 0x122336 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1695]
    (.letOp (n := 1698) (.exec 0x122336 (fun s => s.RIP = 0x122336) (rolR32Effect 0x122336 3 7 14) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1695]
    (.letOp (n := 1699) (.out 0x122339 (xorR32R32Effect 0x122339 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[1697, 1693]
    (.letOp (n := 1700) (.exec 0x122339 (fun s => s.RIP = 0x122339) (xorR32R32Effect 0x122339 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[1697, 1693]
    (.letOp (n := 1701) (.out 0x12233b (movR32R32Effect 0x12233b 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[1689]
    (.letOp (n := 1702) (.exec 0x12233b (fun s => s.RIP = 0x12233b) (movR32R32Effect 0x12233b 3 6 8) (Reg.operands [.gpr 8] [])) #v[1689]
    (.letOp (n := 1703) (.out 0x12233e (shrR32Effect 0x12233e 3 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1701]
    (.letOp (n := 1704) (.exec 0x12233e (fun s => s.RIP = 0x12233e) (shrR32Effect 0x12233e 3 6 3) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1701]
    (.letOp (n := 1705) (.out 0x122341 (xorR32R32Effect 0x122341 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[1703, 1699]
    (.letOp (n := 1706) (.exec 0x122341 (fun s => s.RIP = 0x122341) (xorR32R32Effect 0x122341 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[1703, 1699]
    (.letOp (n := 1707) (.out 0x122343 (movR32R32Effect 0x122343 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[1705]
    (.letOp (n := 1708) (.exec 0x122343 (fun s => s.RIP = 0x122343) (movR32R32Effect 0x122343 2 7 6) (Reg.operands [.gpr 6] [])) #v[1705]
    (.letOp (n := 1709) (.out 0x122345 (movR32M32LowEffect 0x122345 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 1710) (.exec 0x122345 (LoadPre 0x122345 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x122345 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x122345 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1711) (.exec 0x122349 (StorePre 0x122349 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x122349 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x122349 6 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1709, 4]
    (.letOp (n := 1712) (.exec 0x122350 (StorePre 0x122350 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x122350 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x122350 6 (.sib 4 none 0 (.d32 0xac))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1709, 4]
    (.letOp (n := 1713) (.exec 0x122357 (StorePre 0x122357 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x122357 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x122357 6 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1709, 4]
    (.letOp (n := 1714) (.out 0x12235e (addR32R32Effect 0x12235e 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[1709, 1276]
    (.letOp (n := 1715) (.exec 0x12235e (fun s => s.RIP = 0x12235e) (addR32R32Effect 0x12235e 3 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[1709, 1276]
    (.letOp (n := 1716) (.exec 0x122361 (StorePre 0x122361 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x122361 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x122361 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1714, 4]
    (.letOp (n := 1717) (.out 0x122365 (addR32R32Effect 0x122365 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[1707, 1276]
    (.letOp (n := 1718) (.exec 0x122365 (fun s => s.RIP = 0x122365) (addR32R32Effect 0x122365 3 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[1707, 1276]
    (.letOp (n := 1719) (.exec 0x122368 (StorePre 0x122368 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x122368 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x122368 7 (.sib 4 none 0 (.d32 0x8c))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1717, 4]
    (.letOp (n := 1720) (.out 0x12236f (shrR32Effect 0x12236f 4 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1276]
    (.letOp (n := 1721) (.exec 0x12236f (fun s => s.RIP = 0x12236f) (shrR32Effect 0x12236f 4 13 3) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1276]
    (.letOp (n := 1722) (.out 0x122373 (xorR32R32Effect 0x122373 3 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[1720, 1687]
    (.letOp (n := 1723) (.exec 0x122373 (fun s => s.RIP = 0x122373) (xorR32R32Effect 0x122373 3 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[1720, 1687]
    (.letOp (n := 1724) (.out 0x122376 (movR32M32LowEffect 0x122376 1 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 1725) (.exec 0x122376 (LoadPre 0x122376 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x122376 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x122376 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1726) (.exec 0x12237a (StorePre 0x12237a 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x12237a + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x12237a 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1724, 4]
    (b_l121930_43))))))))))))))))))))))))))))))))))

def bytes_l121930_42 : List UInt8 :=
  [0xC1, 0xC6, 0x19, 0x44, 0x89, 0xC7, 0xC1, 0xC7, 0x0E, 0x31, 0xF7, 0x44, 0x89, 0xC6, 0xC1, 0xEE,
    0x03, 0x31, 0xFE, 0x89, 0xF7, 0x8B, 0x74, 0x24, 0x28, 0x89, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0x89, 0xB4, 0x24, 0xAC, 0x00, 0x00, 0x00, 0x89, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x44, 0x01,
    0xEE, 0x89, 0x74, 0x24, 0x28, 0x44, 0x01, 0xEF, 0x89, 0xBC, 0x24, 0x8C, 0x00, 0x00, 0x00, 0x41,
    0xC1, 0xED, 0x03, 0x41, 0x31, 0xCD, 0x8B, 0x4C, 0x24, 0x40, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00,
    0x00] ++ bytes_l121930_43

theorem code_l121930_42 : ∀ x ∈ codeRange 0x122330 bytes_l121930_42, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22330 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_43

def b_l121930_41 : Block Op Label signature Reg.count 1654 :=
  .letOp (n := 1654) (.out 0x1222f0 (xorR32R32Effect 0x1222f0 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[1610, 1608]
    (.letOp (n := 1655) (.exec 0x1222f0 (fun s => s.RIP = 0x1222f0) (xorR32R32Effect 0x1222f0 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[1610, 1608]
    (.letOp (n := 1656) (.exec 0x1222f3 (StorePre 0x1222f3 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x1222f3 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1222f3 2 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1654, 4]
    (.letOp (n := 1657) (.out 0x1222fa (movR32R32Effect 0x1222fa 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[1648]
    (.letOp (n := 1658) (.exec 0x1222fa (fun s => s.RIP = 0x1222fa) (movR32R32Effect 0x1222fa 2 2 5) (Reg.operands [.gpr 5] [])) #v[1648]
    (.letOp (n := 1659) (.out 0x1222fc (rolR32Effect 0x1222fc 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1657]
    (.letOp (n := 1660) (.exec 0x1222fc (fun s => s.RIP = 0x1222fc) (rolR32Effect 0x1222fc 3 2 14) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1657]
    (.letOp (n := 1661) (.out 0x1222ff (xorR32R32Effect 0x1222ff 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[1627, 1622]
    (.letOp (n := 1662) (.exec 0x1222ff (fun s => s.RIP = 0x1222ff) (xorR32R32Effect 0x1222ff 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[1627, 1622]
    (.letOp (n := 1663) (.out 0x122302 (movR32M32Effect 0x122302 10 (.sib 4 none 0 (.d8 0x64))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 1664) (.exec 0x122302 (LoadPre 0x122302 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x122302 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x122302 10 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1665) (.out 0x122307 (movR32R32Effect 0x122307 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 10] []) (.reg (.gpr 7))) #v[1663]
    (.letOp (n := 1666) (.exec 0x122307 (fun s => s.RIP = 0x122307) (movR32R32Effect 0x122307 3 7 10) (Reg.operands [.gpr 10] [])) #v[1663]
    (.letOp (n := 1667) (.out 0x12230a (rolR32Effect 0x12230a 3 7 25) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1665]
    (.letOp (n := 1668) (.exec 0x12230a (fun s => s.RIP = 0x12230a) (rolR32Effect 0x12230a 3 7 25) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1665]
    (.letOp (n := 1669) (.out 0x12230d (xorR32R32Effect 0x12230d 3 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[1643, 1636]
    (.letOp (n := 1670) (.exec 0x12230d (fun s => s.RIP = 0x12230d) (xorR32R32Effect 0x12230d 3 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[1643, 1636]
    (.letOp (n := 1671) (.out 0x122310 (movR32R32Effect 0x122310 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[1663]
    (.letOp (n := 1672) (.exec 0x122310 (fun s => s.RIP = 0x122310) (movR32R32Effect 0x122310 3 0 10) (Reg.operands [.gpr 10] [])) #v[1663]
    (.letOp (n := 1673) (.out 0x122313 (rolR32Effect 0x122313 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1671]
    (.letOp (n := 1674) (.exec 0x122313 (fun s => s.RIP = 0x122313) (rolR32Effect 0x122313 3 0 14) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1671]
    (.letOp (n := 1675) (.out 0x122316 (xorR32R32Effect 0x122316 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[1659, 1652]
    (.letOp (n := 1676) (.exec 0x122316 (fun s => s.RIP = 0x122316) (xorR32R32Effect 0x122316 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[1659, 1652]
    (.letOp (n := 1677) (.out 0x122318 (movR32R32Effect 0x122318 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[1276]
    (.letOp (n := 1678) (.exec 0x122318 (fun s => s.RIP = 0x122318) (movR32R32Effect 0x122318 3 6 13) (Reg.operands [.gpr 13] [])) #v[1276]
    (.letOp (n := 1679) (.out 0x12231b (rolR32Effect 0x12231b 3 6 25) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1677]
    (.letOp (n := 1680) (.exec 0x12231b (fun s => s.RIP = 0x12231b) (rolR32Effect 0x12231b 3 6 25) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1677]
    (.letOp (n := 1681) (.out 0x12231e (xorR32R32Effect 0x12231e 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[1673, 1667]
    (.letOp (n := 1682) (.exec 0x12231e (fun s => s.RIP = 0x12231e) (xorR32R32Effect 0x12231e 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[1673, 1667]
    (.letOp (n := 1683) (.out 0x122320 (movR32R32Effect 0x122320 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[1276]
    (.letOp (n := 1684) (.exec 0x122320 (fun s => s.RIP = 0x122320) (movR32R32Effect 0x122320 3 1 13) (Reg.operands [.gpr 13] [])) #v[1276]
    (.letOp (n := 1685) (.out 0x122323 (rolR32Effect 0x122323 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1683]
    (.letOp (n := 1686) (.exec 0x122323 (fun s => s.RIP = 0x122323) (rolR32Effect 0x122323 3 1 14) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1683]
    (.letOp (n := 1687) (.out 0x122326 (xorR32R32Effect 0x122326 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1685, 1679]
    (.letOp (n := 1688) (.exec 0x122326 (fun s => s.RIP = 0x122326) (xorR32R32Effect 0x122326 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1685, 1679]
    (.letOp (n := 1689) (.out 0x122328 (movR64M64Effect 0x122328 8 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 1690) (.exec 0x122328 (LoadPre 0x122328 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x122328 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x122328 8 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1691) (.out 0x12232d (movR32R32Effect 0x12232d 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[1689]
    (.letOp (n := 1692) (.exec 0x12232d (fun s => s.RIP = 0x12232d) (movR32R32Effect 0x12232d 3 6 8) (Reg.operands [.gpr 8] [])) #v[1689]
    (b_l121930_42)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_41 : List UInt8 :=
  [0x44, 0x31, 0xCA, 0x89, 0x94, 0x24, 0x9C, 0x00, 0x00, 0x00, 0x89, 0xEA, 0xC1, 0xC2, 0x0E, 0x41,
    0x31, 0xC3, 0x44, 0x8B, 0x54, 0x24, 0x64, 0x44, 0x89, 0xD7, 0xC1, 0xC7, 0x19, 0x41, 0x31, 0xF6,
    0x44, 0x89, 0xD0, 0xC1, 0xC0, 0x0E, 0x31, 0xCA, 0x44, 0x89, 0xEE, 0xC1, 0xC6, 0x19, 0x31, 0xF8,
    0x44, 0x89, 0xE9, 0xC1, 0xC1, 0x0E, 0x31, 0xF1, 0x4C, 0x8B, 0x44, 0x24, 0x50, 0x44, 0x89, 0xC6] ++ bytes_l121930_42

theorem code_l121930_41 : ∀ x ∈ codeRange 0x1222f0 bytes_l121930_41, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x222f0 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_42

def b_l121930_40 : Block Op Label signature Reg.count 1618 :=
  .letOp (n := 1618) (.out 0x12229d (movR32M32Effect 0x12229d 11 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 1619) (.exec 0x12229d (LoadPre 0x12229d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x12229d + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12229d 11 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1620) (.out 0x1222a2 (movR32R32Effect 0x1222a2 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[1618]
    (.letOp (n := 1621) (.exec 0x1222a2 (fun s => s.RIP = 0x1222a2) (movR32R32Effect 0x1222a2 3 0 11) (Reg.operands [.gpr 11] [])) #v[1618]
    (.letOp (n := 1622) (.out 0x1222a5 (rolR32Effect 0x1222a5 3 0 25) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1620]
    (.letOp (n := 1623) (.exec 0x1222a5 (fun s => s.RIP = 0x1222a5) (rolR32Effect 0x1222a5 3 0 25) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1620]
    (.letOp (n := 1624) (.out 0x1222a8 (xorR32R32Effect 0x1222a8 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[1616, 1602]
    (.letOp (n := 1625) (.exec 0x1222a8 (fun s => s.RIP = 0x1222a8) (xorR32R32Effect 0x1222a8 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[1616, 1602]
    (.letOp (n := 1626) (.exec 0x1222ab (StorePre 0x1222ab 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1222ab + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x1222ab 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1624, 4]
    (.letOp (n := 1627) (.out 0x1222b3 (rolR32Effect 0x1222b3 4 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1618]
    (.letOp (n := 1628) (.exec 0x1222b3 (fun s => s.RIP = 0x1222b3) (rolR32Effect 0x1222b3 4 11 14) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1618]
    (.letOp (n := 1629) (.out 0x1222b7 (xorR32M32Effect 0x1222b7 12 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[1566, 4]
    (.letOp (n := 1630) (.exec 0x1222b7 (LoadPre 0x1222b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1222b7 + BitVec.ofNat 64 5)) 4) (xorR32M32Effect 0x1222b7 12 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[1566, 4]
    (.letOp (n := 1631) (.exec 0x1222bc (StorePre 0x1222bc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x1222bc + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x1222bc 12 (.sib 4 none 0 (.d32 0xb4))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[1629, 4]
    (.letOp (n := 1632) (.out 0x1222c4 (movR32M32LowEffect 0x1222c4 7 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 1633) (.exec 0x1222c4 (LoadPre 0x1222c4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1222c4 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1222c4 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1634) (.out 0x1222c7 (movR32R32Effect 0x1222c7 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[1632]
    (.letOp (n := 1635) (.exec 0x1222c7 (fun s => s.RIP = 0x1222c7) (movR32R32Effect 0x1222c7 2 6 7) (Reg.operands [.gpr 7] [])) #v[1632]
    (.letOp (n := 1636) (.out 0x1222c9 (rolR32Effect 0x1222c9 3 6 25) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1634]
    (.letOp (n := 1637) (.exec 0x1222c9 (fun s => s.RIP = 0x1222c9) (rolR32Effect 0x1222c9 3 6 25) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1634]
    (.letOp (n := 1638) (.out 0x1222cc (xorR32R32Effect 0x1222cc 3 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10] []) (.reg (.gpr 14))) #v[1580, 1574]
    (.letOp (n := 1639) (.exec 0x1222cc (fun s => s.RIP = 0x1222cc) (xorR32R32Effect 0x1222cc 3 14 10) (Reg.operands [.gpr 14, .gpr 10] [])) #v[1580, 1574]
    (.letOp (n := 1640) (.exec 0x1222cf (StorePre 0x1222cf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x1222cf + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x1222cf 14 (.sib 4 none 0 (.d32 0xa4))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[1638, 4]
    (.letOp (n := 1641) (.out 0x1222d7 (movR32R32Effect 0x1222d7 3 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[1632]
    (.letOp (n := 1642) (.exec 0x1222d7 (fun s => s.RIP = 0x1222d7) (movR32R32Effect 0x1222d7 3 14 7) (Reg.operands [.gpr 7] [])) #v[1632]
    (.letOp (n := 1643) (.out 0x1222da (rolR32Effect 0x1222da 4 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[1641]
    (.letOp (n := 1644) (.exec 0x1222da (fun s => s.RIP = 0x1222da) (rolR32Effect 0x1222da 4 14 14) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1641]
    (.letOp (n := 1645) (.out 0x1222de (xorR32R32Effect 0x1222de 2 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[1600, 1591]
    (.letOp (n := 1646) (.exec 0x1222de (fun s => s.RIP = 0x1222de) (xorR32R32Effect 0x1222de 2 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[1600, 1591]
    (.letOp (n := 1647) (.exec 0x1222e0 (StorePre 0x1222e0 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1222e0 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1222e0 5 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[1645, 4]
    (.letOp (n := 1648) (.out 0x1222e7 (movR32M32LowEffect 0x1222e7 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 1649) (.exec 0x1222e7 (LoadPre 0x1222e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1222e7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1222e7 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1650) (.out 0x1222eb (movR32R32Effect 0x1222eb 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[1648]
    (.letOp (n := 1651) (.exec 0x1222eb (fun s => s.RIP = 0x1222eb) (movR32R32Effect 0x1222eb 2 1 5) (Reg.operands [.gpr 5] [])) #v[1648]
    (.letOp (n := 1652) (.out 0x1222ed (rolR32Effect 0x1222ed 3 1 25) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1650]
    (.letOp (n := 1653) (.exec 0x1222ed (fun s => s.RIP = 0x1222ed) (rolR32Effect 0x1222ed 3 1 25) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1650]
    (b_l121930_41))))))))))))))))))))))))))))))))))))

def bytes_l121930_40 : List UInt8 :=
  [0x44, 0x8B, 0x5C, 0x24, 0x34, 0x44, 0x89, 0xD8, 0xC1, 0xC0, 0x19, 0x41, 0x31, 0xF8, 0x44, 0x89,
    0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x41, 0xC1, 0xC3, 0x0E, 0x44, 0x33, 0x64, 0x24, 0x04, 0x44,
    0x89, 0xA4, 0x24, 0xB4, 0x00, 0x00, 0x00, 0x8B, 0x3C, 0x24, 0x89, 0xFE, 0xC1, 0xC6, 0x19, 0x45,
    0x31, 0xD6, 0x44, 0x89, 0xB4, 0x24, 0xA4, 0x00, 0x00, 0x00, 0x41, 0x89, 0xFE, 0x41, 0xC1, 0xC6,
    0x0E, 0x31, 0xCD, 0x89, 0xAC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x8B, 0x6C, 0x24, 0x10, 0x89, 0xE9,
    0xC1, 0xC1, 0x19] ++ bytes_l121930_41

theorem code_l121930_40 : ∀ x ∈ codeRange 0x12229d bytes_l121930_40, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2229d 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_41

def b_l121930_39 : Block Op Label signature Reg.count 1580 :=
  .letOp (n := 1580) (.out 0x12225c (movR32R32Effect 0x12225c 3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[1578]
    (.letOp (n := 1581) (.exec 0x12225c (fun s => s.RIP = 0x12225c) (movR32R32Effect 0x12225c 3 14 1) (Reg.operands [.gpr 1] [])) #v[1578]
    (.letOp (n := 1582) (.out 0x12225f (movR64M64Effect 0x12225f 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 1583) (.exec 0x12225f (LoadPre 0x12225f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12225f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12225f 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1584) (.out 0x122264 (addR32R32Effect 0x122264 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[1582, 1517]
    (.letOp (n := 1585) (.exec 0x122264 (fun s => s.RIP = 0x122264) (addR32R32Effect 0x122264 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1582, 1517]
    (.letOp (n := 1586) (.exec 0x122266 (StorePre 0x122266 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x122266 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x122266 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1584, 4]
    (.letOp (n := 1587) (.out 0x12226b (movR32M32LowEffect 0x12226b 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 1588) (.exec 0x12226b (LoadPre 0x12226b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12226b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12226b 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1589) (.out 0x12226f (movR32R32Effect 0x12226f 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[1587]
    (.letOp (n := 1590) (.exec 0x12226f (fun s => s.RIP = 0x12226f) (movR32R32Effect 0x12226f 2 1 6) (Reg.operands [.gpr 6] [])) #v[1587]
    (.letOp (n := 1591) (.out 0x122271 (rolR32Effect 0x122271 3 1 25) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1589]
    (.letOp (n := 1592) (.exec 0x122271 (fun s => s.RIP = 0x122271) (rolR32Effect 0x122271 3 1 25) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1589]
    (.letOp (n := 1593) (.out 0x122274 (addR32R32Effect 0x122274 2 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[1576, 1517]
    (.letOp (n := 1594) (.exec 0x122274 (fun s => s.RIP = 0x122274) (addR32R32Effect 0x122274 2 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[1576, 1517]
    (.letOp (n := 1595) (.exec 0x122276 (StorePre 0x122276 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x122276 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x122276 5 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[1593, 4]
    (.letOp (n := 1596) (.out 0x12227e (movR32R32Effect 0x12227e 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[1587]
    (.letOp (n := 1597) (.exec 0x12227e (fun s => s.RIP = 0x12227e) (movR32R32Effect 0x12227e 2 2 6) (Reg.operands [.gpr 6] [])) #v[1587]
    (.letOp (n := 1598) (.out 0x122280 (rolR32Effect 0x122280 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1596]
    (.letOp (n := 1599) (.exec 0x122280 (fun s => s.RIP = 0x122280) (rolR32Effect 0x122280 3 2 14) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1596]
    (.letOp (n := 1600) (.out 0x122283 (movR32R32Effect 0x122283 2 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[1598]
    (.letOp (n := 1601) (.exec 0x122283 (fun s => s.RIP = 0x122283) (movR32R32Effect 0x122283 2 5 2) (Reg.operands [.gpr 2] [])) #v[1598]
    (.letOp (n := 1602) (.out 0x122285 (xorR32R32Effect 0x122285 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[1552, 1548]
    (.letOp (n := 1603) (.exec 0x122285 (fun s => s.RIP = 0x122285) (xorR32R32Effect 0x122285 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1552, 1548]
    (.letOp (n := 1604) (.out 0x122287 (movR32M32LowEffect 0x122287 2 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 1605) (.exec 0x122287 (LoadPre 0x122287 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x122287 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x122287 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1606) (.out 0x12228b (movR32R32Effect 0x12228b 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[1604]
    (.letOp (n := 1607) (.exec 0x12228b (fun s => s.RIP = 0x12228b) (movR32R32Effect 0x12228b 3 9 2) (Reg.operands [.gpr 2] [])) #v[1604]
    (.letOp (n := 1608) (.out 0x12228e (rolR32Effect 0x12228e 4 9 25) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[1606]
    (.letOp (n := 1609) (.exec 0x12228e (fun s => s.RIP = 0x12228e) (rolR32Effect 0x12228e 4 9 25) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1606]
    (.letOp (n := 1610) (.out 0x122292 (rolR32Effect 0x122292 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1604]
    (.letOp (n := 1611) (.exec 0x122292 (fun s => s.RIP = 0x122292) (rolR32Effect 0x122292 3 2 14) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1604]
    (.letOp (n := 1612) (.out 0x122295 (movR32R32Effect 0x122295 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[1544]
    (.letOp (n := 1613) (.exec 0x122295 (fun s => s.RIP = 0x122295) (movR32R32Effect 0x122295 2 0 3) (Reg.operands [.gpr 3] [])) #v[1544]
    (.letOp (n := 1614) (.out 0x122297 (shrR32Effect 0x122297 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1612]
    (.letOp (n := 1615) (.exec 0x122297 (fun s => s.RIP = 0x122297) (shrR32Effect 0x122297 3 0 3) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1612]
    (.letOp (n := 1616) (.out 0x12229a (movR32R32Effect 0x12229a 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[1614]
    (.letOp (n := 1617) (.exec 0x12229a (fun s => s.RIP = 0x12229a) (movR32R32Effect 0x12229a 3 8 0) (Reg.operands [.gpr 0] [])) #v[1614]
    (b_l121930_40))))))))))))))))))))))))))))))))))))))

def bytes_l121930_39 : List UInt8 :=
  [0x41, 0x89, 0xCE, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0x01, 0xD1, 0x48, 0x89, 0x4C, 0x24, 0x58, 0x8B,
    0x74, 0x24, 0x08, 0x89, 0xF1, 0xC1, 0xC1, 0x19, 0x01, 0xD5, 0x48, 0x89, 0xAC, 0x24, 0xD0, 0x00,
    0x00, 0x00, 0x89, 0xF2, 0xC1, 0xC2, 0x0E, 0x89, 0xD5, 0x31, 0xC7, 0x8B, 0x54, 0x24, 0x0C, 0x41,
    0x89, 0xD1, 0x41, 0xC1, 0xC1, 0x19, 0xC1, 0xC2, 0x0E, 0x89, 0xD8, 0xC1, 0xE8, 0x03, 0x41, 0x89,
    0xC0] ++ bytes_l121930_40

theorem code_l121930_39 : ∀ x ∈ codeRange 0x12225c bytes_l121930_39, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2225c 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_40

def b_l121930_38 : Block Op Label signature Reg.count 1542 :=
  .letOp (n := 1542) (.out 0x12221a (andR32R32Effect 0x12221a 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[1539, 1254]
    (.letOp (n := 1543) (.exec 0x12221a (fun s => s.RIP = 0x12221a) (andR32R32Effect 0x12221a 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[1539, 1254]
    (.letOp (n := 1544) (.out 0x12221d (movR64M64Effect 0x12221d 3 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1545) (.exec 0x12221d (LoadPre 0x12221d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12221d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12221d 3 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1546) (.out 0x122222 (movR32R32Effect 0x122222 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[1544]
    (.letOp (n := 1547) (.exec 0x122222 (fun s => s.RIP = 0x122222) (movR32R32Effect 0x122222 2 0 3) (Reg.operands [.gpr 3] [])) #v[1544]
    (.letOp (n := 1548) (.out 0x122224 (rolR32Effect 0x122224 3 0 25) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1546]
    (.letOp (n := 1549) (.exec 0x122224 (fun s => s.RIP = 0x122224) (rolR32Effect 0x122224 3 0 25) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1546]
    (.letOp (n := 1550) (.out 0x122227 (movR32R32Effect 0x122227 2 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[1544]
    (.letOp (n := 1551) (.exec 0x122227 (fun s => s.RIP = 0x122227) (movR32R32Effect 0x122227 2 7 3) (Reg.operands [.gpr 3] [])) #v[1544]
    (.letOp (n := 1552) (.out 0x122229 (rolR32Effect 0x122229 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1550]
    (.letOp (n := 1553) (.exec 0x122229 (fun s => s.RIP = 0x122229) (rolR32Effect 0x122229 3 7 14) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1550]
    (.letOp (n := 1554) (.out 0x12222c (xorR32R32Effect 0x12222c 3 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[1416, 1254]
    (.letOp (n := 1555) (.exec 0x12222c (fun s => s.RIP = 0x12222c) (xorR32R32Effect 0x12222c 3 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[1416, 1254]
    (.letOp (n := 1556) (.exec 0x12222f (StorePre 0x12222f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x12222f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12222f 10 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[1371, 4]
    (.letOp (n := 1557) (.out 0x122234 (movR32R32Effect 0x122234 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[1371]
    (.letOp (n := 1558) (.exec 0x122234 (fun s => s.RIP = 0x122234) (movR32R32Effect 0x122234 3 11 10) (Reg.operands [.gpr 10] [])) #v[1371]
    (.letOp (n := 1559) (.out 0x122237 (rolR32Effect 0x122237 4 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1557]
    (.letOp (n := 1560) (.exec 0x122237 (fun s => s.RIP = 0x122237) (rolR32Effect 0x122237 4 11 15) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1557]
    (.letOp (n := 1561) (.exec 0x12223b (StorePre 0x12223b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x12223b + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x12223b 11 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[1559, 4]
    (.letOp (n := 1562) (.out 0x122240 (andR32R32Effect 0x122240 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[1554, 1531]
    (.letOp (n := 1563) (.exec 0x122240 (fun s => s.RIP = 0x122240) (andR32R32Effect 0x122240 3 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[1554, 1531]
    (.letOp (n := 1564) (.out 0x122243 (movR32R32Effect 0x122243 3 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 10] []) (.reg (.gpr 12))) #v[1371]
    (.letOp (n := 1565) (.exec 0x122243 (fun s => s.RIP = 0x122243) (movR32R32Effect 0x122243 3 12 10) (Reg.operands [.gpr 10] [])) #v[1371]
    (.letOp (n := 1566) (.out 0x122246 (rolR32Effect 0x122246 4 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1564]
    (.letOp (n := 1567) (.exec 0x122246 (fun s => s.RIP = 0x122246) (rolR32Effect 0x122246 4 12 13) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1564]
    (.letOp (n := 1568) (.out 0x12224a (xorR32R32Effect 0x12224a 2 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[1562, 1542]
    (.letOp (n := 1569) (.exec 0x12224a (fun s => s.RIP = 0x12224a) (xorR32R32Effect 0x12224a 2 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[1562, 1542]
    (.letOp (n := 1570) (.out 0x12224c (movR32M32LowEffect 0x12224c 1 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 1571) (.exec 0x12224c (LoadPre 0x12224c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12224c + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12224c 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1572) (.out 0x122250 (movR32R32Effect 0x122250 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[1570]
    (.letOp (n := 1573) (.exec 0x122250 (fun s => s.RIP = 0x122250) (movR32R32Effect 0x122250 3 10 1) (Reg.operands [.gpr 1] [])) #v[1570]
    (.letOp (n := 1574) (.out 0x122253 (rolR32Effect 0x122253 4 10 25) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[1572]
    (.letOp (n := 1575) (.exec 0x122253 (fun s => s.RIP = 0x122253) (rolR32Effect 0x122253 4 10 25) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1572]
    (.letOp (n := 1576) (.out 0x122257 (addR32R32Effect 0x122257 2 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 6] []) (.reg (.gpr 5))) #v[1568, 1536]
    (.letOp (n := 1577) (.exec 0x122257 (fun s => s.RIP = 0x122257) (addR32R32Effect 0x122257 2 5 6) (Reg.operands [.gpr 5, .gpr 6] [])) #v[1568, 1536]
    (.letOp (n := 1578) (.out 0x122259 (rolR32Effect 0x122259 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1570]
    (.letOp (n := 1579) (.exec 0x122259 (fun s => s.RIP = 0x122259) (rolR32Effect 0x122259 3 1 14) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1570]
    (b_l121930_39))))))))))))))))))))))))))))))))))))))

def bytes_l121930_38 : List UInt8 :=
  [0x44, 0x21, 0xD9, 0x48, 0x8B, 0x5C, 0x24, 0x48, 0x89, 0xD8, 0xC1, 0xC0, 0x19, 0x89, 0xDF, 0xC1,
    0xC7, 0x0E, 0x44, 0x31, 0xDD, 0x4C, 0x89, 0x54, 0x24, 0x50, 0x45, 0x89, 0xD3, 0x41, 0xC1, 0xC3,
    0x0F, 0x44, 0x89, 0x5C, 0x24, 0x04, 0x44, 0x21, 0xCD, 0x45, 0x89, 0xD4, 0x41, 0xC1, 0xC4, 0x0D,
    0x31, 0xCD, 0x8B, 0x4C, 0x24, 0x60, 0x41, 0x89, 0xCA, 0x41, 0xC1, 0xC2, 0x19, 0x01, 0xF5, 0xC1,
    0xC1, 0x0E] ++ bytes_l121930_39

theorem code_l121930_38 : ∀ x ∈ codeRange 0x12221a bytes_l121930_38, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2221a 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_39

def b_l121930_37 : Block Op Label signature Reg.count 1505 :=
  .letOp (n := 1505) (.out 0x1221d7 (xorR32R32Effect 0x1221d7 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[1503, 1250]
    (.letOp (n := 1506) (.exec 0x1221d7 (fun s => s.RIP = 0x1221d7) (xorR32R32Effect 0x1221d7 3 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[1503, 1250]
    (.letOp (n := 1507) (.out 0x1221da (andR32R32Effect 0x1221da 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[1505, 1447]
    (.letOp (n := 1508) (.exec 0x1221da (fun s => s.RIP = 0x1221da) (andR32R32Effect 0x1221da 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[1505, 1447]
    (.letOp (n := 1509) (.out 0x1221dd (xorR32R32Effect 0x1221dd 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[1507, 1250]
    (.letOp (n := 1510) (.exec 0x1221dd (fun s => s.RIP = 0x1221dd) (xorR32R32Effect 0x1221dd 3 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[1507, 1250]
    (.letOp (n := 1511) (.out 0x1221e0 (addR32R32Effect 0x1221e0 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[1174, 1488]
    (.letOp (n := 1512) (.exec 0x1221e0 (fun s => s.RIP = 0x1221e0) (addR32R32Effect 0x1221e0 3 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[1174, 1488]
    (.letOp (n := 1513) (.out 0x1221e3 (addR32R32Effect 0x1221e3 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[1511, 1509]
    (.letOp (n := 1514) (.exec 0x1221e3 (fun s => s.RIP = 0x1221e3) (addR32R32Effect 0x1221e3 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[1511, 1509]
    (.letOp (n := 1515) (.out 0x1221e5 (addR32R32Effect 0x1221e5 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[1513, 1501]
    (.letOp (n := 1516) (.exec 0x1221e5 (fun s => s.RIP = 0x1221e5) (addR32R32Effect 0x1221e5 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[1513, 1501]
    (.letOp (n := 1517) (.out 0x1221e7 (addR32Imm32Effect 0x1221e7 6 2 0xefbe4786) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[1515]
    (.letOp (n := 1518) (.exec 0x1221e7 (fun s => s.RIP = 0x1221e7) (addR32Imm32Effect 0x1221e7 6 2 0xefbe4786) (Reg.operands [.gpr 2] [])) #v[1515]
    (.letOp (n := 1519) (.out 0x1221ed (movR32R32Effect 0x1221ed 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[1453]
    (.letOp (n := 1520) (.exec 0x1221ed (fun s => s.RIP = 0x1221ed) (movR32R32Effect 0x1221ed 3 0 8) (Reg.operands [.gpr 8] [])) #v[1453]
    (.letOp (n := 1521) (.out 0x1221f0 (rolR32Effect 0x1221f0 3 0 30) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1519]
    (.letOp (n := 1522) (.exec 0x1221f0 (fun s => s.RIP = 0x1221f0) (rolR32Effect 0x1221f0 3 0 30) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1519]
    (.letOp (n := 1523) (.out 0x1221f3 (movR32R32Effect 0x1221f3 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[1453]
    (.letOp (n := 1524) (.exec 0x1221f3 (fun s => s.RIP = 0x1221f3) (movR32R32Effect 0x1221f3 3 1 8) (Reg.operands [.gpr 8] [])) #v[1453]
    (.letOp (n := 1525) (.out 0x1221f6 (rolR32Effect 0x1221f6 3 1 19) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1523]
    (.letOp (n := 1526) (.exec 0x1221f6 (fun s => s.RIP = 0x1221f6) (rolR32Effect 0x1221f6 3 1 19) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1523]
    (.letOp (n := 1527) (.out 0x1221f9 (xorR32R32Effect 0x1221f9 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1525, 1521]
    (.letOp (n := 1528) (.exec 0x1221f9 (fun s => s.RIP = 0x1221f9) (xorR32R32Effect 0x1221f9 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1525, 1521]
    (.letOp (n := 1529) (.out 0x1221fb (movR32R32Effect 0x1221fb 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[1453]
    (.letOp (n := 1530) (.exec 0x1221fb (fun s => s.RIP = 0x1221fb) (movR32R32Effect 0x1221fb 3 6 8) (Reg.operands [.gpr 8] [])) #v[1453]
    (.letOp (n := 1531) (.out 0x1221fe (movR64R64Effect 0x1221fe 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[1453]
    (.letOp (n := 1532) (.exec 0x1221fe (fun s => s.RIP = 0x1221fe) (movR64R64Effect 0x1221fe 9 8) (Reg.operands [.gpr 8] [])) #v[1453]
    (.letOp (n := 1533) (.exec 0x122201 (StorePre 0x122201 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x122201 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x122201 8 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1453, 4]
    (.letOp (n := 1534) (.out 0x122206 (rolR32Effect 0x122206 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1529]
    (.letOp (n := 1535) (.exec 0x122206 (fun s => s.RIP = 0x122206) (rolR32Effect 0x122206 3 6 10) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1529]
    (.letOp (n := 1536) (.out 0x122209 (xorR32R32Effect 0x122209 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1534, 1527]
    (.letOp (n := 1537) (.exec 0x122209 (fun s => s.RIP = 0x122209) (xorR32R32Effect 0x122209 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1534, 1527]
    (.letOp (n := 1538) (.exec 0x12220b (StorePre 0x12220b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x12220b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12220b 5 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[1416, 4]
    (.letOp (n := 1539) (.out 0x122210 (movR32R32Effect 0x122210 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[1416]
    (.letOp (n := 1540) (.exec 0x122210 (fun s => s.RIP = 0x122210) (movR32R32Effect 0x122210 2 1 5) (Reg.operands [.gpr 5] [])) #v[1416]
    (.letOp (n := 1541) (.exec 0x122212 (StorePre 0x122212 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x122212 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x122212 11 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[1254, 4]
    (b_l121930_38)))))))))))))))))))))))))))))))))))))

def bytes_l121930_37 : List UInt8 :=
  [0x44, 0x31, 0xF9, 0x44, 0x21, 0xC9, 0x44, 0x31, 0xF9, 0x44, 0x01, 0xE2, 0x01, 0xCA, 0x01, 0xC2,
    0x81, 0xC2, 0x86, 0x47, 0xBE, 0xEF, 0x44, 0x89, 0xC0, 0xC1, 0xC0, 0x1E, 0x44, 0x89, 0xC1, 0xC1,
    0xC1, 0x13, 0x31, 0xC1, 0x44, 0x89, 0xC6, 0x4D, 0x89, 0xC1, 0x4C, 0x89, 0x44, 0x24, 0x70, 0xC1,
    0xC6, 0x0A, 0x31, 0xCE, 0x48, 0x89, 0x6C, 0x24, 0x78, 0x89, 0xE9, 0x4C, 0x89, 0x9C, 0x24, 0xD8,
    0x00, 0x00, 0x00] ++ bytes_l121930_38

theorem code_l121930_37 : ∀ x ∈ codeRange 0x1221d7 bytes_l121930_37, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x221d7 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_38

def b_l121930_36 : Block Op Label signature Reg.count 1467 :=
  .letOp (n := 1467) (.out 0x122197 (movR32R32Effect 0x122197 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[1276]
    (.letOp (n := 1468) (.exec 0x122197 (fun s => s.RIP = 0x122197) (movR32R32Effect 0x122197 3 6 13) (Reg.operands [.gpr 13] [])) #v[1276]
    (.letOp (n := 1469) (.out 0x12219a (rolR32Effect 0x12219a 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1467]
    (.letOp (n := 1470) (.exec 0x12219a (fun s => s.RIP = 0x12219a) (rolR32Effect 0x12219a 3 6 13) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1467]
    (.letOp (n := 1471) (.out 0x12219d (xorR32R32Effect 0x12219d 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1469, 1465]
    (.letOp (n := 1472) (.exec 0x12219d (fun s => s.RIP = 0x12219d) (xorR32R32Effect 0x12219d 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1469, 1465]
    (.letOp (n := 1473) (.out 0x12219f (movR32R32Effect 0x12219f 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[1276]
    (.letOp (n := 1474) (.exec 0x12219f (fun s => s.RIP = 0x12219f) (movR32R32Effect 0x12219f 3 1 13) (Reg.operands [.gpr 13] [])) #v[1276]
    (.letOp (n := 1475) (.out 0x1221a2 (shrR32Effect 0x1221a2 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1473]
    (.letOp (n := 1476) (.exec 0x1221a2 (fun s => s.RIP = 0x1221a2) (shrR32Effect 0x1221a2 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1473]
    (.letOp (n := 1477) (.out 0x1221a5 (xorR32R32Effect 0x1221a5 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1475, 1471]
    (.letOp (n := 1478) (.exec 0x1221a5 (fun s => s.RIP = 0x1221a5) (xorR32R32Effect 0x1221a5 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1475, 1471]
    (.letOp (n := 1479) (.out 0x1221a7 (addR32M32Effect 0x1221a7 5 12 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[1330, 4]
    (.letOp (n := 1480) (.exec 0x1221a7 (LoadPre 0x1221a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1221a7 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x1221a7 5 12 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[1330, 4]
    (.letOp (n := 1481) (.out 0x1221ac (addR32R32Effect 0x1221ac 3 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[1479, 1461]
    (.letOp (n := 1482) (.exec 0x1221ac (fun s => s.RIP = 0x1221ac) (addR32R32Effect 0x1221ac 3 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[1479, 1461]
    (.letOp (n := 1483) (.exec 0x1221af (StorePre 0x1221af 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1221af + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1221af 9 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[1447, 4]
    (.letOp (n := 1484) (.out 0x1221b7 (movR32R32Effect 0x1221b7 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[1447]
    (.letOp (n := 1485) (.exec 0x1221b7 (fun s => s.RIP = 0x1221b7) (movR32R32Effect 0x1221b7 3 0 9) (Reg.operands [.gpr 9] [])) #v[1447]
    (.letOp (n := 1486) (.out 0x1221ba (rolR32Effect 0x1221ba 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1484]
    (.letOp (n := 1487) (.exec 0x1221ba (fun s => s.RIP = 0x1221ba) (rolR32Effect 0x1221ba 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1484]
    (.letOp (n := 1488) (.out 0x1221bd (addR32R32Effect 0x1221bd 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[1481, 1477]
    (.letOp (n := 1489) (.exec 0x1221bd (fun s => s.RIP = 0x1221bd) (addR32R32Effect 0x1221bd 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[1481, 1477]
    (.letOp (n := 1490) (.exec 0x1221c0 (StorePre 0x1221c0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1221c0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1221c0 12 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[1488, 4]
    (.letOp (n := 1491) (.out 0x1221c5 (movR32R32Effect 0x1221c5 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[1447]
    (.letOp (n := 1492) (.exec 0x1221c5 (fun s => s.RIP = 0x1221c5) (movR32R32Effect 0x1221c5 3 1 9) (Reg.operands [.gpr 9] [])) #v[1447]
    (.letOp (n := 1493) (.out 0x1221c8 (rolR32Effect 0x1221c8 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1491]
    (.letOp (n := 1494) (.exec 0x1221c8 (fun s => s.RIP = 0x1221c8) (rolR32Effect 0x1221c8 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1491]
    (.letOp (n := 1495) (.out 0x1221cb (xorR32R32Effect 0x1221cb 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1493, 1486]
    (.letOp (n := 1496) (.exec 0x1221cb (fun s => s.RIP = 0x1221cb) (xorR32R32Effect 0x1221cb 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1493, 1486]
    (.letOp (n := 1497) (.out 0x1221cd (movR32R32Effect 0x1221cd 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[1447]
    (.letOp (n := 1498) (.exec 0x1221cd (fun s => s.RIP = 0x1221cd) (movR32R32Effect 0x1221cd 3 0 9) (Reg.operands [.gpr 9] [])) #v[1447]
    (.letOp (n := 1499) (.out 0x1221d0 (rolR32Effect 0x1221d0 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1497]
    (.letOp (n := 1500) (.exec 0x1221d0 (fun s => s.RIP = 0x1221d0) (rolR32Effect 0x1221d0 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1497]
    (.letOp (n := 1501) (.out 0x1221d3 (xorR32R32Effect 0x1221d3 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1499, 1495]
    (.letOp (n := 1502) (.exec 0x1221d3 (fun s => s.RIP = 0x1221d3) (xorR32R32Effect 0x1221d3 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1499, 1495]
    (.letOp (n := 1503) (.out 0x1221d5 (movR32R32Effect 0x1221d5 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[1328]
    (.letOp (n := 1504) (.exec 0x1221d5 (fun s => s.RIP = 0x1221d5) (movR32R32Effect 0x1221d5 2 1 3) (Reg.operands [.gpr 3] [])) #v[1328]
    (b_l121930_37))))))))))))))))))))))))))))))))))))))

def bytes_l121930_36 : List UInt8 :=
  [0x44, 0x89, 0xEE, 0xC1, 0xC6, 0x0D, 0x31, 0xCE, 0x44, 0x89, 0xE9, 0xC1, 0xE9, 0x0A, 0x31, 0xF1,
    0x44, 0x03, 0x64, 0x24, 0x0C, 0x41, 0x01, 0xC4, 0x4C, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00,
    0x44, 0x89, 0xC8, 0xC1, 0xC0, 0x1A, 0x41, 0x01, 0xCC, 0x4C, 0x89, 0x64, 0x24, 0x38, 0x44, 0x89,
    0xC9, 0xC1, 0xC1, 0x15, 0x31, 0xC1, 0x44, 0x89, 0xC8, 0xC1, 0xC0, 0x07, 0x31, 0xC8, 0x89, 0xD9] ++ bytes_l121930_37

theorem code_l121930_36 : ∀ x ∈ codeRange 0x122197 bytes_l121930_36, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22197 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_37

def b_l121930_35 : Block Op Label signature Reg.count 1427 :=
  .letOp (n := 1427) (.out 0x122161 (andR32R32Effect 0x122161 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[1424, 1180]
    (.letOp (n := 1428) (.exec 0x122161 (fun s => s.RIP = 0x122161) (andR32R32Effect 0x122161 3 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[1424, 1180]
    (.letOp (n := 1429) (.out 0x122164 (movR32R32Effect 0x122164 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 11] []) (.reg (.gpr 7))) #v[1254]
    (.letOp (n := 1430) (.exec 0x122164 (fun s => s.RIP = 0x122164) (movR32R32Effect 0x122164 3 7 11) (Reg.operands [.gpr 11] [])) #v[1254]
    (.letOp (n := 1431) (.out 0x122167 (xorR32R32Effect 0x122167 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[1429, 1180]
    (.letOp (n := 1432) (.exec 0x122167 (fun s => s.RIP = 0x122167) (xorR32R32Effect 0x122167 3 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[1429, 1180]
    (.letOp (n := 1433) (.out 0x12216a (andR32R32Effect 0x12216a 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[1431, 1416]
    (.letOp (n := 1434) (.exec 0x12216a (fun s => s.RIP = 0x12216a) (andR32R32Effect 0x12216a 2 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[1431, 1416]
    (.letOp (n := 1435) (.out 0x12216c (xorR32R32Effect 0x12216c 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[1433, 1427]
    (.letOp (n := 1436) (.exec 0x12216c (fun s => s.RIP = 0x12216c) (xorR32R32Effect 0x12216c 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[1433, 1427]
    (.letOp (n := 1437) (.out 0x12216e (addR32R32Effect 0x12216e 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[1435, 1422]
    (.letOp (n := 1438) (.exec 0x12216e (fun s => s.RIP = 0x12216e) (addR32R32Effect 0x12216e 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[1435, 1422]
    (.letOp (n := 1439) (.out 0x122170 (movR64R64Effect 0x122170 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[1437]
    (.letOp (n := 1440) (.exec 0x122170 (fun s => s.RIP = 0x122170) (movR64R64Effect 0x122170 8 7) (Reg.operands [.gpr 7] [])) #v[1437]
    (.letOp (n := 1441) (.out 0x122173 (movR64M64Effect 0x122173 7 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 1442) (.exec 0x122173 (LoadPre 0x122173 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x122173 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x122173 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1443) (.out 0x122178 (movR32R32Effect 0x122178 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[1441]
    (.letOp (n := 1444) (.exec 0x122178 (fun s => s.RIP = 0x122178) (movR32R32Effect 0x122178 2 1 7) (Reg.operands [.gpr 7] [])) #v[1441]
    (.letOp (n := 1445) (.out 0x12217a (rolR32Effect 0x12217a 3 1 25) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1443]
    (.letOp (n := 1446) (.exec 0x12217a (fun s => s.RIP = 0x12217a) (rolR32Effect 0x12217a 3 1 25) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1443]
    (.letOp (n := 1447) (.out 0x12217d (addR32R32Effect 0x12217d 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[1099, 1412]
    (.letOp (n := 1448) (.exec 0x12217d (fun s => s.RIP = 0x12217d) (addR32R32Effect 0x12217d 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1099, 1412]
    (.letOp (n := 1449) (.out 0x122180 (movR32R32Effect 0x122180 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[1441]
    (.letOp (n := 1450) (.exec 0x122180 (fun s => s.RIP = 0x122180) (movR32R32Effect 0x122180 2 6 7) (Reg.operands [.gpr 7] [])) #v[1441]
    (.letOp (n := 1451) (.out 0x122182 (rolR32Effect 0x122182 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1449]
    (.letOp (n := 1452) (.exec 0x122182 (fun s => s.RIP = 0x122182) (rolR32Effect 0x122182 3 6 14) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1449]
    (.letOp (n := 1453) (.out 0x122185 (addR32R32Effect 0x122185 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[1439, 1412]
    (.letOp (n := 1454) (.exec 0x122185 (fun s => s.RIP = 0x122185) (addR32R32Effect 0x122185 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1439, 1412]
    (.letOp (n := 1455) (.out 0x122188 (xorR32R32Effect 0x122188 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1451, 1445]
    (.letOp (n := 1456) (.exec 0x122188 (fun s => s.RIP = 0x122188) (xorR32R32Effect 0x122188 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1451, 1445]
    (.letOp (n := 1457) (.out 0x12218a (movR32R32Effect 0x12218a 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[1441]
    (.letOp (n := 1458) (.exec 0x12218a (fun s => s.RIP = 0x12218a) (movR32R32Effect 0x12218a 2 0 7) (Reg.operands [.gpr 7] [])) #v[1441]
    (.letOp (n := 1459) (.out 0x12218c (shrR32Effect 0x12218c 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1457]
    (.letOp (n := 1460) (.exec 0x12218c (fun s => s.RIP = 0x12218c) (shrR32Effect 0x12218c 3 0 3) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1457]
    (.letOp (n := 1461) (.out 0x12218f (xorR32R32Effect 0x12218f 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1459, 1455]
    (.letOp (n := 1462) (.exec 0x12218f (fun s => s.RIP = 0x12218f) (xorR32R32Effect 0x12218f 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1459, 1455]
    (.letOp (n := 1463) (.out 0x122191 (movR32R32Effect 0x122191 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[1276]
    (.letOp (n := 1464) (.exec 0x122191 (fun s => s.RIP = 0x122191) (movR32R32Effect 0x122191 3 1 13) (Reg.operands [.gpr 13] [])) #v[1276]
    (.letOp (n := 1465) (.out 0x122194 (rolR32Effect 0x122194 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1463]
    (.letOp (n := 1466) (.exec 0x122194 (fun s => s.RIP = 0x122194) (rolR32Effect 0x122194 3 1 15) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1463]
    (b_l121930_36))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_35 : List UInt8 :=
  [0x44, 0x21, 0xF6, 0x44, 0x89, 0xDF, 0x44, 0x31, 0xF7, 0x21, 0xEF, 0x31, 0xF7, 0x01, 0xCF, 0x49,
    0x89, 0xF8, 0x48, 0x8B, 0x7C, 0x24, 0x68, 0x89, 0xF9, 0xC1, 0xC1, 0x19, 0x41, 0x01, 0xC1, 0x89,
    0xFE, 0xC1, 0xC6, 0x0E, 0x41, 0x01, 0xC0, 0x31, 0xCE, 0x89, 0xF8, 0xC1, 0xE8, 0x03, 0x31, 0xF0,
    0x44, 0x89, 0xE9, 0xC1, 0xC1, 0x0F] ++ bytes_l121930_36

theorem code_l121930_35 : ∀ x ∈ codeRange 0x122161 bytes_l121930_35, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22161 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_36

def b_l121930_34 : Block Op Label signature Reg.count 1389 :=
  .letOp (n := 1389) (.out 0x122123 (movR32R32Effect 0x122123 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[1250]
    (.letOp (n := 1390) (.exec 0x122123 (fun s => s.RIP = 0x122123) (movR32R32Effect 0x122123 3 6 15) (Reg.operands [.gpr 15] [])) #v[1250]
    (.letOp (n := 1391) (.out 0x122126 (xorR32R32Effect 0x122126 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[1389, 1174]
    (.letOp (n := 1392) (.exec 0x122126 (fun s => s.RIP = 0x122126) (xorR32R32Effect 0x122126 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[1389, 1174]
    (.letOp (n := 1393) (.out 0x122128 (andR32R32Effect 0x122128 2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[1391, 1328]
    (.letOp (n := 1394) (.exec 0x122128 (fun s => s.RIP = 0x122128) (andR32R32Effect 0x122128 2 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[1391, 1328]
    (.letOp (n := 1395) (.exec 0x12212a (StorePre 0x12212a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x12212a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12212a 3 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1328, 4]
    (.letOp (n := 1396) (.out 0x122132 (xorR32R32Effect 0x122132 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[1393, 1174]
    (.letOp (n := 1397) (.exec 0x122132 (fun s => s.RIP = 0x122132) (xorR32R32Effect 0x122132 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[1393, 1174]
    (.letOp (n := 1398) (.out 0x122134 (addR32R32Effect 0x122134 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[1097, 1371]
    (.letOp (n := 1399) (.exec 0x122134 (fun s => s.RIP = 0x122134) (addR32R32Effect 0x122134 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[1097, 1371]
    (.letOp (n := 1400) (.out 0x122137 (movR32R32Effect 0x122137 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[1336]
    (.letOp (n := 1401) (.exec 0x122137 (fun s => s.RIP = 0x122137) (movR32R32Effect 0x122137 3 7 8) (Reg.operands [.gpr 8] [])) #v[1336]
    (.letOp (n := 1402) (.out 0x12213a (rolR32Effect 0x12213a 3 7 30) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1400]
    (.letOp (n := 1403) (.exec 0x12213a (fun s => s.RIP = 0x12213a) (rolR32Effect 0x12213a 3 7 30) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1400]
    (.letOp (n := 1404) (.out 0x12213d (addR32R32Effect 0x12213d 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1398, 1396]
    (.letOp (n := 1405) (.exec 0x12213d (fun s => s.RIP = 0x12213d) (addR32R32Effect 0x12213d 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1398, 1396]
    (.letOp (n := 1406) (.out 0x12213f (movR32R32Effect 0x12213f 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[1336]
    (.letOp (n := 1407) (.exec 0x12213f (fun s => s.RIP = 0x12213f) (movR32R32Effect 0x12213f 3 6 8) (Reg.operands [.gpr 8] [])) #v[1336]
    (.letOp (n := 1408) (.out 0x122142 (rolR32Effect 0x122142 3 6 19) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1406]
    (.letOp (n := 1409) (.exec 0x122142 (fun s => s.RIP = 0x122142) (rolR32Effect 0x122142 3 6 19) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1406]
    (.letOp (n := 1410) (.out 0x122145 (addR32R32Effect 0x122145 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1404, 1387]
    (.letOp (n := 1411) (.exec 0x122145 (fun s => s.RIP = 0x122145) (addR32R32Effect 0x122145 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1404, 1387]
    (.letOp (n := 1412) (.out 0x122147 (addEaxImm32Effect 0x122147 0xe49b69c1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1410]
    (.letOp (n := 1413) (.exec 0x122147 (fun s => s.RIP = 0x122147) (addEaxImm32Effect 0x122147 0xe49b69c1) (Reg.operands [.gpr 0] [])) #v[1410]
    (.letOp (n := 1414) (.out 0x12214c (movR32R32Effect 0x12214c 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[1336]
    (.letOp (n := 1415) (.exec 0x12214c (fun s => s.RIP = 0x12214c) (movR32R32Effect 0x12214c 3 1 8) (Reg.operands [.gpr 8] [])) #v[1336]
    (.letOp (n := 1416) (.out 0x12214f (movR64R64Effect 0x12214f 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 8] []) (.reg (.gpr 5))) #v[1336]
    (.letOp (n := 1417) (.exec 0x12214f (fun s => s.RIP = 0x12214f) (movR64R64Effect 0x12214f 5 8) (Reg.operands [.gpr 8] [])) #v[1336]
    (.letOp (n := 1418) (.out 0x122152 (rolR32Effect 0x122152 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1414]
    (.letOp (n := 1419) (.exec 0x122152 (fun s => s.RIP = 0x122152) (rolR32Effect 0x122152 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1414]
    (.letOp (n := 1420) (.out 0x122155 (xorR32R32Effect 0x122155 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[1408, 1402]
    (.letOp (n := 1421) (.exec 0x122155 (fun s => s.RIP = 0x122155) (xorR32R32Effect 0x122155 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[1408, 1402]
    (.letOp (n := 1422) (.out 0x122157 (xorR32R32Effect 0x122157 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1418, 1420]
    (.letOp (n := 1423) (.exec 0x122157 (fun s => s.RIP = 0x122157) (xorR32R32Effect 0x122157 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1418, 1420]
    (.letOp (n := 1424) (.out 0x122159 (movR32R32Effect 0x122159 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[1254]
    (.letOp (n := 1425) (.exec 0x122159 (fun s => s.RIP = 0x122159) (movR32R32Effect 0x122159 3 6 11) (Reg.operands [.gpr 11] [])) #v[1254]
    (.letOp (n := 1426) (.exec 0x12215c (StorePre 0x12215c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12215c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12215c 14 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[1180, 4]
    (b_l121930_35))))))))))))))))))))))))))))))))))))))

def bytes_l121930_34 : List UInt8 :=
  [0x44, 0x89, 0xFE, 0x31, 0xD6, 0x21, 0xDE, 0x48, 0x89, 0x9C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x31,
    0xD6, 0x44, 0x01, 0xD0, 0x44, 0x89, 0xC7, 0xC1, 0xC7, 0x1E, 0x01, 0xF0, 0x44, 0x89, 0xC6, 0xC1,
    0xC6, 0x13, 0x01, 0xC8, 0x05, 0xC1, 0x69, 0x9B, 0xE4, 0x44, 0x89, 0xC1, 0x4C, 0x89, 0xC5, 0xC1,
    0xC1, 0x0A, 0x31, 0xFE, 0x31, 0xF1, 0x44, 0x89, 0xDE, 0x4C, 0x89, 0x74, 0x24, 0x58] ++ bytes_l121930_35

theorem code_l121930_34 : ∀ x ∈ codeRange 0x122123 bytes_l121930_34, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22123 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_35

def b_l121930_33 : Block Op Label signature Reg.count 1350 :=
  .letOp (n := 1350) (.exec 0x1220eb (StorePre 0x1220eb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x1220eb + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1220eb 5 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[1198, 4]
    (.letOp (n := 1351) (.out 0x1220ef (movR32R32Effect 0x1220ef 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[1198]
    (.letOp (n := 1352) (.exec 0x1220ef (fun s => s.RIP = 0x1220ef) (movR32R32Effect 0x1220ef 2 1 5) (Reg.operands [.gpr 5] [])) #v[1198]
    (.letOp (n := 1353) (.out 0x1220f1 (rolR32Effect 0x1220f1 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1351]
    (.letOp (n := 1354) (.exec 0x1220f1 (fun s => s.RIP = 0x1220f1) (rolR32Effect 0x1220f1 3 1 15) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1351]
    (.letOp (n := 1355) (.out 0x1220f4 (movR32R32Effect 0x1220f4 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[1198]
    (.letOp (n := 1356) (.exec 0x1220f4 (fun s => s.RIP = 0x1220f4) (movR32R32Effect 0x1220f4 2 7 5) (Reg.operands [.gpr 5] [])) #v[1198]
    (.letOp (n := 1357) (.out 0x1220f6 (rolR32Effect 0x1220f6 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1355]
    (.letOp (n := 1358) (.exec 0x1220f6 (fun s => s.RIP = 0x1220f6) (rolR32Effect 0x1220f6 3 7 13) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1355]
    (.letOp (n := 1359) (.out 0x1220f9 (xorR32R32Effect 0x1220f9 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[1357, 1353]
    (.letOp (n := 1360) (.exec 0x1220f9 (fun s => s.RIP = 0x1220f9) (xorR32R32Effect 0x1220f9 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[1357, 1353]
    (.letOp (n := 1361) (.out 0x1220fb (shrR32Effect 0x1220fb 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[1198]
    (.letOp (n := 1362) (.exec 0x1220fb (fun s => s.RIP = 0x1220fb) (shrR32Effect 0x1220fb 3 5 10) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1198]
    (.letOp (n := 1363) (.out 0x1220fe (xorR32R32Effect 0x1220fe 2 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 7] []) (.reg (.gpr 5))) #v[1361, 1359]
    (.letOp (n := 1364) (.exec 0x1220fe (fun s => s.RIP = 0x1220fe) (xorR32R32Effect 0x1220fe 2 5 7) (Reg.operands [.gpr 5, .gpr 7] [])) #v[1361, 1359]
    (.letOp (n := 1365) (.out 0x122100 (movR64M64Effect 0x122100 10 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 1366) (.exec 0x122100 (LoadPre 0x122100 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x122100 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x122100 10 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1367) (.out 0x122105 (addR32M32Effect 0x122105 5 10 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[1365, 4]
    (.letOp (n := 1368) (.exec 0x122105 (LoadPre 0x122105 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x122105 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x122105 5 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[1365, 4]
    (.letOp (n := 1369) (.out 0x12210a (addR32R32Effect 0x12210a 3 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[1367, 1348]
    (.letOp (n := 1370) (.exec 0x12210a (fun s => s.RIP = 0x12210a) (addR32R32Effect 0x12210a 3 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[1367, 1348]
    (.letOp (n := 1371) (.out 0x12210d (addR32R32Effect 0x12210d 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[1369, 1363]
    (.letOp (n := 1372) (.exec 0x12210d (fun s => s.RIP = 0x12210d) (addR32R32Effect 0x12210d 3 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[1369, 1363]
    (.letOp (n := 1373) (.out 0x122110 (movR32R32Effect 0x122110 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[1328]
    (.letOp (n := 1374) (.exec 0x122110 (fun s => s.RIP = 0x122110) (movR32R32Effect 0x122110 2 1 3) (Reg.operands [.gpr 3] [])) #v[1328]
    (.letOp (n := 1375) (.out 0x122112 (rolR32Effect 0x122112 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1373]
    (.letOp (n := 1376) (.exec 0x122112 (fun s => s.RIP = 0x122112) (rolR32Effect 0x122112 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1373]
    (.letOp (n := 1377) (.out 0x122115 (movR32R32Effect 0x122115 2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[1328]
    (.letOp (n := 1378) (.exec 0x122115 (fun s => s.RIP = 0x122115) (movR32R32Effect 0x122115 2 6 3) (Reg.operands [.gpr 3] [])) #v[1328]
    (.letOp (n := 1379) (.out 0x122117 (rolR32Effect 0x122117 3 6 21) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1377]
    (.letOp (n := 1380) (.exec 0x122117 (fun s => s.RIP = 0x122117) (rolR32Effect 0x122117 3 6 21) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1377]
    (.letOp (n := 1381) (.out 0x12211a (xorR32R32Effect 0x12211a 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1379, 1375]
    (.letOp (n := 1382) (.exec 0x12211a (fun s => s.RIP = 0x12211a) (xorR32R32Effect 0x12211a 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1379, 1375]
    (.letOp (n := 1383) (.out 0x12211c (movR32R32Effect 0x12211c 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[1328]
    (.letOp (n := 1384) (.exec 0x12211c (fun s => s.RIP = 0x12211c) (movR32R32Effect 0x12211c 2 1 3) (Reg.operands [.gpr 3] [])) #v[1328]
    (.letOp (n := 1385) (.out 0x12211e (rolR32Effect 0x12211e 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1383]
    (.letOp (n := 1386) (.exec 0x12211e (fun s => s.RIP = 0x12211e) (rolR32Effect 0x12211e 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1383]
    (.letOp (n := 1387) (.out 0x122121 (xorR32R32Effect 0x122121 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1385, 1381]
    (.letOp (n := 1388) (.exec 0x122121 (fun s => s.RIP = 0x122121) (xorR32R32Effect 0x122121 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1385, 1381]
    (b_l121930_34)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_33 : List UInt8 :=
  [0x89, 0x6C, 0x24, 0x64, 0x89, 0xE9, 0xC1, 0xC1, 0x0F, 0x89, 0xEF, 0xC1, 0xC7, 0x0D, 0x31, 0xCF,
    0xC1, 0xED, 0x0A, 0x31, 0xFD, 0x4C, 0x8B, 0x54, 0x24, 0x50, 0x44, 0x03, 0x54, 0x24, 0x08, 0x41,
    0x01, 0xF2, 0x41, 0x01, 0xEA, 0x89, 0xD9, 0xC1, 0xC1, 0x1A, 0x89, 0xDE, 0xC1, 0xC6, 0x15, 0x31,
    0xCE, 0x89, 0xD9, 0xC1, 0xC1, 0x07, 0x31, 0xF1] ++ bytes_l121930_34

theorem code_l121930_33 : ∀ x ∈ codeRange 0x1220eb bytes_l121930_33, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x220eb 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_34

def b_l121930_32 : Block Op Label signature Reg.count 1310 :=
  .letOp (n := 1310) (.out 0x1220b1 (rolR32Effect 0x1220b1 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1308]
    (.letOp (n := 1311) (.exec 0x1220b1 (fun s => s.RIP = 0x1220b1) (rolR32Effect 0x1220b1 3 6 10) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1308]
    (.letOp (n := 1312) (.out 0x1220b4 (xorR32R32Effect 0x1220b4 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[1310, 1306]
    (.letOp (n := 1313) (.exec 0x1220b4 (fun s => s.RIP = 0x1220b4) (xorR32R32Effect 0x1220b4 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[1310, 1306]
    (.letOp (n := 1314) (.out 0x1220b6 (movR32R32Effect 0x1220b6 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[1180]
    (.letOp (n := 1315) (.exec 0x1220b6 (fun s => s.RIP = 0x1220b6) (movR32R32Effect 0x1220b6 3 7 14) (Reg.operands [.gpr 14] [])) #v[1180]
    (.letOp (n := 1316) (.out 0x1220b9 (andR32R32Effect 0x1220b9 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[1314, 1099]
    (.letOp (n := 1317) (.exec 0x1220b9 (fun s => s.RIP = 0x1220b9) (andR32R32Effect 0x1220b9 3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[1314, 1099]
    (.letOp (n := 1318) (.out 0x1220bc (movR32R32Effect 0x1220bc 3 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[1180]
    (.letOp (n := 1319) (.exec 0x1220bc (fun s => s.RIP = 0x1220bc) (movR32R32Effect 0x1220bc 3 8 14) (Reg.operands [.gpr 14] [])) #v[1180]
    (.letOp (n := 1320) (.out 0x1220bf (xorR32R32Effect 0x1220bf 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[1318, 1099]
    (.letOp (n := 1321) (.exec 0x1220bf (fun s => s.RIP = 0x1220bf) (xorR32R32Effect 0x1220bf 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[1318, 1099]
    (.letOp (n := 1322) (.out 0x1220c2 (andR32R32Effect 0x1220c2 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[1320, 1254]
    (.letOp (n := 1323) (.exec 0x1220c2 (fun s => s.RIP = 0x1220c2) (andR32R32Effect 0x1220c2 3 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[1320, 1254]
    (.letOp (n := 1324) (.out 0x1220c5 (xorR32R32Effect 0x1220c5 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[1322, 1316]
    (.letOp (n := 1325) (.exec 0x1220c5 (fun s => s.RIP = 0x1220c5) (xorR32R32Effect 0x1220c5 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[1322, 1316]
    (.letOp (n := 1326) (.out 0x1220c8 (addR32R32Effect 0x1220c8 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[1324, 1312]
    (.letOp (n := 1327) (.exec 0x1220c8 (fun s => s.RIP = 0x1220c8) (addR32R32Effect 0x1220c8 3 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[1324, 1312]
    (.letOp (n := 1328) (.out 0x1220cb (addR32R32Effect 0x1220cb 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[1026, 1300]
    (.letOp (n := 1329) (.exec 0x1220cb (fun s => s.RIP = 0x1220cb) (addR32R32Effect 0x1220cb 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[1026, 1300]
    (.letOp (n := 1330) (.out 0x1220cd (movR64M64Effect 0x1220cd 12 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 1331) (.exec 0x1220cd (LoadPre 0x1220cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1220cd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1220cd 12 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1332) (.out 0x1220d2 (movR32R32Effect 0x1220d2 3 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[1330]
    (.letOp (n := 1333) (.exec 0x1220d2 (fun s => s.RIP = 0x1220d2) (movR32R32Effect 0x1220d2 3 6 12) (Reg.operands [.gpr 12] [])) #v[1330]
    (.letOp (n := 1334) (.out 0x1220d5 (rolR32Effect 0x1220d5 3 6 25) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1332]
    (.letOp (n := 1335) (.exec 0x1220d5 (fun s => s.RIP = 0x1220d5) (rolR32Effect 0x1220d5 3 6 25) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1332]
    (.letOp (n := 1336) (.out 0x1220d8 (addR32R32Effect 0x1220d8 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[1326, 1300]
    (.letOp (n := 1337) (.exec 0x1220d8 (fun s => s.RIP = 0x1220d8) (addR32R32Effect 0x1220d8 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[1326, 1300]
    (.letOp (n := 1338) (.out 0x1220db (movR32R32Effect 0x1220db 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[1330]
    (.letOp (n := 1339) (.exec 0x1220db (fun s => s.RIP = 0x1220db) (movR32R32Effect 0x1220db 3 1 12) (Reg.operands [.gpr 12] [])) #v[1330]
    (.letOp (n := 1340) (.out 0x1220de (rolR32Effect 0x1220de 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1338]
    (.letOp (n := 1341) (.exec 0x1220de (fun s => s.RIP = 0x1220de) (rolR32Effect 0x1220de 3 1 14) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1338]
    (.letOp (n := 1342) (.out 0x1220e1 (xorR32R32Effect 0x1220e1 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1340, 1334]
    (.letOp (n := 1343) (.exec 0x1220e1 (fun s => s.RIP = 0x1220e1) (xorR32R32Effect 0x1220e1 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1340, 1334]
    (.letOp (n := 1344) (.out 0x1220e3 (movR32R32Effect 0x1220e3 3 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[1330]
    (.letOp (n := 1345) (.exec 0x1220e3 (fun s => s.RIP = 0x1220e3) (movR32R32Effect 0x1220e3 3 6 12) (Reg.operands [.gpr 12] [])) #v[1330]
    (.letOp (n := 1346) (.out 0x1220e6 (shrR32Effect 0x1220e6 3 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1344]
    (.letOp (n := 1347) (.exec 0x1220e6 (fun s => s.RIP = 0x1220e6) (shrR32Effect 0x1220e6 3 6 3) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1344]
    (.letOp (n := 1348) (.out 0x1220e9 (xorR32R32Effect 0x1220e9 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1346, 1342]
    (.letOp (n := 1349) (.exec 0x1220e9 (fun s => s.RIP = 0x1220e9) (xorR32R32Effect 0x1220e9 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1346, 1342]
    (b_l121930_33))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_32 : List UInt8 :=
  [0xC1, 0xC6, 0x0A, 0x31, 0xFE, 0x44, 0x89, 0xF7, 0x44, 0x21, 0xCF, 0x45, 0x89, 0xF0, 0x45, 0x31,
    0xC8, 0x45, 0x21, 0xD8, 0x41, 0x31, 0xF8, 0x41, 0x01, 0xF0, 0x01, 0xCB, 0x4C, 0x8B, 0x64, 0x24,
    0x38, 0x44, 0x89, 0xE6, 0xC1, 0xC6, 0x19, 0x41, 0x01, 0xC8, 0x44, 0x89, 0xE1, 0xC1, 0xC1, 0x0E,
    0x31, 0xF1, 0x44, 0x89, 0xE6, 0xC1, 0xEE, 0x03, 0x31, 0xCE] ++ bytes_l121930_33

theorem code_l121930_32 : ∀ x ∈ codeRange 0x1220b1 bytes_l121930_32, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x220b1 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_33

def b_l121930_31 : Block Op Label signature Reg.count 1270 :=
  .letOp (n := 1270) (.out 0x122074 (xorR32R32Effect 0x122074 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1268, 1264]
    (.letOp (n := 1271) (.exec 0x122074 (fun s => s.RIP = 0x122074) (xorR32R32Effect 0x122074 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1268, 1264]
    (.letOp (n := 1272) (.out 0x122076 (movR64M64Effect 0x122076 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 1273) (.exec 0x122076 (LoadPre 0x122076 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x122076 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x122076 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1274) (.out 0x12207b (movR32M32Effect 0x12207b 13 (.base 6 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[1272]
    (.letOp (n := 1275) (.exec 0x12207b (LoadPre 0x12207b (fun s => AddrMode.addr (.base 6 (.d8 0x3c)) s (0x12207b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12207b 13 (.base 6 (.d8 0x3c))) (Reg.operands [.gpr 6] [])) #v[1272]
    (.letOp (n := 1276) (.out 0x12207f (bswapR32Effect 0x12207f 3 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[1274]
    (.letOp (n := 1277) (.exec 0x12207f (fun s => s.RIP = 0x12207f) (bswapR32Effect 0x12207f 3 13) (Reg.operands [.gpr 13] [])) #v[1274]
    (.letOp (n := 1278) (.out 0x122082 (movR32R32Effect 0x122082 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[1250]
    (.letOp (n := 1279) (.exec 0x122082 (fun s => s.RIP = 0x122082) (movR32R32Effect 0x122082 3 6 15) (Reg.operands [.gpr 15] [])) #v[1250]
    (.letOp (n := 1280) (.out 0x122085 (andR32R32Effect 0x122085 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[1278, 1174]
    (.letOp (n := 1281) (.exec 0x122085 (fun s => s.RIP = 0x122085) (andR32R32Effect 0x122085 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[1278, 1174]
    (.letOp (n := 1282) (.out 0x122087 (addR32R32Effect 0x122087 3 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[1020, 1276]
    (.letOp (n := 1283) (.exec 0x122087 (fun s => s.RIP = 0x122087) (addR32R32Effect 0x122087 3 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[1020, 1276]
    (.letOp (n := 1284) (.out 0x12208a (addR32R32Effect 0x12208a 3 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[1282, 1280]
    (.letOp (n := 1285) (.exec 0x12208a (fun s => s.RIP = 0x12208a) (addR32R32Effect 0x12208a 3 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[1282, 1280]
    (.letOp (n := 1286) (.out 0x12208d (movR32R32Effect 0x12208d 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[1250]
    (.letOp (n := 1287) (.exec 0x12208d (fun s => s.RIP = 0x12208d) (movR32R32Effect 0x12208d 3 6 15) (Reg.operands [.gpr 15] [])) #v[1250]
    (.letOp (n := 1288) (.out 0x122090 (notR32Effect 0x122090 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[1286]
    (.letOp (n := 1289) (.exec 0x122090 (fun s => s.RIP = 0x122090) (notR32Effect 0x122090 2 6) (Reg.operands [.gpr 6] [])) #v[1286]
    (.letOp (n := 1290) (.out 0x122092 (andR32R32Effect 0x122092 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[1288, 1097]
    (.letOp (n := 1291) (.exec 0x122092 (fun s => s.RIP = 0x122092) (andR32R32Effect 0x122092 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[1288, 1097]
    (.letOp (n := 1292) (.out 0x122094 (addR32R32Effect 0x122094 3 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[1284, 1290]
    (.letOp (n := 1293) (.exec 0x122094 (fun s => s.RIP = 0x122094) (addR32R32Effect 0x122094 3 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[1284, 1290]
    (.letOp (n := 1294) (.out 0x122097 (movR32R32Effect 0x122097 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[1254]
    (.letOp (n := 1295) (.exec 0x122097 (fun s => s.RIP = 0x122097) (movR32R32Effect 0x122097 3 6 11) (Reg.operands [.gpr 11] [])) #v[1254]
    (.letOp (n := 1296) (.out 0x12209a (rolR32Effect 0x12209a 3 6 30) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1294]
    (.letOp (n := 1297) (.exec 0x12209a (fun s => s.RIP = 0x12209a) (rolR32Effect 0x12209a 3 6 30) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1294]
    (.letOp (n := 1298) (.out 0x12209d (addR32R32Effect 0x12209d 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[1270, 1292]
    (.letOp (n := 1299) (.exec 0x12209d (fun s => s.RIP = 0x12209d) (addR32R32Effect 0x12209d 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[1270, 1292]
    (.letOp (n := 1300) (.out 0x1220a0 (addR32Imm32Effect 0x1220a0 6 1 0xc19bf174) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1298]
    (.letOp (n := 1301) (.exec 0x1220a0 (fun s => s.RIP = 0x1220a0) (addR32Imm32Effect 0x1220a0 6 1 0xc19bf174) (Reg.operands [.gpr 1] [])) #v[1298]
    (.letOp (n := 1302) (.out 0x1220a6 (movR32R32Effect 0x1220a6 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 11] []) (.reg (.gpr 7))) #v[1254]
    (.letOp (n := 1303) (.exec 0x1220a6 (fun s => s.RIP = 0x1220a6) (movR32R32Effect 0x1220a6 3 7 11) (Reg.operands [.gpr 11] [])) #v[1254]
    (.letOp (n := 1304) (.out 0x1220a9 (rolR32Effect 0x1220a9 3 7 19) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1302]
    (.letOp (n := 1305) (.exec 0x1220a9 (fun s => s.RIP = 0x1220a9) (rolR32Effect 0x1220a9 3 7 19) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1302]
    (.letOp (n := 1306) (.out 0x1220ac (xorR32R32Effect 0x1220ac 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[1304, 1296]
    (.letOp (n := 1307) (.exec 0x1220ac (fun s => s.RIP = 0x1220ac) (xorR32R32Effect 0x1220ac 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[1304, 1296]
    (.letOp (n := 1308) (.out 0x1220ae (movR32R32Effect 0x1220ae 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[1254]
    (.letOp (n := 1309) (.exec 0x1220ae (fun s => s.RIP = 0x1220ae) (movR32R32Effect 0x1220ae 3 6 11) (Reg.operands [.gpr 11] [])) #v[1254]
    (b_l121930_32))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_31 : List UInt8 :=
  [0x31, 0xF1, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x44, 0x8B, 0x6E, 0x3C, 0x41, 0x0F, 0xCD, 0x44, 0x89,
    0xFE, 0x21, 0xD6, 0x45, 0x01, 0xEA, 0x41, 0x01, 0xF2, 0x44, 0x89, 0xFE, 0xF7, 0xD6, 0x21, 0xC6,
    0x41, 0x01, 0xF2, 0x44, 0x89, 0xDE, 0xC1, 0xC6, 0x1E, 0x44, 0x01, 0xD1, 0x81, 0xC1, 0x74, 0xF1,
    0x9B, 0xC1, 0x44, 0x89, 0xDF, 0xC1, 0xC7, 0x13, 0x31, 0xF7, 0x44, 0x89, 0xDE] ++ bytes_l121930_32

theorem code_l121930_31 : ∀ x ∈ codeRange 0x122074 bytes_l121930_31, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22074 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_32

def b_l121930_30 : Block Op Label signature Reg.count 1230 :=
  .letOp (n := 1230) (.out 0x12203b (movR32R32Effect 0x12203b 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[1180]
    (.letOp (n := 1231) (.exec 0x12203b (fun s => s.RIP = 0x12203b) (movR32R32Effect 0x12203b 3 6 14) (Reg.operands [.gpr 14] [])) #v[1180]
    (.letOp (n := 1232) (.out 0x12203e (rolR32Effect 0x12203e 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1230]
    (.letOp (n := 1233) (.exec 0x12203e (fun s => s.RIP = 0x12203e) (rolR32Effect 0x12203e 3 6 10) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1230]
    (.letOp (n := 1234) (.out 0x122041 (xorR32R32Effect 0x122041 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[1232, 1228]
    (.letOp (n := 1235) (.exec 0x122041 (fun s => s.RIP = 0x122041) (xorR32R32Effect 0x122041 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[1232, 1228]
    (.letOp (n := 1236) (.out 0x122043 (movR32R32Effect 0x122043 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[1099]
    (.letOp (n := 1237) (.exec 0x122043 (fun s => s.RIP = 0x122043) (movR32R32Effect 0x122043 3 7 9) (Reg.operands [.gpr 9] [])) #v[1099]
    (.letOp (n := 1238) (.out 0x122046 (andR32R32Effect 0x122046 2 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[1236, 1026]
    (.letOp (n := 1239) (.exec 0x122046 (fun s => s.RIP = 0x122046) (andR32R32Effect 0x122046 2 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[1236, 1026]
    (.letOp (n := 1240) (.out 0x122048 (movR32R32Effect 0x122048 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[1099]
    (.letOp (n := 1241) (.exec 0x122048 (fun s => s.RIP = 0x122048) (movR32R32Effect 0x122048 3 8 9) (Reg.operands [.gpr 9] [])) #v[1099]
    (.letOp (n := 1242) (.out 0x12204b (xorR32R32Effect 0x12204b 3 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[1240, 1026]
    (.letOp (n := 1243) (.exec 0x12204b (fun s => s.RIP = 0x12204b) (xorR32R32Effect 0x12204b 3 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[1240, 1026]
    (.letOp (n := 1244) (.out 0x12204e (andR32R32Effect 0x12204e 3 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[1242, 1180]
    (.letOp (n := 1245) (.exec 0x12204e (fun s => s.RIP = 0x12204e) (andR32R32Effect 0x12204e 3 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[1242, 1180]
    (.letOp (n := 1246) (.out 0x122051 (xorR32R32Effect 0x122051 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[1244, 1238]
    (.letOp (n := 1247) (.exec 0x122051 (fun s => s.RIP = 0x122051) (xorR32R32Effect 0x122051 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[1244, 1238]
    (.letOp (n := 1248) (.out 0x122054 (addR32R32Effect 0x122054 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[1246, 1234]
    (.letOp (n := 1249) (.exec 0x122054 (fun s => s.RIP = 0x122054) (addR32R32Effect 0x122054 3 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[1246, 1234]
    (.letOp (n := 1250) (.out 0x122057 (addR32R32Effect 0x122057 3 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[945, 1218]
    (.letOp (n := 1251) (.exec 0x122057 (fun s => s.RIP = 0x122057) (addR32R32Effect 0x122057 3 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[945, 1218]
    (.letOp (n := 1252) (.out 0x12205a (addR32R32Effect 0x12205a 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[1248, 1218]
    (.letOp (n := 1253) (.exec 0x12205a (fun s => s.RIP = 0x12205a) (addR32R32Effect 0x12205a 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[1248, 1218]
    (.letOp (n := 1254) (.out 0x12205d (movR64R64Effect 0x12205d 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 8] []) (.reg (.gpr 11))) #v[1252]
    (.letOp (n := 1255) (.exec 0x12205d (fun s => s.RIP = 0x12205d) (movR64R64Effect 0x12205d 11 8) (Reg.operands [.gpr 8] [])) #v[1252]
    (.letOp (n := 1256) (.out 0x122060 (movR32R32Effect 0x122060 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[1250]
    (.letOp (n := 1257) (.exec 0x122060 (fun s => s.RIP = 0x122060) (movR32R32Effect 0x122060 3 1 15) (Reg.operands [.gpr 15] [])) #v[1250]
    (.letOp (n := 1258) (.out 0x122063 (rolR32Effect 0x122063 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1256]
    (.letOp (n := 1259) (.exec 0x122063 (fun s => s.RIP = 0x122063) (rolR32Effect 0x122063 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1256]
    (.letOp (n := 1260) (.out 0x122066 (movR32R32Effect 0x122066 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[1250]
    (.letOp (n := 1261) (.exec 0x122066 (fun s => s.RIP = 0x122066) (movR32R32Effect 0x122066 3 6 15) (Reg.operands [.gpr 15] [])) #v[1250]
    (.letOp (n := 1262) (.out 0x122069 (rolR32Effect 0x122069 3 6 21) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1260]
    (.letOp (n := 1263) (.exec 0x122069 (fun s => s.RIP = 0x122069) (rolR32Effect 0x122069 3 6 21) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1260]
    (.letOp (n := 1264) (.out 0x12206c (xorR32R32Effect 0x12206c 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1262, 1258]
    (.letOp (n := 1265) (.exec 0x12206c (fun s => s.RIP = 0x12206c) (xorR32R32Effect 0x12206c 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1262, 1258]
    (.letOp (n := 1266) (.out 0x12206e (movR32R32Effect 0x12206e 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[1250]
    (.letOp (n := 1267) (.exec 0x12206e (fun s => s.RIP = 0x12206e) (movR32R32Effect 0x12206e 3 1 15) (Reg.operands [.gpr 15] [])) #v[1250]
    (.letOp (n := 1268) (.out 0x122071 (rolR32Effect 0x122071 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1266]
    (.letOp (n := 1269) (.exec 0x122071 (fun s => s.RIP = 0x122071) (rolR32Effect 0x122071 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1266]
    (b_l121930_31))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_30 : List UInt8 :=
  [0x44, 0x89, 0xF6, 0xC1, 0xC6, 0x0A, 0x31, 0xFE, 0x44, 0x89, 0xCF, 0x21, 0xDF, 0x45, 0x89, 0xC8,
    0x41, 0x31, 0xD8, 0x45, 0x21, 0xF0, 0x41, 0x31, 0xF8, 0x41, 0x01, 0xF0, 0x41, 0x01, 0xCF, 0x41,
    0x01, 0xC8, 0x4D, 0x89, 0xC3, 0x44, 0x89, 0xF9, 0xC1, 0xC1, 0x1A, 0x44, 0x89, 0xFE, 0xC1, 0xC6,
    0x15, 0x31, 0xCE, 0x44, 0x89, 0xF9, 0xC1, 0xC1, 0x07] ++ bytes_l121930_31

theorem code_l121930_30 : ∀ x ∈ codeRange 0x12203b bytes_l121930_30, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2203b 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_31

def b_l121930_29 : Block Op Label signature Reg.count 1190 :=
  .letOp (n := 1190) (.out 0x122000 (rolR32Effect 0x122000 3 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1188]
    (.letOp (n := 1191) (.exec 0x122000 (fun s => s.RIP = 0x122000) (rolR32Effect 0x122000 3 6 7) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1188]
    (.letOp (n := 1192) (.out 0x122003 (xorR32R32Effect 0x122003 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1190, 1186]
    (.letOp (n := 1193) (.exec 0x122003 (fun s => s.RIP = 0x122003) (xorR32R32Effect 0x122003 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1190, 1186]
    (.letOp (n := 1194) (.out 0x122005 (movR64M64Effect 0x122005 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 1195) (.exec 0x122005 (LoadPre 0x122005 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x122005 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x122005 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1196) (.out 0x12200a (movR32M32LowEffect 0x12200a 5 (.base 1 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[1194]
    (.letOp (n := 1197) (.exec 0x12200a (LoadPre 0x12200a (fun s => AddrMode.addr (.base 1 (.d8 0x38)) s (0x12200a + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12200a 5 (.base 1 (.d8 0x38))) (Reg.operands [.gpr 1] [])) #v[1194]
    (.letOp (n := 1198) (.out 0x12200d (bswapR32Effect 0x12200d 2 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[1196]
    (.letOp (n := 1199) (.exec 0x12200d (fun s => s.RIP = 0x12200d) (bswapR32Effect 0x12200d 2 5) (Reg.operands [.gpr 5] [])) #v[1196]
    (.letOp (n := 1200) (.out 0x12200f (movR32R32Effect 0x12200f 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1174]
    (.letOp (n := 1201) (.exec 0x12200f (fun s => s.RIP = 0x12200f) (movR32R32Effect 0x12200f 2 1 2) (Reg.operands [.gpr 2] [])) #v[1174]
    (.letOp (n := 1202) (.out 0x122011 (andR32R32Effect 0x122011 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1200, 1097]
    (.letOp (n := 1203) (.exec 0x122011 (fun s => s.RIP = 0x122011) (andR32R32Effect 0x122011 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1200, 1097]
    (.letOp (n := 1204) (.out 0x122013 (addR32R32Effect 0x122013 3 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[943, 1198]
    (.letOp (n := 1205) (.exec 0x122013 (fun s => s.RIP = 0x122013) (addR32R32Effect 0x122013 3 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[943, 1198]
    (.letOp (n := 1206) (.out 0x122016 (addR32R32Effect 0x122016 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[1204, 1202]
    (.letOp (n := 1207) (.exec 0x122016 (fun s => s.RIP = 0x122016) (addR32R32Effect 0x122016 3 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[1204, 1202]
    (.letOp (n := 1208) (.out 0x122019 (movR32R32Effect 0x122019 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1174]
    (.letOp (n := 1209) (.exec 0x122019 (fun s => s.RIP = 0x122019) (movR32R32Effect 0x122019 2 1 2) (Reg.operands [.gpr 2] [])) #v[1174]
    (.letOp (n := 1210) (.out 0x12201b (notR32Effect 0x12201b 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1208]
    (.letOp (n := 1211) (.exec 0x12201b (fun s => s.RIP = 0x12201b) (notR32Effect 0x12201b 2 1) (Reg.operands [.gpr 1] [])) #v[1208]
    (.letOp (n := 1212) (.out 0x12201d (andR32R32Effect 0x12201d 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[1210, 1020]
    (.letOp (n := 1213) (.exec 0x12201d (fun s => s.RIP = 0x12201d) (andR32R32Effect 0x12201d 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[1210, 1020]
    (.letOp (n := 1214) (.out 0x122020 (addR32R32Effect 0x122020 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[1206, 1212]
    (.letOp (n := 1215) (.exec 0x122020 (fun s => s.RIP = 0x122020) (addR32R32Effect 0x122020 3 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[1206, 1212]
    (.letOp (n := 1216) (.out 0x122023 (leaR32Effect 0x122023 4 1 (.sib 6 (some 11) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 11] []) (.reg (.gpr 1))) #v[1192, 1214]
    (.letOp (n := 1217) (.exec 0x122023 (fun s => s.RIP = 0x122023) (leaR32Effect 0x122023 4 1 (.sib 6 (some 11) 0 .none)) (Reg.operands [.gpr 6, .gpr 11] [])) #v[1192, 1214]
    (.letOp (n := 1218) (.out 0x122027 (addR32Imm32Effect 0x122027 6 1 0x9bdc06a7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1216]
    (.letOp (n := 1219) (.exec 0x122027 (fun s => s.RIP = 0x122027) (addR32Imm32Effect 0x122027 6 1 0x9bdc06a7) (Reg.operands [.gpr 1] [])) #v[1216]
    (.letOp (n := 1220) (.out 0x12202d (movR32R32Effect 0x12202d 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[1180]
    (.letOp (n := 1221) (.exec 0x12202d (fun s => s.RIP = 0x12202d) (movR32R32Effect 0x12202d 3 6 14) (Reg.operands [.gpr 14] [])) #v[1180]
    (.letOp (n := 1222) (.out 0x122030 (rolR32Effect 0x122030 3 6 30) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1220]
    (.letOp (n := 1223) (.exec 0x122030 (fun s => s.RIP = 0x122030) (rolR32Effect 0x122030 3 6 30) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1220]
    (.letOp (n := 1224) (.out 0x122033 (movR32R32Effect 0x122033 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[1180]
    (.letOp (n := 1225) (.exec 0x122033 (fun s => s.RIP = 0x122033) (movR32R32Effect 0x122033 3 7 14) (Reg.operands [.gpr 14] [])) #v[1180]
    (.letOp (n := 1226) (.out 0x122036 (rolR32Effect 0x122036 3 7 19) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1224]
    (.letOp (n := 1227) (.exec 0x122036 (fun s => s.RIP = 0x122036) (rolR32Effect 0x122036 3 7 19) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1224]
    (.letOp (n := 1228) (.out 0x122039 (xorR32R32Effect 0x122039 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[1226, 1222]
    (.letOp (n := 1229) (.exec 0x122039 (fun s => s.RIP = 0x122039) (xorR32R32Effect 0x122039 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[1226, 1222]
    (b_l121930_30))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_29 : List UInt8 :=
  [0xC1, 0xC6, 0x07, 0x31, 0xCE, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x8B, 0x69, 0x38, 0x0F, 0xCD, 0x89,
    0xD1, 0x21, 0xC1, 0x41, 0x01, 0xEB, 0x41, 0x01, 0xCB, 0x89, 0xD1, 0xF7, 0xD1, 0x44, 0x21, 0xD1,
    0x41, 0x01, 0xCB, 0x42, 0x8D, 0x0C, 0x1E, 0x81, 0xC1, 0xA7, 0x06, 0xDC, 0x9B, 0x44, 0x89, 0xF6,
    0xC1, 0xC6, 0x1E, 0x44, 0x89, 0xF7, 0xC1, 0xC7, 0x13, 0x31, 0xF7] ++ bytes_l121930_30

theorem code_l121930_29 : ∀ x ∈ codeRange 0x122000 bytes_l121930_29, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22000 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_30

def b_l121930_28 : Block Op Label signature Reg.count 1150 :=
  .letOp (n := 1150) (.out 0x121fcc (rolR32Effect 0x121fcc 3 7 19) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1148]
    (.letOp (n := 1151) (.exec 0x121fcc (fun s => s.RIP = 0x121fcc) (rolR32Effect 0x121fcc 3 7 19) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1148]
    (.letOp (n := 1152) (.out 0x121fcf (xorR32R32Effect 0x121fcf 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[1150, 1142]
    (.letOp (n := 1153) (.exec 0x121fcf (fun s => s.RIP = 0x121fcf) (xorR32R32Effect 0x121fcf 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[1150, 1142]
    (.letOp (n := 1154) (.out 0x121fd1 (movR32R32Effect 0x121fd1 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[1099]
    (.letOp (n := 1155) (.exec 0x121fd1 (fun s => s.RIP = 0x121fd1) (movR32R32Effect 0x121fd1 3 6 9) (Reg.operands [.gpr 9] [])) #v[1099]
    (.letOp (n := 1156) (.out 0x121fd4 (rolR32Effect 0x121fd4 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1154]
    (.letOp (n := 1157) (.exec 0x121fd4 (fun s => s.RIP = 0x121fd4) (rolR32Effect 0x121fd4 3 6 10) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1154]
    (.letOp (n := 1158) (.out 0x121fd7 (xorR32R32Effect 0x121fd7 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[1156, 1152]
    (.letOp (n := 1159) (.exec 0x121fd7 (fun s => s.RIP = 0x121fd7) (xorR32R32Effect 0x121fd7 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[1156, 1152]
    (.letOp (n := 1160) (.out 0x121fd9 (movR32R32Effect 0x121fd9 2 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[1026]
    (.letOp (n := 1161) (.exec 0x121fd9 (fun s => s.RIP = 0x121fd9) (movR32R32Effect 0x121fd9 2 7 3) (Reg.operands [.gpr 3] [])) #v[1026]
    (.letOp (n := 1162) (.out 0x121fdb (andR32R32Effect 0x121fdb 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[1160, 945]
    (.letOp (n := 1163) (.exec 0x121fdb (fun s => s.RIP = 0x121fdb) (andR32R32Effect 0x121fdb 3 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[1160, 945]
    (.letOp (n := 1164) (.out 0x121fde (movR32R32Effect 0x121fde 3 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 3] []) (.reg (.gpr 14))) #v[1026]
    (.letOp (n := 1165) (.exec 0x121fde (fun s => s.RIP = 0x121fde) (movR32R32Effect 0x121fde 3 14 3) (Reg.operands [.gpr 3] [])) #v[1026]
    (.letOp (n := 1166) (.out 0x121fe1 (xorR32R32Effect 0x121fe1 3 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[1164, 945]
    (.letOp (n := 1167) (.exec 0x121fe1 (fun s => s.RIP = 0x121fe1) (xorR32R32Effect 0x121fe1 3 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[1164, 945]
    (.letOp (n := 1168) (.out 0x121fe4 (andR32R32Effect 0x121fe4 3 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[1166, 1099]
    (.letOp (n := 1169) (.exec 0x121fe4 (fun s => s.RIP = 0x121fe4) (andR32R32Effect 0x121fe4 3 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[1166, 1099]
    (.letOp (n := 1170) (.out 0x121fe7 (xorR32R32Effect 0x121fe7 3 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[1168, 1162]
    (.letOp (n := 1171) (.exec 0x121fe7 (fun s => s.RIP = 0x121fe7) (xorR32R32Effect 0x121fe7 3 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[1168, 1162]
    (.letOp (n := 1172) (.out 0x121fea (addR32R32Effect 0x121fea 3 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[1170, 1158]
    (.letOp (n := 1173) (.exec 0x121fea (fun s => s.RIP = 0x121fea) (addR32R32Effect 0x121fea 3 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[1170, 1158]
    (.letOp (n := 1174) (.out 0x121fed (addR32R32Effect 0x121fed 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[872, 1146]
    (.letOp (n := 1175) (.exec 0x121fed (fun s => s.RIP = 0x121fed) (addR32R32Effect 0x121fed 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[872, 1146]
    (.letOp (n := 1176) (.out 0x121fef (movR32R32Effect 0x121fef 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1174]
    (.letOp (n := 1177) (.exec 0x121fef (fun s => s.RIP = 0x121fef) (movR32R32Effect 0x121fef 2 6 2) (Reg.operands [.gpr 2] [])) #v[1174]
    (.letOp (n := 1178) (.out 0x121ff1 (rolR32Effect 0x121ff1 3 6 26) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1176]
    (.letOp (n := 1179) (.exec 0x121ff1 (fun s => s.RIP = 0x121ff1) (rolR32Effect 0x121ff1 3 6 26) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1176]
    (.letOp (n := 1180) (.out 0x121ff4 (addR32R32Effect 0x121ff4 3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[1172, 1146]
    (.letOp (n := 1181) (.exec 0x121ff4 (fun s => s.RIP = 0x121ff4) (addR32R32Effect 0x121ff4 3 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[1172, 1146]
    (.letOp (n := 1182) (.out 0x121ff7 (movR32R32Effect 0x121ff7 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[1174]
    (.letOp (n := 1183) (.exec 0x121ff7 (fun s => s.RIP = 0x121ff7) (movR32R32Effect 0x121ff7 2 1 2) (Reg.operands [.gpr 2] [])) #v[1174]
    (.letOp (n := 1184) (.out 0x121ff9 (rolR32Effect 0x121ff9 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1182]
    (.letOp (n := 1185) (.exec 0x121ff9 (fun s => s.RIP = 0x121ff9) (rolR32Effect 0x121ff9 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1182]
    (.letOp (n := 1186) (.out 0x121ffc (xorR32R32Effect 0x121ffc 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1184, 1178]
    (.letOp (n := 1187) (.exec 0x121ffc (fun s => s.RIP = 0x121ffc) (xorR32R32Effect 0x121ffc 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1184, 1178]
    (.letOp (n := 1188) (.out 0x121ffe (movR32R32Effect 0x121ffe 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[1174]
    (.letOp (n := 1189) (.exec 0x121ffe (fun s => s.RIP = 0x121ffe) (movR32R32Effect 0x121ffe 2 6 2) (Reg.operands [.gpr 2] [])) #v[1174]
    (b_l121930_29))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_28 : List UInt8 :=
  [0xC1, 0xC7, 0x13, 0x31, 0xF7, 0x44, 0x89, 0xCE, 0xC1, 0xC6, 0x0A, 0x31, 0xFE, 0x89, 0xDF, 0x44,
    0x21, 0xFF, 0x41, 0x89, 0xDE, 0x45, 0x31, 0xFE, 0x45, 0x21, 0xCE, 0x41, 0x31, 0xFE, 0x41, 0x01,
    0xF6, 0x01, 0xCA, 0x89, 0xD6, 0xC1, 0xC6, 0x1A, 0x41, 0x01, 0xCE, 0x89, 0xD1, 0xC1, 0xC1, 0x15,
    0x31, 0xF1, 0x89, 0xD6] ++ bytes_l121930_29

theorem code_l121930_28 : ∀ x ∈ codeRange 0x121fcc bytes_l121930_28, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21fcc 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_29

def b_l121930_27 : Block Op Label signature Reg.count 1111 :=
  .letOp (n := 1111) (.out 0x121f90 (movR32R32Effect 0x121f90 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1097]
    (.letOp (n := 1112) (.exec 0x121f90 (fun s => s.RIP = 0x121f90) (movR32R32Effect 0x121f90 2 1 0) (Reg.operands [.gpr 0] [])) #v[1097]
    (.letOp (n := 1113) (.out 0x121f92 (rolR32Effect 0x121f92 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1111]
    (.letOp (n := 1114) (.exec 0x121f92 (fun s => s.RIP = 0x121f92) (rolR32Effect 0x121f92 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1111]
    (.letOp (n := 1115) (.out 0x121f95 (xorR32R32Effect 0x121f95 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1113, 1109]
    (.letOp (n := 1116) (.exec 0x121f95 (fun s => s.RIP = 0x121f95) (xorR32R32Effect 0x121f95 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1113, 1109]
    (.letOp (n := 1117) (.out 0x121f97 (movR64M64Effect 0x121f97 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 1118) (.exec 0x121f97 (LoadPre 0x121f97 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121f97 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121f97 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1119) (.out 0x121f9c (movR32M32LowEffect 0x121f9c 7 (.base 6 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[1117]
    (.letOp (n := 1120) (.exec 0x121f9c (LoadPre 0x121f9c (fun s => AddrMode.addr (.base 6 (.d8 0x34)) s (0x121f9c + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x121f9c 7 (.base 6 (.d8 0x34))) (Reg.operands [.gpr 6] [])) #v[1117]
    (.letOp (n := 1121) (.out 0x121f9f (bswapR32Effect 0x121f9f 2 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[1119]
    (.letOp (n := 1122) (.exec 0x121f9f (fun s => s.RIP = 0x121f9f) (bswapR32Effect 0x121f9f 2 7) (Reg.operands [.gpr 7] [])) #v[1119]
    (.letOp (n := 1123) (.exec 0x121fa1 (StorePre 0x121fa1 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x121fa1 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x121fa1 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1121, 4]
    (.letOp (n := 1124) (.out 0x121fa5 (movR32R32Effect 0x121fa5 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1097]
    (.letOp (n := 1125) (.exec 0x121fa5 (fun s => s.RIP = 0x121fa5) (movR32R32Effect 0x121fa5 2 6 0) (Reg.operands [.gpr 0] [])) #v[1097]
    (.letOp (n := 1126) (.out 0x121fa7 (andR32R32Effect 0x121fa7 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[1124, 1020]
    (.letOp (n := 1127) (.exec 0x121fa7 (fun s => s.RIP = 0x121fa7) (andR32R32Effect 0x121fa7 3 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[1124, 1020]
    (.letOp (n := 1128) (.out 0x121faa (addR32R32Effect 0x121faa 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[866, 1121]
    (.letOp (n := 1129) (.exec 0x121faa (fun s => s.RIP = 0x121faa) (addR32R32Effect 0x121faa 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[866, 1121]
    (.letOp (n := 1130) (.out 0x121fad (addR32R32Effect 0x121fad 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[1128, 1126]
    (.letOp (n := 1131) (.exec 0x121fad (fun s => s.RIP = 0x121fad) (addR32R32Effect 0x121fad 3 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[1128, 1126]
    (.letOp (n := 1132) (.out 0x121fb0 (movR32R32Effect 0x121fb0 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1097]
    (.letOp (n := 1133) (.exec 0x121fb0 (fun s => s.RIP = 0x121fb0) (movR32R32Effect 0x121fb0 2 6 0) (Reg.operands [.gpr 0] [])) #v[1097]
    (.letOp (n := 1134) (.out 0x121fb2 (notR32Effect 0x121fb2 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[1132]
    (.letOp (n := 1135) (.exec 0x121fb2 (fun s => s.RIP = 0x121fb2) (notR32Effect 0x121fb2 2 6) (Reg.operands [.gpr 6] [])) #v[1132]
    (.letOp (n := 1136) (.out 0x121fb4 (andR32R32Effect 0x121fb4 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[1134, 943]
    (.letOp (n := 1137) (.exec 0x121fb4 (fun s => s.RIP = 0x121fb4) (andR32R32Effect 0x121fb4 3 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[1134, 943]
    (.letOp (n := 1138) (.out 0x121fb7 (addR32R32Effect 0x121fb7 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[1130, 1136]
    (.letOp (n := 1139) (.exec 0x121fb7 (fun s => s.RIP = 0x121fb7) (addR32R32Effect 0x121fb7 3 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[1130, 1136]
    (.letOp (n := 1140) (.out 0x121fba (movR32R32Effect 0x121fba 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[1099]
    (.letOp (n := 1141) (.exec 0x121fba (fun s => s.RIP = 0x121fba) (movR32R32Effect 0x121fba 3 6 9) (Reg.operands [.gpr 9] [])) #v[1099]
    (.letOp (n := 1142) (.out 0x121fbd (rolR32Effect 0x121fbd 3 6 30) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1140]
    (.letOp (n := 1143) (.exec 0x121fbd (fun s => s.RIP = 0x121fbd) (rolR32Effect 0x121fbd 3 6 30) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1140]
    (.letOp (n := 1144) (.out 0x121fc0 (addR32R32Effect 0x121fc0 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[1115, 1138]
    (.letOp (n := 1145) (.exec 0x121fc0 (fun s => s.RIP = 0x121fc0) (addR32R32Effect 0x121fc0 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[1115, 1138]
    (.letOp (n := 1146) (.out 0x121fc3 (addR32Imm32Effect 0x121fc3 6 1 0x80deb1fe) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1144]
    (.letOp (n := 1147) (.exec 0x121fc3 (fun s => s.RIP = 0x121fc3) (addR32Imm32Effect 0x121fc3 6 1 0x80deb1fe) (Reg.operands [.gpr 1] [])) #v[1144]
    (.letOp (n := 1148) (.out 0x121fc9 (movR32R32Effect 0x121fc9 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[1099]
    (.letOp (n := 1149) (.exec 0x121fc9 (fun s => s.RIP = 0x121fc9) (movR32R32Effect 0x121fc9 3 7 9) (Reg.operands [.gpr 9] [])) #v[1099]
    (b_l121930_28)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_27 : List UInt8 :=
  [0x89, 0xC1, 0xC1, 0xC1, 0x07, 0x31, 0xF1, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x8B, 0x7E, 0x34, 0x0F,
    0xCF, 0x89, 0x7C, 0x24, 0x10, 0x89, 0xC6, 0x44, 0x21, 0xD6, 0x41, 0x01, 0xF8, 0x41, 0x01, 0xF0,
    0x89, 0xC6, 0xF7, 0xD6, 0x44, 0x21, 0xDE, 0x41, 0x01, 0xF0, 0x44, 0x89, 0xCE, 0xC1, 0xC6, 0x1E,
    0x44, 0x01, 0xC1, 0x81, 0xC1, 0xFE, 0xB1, 0xDE, 0x80, 0x44, 0x89, 0xCF] ++ bytes_l121930_28

theorem code_l121930_27 : ∀ x ∈ codeRange 0x121f90 bytes_l121930_27, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21f90 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_28

def b_l121930_26 : Block Op Label signature Reg.count 1071 :=
  .letOp (n := 1071) (.out 0x121f5d (movR32R32Effect 0x121f5d 2 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[1026]
    (.letOp (n := 1072) (.exec 0x121f5d (fun s => s.RIP = 0x121f5d) (movR32R32Effect 0x121f5d 2 7 3) (Reg.operands [.gpr 3] [])) #v[1026]
    (.letOp (n := 1073) (.out 0x121f5f (rolR32Effect 0x121f5f 3 7 19) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1071]
    (.letOp (n := 1074) (.exec 0x121f5f (fun s => s.RIP = 0x121f5f) (rolR32Effect 0x121f5f 3 7 19) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1071]
    (.letOp (n := 1075) (.out 0x121f62 (xorR32R32Effect 0x121f62 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[1073, 1069]
    (.letOp (n := 1076) (.exec 0x121f62 (fun s => s.RIP = 0x121f62) (xorR32R32Effect 0x121f62 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[1073, 1069]
    (.letOp (n := 1077) (.out 0x121f64 (movR32R32Effect 0x121f64 2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[1026]
    (.letOp (n := 1078) (.exec 0x121f64 (fun s => s.RIP = 0x121f64) (movR32R32Effect 0x121f64 2 6 3) (Reg.operands [.gpr 3] [])) #v[1026]
    (.letOp (n := 1079) (.out 0x121f66 (rolR32Effect 0x121f66 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1077]
    (.letOp (n := 1080) (.exec 0x121f66 (fun s => s.RIP = 0x121f66) (rolR32Effect 0x121f66 3 6 10) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1077]
    (.letOp (n := 1081) (.out 0x121f69 (xorR32R32Effect 0x121f69 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[1079, 1075]
    (.letOp (n := 1082) (.exec 0x121f69 (fun s => s.RIP = 0x121f69) (xorR32R32Effect 0x121f69 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[1079, 1075]
    (.letOp (n := 1083) (.out 0x121f6b (movR32R32Effect 0x121f6b 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[945]
    (.letOp (n := 1084) (.exec 0x121f6b (fun s => s.RIP = 0x121f6b) (movR32R32Effect 0x121f6b 3 7 15) (Reg.operands [.gpr 15] [])) #v[945]
    (.letOp (n := 1085) (.out 0x121f6e (andR32R32Effect 0x121f6e 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[1083, 872]
    (.letOp (n := 1086) (.exec 0x121f6e (fun s => s.RIP = 0x121f6e) (andR32R32Effect 0x121f6e 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[1083, 872]
    (.letOp (n := 1087) (.out 0x121f70 (movR32R32Effect 0x121f70 3 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 15] []) (.reg (.gpr 9))) #v[945]
    (.letOp (n := 1088) (.exec 0x121f70 (fun s => s.RIP = 0x121f70) (movR32R32Effect 0x121f70 3 9 15) (Reg.operands [.gpr 15] [])) #v[945]
    (.letOp (n := 1089) (.out 0x121f73 (xorR32R32Effect 0x121f73 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[1087, 872]
    (.letOp (n := 1090) (.exec 0x121f73 (fun s => s.RIP = 0x121f73) (xorR32R32Effect 0x121f73 3 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[1087, 872]
    (.letOp (n := 1091) (.out 0x121f76 (andR32R32Effect 0x121f76 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[1089, 1026]
    (.letOp (n := 1092) (.exec 0x121f76 (fun s => s.RIP = 0x121f76) (andR32R32Effect 0x121f76 3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[1089, 1026]
    (.letOp (n := 1093) (.out 0x121f79 (xorR32R32Effect 0x121f79 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[1091, 1085]
    (.letOp (n := 1094) (.exec 0x121f79 (fun s => s.RIP = 0x121f79) (xorR32R32Effect 0x121f79 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[1091, 1085]
    (.letOp (n := 1095) (.out 0x121f7c (addR32R32Effect 0x121f7c 3 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[1093, 1081]
    (.letOp (n := 1096) (.exec 0x121f7c (fun s => s.RIP = 0x121f7c) (addR32R32Effect 0x121f7c 3 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[1093, 1081]
    (.letOp (n := 1097) (.out 0x121f7f (addR32R32Effect 0x121f7f 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[791, 1065]
    (.letOp (n := 1098) (.exec 0x121f7f (fun s => s.RIP = 0x121f7f) (addR32R32Effect 0x121f7f 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[791, 1065]
    (.letOp (n := 1099) (.out 0x121f81 (addR32R32Effect 0x121f81 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[1095, 1065]
    (.letOp (n := 1100) (.exec 0x121f81 (fun s => s.RIP = 0x121f81) (addR32R32Effect 0x121f81 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[1095, 1065]
    (.letOp (n := 1101) (.out 0x121f84 (movR32R32Effect 0x121f84 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1097]
    (.letOp (n := 1102) (.exec 0x121f84 (fun s => s.RIP = 0x121f84) (movR32R32Effect 0x121f84 2 1 0) (Reg.operands [.gpr 0] [])) #v[1097]
    (.letOp (n := 1103) (.out 0x121f86 (rolR32Effect 0x121f86 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1101]
    (.letOp (n := 1104) (.exec 0x121f86 (fun s => s.RIP = 0x121f86) (rolR32Effect 0x121f86 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1101]
    (.letOp (n := 1105) (.out 0x121f89 (movR32R32Effect 0x121f89 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1097]
    (.letOp (n := 1106) (.exec 0x121f89 (fun s => s.RIP = 0x121f89) (movR32R32Effect 0x121f89 2 6 0) (Reg.operands [.gpr 0] [])) #v[1097]
    (.letOp (n := 1107) (.out 0x121f8b (rolR32Effect 0x121f8b 3 6 21) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1105]
    (.letOp (n := 1108) (.exec 0x121f8b (fun s => s.RIP = 0x121f8b) (rolR32Effect 0x121f8b 3 6 21) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1105]
    (.letOp (n := 1109) (.out 0x121f8e (xorR32R32Effect 0x121f8e 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1107, 1103]
    (.letOp (n := 1110) (.exec 0x121f8e (fun s => s.RIP = 0x121f8e) (xorR32R32Effect 0x121f8e 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1107, 1103]
    (b_l121930_27))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_26 : List UInt8 :=
  [0x89, 0xDF, 0xC1, 0xC7, 0x13, 0x31, 0xF7, 0x89, 0xDE, 0xC1, 0xC6, 0x0A, 0x31, 0xFE, 0x44, 0x89,
    0xFF, 0x21, 0xD7, 0x45, 0x89, 0xF9, 0x41, 0x31, 0xD1, 0x41, 0x21, 0xD9, 0x41, 0x31, 0xF9, 0x41,
    0x01, 0xF1, 0x01, 0xC8, 0x41, 0x01, 0xC9, 0x89, 0xC1, 0xC1, 0xC1, 0x1A, 0x89, 0xC6, 0xC1, 0xC6,
    0x15, 0x31, 0xCE] ++ bytes_l121930_27

theorem code_l121930_26 : ∀ x ∈ codeRange 0x121f5d bytes_l121930_26, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21f5d 51 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_27

def b_l121930_25 : Block Op Label signature Reg.count 1032 :=
  .letOp (n := 1032) (.out 0x121f20 (xorR32R32Effect 0x121f20 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1030, 1024]
    (.letOp (n := 1033) (.exec 0x121f20 (fun s => s.RIP = 0x121f20) (xorR32R32Effect 0x121f20 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1030, 1024]
    (.letOp (n := 1034) (.out 0x121f22 (movR32R32Effect 0x121f22 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[1020]
    (.letOp (n := 1035) (.exec 0x121f22 (fun s => s.RIP = 0x121f22) (movR32R32Effect 0x121f22 3 6 10) (Reg.operands [.gpr 10] [])) #v[1020]
    (.letOp (n := 1036) (.out 0x121f25 (rolR32Effect 0x121f25 3 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1034]
    (.letOp (n := 1037) (.exec 0x121f25 (fun s => s.RIP = 0x121f25) (rolR32Effect 0x121f25 3 6 7) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1034]
    (.letOp (n := 1038) (.out 0x121f28 (xorR32R32Effect 0x121f28 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1036, 1032]
    (.letOp (n := 1039) (.exec 0x121f28 (fun s => s.RIP = 0x121f28) (xorR32R32Effect 0x121f28 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1036, 1032]
    (.letOp (n := 1040) (.out 0x121f2a (movR64M64Effect 0x121f2a 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 1041) (.exec 0x121f2a (LoadPre 0x121f2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121f2a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121f2a 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1042) (.out 0x121f2f (movR32M32LowEffect 0x121f2f 7 (.base 1 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1040]
    (.letOp (n := 1043) (.exec 0x121f2f (LoadPre 0x121f2f (fun s => AddrMode.addr (.base 1 (.d8 0x30)) s (0x121f2f + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x121f2f 7 (.base 1 (.d8 0x30))) (Reg.operands [.gpr 1] [])) #v[1040]
    (.letOp (n := 1044) (.out 0x121f32 (bswapR32Effect 0x121f32 2 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[1042]
    (.letOp (n := 1045) (.exec 0x121f32 (fun s => s.RIP = 0x121f32) (bswapR32Effect 0x121f32 2 7) (Reg.operands [.gpr 7] [])) #v[1042]
    (.letOp (n := 1046) (.exec 0x121f34 (StorePre 0x121f34 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x121f34 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x121f34 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1044, 4]
    (.letOp (n := 1047) (.out 0x121f37 (movR32R32Effect 0x121f37 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[1020]
    (.letOp (n := 1048) (.exec 0x121f37 (fun s => s.RIP = 0x121f37) (movR32R32Effect 0x121f37 3 1 10) (Reg.operands [.gpr 10] [])) #v[1020]
    (.letOp (n := 1049) (.out 0x121f3a (andR32R32Effect 0x121f3a 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[1047, 943]
    (.letOp (n := 1050) (.exec 0x121f3a (fun s => s.RIP = 0x121f3a) (andR32R32Effect 0x121f3a 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[1047, 943]
    (.letOp (n := 1051) (.out 0x121f3d (addR32R32Effect 0x121f3d 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[789, 1044]
    (.letOp (n := 1052) (.exec 0x121f3d (fun s => s.RIP = 0x121f3d) (addR32R32Effect 0x121f3d 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[789, 1044]
    (.letOp (n := 1053) (.out 0x121f40 (addR32R32Effect 0x121f40 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[1051, 1049]
    (.letOp (n := 1054) (.exec 0x121f40 (fun s => s.RIP = 0x121f40) (addR32R32Effect 0x121f40 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[1051, 1049]
    (.letOp (n := 1055) (.out 0x121f43 (movR32R32Effect 0x121f43 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[1020]
    (.letOp (n := 1056) (.exec 0x121f43 (fun s => s.RIP = 0x121f43) (movR32R32Effect 0x121f43 3 1 10) (Reg.operands [.gpr 10] [])) #v[1020]
    (.letOp (n := 1057) (.out 0x121f46 (notR32Effect 0x121f46 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1055]
    (.letOp (n := 1058) (.exec 0x121f46 (fun s => s.RIP = 0x121f46) (notR32Effect 0x121f46 2 1) (Reg.operands [.gpr 1] [])) #v[1055]
    (.letOp (n := 1059) (.out 0x121f48 (andR32R32Effect 0x121f48 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[1057, 866]
    (.letOp (n := 1060) (.exec 0x121f48 (fun s => s.RIP = 0x121f48) (andR32R32Effect 0x121f48 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[1057, 866]
    (.letOp (n := 1061) (.out 0x121f4b (addR32R32Effect 0x121f4b 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[1053, 1059]
    (.letOp (n := 1062) (.exec 0x121f4b (fun s => s.RIP = 0x121f4b) (addR32R32Effect 0x121f4b 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[1053, 1059]
    (.letOp (n := 1063) (.out 0x121f4e (leaR32Effect 0x121f4e 4 1 (.sib 6 (some 9) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 9] []) (.reg (.gpr 1))) #v[1038, 1061]
    (.letOp (n := 1064) (.exec 0x121f4e (fun s => s.RIP = 0x121f4e) (leaR32Effect 0x121f4e 4 1 (.sib 6 (some 9) 0 .none)) (Reg.operands [.gpr 6, .gpr 9] [])) #v[1038, 1061]
    (.letOp (n := 1065) (.out 0x121f52 (addR32Imm32Effect 0x121f52 6 1 0x72be5d74) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1063]
    (.letOp (n := 1066) (.exec 0x121f52 (fun s => s.RIP = 0x121f52) (addR32Imm32Effect 0x121f52 6 1 0x72be5d74) (Reg.operands [.gpr 1] [])) #v[1063]
    (.letOp (n := 1067) (.out 0x121f58 (movR32R32Effect 0x121f58 2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[1026]
    (.letOp (n := 1068) (.exec 0x121f58 (fun s => s.RIP = 0x121f58) (movR32R32Effect 0x121f58 2 6 3) (Reg.operands [.gpr 3] [])) #v[1026]
    (.letOp (n := 1069) (.out 0x121f5a (rolR32Effect 0x121f5a 3 6 30) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1067]
    (.letOp (n := 1070) (.exec 0x121f5a (fun s => s.RIP = 0x121f5a) (rolR32Effect 0x121f5a 3 6 30) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1067]
    (b_l121930_26)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_25 : List UInt8 :=
  [0x31, 0xF1, 0x44, 0x89, 0xD6, 0xC1, 0xC6, 0x07, 0x31, 0xCE, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x8B,
    0x79, 0x30, 0x0F, 0xCF, 0x89, 0x3C, 0x24, 0x44, 0x89, 0xD1, 0x44, 0x21, 0xD9, 0x41, 0x01, 0xF9,
    0x41, 0x01, 0xC9, 0x44, 0x89, 0xD1, 0xF7, 0xD1, 0x44, 0x21, 0xC1, 0x41, 0x01, 0xC9, 0x42, 0x8D,
    0x0C, 0x0E, 0x81, 0xC1, 0x74, 0x5D, 0xBE, 0x72, 0x89, 0xDE, 0xC1, 0xC6, 0x1E] ++ bytes_l121930_26

theorem code_l121930_25 : ∀ x ∈ codeRange 0x121f20 bytes_l121930_25, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21f20 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_26

def b_l121930_24 : Block Op Label signature Reg.count 992 :=
  .letOp (n := 992) (.out 0x121eea (addR32Imm32Effect 0x121eea 6 1 0x550c7dc3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[990]
    (.letOp (n := 993) (.exec 0x121eea (fun s => s.RIP = 0x121eea) (addR32Imm32Effect 0x121eea 6 1 0x550c7dc3) (Reg.operands [.gpr 1] [])) #v[990]
    (.letOp (n := 994) (.out 0x121ef0 (movR32R32Effect 0x121ef0 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[945]
    (.letOp (n := 995) (.exec 0x121ef0 (fun s => s.RIP = 0x121ef0) (movR32R32Effect 0x121ef0 3 7 15) (Reg.operands [.gpr 15] [])) #v[945]
    (.letOp (n := 996) (.out 0x121ef3 (rolR32Effect 0x121ef3 3 7 19) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[994]
    (.letOp (n := 997) (.exec 0x121ef3 (fun s => s.RIP = 0x121ef3) (rolR32Effect 0x121ef3 3 7 19) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[994]
    (.letOp (n := 998) (.out 0x121ef6 (xorR32R32Effect 0x121ef6 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[996, 988]
    (.letOp (n := 999) (.exec 0x121ef6 (fun s => s.RIP = 0x121ef6) (xorR32R32Effect 0x121ef6 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[996, 988]
    (.letOp (n := 1000) (.out 0x121ef8 (movR32R32Effect 0x121ef8 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[945]
    (.letOp (n := 1001) (.exec 0x121ef8 (fun s => s.RIP = 0x121ef8) (movR32R32Effect 0x121ef8 3 6 15) (Reg.operands [.gpr 15] [])) #v[945]
    (.letOp (n := 1002) (.out 0x121efb (rolR32Effect 0x121efb 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1000]
    (.letOp (n := 1003) (.exec 0x121efb (fun s => s.RIP = 0x121efb) (rolR32Effect 0x121efb 3 6 10) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1000]
    (.letOp (n := 1004) (.out 0x121efe (xorR32R32Effect 0x121efe 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[1002, 998]
    (.letOp (n := 1005) (.exec 0x121efe (fun s => s.RIP = 0x121efe) (xorR32R32Effect 0x121efe 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[1002, 998]
    (.letOp (n := 1006) (.out 0x121f00 (movR32R32Effect 0x121f00 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[872]
    (.letOp (n := 1007) (.exec 0x121f00 (fun s => s.RIP = 0x121f00) (movR32R32Effect 0x121f00 2 7 2) (Reg.operands [.gpr 2] [])) #v[872]
    (.letOp (n := 1008) (.out 0x121f02 (andR32R32Effect 0x121f02 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[1006, 791]
    (.letOp (n := 1009) (.exec 0x121f02 (fun s => s.RIP = 0x121f02) (andR32R32Effect 0x121f02 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[1006, 791]
    (.letOp (n := 1010) (.out 0x121f04 (movR32R32Effect 0x121f04 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[872]
    (.letOp (n := 1011) (.exec 0x121f04 (fun s => s.RIP = 0x121f04) (movR32R32Effect 0x121f04 2 3 2) (Reg.operands [.gpr 2] [])) #v[872]
    (.letOp (n := 1012) (.out 0x121f06 (xorR32R32Effect 0x121f06 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[1010, 791]
    (.letOp (n := 1013) (.exec 0x121f06 (fun s => s.RIP = 0x121f06) (xorR32R32Effect 0x121f06 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1010, 791]
    (.letOp (n := 1014) (.out 0x121f08 (andR32R32Effect 0x121f08 3 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[1012, 945]
    (.letOp (n := 1015) (.exec 0x121f08 (fun s => s.RIP = 0x121f08) (andR32R32Effect 0x121f08 3 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[1012, 945]
    (.letOp (n := 1016) (.out 0x121f0b (xorR32R32Effect 0x121f0b 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[1014, 1008]
    (.letOp (n := 1017) (.exec 0x121f0b (fun s => s.RIP = 0x121f0b) (xorR32R32Effect 0x121f0b 2 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[1014, 1008]
    (.letOp (n := 1018) (.out 0x121f0d (addR32R32Effect 0x121f0d 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[1016, 1004]
    (.letOp (n := 1019) (.exec 0x121f0d (fun s => s.RIP = 0x121f0d) (addR32R32Effect 0x121f0d 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[1016, 1004]
    (.letOp (n := 1020) (.out 0x121f0f (addR32R32Effect 0x121f0f 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[718, 992]
    (.letOp (n := 1021) (.exec 0x121f0f (fun s => s.RIP = 0x121f0f) (addR32R32Effect 0x121f0f 3 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[718, 992]
    (.letOp (n := 1022) (.out 0x121f12 (movR32R32Effect 0x121f12 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[1020]
    (.letOp (n := 1023) (.exec 0x121f12 (fun s => s.RIP = 0x121f12) (movR32R32Effect 0x121f12 3 6 10) (Reg.operands [.gpr 10] [])) #v[1020]
    (.letOp (n := 1024) (.out 0x121f15 (rolR32Effect 0x121f15 3 6 26) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1022]
    (.letOp (n := 1025) (.exec 0x121f15 (fun s => s.RIP = 0x121f15) (rolR32Effect 0x121f15 3 6 26) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1022]
    (.letOp (n := 1026) (.out 0x121f18 (addR32R32Effect 0x121f18 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[1018, 992]
    (.letOp (n := 1027) (.exec 0x121f18 (fun s => s.RIP = 0x121f18) (addR32R32Effect 0x121f18 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[1018, 992]
    (.letOp (n := 1028) (.out 0x121f1a (movR32R32Effect 0x121f1a 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[1020]
    (.letOp (n := 1029) (.exec 0x121f1a (fun s => s.RIP = 0x121f1a) (movR32R32Effect 0x121f1a 3 1 10) (Reg.operands [.gpr 10] [])) #v[1020]
    (.letOp (n := 1030) (.out 0x121f1d (rolR32Effect 0x121f1d 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1028]
    (.letOp (n := 1031) (.exec 0x121f1d (fun s => s.RIP = 0x121f1d) (rolR32Effect 0x121f1d 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1028]
    (b_l121930_25))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_24 : List UInt8 :=
  [0x81, 0xC1, 0xC3, 0x7D, 0x0C, 0x55, 0x44, 0x89, 0xFF, 0xC1, 0xC7, 0x13, 0x31, 0xF7, 0x44, 0x89,
    0xFE, 0xC1, 0xC6, 0x0A, 0x31, 0xFE, 0x89, 0xD7, 0x21, 0xC7, 0x89, 0xD3, 0x31, 0xC3, 0x44, 0x21,
    0xFB, 0x31, 0xFB, 0x01, 0xF3, 0x41, 0x01, 0xCA, 0x44, 0x89, 0xD6, 0xC1, 0xC6, 0x1A, 0x01, 0xCB,
    0x44, 0x89, 0xD1, 0xC1, 0xC1, 0x15] ++ bytes_l121930_25

theorem code_l121930_24 : ∀ x ∈ codeRange 0x121eea bytes_l121930_24, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21eea 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_25

def b_l121930_23 : Block Op Label signature Reg.count 953 :=
  .letOp (n := 953) (.out 0x121eb3 (rolR32Effect 0x121eb3 3 6 21) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[951]
    (.letOp (n := 954) (.exec 0x121eb3 (fun s => s.RIP = 0x121eb3) (rolR32Effect 0x121eb3 3 6 21) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[951]
    (.letOp (n := 955) (.out 0x121eb6 (xorR32R32Effect 0x121eb6 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[953, 949]
    (.letOp (n := 956) (.exec 0x121eb6 (fun s => s.RIP = 0x121eb6) (xorR32R32Effect 0x121eb6 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[953, 949]
    (.letOp (n := 957) (.out 0x121eb8 (movR32R32Effect 0x121eb8 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11] []) (.reg (.gpr 1))) #v[943]
    (.letOp (n := 958) (.exec 0x121eb8 (fun s => s.RIP = 0x121eb8) (movR32R32Effect 0x121eb8 3 1 11) (Reg.operands [.gpr 11] [])) #v[943]
    (.letOp (n := 959) (.out 0x121ebb (rolR32Effect 0x121ebb 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[957]
    (.letOp (n := 960) (.exec 0x121ebb (fun s => s.RIP = 0x121ebb) (rolR32Effect 0x121ebb 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[957]
    (.letOp (n := 961) (.out 0x121ebe (xorR32R32Effect 0x121ebe 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[959, 955]
    (.letOp (n := 962) (.exec 0x121ebe (fun s => s.RIP = 0x121ebe) (xorR32R32Effect 0x121ebe 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[959, 955]
    (.letOp (n := 963) (.out 0x121ec0 (movR64M64Effect 0x121ec0 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 964) (.exec 0x121ec0 (LoadPre 0x121ec0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121ec0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121ec0 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 965) (.out 0x121ec5 (movR32M32LowEffect 0x121ec5 3 (.base 6 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[963]
    (.letOp (n := 966) (.exec 0x121ec5 (LoadPre 0x121ec5 (fun s => AddrMode.addr (.base 6 (.d8 0x2c)) s (0x121ec5 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x121ec5 3 (.base 6 (.d8 0x2c))) (Reg.operands [.gpr 6] [])) #v[963]
    (.letOp (n := 967) (.out 0x121ec8 (bswapR32Effect 0x121ec8 2 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[965]
    (.letOp (n := 968) (.exec 0x121ec8 (fun s => s.RIP = 0x121ec8) (bswapR32Effect 0x121ec8 2 3) (Reg.operands [.gpr 3] [])) #v[965]
    (.letOp (n := 969) (.exec 0x121eca (StorePre 0x121eca 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x121eca + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x121eca 3 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[967, 4]
    (.letOp (n := 970) (.out 0x121ece (movR32R32Effect 0x121ece 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[943]
    (.letOp (n := 971) (.exec 0x121ece (fun s => s.RIP = 0x121ece) (movR32R32Effect 0x121ece 3 6 11) (Reg.operands [.gpr 11] [])) #v[943]
    (.letOp (n := 972) (.out 0x121ed1 (andR32R32Effect 0x121ed1 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[970, 866]
    (.letOp (n := 973) (.exec 0x121ed1 (fun s => s.RIP = 0x121ed1) (andR32R32Effect 0x121ed1 3 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[970, 866]
    (.letOp (n := 974) (.out 0x121ed4 (addR32R32Effect 0x121ed4 2 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[712, 967]
    (.letOp (n := 975) (.exec 0x121ed4 (fun s => s.RIP = 0x121ed4) (addR32R32Effect 0x121ed4 2 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[712, 967]
    (.letOp (n := 976) (.out 0x121ed6 (addR32R32Effect 0x121ed6 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[974, 972]
    (.letOp (n := 977) (.exec 0x121ed6 (fun s => s.RIP = 0x121ed6) (addR32R32Effect 0x121ed6 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[974, 972]
    (.letOp (n := 978) (.out 0x121ed8 (movR32R32Effect 0x121ed8 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[943]
    (.letOp (n := 979) (.exec 0x121ed8 (fun s => s.RIP = 0x121ed8) (movR32R32Effect 0x121ed8 3 6 11) (Reg.operands [.gpr 11] [])) #v[943]
    (.letOp (n := 980) (.out 0x121edb (notR32Effect 0x121edb 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[978]
    (.letOp (n := 981) (.exec 0x121edb (fun s => s.RIP = 0x121edb) (notR32Effect 0x121edb 2 6) (Reg.operands [.gpr 6] [])) #v[978]
    (.letOp (n := 982) (.out 0x121edd (andR32R32Effect 0x121edd 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[980, 789]
    (.letOp (n := 983) (.exec 0x121edd (fun s => s.RIP = 0x121edd) (andR32R32Effect 0x121edd 3 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[980, 789]
    (.letOp (n := 984) (.out 0x121ee0 (addR32R32Effect 0x121ee0 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[976, 982]
    (.letOp (n := 985) (.exec 0x121ee0 (fun s => s.RIP = 0x121ee0) (addR32R32Effect 0x121ee0 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[976, 982]
    (.letOp (n := 986) (.out 0x121ee2 (movR32R32Effect 0x121ee2 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[945]
    (.letOp (n := 987) (.exec 0x121ee2 (fun s => s.RIP = 0x121ee2) (movR32R32Effect 0x121ee2 3 6 15) (Reg.operands [.gpr 15] [])) #v[945]
    (.letOp (n := 988) (.out 0x121ee5 (rolR32Effect 0x121ee5 3 6 30) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[986]
    (.letOp (n := 989) (.exec 0x121ee5 (fun s => s.RIP = 0x121ee5) (rolR32Effect 0x121ee5 3 6 30) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[986]
    (.letOp (n := 990) (.out 0x121ee8 (addR32R32Effect 0x121ee8 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[961, 984]
    (.letOp (n := 991) (.exec 0x121ee8 (fun s => s.RIP = 0x121ee8) (addR32R32Effect 0x121ee8 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[961, 984]
    (b_l121930_24)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_23 : List UInt8 :=
  [0xC1, 0xC6, 0x15, 0x31, 0xCE, 0x44, 0x89, 0xD9, 0xC1, 0xC1, 0x07, 0x31, 0xF1, 0x48, 0x8B, 0x74,
    0x24, 0x18, 0x8B, 0x5E, 0x2C, 0x0F, 0xCB, 0x89, 0x5C, 0x24, 0x34, 0x44, 0x89, 0xDE, 0x44, 0x21,
    0xC6, 0x01, 0xDF, 0x01, 0xF7, 0x44, 0x89, 0xDE, 0xF7, 0xD6, 0x44, 0x21, 0xCE, 0x01, 0xF7, 0x44,
    0x89, 0xFE, 0xC1, 0xC6, 0x1E, 0x01, 0xF9] ++ bytes_l121930_24

theorem code_l121930_23 : ∀ x ∈ codeRange 0x121eb3 bytes_l121930_23, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21eb3 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_24

def b_l121930_22 : Block Op Label signature Reg.count 913 :=
  .letOp (n := 913) (.out 0x121e7d (movR32R32Effect 0x121e7d 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[872]
    (.letOp (n := 914) (.exec 0x121e7d (fun s => s.RIP = 0x121e7d) (movR32R32Effect 0x121e7d 2 6 2) (Reg.operands [.gpr 2] [])) #v[872]
    (.letOp (n := 915) (.out 0x121e7f (rolR32Effect 0x121e7f 3 6 30) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[913]
    (.letOp (n := 916) (.exec 0x121e7f (fun s => s.RIP = 0x121e7f) (rolR32Effect 0x121e7f 3 6 30) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[913]
    (.letOp (n := 917) (.out 0x121e82 (movR32R32Effect 0x121e82 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[872]
    (.letOp (n := 918) (.exec 0x121e82 (fun s => s.RIP = 0x121e82) (movR32R32Effect 0x121e82 2 3 2) (Reg.operands [.gpr 2] [])) #v[872]
    (.letOp (n := 919) (.out 0x121e84 (rolR32Effect 0x121e84 3 3 19) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[917]
    (.letOp (n := 920) (.exec 0x121e84 (fun s => s.RIP = 0x121e84) (rolR32Effect 0x121e84 3 3 19) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[917]
    (.letOp (n := 921) (.out 0x121e87 (xorR32R32Effect 0x121e87 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[919, 915]
    (.letOp (n := 922) (.exec 0x121e87 (fun s => s.RIP = 0x121e87) (xorR32R32Effect 0x121e87 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[919, 915]
    (.letOp (n := 923) (.out 0x121e89 (movR32R32Effect 0x121e89 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[872]
    (.letOp (n := 924) (.exec 0x121e89 (fun s => s.RIP = 0x121e89) (movR32R32Effect 0x121e89 2 6 2) (Reg.operands [.gpr 2] [])) #v[872]
    (.letOp (n := 925) (.out 0x121e8b (rolR32Effect 0x121e8b 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[923]
    (.letOp (n := 926) (.exec 0x121e8b (fun s => s.RIP = 0x121e8b) (rolR32Effect 0x121e8b 3 6 10) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[923]
    (.letOp (n := 927) (.out 0x121e8e (xorR32R32Effect 0x121e8e 2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[925, 921]
    (.letOp (n := 928) (.exec 0x121e8e (fun s => s.RIP = 0x121e8e) (xorR32R32Effect 0x121e8e 2 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[925, 921]
    (.letOp (n := 929) (.out 0x121e90 (movR32R32Effect 0x121e90 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[791]
    (.letOp (n := 930) (.exec 0x121e90 (fun s => s.RIP = 0x121e90) (movR32R32Effect 0x121e90 2 3 0) (Reg.operands [.gpr 0] [])) #v[791]
    (.letOp (n := 931) (.out 0x121e92 (andR32R32Effect 0x121e92 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[929, 718]
    (.letOp (n := 932) (.exec 0x121e92 (fun s => s.RIP = 0x121e92) (andR32R32Effect 0x121e92 3 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[929, 718]
    (.letOp (n := 933) (.out 0x121e95 (movR32R32Effect 0x121e95 3 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[791]
    (.letOp (n := 934) (.exec 0x121e95 (fun s => s.RIP = 0x121e95) (movR32R32Effect 0x121e95 3 15 0) (Reg.operands [.gpr 0] [])) #v[791]
    (.letOp (n := 935) (.out 0x121e98 (xorR32R32Effect 0x121e98 3 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[933, 718]
    (.letOp (n := 936) (.exec 0x121e98 (fun s => s.RIP = 0x121e98) (xorR32R32Effect 0x121e98 3 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[933, 718]
    (.letOp (n := 937) (.out 0x121e9b (andR32R32Effect 0x121e9b 3 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[935, 872]
    (.letOp (n := 938) (.exec 0x121e9b (fun s => s.RIP = 0x121e9b) (andR32R32Effect 0x121e9b 3 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[935, 872]
    (.letOp (n := 939) (.out 0x121e9e (xorR32R32Effect 0x121e9e 3 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[937, 931]
    (.letOp (n := 940) (.exec 0x121e9e (fun s => s.RIP = 0x121e9e) (xorR32R32Effect 0x121e9e 3 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[937, 931]
    (.letOp (n := 941) (.out 0x121ea1 (addR32R32Effect 0x121ea1 3 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[939, 927]
    (.letOp (n := 942) (.exec 0x121ea1 (fun s => s.RIP = 0x121ea1) (addR32R32Effect 0x121ea1 3 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[939, 927]
    (.letOp (n := 943) (.out 0x121ea4 (addR32R32Effect 0x121ea4 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[637, 911]
    (.letOp (n := 944) (.exec 0x121ea4 (fun s => s.RIP = 0x121ea4) (addR32R32Effect 0x121ea4 3 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[637, 911]
    (.letOp (n := 945) (.out 0x121ea7 (addR32R32Effect 0x121ea7 3 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[941, 911]
    (.letOp (n := 946) (.exec 0x121ea7 (fun s => s.RIP = 0x121ea7) (addR32R32Effect 0x121ea7 3 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[941, 911]
    (.letOp (n := 947) (.out 0x121eaa (movR32R32Effect 0x121eaa 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11] []) (.reg (.gpr 1))) #v[943]
    (.letOp (n := 948) (.exec 0x121eaa (fun s => s.RIP = 0x121eaa) (movR32R32Effect 0x121eaa 3 1 11) (Reg.operands [.gpr 11] [])) #v[943]
    (.letOp (n := 949) (.out 0x121ead (rolR32Effect 0x121ead 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[947]
    (.letOp (n := 950) (.exec 0x121ead (fun s => s.RIP = 0x121ead) (rolR32Effect 0x121ead 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[947]
    (.letOp (n := 951) (.out 0x121eb0 (movR32R32Effect 0x121eb0 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[943]
    (.letOp (n := 952) (.exec 0x121eb0 (fun s => s.RIP = 0x121eb0) (movR32R32Effect 0x121eb0 3 6 11) (Reg.operands [.gpr 11] [])) #v[943]
    (b_l121930_23))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_22 : List UInt8 :=
  [0x89, 0xD6, 0xC1, 0xC6, 0x1E, 0x89, 0xD3, 0xC1, 0xC3, 0x13, 0x31, 0xF3, 0x89, 0xD6, 0xC1, 0xC6,
    0x0A, 0x31, 0xDE, 0x89, 0xC3, 0x44, 0x21, 0xD3, 0x41, 0x89, 0xC7, 0x45, 0x31, 0xD7, 0x41, 0x21,
    0xD7, 0x41, 0x31, 0xDF, 0x41, 0x01, 0xF7, 0x41, 0x01, 0xCB, 0x41, 0x01, 0xCF, 0x44, 0x89, 0xD9,
    0xC1, 0xC1, 0x1A, 0x44, 0x89, 0xDE] ++ bytes_l121930_23

theorem code_l121930_22 : ∀ x ∈ codeRange 0x121e7d bytes_l121930_22, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21e7d 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_23

def b_l121930_21 : Block Op Label signature Reg.count 874 :=
  .letOp (n := 874) (.out 0x121e43 (movR32R32Effect 0x121e43 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[866]
    (.letOp (n := 875) (.exec 0x121e43 (fun s => s.RIP = 0x121e43) (movR32R32Effect 0x121e43 3 1 8) (Reg.operands [.gpr 8] [])) #v[866]
    (.letOp (n := 876) (.out 0x121e46 (rolR32Effect 0x121e46 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[874]
    (.letOp (n := 877) (.exec 0x121e46 (fun s => s.RIP = 0x121e46) (rolR32Effect 0x121e46 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[874]
    (.letOp (n := 878) (.out 0x121e49 (xorR32R32Effect 0x121e49 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[876, 870]
    (.letOp (n := 879) (.exec 0x121e49 (fun s => s.RIP = 0x121e49) (xorR32R32Effect 0x121e49 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[876, 870]
    (.letOp (n := 880) (.out 0x121e4b (movR32R32Effect 0x121e4b 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[866]
    (.letOp (n := 881) (.exec 0x121e4b (fun s => s.RIP = 0x121e4b) (movR32R32Effect 0x121e4b 3 3 8) (Reg.operands [.gpr 8] [])) #v[866]
    (.letOp (n := 882) (.out 0x121e4e (rolR32Effect 0x121e4e 3 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[880]
    (.letOp (n := 883) (.exec 0x121e4e (fun s => s.RIP = 0x121e4e) (rolR32Effect 0x121e4e 3 3 7) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[880]
    (.letOp (n := 884) (.out 0x121e51 (xorR32R32Effect 0x121e51 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[882, 878]
    (.letOp (n := 885) (.exec 0x121e51 (fun s => s.RIP = 0x121e51) (xorR32R32Effect 0x121e51 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[882, 878]
    (.letOp (n := 886) (.out 0x121e53 (movR64M64Effect 0x121e53 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 887) (.exec 0x121e53 (LoadPre 0x121e53 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121e53 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121e53 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 888) (.out 0x121e58 (movR32M32LowEffect 0x121e58 5 (.base 1 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[886]
    (.letOp (n := 889) (.exec 0x121e58 (LoadPre 0x121e58 (fun s => AddrMode.addr (.base 1 (.d8 0x28)) s (0x121e58 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x121e58 5 (.base 1 (.d8 0x28))) (Reg.operands [.gpr 1] [])) #v[886]
    (.letOp (n := 890) (.out 0x121e5b (bswapR32Effect 0x121e5b 2 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[888]
    (.letOp (n := 891) (.exec 0x121e5b (fun s => s.RIP = 0x121e5b) (bswapR32Effect 0x121e5b 2 5) (Reg.operands [.gpr 5] [])) #v[888]
    (.letOp (n := 892) (.exec 0x121e5d (StorePre 0x121e5d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x121e5d + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x121e5d 5 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[890, 4]
    (.letOp (n := 893) (.out 0x121e61 (movR32R32Effect 0x121e61 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[866]
    (.letOp (n := 894) (.exec 0x121e61 (fun s => s.RIP = 0x121e61) (movR32R32Effect 0x121e61 3 1 8) (Reg.operands [.gpr 8] [])) #v[866]
    (.letOp (n := 895) (.out 0x121e64 (andR32R32Effect 0x121e64 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[893, 789]
    (.letOp (n := 896) (.exec 0x121e64 (fun s => s.RIP = 0x121e64) (andR32R32Effect 0x121e64 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[893, 789]
    (.letOp (n := 897) (.out 0x121e67 (addR32R32Effect 0x121e67 2 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[635, 890]
    (.letOp (n := 898) (.exec 0x121e67 (fun s => s.RIP = 0x121e67) (addR32R32Effect 0x121e67 2 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[635, 890]
    (.letOp (n := 899) (.out 0x121e69 (addR32R32Effect 0x121e69 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[897, 895]
    (.letOp (n := 900) (.exec 0x121e69 (fun s => s.RIP = 0x121e69) (addR32R32Effect 0x121e69 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[897, 895]
    (.letOp (n := 901) (.out 0x121e6b (movR32R32Effect 0x121e6b 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[866]
    (.letOp (n := 902) (.exec 0x121e6b (fun s => s.RIP = 0x121e6b) (movR32R32Effect 0x121e6b 3 1 8) (Reg.operands [.gpr 8] [])) #v[866]
    (.letOp (n := 903) (.out 0x121e6e (notR32Effect 0x121e6e 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[901]
    (.letOp (n := 904) (.exec 0x121e6e (fun s => s.RIP = 0x121e6e) (notR32Effect 0x121e6e 2 1) (Reg.operands [.gpr 1] [])) #v[901]
    (.letOp (n := 905) (.out 0x121e70 (andR32R32Effect 0x121e70 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[903, 712]
    (.letOp (n := 906) (.exec 0x121e70 (fun s => s.RIP = 0x121e70) (andR32R32Effect 0x121e70 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[903, 712]
    (.letOp (n := 907) (.out 0x121e72 (addR32R32Effect 0x121e72 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[899, 905]
    (.letOp (n := 908) (.exec 0x121e72 (fun s => s.RIP = 0x121e72) (addR32R32Effect 0x121e72 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[899, 905]
    (.letOp (n := 909) (.out 0x121e74 (leaR32Effect 0x121e74 3 1 (.sib 3 (some 6) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3, .gpr 6] []) (.reg (.gpr 1))) #v[884, 907]
    (.letOp (n := 910) (.exec 0x121e74 (fun s => s.RIP = 0x121e74) (leaR32Effect 0x121e74 3 1 (.sib 3 (some 6) 0 .none)) (Reg.operands [.gpr 3, .gpr 6] [])) #v[884, 907]
    (.letOp (n := 911) (.out 0x121e77 (addR32Imm32Effect 0x121e77 6 1 0x243185be) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[909]
    (.letOp (n := 912) (.exec 0x121e77 (fun s => s.RIP = 0x121e77) (addR32Imm32Effect 0x121e77 6 1 0x243185be) (Reg.operands [.gpr 1] [])) #v[909]
    (b_l121930_22)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_21 : List UInt8 :=
  [0x44, 0x89, 0xC1, 0xC1, 0xC1, 0x15, 0x31, 0xD9, 0x44, 0x89, 0xC3, 0xC1, 0xC3, 0x07, 0x31, 0xCB,
    0x48, 0x8B, 0x4C, 0x24, 0x18, 0x8B, 0x69, 0x28, 0x0F, 0xCD, 0x89, 0x6C, 0x24, 0x0C, 0x44, 0x89,
    0xC1, 0x44, 0x21, 0xC9, 0x01, 0xEE, 0x01, 0xCE, 0x44, 0x89, 0xC1, 0xF7, 0xD1, 0x21, 0xF9, 0x01,
    0xCE, 0x8D, 0x0C, 0x33, 0x81, 0xC1, 0xBE, 0x85, 0x31, 0x24] ++ bytes_l121930_22

theorem code_l121930_21 : ∀ x ∈ codeRange 0x121e43 bytes_l121930_21, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21e43 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_22

def b_l121930_20 : Block Op Label signature Reg.count 834 :=
  .letOp (n := 834) (.out 0x121e0d (rolR32Effect 0x121e0d 3 3 30) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[832]
    (.letOp (n := 835) (.exec 0x121e0d (fun s => s.RIP = 0x121e0d) (rolR32Effect 0x121e0d 3 3 30) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[832]
    (.letOp (n := 836) (.out 0x121e10 (addR32R32Effect 0x121e10 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[830, 807]
    (.letOp (n := 837) (.exec 0x121e10 (fun s => s.RIP = 0x121e10) (addR32R32Effect 0x121e10 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[830, 807]
    (.letOp (n := 838) (.out 0x121e12 (addR32Imm32Effect 0x121e12 6 1 0x12835b01) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[836]
    (.letOp (n := 839) (.exec 0x121e12 (fun s => s.RIP = 0x121e12) (addR32Imm32Effect 0x121e12 6 1 0x12835b01) (Reg.operands [.gpr 1] [])) #v[836]
    (.letOp (n := 840) (.out 0x121e18 (movR32R32Effect 0x121e18 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[791]
    (.letOp (n := 841) (.exec 0x121e18 (fun s => s.RIP = 0x121e18) (movR32R32Effect 0x121e18 2 2 0) (Reg.operands [.gpr 0] [])) #v[791]
    (.letOp (n := 842) (.out 0x121e1a (rolR32Effect 0x121e1a 3 2 19) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[840]
    (.letOp (n := 843) (.exec 0x121e1a (fun s => s.RIP = 0x121e1a) (rolR32Effect 0x121e1a 3 2 19) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[840]
    (.letOp (n := 844) (.out 0x121e1d (xorR32R32Effect 0x121e1d 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[842, 834]
    (.letOp (n := 845) (.exec 0x121e1d (fun s => s.RIP = 0x121e1d) (xorR32R32Effect 0x121e1d 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[842, 834]
    (.letOp (n := 846) (.out 0x121e1f (movR32R32Effect 0x121e1f 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[791]
    (.letOp (n := 847) (.exec 0x121e1f (fun s => s.RIP = 0x121e1f) (movR32R32Effect 0x121e1f 2 3 0) (Reg.operands [.gpr 0] [])) #v[791]
    (.letOp (n := 848) (.out 0x121e21 (rolR32Effect 0x121e21 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[846]
    (.letOp (n := 849) (.exec 0x121e21 (fun s => s.RIP = 0x121e21) (rolR32Effect 0x121e21 3 3 10) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[846]
    (.letOp (n := 850) (.out 0x121e24 (xorR32R32Effect 0x121e24 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[848, 844]
    (.letOp (n := 851) (.exec 0x121e24 (fun s => s.RIP = 0x121e24) (xorR32R32Effect 0x121e24 2 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[848, 844]
    (.letOp (n := 852) (.out 0x121e26 (movR32R32Effect 0x121e26 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 10] []) (.reg (.gpr 5))) #v[718]
    (.letOp (n := 853) (.exec 0x121e26 (fun s => s.RIP = 0x121e26) (movR32R32Effect 0x121e26 3 5 10) (Reg.operands [.gpr 10] [])) #v[718]
    (.letOp (n := 854) (.out 0x121e29 (andR32R32Effect 0x121e29 3 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[852, 637]
    (.letOp (n := 855) (.exec 0x121e29 (fun s => s.RIP = 0x121e29) (andR32R32Effect 0x121e29 3 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[852, 637]
    (.letOp (n := 856) (.out 0x121e2c (movR32R32Effect 0x121e2c 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[718]
    (.letOp (n := 857) (.exec 0x121e2c (fun s => s.RIP = 0x121e2c) (movR32R32Effect 0x121e2c 3 2 10) (Reg.operands [.gpr 10] [])) #v[718]
    (.letOp (n := 858) (.out 0x121e2f (xorR32R32Effect 0x121e2f 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[856, 637]
    (.letOp (n := 859) (.exec 0x121e2f (fun s => s.RIP = 0x121e2f) (xorR32R32Effect 0x121e2f 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[856, 637]
    (.letOp (n := 860) (.out 0x121e32 (andR32R32Effect 0x121e32 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[858, 791]
    (.letOp (n := 861) (.exec 0x121e32 (fun s => s.RIP = 0x121e32) (andR32R32Effect 0x121e32 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[858, 791]
    (.letOp (n := 862) (.out 0x121e34 (xorR32R32Effect 0x121e34 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[860, 854]
    (.letOp (n := 863) (.exec 0x121e34 (fun s => s.RIP = 0x121e34) (xorR32R32Effect 0x121e34 2 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[860, 854]
    (.letOp (n := 864) (.out 0x121e36 (addR32R32Effect 0x121e36 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[862, 850]
    (.letOp (n := 865) (.exec 0x121e36 (fun s => s.RIP = 0x121e36) (addR32R32Effect 0x121e36 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[862, 850]
    (.letOp (n := 866) (.out 0x121e38 (addR32R32Effect 0x121e38 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[564, 838]
    (.letOp (n := 867) (.exec 0x121e38 (fun s => s.RIP = 0x121e38) (addR32R32Effect 0x121e38 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[564, 838]
    (.letOp (n := 868) (.out 0x121e3b (movR32R32Effect 0x121e3b 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[866]
    (.letOp (n := 869) (.exec 0x121e3b (fun s => s.RIP = 0x121e3b) (movR32R32Effect 0x121e3b 3 3 8) (Reg.operands [.gpr 8] [])) #v[866]
    (.letOp (n := 870) (.out 0x121e3e (rolR32Effect 0x121e3e 3 3 26) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[868]
    (.letOp (n := 871) (.exec 0x121e3e (fun s => s.RIP = 0x121e3e) (rolR32Effect 0x121e3e 3 3 26) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[868]
    (.letOp (n := 872) (.out 0x121e41 (addR32R32Effect 0x121e41 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[864, 838]
    (.letOp (n := 873) (.exec 0x121e41 (fun s => s.RIP = 0x121e41) (addR32R32Effect 0x121e41 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[864, 838]
    (b_l121930_21))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_20 : List UInt8 :=
  [0xC1, 0xC3, 0x1E, 0x01, 0xD1, 0x81, 0xC1, 0x01, 0x5B, 0x83, 0x12, 0x89, 0xC2, 0xC1, 0xC2, 0x13,
    0x31, 0xDA, 0x89, 0xC3, 0xC1, 0xC3, 0x0A, 0x31, 0xD3, 0x44, 0x89, 0xD5, 0x44, 0x21, 0xDD, 0x44,
    0x89, 0xD2, 0x44, 0x31, 0xDA, 0x21, 0xC2, 0x31, 0xEA, 0x01, 0xDA, 0x41, 0x01, 0xC8, 0x44, 0x89,
    0xC3, 0xC1, 0xC3, 0x1A, 0x01, 0xCA] ++ bytes_l121930_21

theorem code_l121930_20 : ∀ x ∈ codeRange 0x121e0d bytes_l121930_20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21e0d 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_21

def b_l121930_19 : Block Op Label signature Reg.count 795 :=
  .letOp (n := 795) (.out 0x121dd8 (rolR32Effect 0x121dd8 3 2 26) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[793]
    (.letOp (n := 796) (.exec 0x121dd8 (fun s => s.RIP = 0x121dd8) (rolR32Effect 0x121dd8 3 2 26) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[793]
    (.letOp (n := 797) (.out 0x121ddb (movR32R32Effect 0x121ddb 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[789]
    (.letOp (n := 798) (.exec 0x121ddb (fun s => s.RIP = 0x121ddb) (movR32R32Effect 0x121ddb 3 3 9) (Reg.operands [.gpr 9] [])) #v[789]
    (.letOp (n := 799) (.out 0x121dde (rolR32Effect 0x121dde 3 3 21) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[797]
    (.letOp (n := 800) (.exec 0x121dde (fun s => s.RIP = 0x121dde) (rolR32Effect 0x121dde 3 3 21) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[797]
    (.letOp (n := 801) (.out 0x121de1 (xorR32R32Effect 0x121de1 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[799, 795]
    (.letOp (n := 802) (.exec 0x121de1 (fun s => s.RIP = 0x121de1) (xorR32R32Effect 0x121de1 2 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[799, 795]
    (.letOp (n := 803) (.out 0x121de3 (movR32R32Effect 0x121de3 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[789]
    (.letOp (n := 804) (.exec 0x121de3 (fun s => s.RIP = 0x121de3) (movR32R32Effect 0x121de3 3 2 9) (Reg.operands [.gpr 9] [])) #v[789]
    (.letOp (n := 805) (.out 0x121de6 (rolR32Effect 0x121de6 3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[803]
    (.letOp (n := 806) (.exec 0x121de6 (fun s => s.RIP = 0x121de6) (rolR32Effect 0x121de6 3 2 7) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[803]
    (.letOp (n := 807) (.out 0x121de9 (xorR32R32Effect 0x121de9 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[805, 801]
    (.letOp (n := 808) (.exec 0x121de9 (fun s => s.RIP = 0x121de9) (xorR32R32Effect 0x121de9 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[805, 801]
    (.letOp (n := 809) (.out 0x121deb (movR64M64Effect 0x121deb 3 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 810) (.exec 0x121deb (LoadPre 0x121deb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121deb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121deb 3 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 811) (.out 0x121df0 (movR32M32LowEffect 0x121df0 5 (.base 3 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[809]
    (.letOp (n := 812) (.exec 0x121df0 (LoadPre 0x121df0 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x121df0 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x121df0 5 (.base 3 (.d8 0x24))) (Reg.operands [.gpr 3] [])) #v[809]
    (.letOp (n := 813) (.out 0x121df3 (bswapR32Effect 0x121df3 2 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[811]
    (.letOp (n := 814) (.exec 0x121df3 (fun s => s.RIP = 0x121df3) (bswapR32Effect 0x121df3 2 5) (Reg.operands [.gpr 5] [])) #v[811]
    (.letOp (n := 815) (.exec 0x121df5 (StorePre 0x121df5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x121df5 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x121df5 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[813, 4]
    (.letOp (n := 816) (.out 0x121df9 (movR32R32Effect 0x121df9 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[789]
    (.letOp (n := 817) (.exec 0x121df9 (fun s => s.RIP = 0x121df9) (movR32R32Effect 0x121df9 3 3 9) (Reg.operands [.gpr 9] [])) #v[789]
    (.letOp (n := 818) (.out 0x121dfc (andR32R32Effect 0x121dfc 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[816, 712]
    (.letOp (n := 819) (.exec 0x121dfc (fun s => s.RIP = 0x121dfc) (andR32R32Effect 0x121dfc 2 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[816, 712]
    (.letOp (n := 820) (.out 0x121dfe (addR32R32Effect 0x121dfe 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[558, 813]
    (.letOp (n := 821) (.exec 0x121dfe (fun s => s.RIP = 0x121dfe) (addR32R32Effect 0x121dfe 2 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[558, 813]
    (.letOp (n := 822) (.out 0x121e00 (addR32R32Effect 0x121e00 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[820, 818]
    (.letOp (n := 823) (.exec 0x121e00 (fun s => s.RIP = 0x121e00) (addR32R32Effect 0x121e00 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[820, 818]
    (.letOp (n := 824) (.out 0x121e02 (movR32R32Effect 0x121e02 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[789]
    (.letOp (n := 825) (.exec 0x121e02 (fun s => s.RIP = 0x121e02) (movR32R32Effect 0x121e02 3 3 9) (Reg.operands [.gpr 9] [])) #v[789]
    (.letOp (n := 826) (.out 0x121e05 (notR32Effect 0x121e05 2 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[824]
    (.letOp (n := 827) (.exec 0x121e05 (fun s => s.RIP = 0x121e05) (notR32Effect 0x121e05 2 3) (Reg.operands [.gpr 3] [])) #v[824]
    (.letOp (n := 828) (.out 0x121e07 (andR32R32Effect 0x121e07 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[826, 635]
    (.letOp (n := 829) (.exec 0x121e07 (fun s => s.RIP = 0x121e07) (andR32R32Effect 0x121e07 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[826, 635]
    (.letOp (n := 830) (.out 0x121e09 (addR32R32Effect 0x121e09 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[822, 828]
    (.letOp (n := 831) (.exec 0x121e09 (fun s => s.RIP = 0x121e09) (addR32R32Effect 0x121e09 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[822, 828]
    (.letOp (n := 832) (.out 0x121e0b (movR32R32Effect 0x121e0b 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[791]
    (.letOp (n := 833) (.exec 0x121e0b (fun s => s.RIP = 0x121e0b) (movR32R32Effect 0x121e0b 2 3 0) (Reg.operands [.gpr 0] [])) #v[791]
    (b_l121930_20)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_19 : List UInt8 :=
  [0xC1, 0xC2, 0x1A, 0x44, 0x89, 0xCB, 0xC1, 0xC3, 0x15, 0x31, 0xD3, 0x44, 0x89, 0xCA, 0xC1, 0xC2,
    0x07, 0x31, 0xDA, 0x48, 0x8B, 0x5C, 0x24, 0x18, 0x8B, 0x6B, 0x24, 0x0F, 0xCD, 0x89, 0x6C, 0x24,
    0x08, 0x44, 0x89, 0xCB, 0x21, 0xFB, 0x01, 0xE9, 0x01, 0xD9, 0x44, 0x89, 0xCB, 0xF7, 0xD3, 0x21,
    0xF3, 0x01, 0xD9, 0x89, 0xC3] ++ bytes_l121930_20

theorem code_l121930_19 : ∀ x ∈ codeRange 0x121dd8 bytes_l121930_19, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21dd8 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_20

def b_l121930_18 : Block Op Label signature Reg.count 755 :=
  .letOp (n := 755) (.out 0x121d9e (leaR32Effect 0x121d9e 3 2 (.sib 3 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[730, 753]
    (.letOp (n := 756) (.exec 0x121d9e (fun s => s.RIP = 0x121d9e) (leaR32Effect 0x121d9e 3 2 (.sib 3 (some 0) 0 .none)) (Reg.operands [.gpr 3, .gpr 0] [])) #v[730, 753]
    (.letOp (n := 757) (.out 0x121da1 (addR32Imm32Effect 0x121da1 6 2 0xd807aa98) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[755]
    (.letOp (n := 758) (.exec 0x121da1 (fun s => s.RIP = 0x121da1) (addR32Imm32Effect 0x121da1 6 2 0xd807aa98) (Reg.operands [.gpr 2] [])) #v[755]
    (.letOp (n := 759) (.out 0x121da7 (movR32R32Effect 0x121da7 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[718]
    (.letOp (n := 760) (.exec 0x121da7 (fun s => s.RIP = 0x121da7) (movR32R32Effect 0x121da7 3 0 10) (Reg.operands [.gpr 10] [])) #v[718]
    (.letOp (n := 761) (.out 0x121daa (rolR32Effect 0x121daa 3 0 30) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[759]
    (.letOp (n := 762) (.exec 0x121daa (fun s => s.RIP = 0x121daa) (rolR32Effect 0x121daa 3 0 30) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[759]
    (.letOp (n := 763) (.out 0x121dad (movR32R32Effect 0x121dad 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 10] []) (.reg (.gpr 3))) #v[718]
    (.letOp (n := 764) (.exec 0x121dad (fun s => s.RIP = 0x121dad) (movR32R32Effect 0x121dad 3 3 10) (Reg.operands [.gpr 10] [])) #v[718]
    (.letOp (n := 765) (.out 0x121db0 (rolR32Effect 0x121db0 3 3 19) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[763]
    (.letOp (n := 766) (.exec 0x121db0 (fun s => s.RIP = 0x121db0) (rolR32Effect 0x121db0 3 3 19) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[763]
    (.letOp (n := 767) (.out 0x121db3 (xorR32R32Effect 0x121db3 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[765, 761]
    (.letOp (n := 768) (.exec 0x121db3 (fun s => s.RIP = 0x121db3) (xorR32R32Effect 0x121db3 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[765, 761]
    (.letOp (n := 769) (.out 0x121db5 (movR32R32Effect 0x121db5 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 10] []) (.reg (.gpr 5))) #v[718]
    (.letOp (n := 770) (.exec 0x121db5 (fun s => s.RIP = 0x121db5) (movR32R32Effect 0x121db5 3 5 10) (Reg.operands [.gpr 10] [])) #v[718]
    (.letOp (n := 771) (.out 0x121db8 (rolR32Effect 0x121db8 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[769]
    (.letOp (n := 772) (.exec 0x121db8 (fun s => s.RIP = 0x121db8) (rolR32Effect 0x121db8 3 5 10) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[769]
    (.letOp (n := 773) (.out 0x121dbb (xorR32R32Effect 0x121dbb 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[771, 767]
    (.letOp (n := 774) (.exec 0x121dbb (fun s => s.RIP = 0x121dbb) (xorR32R32Effect 0x121dbb 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[771, 767]
    (.letOp (n := 775) (.out 0x121dbd (movR32R32Effect 0x121dbd 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[637]
    (.letOp (n := 776) (.exec 0x121dbd (fun s => s.RIP = 0x121dbd) (movR32R32Effect 0x121dbd 3 3 11) (Reg.operands [.gpr 11] [])) #v[637]
    (.letOp (n := 777) (.out 0x121dc0 (andR32R32Effect 0x121dc0 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[775, 564]
    (.letOp (n := 778) (.exec 0x121dc0 (fun s => s.RIP = 0x121dc0) (andR32R32Effect 0x121dc0 3 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[775, 564]
    (.letOp (n := 779) (.out 0x121dc3 (movR32R32Effect 0x121dc3 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[637]
    (.letOp (n := 780) (.exec 0x121dc3 (fun s => s.RIP = 0x121dc3) (movR32R32Effect 0x121dc3 3 0 11) (Reg.operands [.gpr 11] [])) #v[637]
    (.letOp (n := 781) (.out 0x121dc6 (xorR32R32Effect 0x121dc6 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[779, 564]
    (.letOp (n := 782) (.exec 0x121dc6 (fun s => s.RIP = 0x121dc6) (xorR32R32Effect 0x121dc6 3 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[779, 564]
    (.letOp (n := 783) (.out 0x121dc9 (andR32R32Effect 0x121dc9 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[781, 718]
    (.letOp (n := 784) (.exec 0x121dc9 (fun s => s.RIP = 0x121dc9) (andR32R32Effect 0x121dc9 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[781, 718]
    (.letOp (n := 785) (.out 0x121dcc (xorR32R32Effect 0x121dcc 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[783, 777]
    (.letOp (n := 786) (.exec 0x121dcc (fun s => s.RIP = 0x121dcc) (xorR32R32Effect 0x121dcc 2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[783, 777]
    (.letOp (n := 787) (.out 0x121dce (addR32R32Effect 0x121dce 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[785, 773]
    (.letOp (n := 788) (.exec 0x121dce (fun s => s.RIP = 0x121dce) (addR32R32Effect 0x121dce 2 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[785, 773]
    (.letOp (n := 789) (.out 0x121dd0 (addR32R32Effect 0x121dd0 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[483, 757]
    (.letOp (n := 790) (.exec 0x121dd0 (fun s => s.RIP = 0x121dd0) (addR32R32Effect 0x121dd0 3 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[483, 757]
    (.letOp (n := 791) (.out 0x121dd3 (addR32R32Effect 0x121dd3 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[787, 757]
    (.letOp (n := 792) (.exec 0x121dd3 (fun s => s.RIP = 0x121dd3) (addR32R32Effect 0x121dd3 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[787, 757]
    (.letOp (n := 793) (.out 0x121dd5 (movR32R32Effect 0x121dd5 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[789]
    (.letOp (n := 794) (.exec 0x121dd5 (fun s => s.RIP = 0x121dd5) (movR32R32Effect 0x121dd5 3 2 9) (Reg.operands [.gpr 9] [])) #v[789]
    (b_l121930_19))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_18 : List UInt8 :=
  [0x8D, 0x14, 0x03, 0x81, 0xC2, 0x98, 0xAA, 0x07, 0xD8, 0x44, 0x89, 0xD0, 0xC1, 0xC0, 0x1E, 0x44,
    0x89, 0xD3, 0xC1, 0xC3, 0x13, 0x31, 0xC3, 0x44, 0x89, 0xD5, 0xC1, 0xC5, 0x0A, 0x31, 0xDD, 0x44,
    0x89, 0xDB, 0x44, 0x21, 0xC3, 0x44, 0x89, 0xD8, 0x44, 0x31, 0xC0, 0x44, 0x21, 0xD0, 0x31, 0xD8,
    0x01, 0xE8, 0x41, 0x01, 0xD1, 0x01, 0xD0, 0x44, 0x89, 0xCA] ++ bytes_l121930_19

theorem code_l121930_18 : ∀ x ∈ codeRange 0x121d9e bytes_l121930_18, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21d9e 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_19

def b_l121930_17 : Block Op Label signature Reg.count 716 :=
  .letOp (n := 716) (.out 0x121d6c (rolR32Effect 0x121d6c 3 3 26) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[714]
    (.letOp (n := 717) (.exec 0x121d6c (fun s => s.RIP = 0x121d6c) (rolR32Effect 0x121d6c 3 3 26) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[714]
    (.letOp (n := 718) (.out 0x121d6f (addR32R32Effect 0x121d6f 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[710, 684]
    (.letOp (n := 719) (.exec 0x121d6f (fun s => s.RIP = 0x121d6f) (addR32R32Effect 0x121d6f 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[710, 684]
    (.letOp (n := 720) (.out 0x121d72 (movR32R32Effect 0x121d72 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[712]
    (.letOp (n := 721) (.exec 0x121d72 (fun s => s.RIP = 0x121d72) (movR32R32Effect 0x121d72 2 2 7) (Reg.operands [.gpr 7] [])) #v[712]
    (.letOp (n := 722) (.out 0x121d74 (rolR32Effect 0x121d74 3 2 21) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[720]
    (.letOp (n := 723) (.exec 0x121d74 (fun s => s.RIP = 0x121d74) (rolR32Effect 0x121d74 3 2 21) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[720]
    (.letOp (n := 724) (.out 0x121d77 (xorR32R32Effect 0x121d77 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[722, 716]
    (.letOp (n := 725) (.exec 0x121d77 (fun s => s.RIP = 0x121d77) (xorR32R32Effect 0x121d77 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[722, 716]
    (.letOp (n := 726) (.out 0x121d79 (movR32R32Effect 0x121d79 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[712]
    (.letOp (n := 727) (.exec 0x121d79 (fun s => s.RIP = 0x121d79) (movR32R32Effect 0x121d79 2 3 7) (Reg.operands [.gpr 7] [])) #v[712]
    (.letOp (n := 728) (.out 0x121d7b (rolR32Effect 0x121d7b 3 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[726]
    (.letOp (n := 729) (.exec 0x121d7b (fun s => s.RIP = 0x121d7b) (rolR32Effect 0x121d7b 3 3 7) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[726]
    (.letOp (n := 730) (.out 0x121d7e (xorR32R32Effect 0x121d7e 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[728, 724]
    (.letOp (n := 731) (.exec 0x121d7e (fun s => s.RIP = 0x121d7e) (xorR32R32Effect 0x121d7e 2 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[728, 724]
    (.letOp (n := 732) (.out 0x121d80 (movR64M64Effect 0x121d80 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 733) (.exec 0x121d80 (LoadPre 0x121d80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121d80 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121d80 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 734) (.out 0x121d85 (movR32M32LowEffect 0x121d85 5 (.base 2 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[732]
    (.letOp (n := 735) (.exec 0x121d85 (LoadPre 0x121d85 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x121d85 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x121d85 5 (.base 2 (.d8 0x20))) (Reg.operands [.gpr 2] [])) #v[732]
    (.letOp (n := 736) (.out 0x121d88 (bswapR32Effect 0x121d88 2 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[734]
    (.letOp (n := 737) (.exec 0x121d88 (fun s => s.RIP = 0x121d88) (bswapR32Effect 0x121d88 2 5) (Reg.operands [.gpr 5] [])) #v[734]
    (.letOp (n := 738) (.exec 0x121d8a (StorePre 0x121d8a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x121d8a + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x121d8a 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[736, 4]
    (.letOp (n := 739) (.out 0x121d8e (movR32R32Effect 0x121d8e 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[712]
    (.letOp (n := 740) (.exec 0x121d8e (fun s => s.RIP = 0x121d8e) (movR32R32Effect 0x121d8e 2 2 7) (Reg.operands [.gpr 7] [])) #v[712]
    (.letOp (n := 741) (.out 0x121d90 (andR32R32Effect 0x121d90 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[739, 635]
    (.letOp (n := 742) (.exec 0x121d90 (fun s => s.RIP = 0x121d90) (andR32R32Effect 0x121d90 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[739, 635]
    (.letOp (n := 743) (.out 0x121d92 (addR32R32Effect 0x121d92 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[481, 736]
    (.letOp (n := 744) (.exec 0x121d92 (fun s => s.RIP = 0x121d92) (addR32R32Effect 0x121d92 2 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[481, 736]
    (.letOp (n := 745) (.out 0x121d94 (addR32R32Effect 0x121d94 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[743, 741]
    (.letOp (n := 746) (.exec 0x121d94 (fun s => s.RIP = 0x121d94) (addR32R32Effect 0x121d94 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[743, 741]
    (.letOp (n := 747) (.out 0x121d96 (movR32R32Effect 0x121d96 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[712]
    (.letOp (n := 748) (.exec 0x121d96 (fun s => s.RIP = 0x121d96) (movR32R32Effect 0x121d96 2 2 7) (Reg.operands [.gpr 7] [])) #v[712]
    (.letOp (n := 749) (.out 0x121d98 (notR32Effect 0x121d98 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[747]
    (.letOp (n := 750) (.exec 0x121d98 (fun s => s.RIP = 0x121d98) (notR32Effect 0x121d98 2 2) (Reg.operands [.gpr 2] [])) #v[747]
    (.letOp (n := 751) (.out 0x121d9a (andR32R32Effect 0x121d9a 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[749, 558]
    (.letOp (n := 752) (.exec 0x121d9a (fun s => s.RIP = 0x121d9a) (andR32R32Effect 0x121d9a 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[749, 558]
    (.letOp (n := 753) (.out 0x121d9c (addR32R32Effect 0x121d9c 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[745, 751]
    (.letOp (n := 754) (.exec 0x121d9c (fun s => s.RIP = 0x121d9c) (addR32R32Effect 0x121d9c 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[745, 751]
    (b_l121930_18)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_17 : List UInt8 :=
  [0xC1, 0xC3, 0x1A, 0x41, 0x01, 0xD2, 0x89, 0xFA, 0xC1, 0xC2, 0x15, 0x31, 0xDA, 0x89, 0xFB, 0xC1,
    0xC3, 0x07, 0x31, 0xD3, 0x48, 0x8B, 0x54, 0x24, 0x18, 0x8B, 0x6A, 0x20, 0x0F, 0xCD, 0x89, 0x6C,
    0x24, 0x60, 0x89, 0xFA, 0x21, 0xF2, 0x01, 0xE8, 0x01, 0xD0, 0x89, 0xFA, 0xF7, 0xD2, 0x21, 0xCA,
    0x01, 0xD0] ++ bytes_l121930_18

theorem code_l121930_17 : ∀ x ∈ codeRange 0x121d6c bytes_l121930_17, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21d6c 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_18

def b_l121930_16 : Block Op Label signature Reg.count 676 :=
  .letOp (n := 676) (.out 0x121d30 (addR32R32Effect 0x121d30 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[668, 674]
    (.letOp (n := 677) (.exec 0x121d30 (fun s => s.RIP = 0x121d30) (addR32R32Effect 0x121d30 3 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[668, 674]
    (.letOp (n := 678) (.out 0x121d33 (movR32R32Effect 0x121d33 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[637]
    (.letOp (n := 679) (.exec 0x121d33 (fun s => s.RIP = 0x121d33) (movR32R32Effect 0x121d33 3 10 11) (Reg.operands [.gpr 11] [])) #v[637]
    (.letOp (n := 680) (.out 0x121d36 (rolR32Effect 0x121d36 4 10 30) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[678]
    (.letOp (n := 681) (.exec 0x121d36 (fun s => s.RIP = 0x121d36) (rolR32Effect 0x121d36 4 10 30) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[678]
    (.letOp (n := 682) (.out 0x121d3a (addR32R32Effect 0x121d3a 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[653, 676]
    (.letOp (n := 683) (.exec 0x121d3a (fun s => s.RIP = 0x121d3a) (addR32R32Effect 0x121d3a 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[653, 676]
    (.letOp (n := 684) (.out 0x121d3c (addR32Imm32Effect 0x121d3c 6 2 0xab1c5ed5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[682]
    (.letOp (n := 685) (.exec 0x121d3c (fun s => s.RIP = 0x121d3c) (addR32Imm32Effect 0x121d3c 6 2 0xab1c5ed5) (Reg.operands [.gpr 2] [])) #v[682]
    (.letOp (n := 686) (.out 0x121d42 (movR32R32Effect 0x121d42 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[637]
    (.letOp (n := 687) (.exec 0x121d42 (fun s => s.RIP = 0x121d42) (movR32R32Effect 0x121d42 3 3 11) (Reg.operands [.gpr 11] [])) #v[637]
    (.letOp (n := 688) (.out 0x121d45 (rolR32Effect 0x121d45 3 3 19) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[686]
    (.letOp (n := 689) (.exec 0x121d45 (fun s => s.RIP = 0x121d45) (rolR32Effect 0x121d45 3 3 19) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[686]
    (.letOp (n := 690) (.out 0x121d48 (xorR32R32Effect 0x121d48 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[688, 680]
    (.letOp (n := 691) (.exec 0x121d48 (fun s => s.RIP = 0x121d48) (xorR32R32Effect 0x121d48 3 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[688, 680]
    (.letOp (n := 692) (.out 0x121d4b (movR32R32Effect 0x121d4b 3 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 11] []) (.reg (.gpr 5))) #v[637]
    (.letOp (n := 693) (.exec 0x121d4b (fun s => s.RIP = 0x121d4b) (movR32R32Effect 0x121d4b 3 5 11) (Reg.operands [.gpr 11] [])) #v[637]
    (.letOp (n := 694) (.out 0x121d4e (rolR32Effect 0x121d4e 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[692]
    (.letOp (n := 695) (.exec 0x121d4e (fun s => s.RIP = 0x121d4e) (rolR32Effect 0x121d4e 3 5 10) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[692]
    (.letOp (n := 696) (.out 0x121d51 (xorR32R32Effect 0x121d51 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[694, 690]
    (.letOp (n := 697) (.exec 0x121d51 (fun s => s.RIP = 0x121d51) (xorR32R32Effect 0x121d51 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[694, 690]
    (.letOp (n := 698) (.out 0x121d53 (movR32R32Effect 0x121d53 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[564]
    (.letOp (n := 699) (.exec 0x121d53 (fun s => s.RIP = 0x121d53) (movR32R32Effect 0x121d53 3 3 8) (Reg.operands [.gpr 8] [])) #v[564]
    (.letOp (n := 700) (.out 0x121d56 (andR32R32Effect 0x121d56 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[698, 483]
    (.letOp (n := 701) (.exec 0x121d56 (fun s => s.RIP = 0x121d56) (andR32R32Effect 0x121d56 3 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[698, 483]
    (.letOp (n := 702) (.out 0x121d59 (movR32R32Effect 0x121d59 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[564]
    (.letOp (n := 703) (.exec 0x121d59 (fun s => s.RIP = 0x121d59) (movR32R32Effect 0x121d59 3 10 8) (Reg.operands [.gpr 8] [])) #v[564]
    (.letOp (n := 704) (.out 0x121d5c (xorR32R32Effect 0x121d5c 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[702, 483]
    (.letOp (n := 705) (.exec 0x121d5c (fun s => s.RIP = 0x121d5c) (xorR32R32Effect 0x121d5c 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[702, 483]
    (.letOp (n := 706) (.out 0x121d5f (andR32R32Effect 0x121d5f 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[704, 637]
    (.letOp (n := 707) (.exec 0x121d5f (fun s => s.RIP = 0x121d5f) (andR32R32Effect 0x121d5f 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[704, 637]
    (.letOp (n := 708) (.out 0x121d62 (xorR32R32Effect 0x121d62 3 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[706, 700]
    (.letOp (n := 709) (.exec 0x121d62 (fun s => s.RIP = 0x121d62) (xorR32R32Effect 0x121d62 3 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[706, 700]
    (.letOp (n := 710) (.out 0x121d65 (addR32R32Effect 0x121d65 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[708, 696]
    (.letOp (n := 711) (.exec 0x121d65 (fun s => s.RIP = 0x121d65) (addR32R32Effect 0x121d65 3 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[708, 696]
    (.letOp (n := 712) (.out 0x121d68 (addR32R32Effect 0x121d68 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[410, 684]
    (.letOp (n := 713) (.exec 0x121d68 (fun s => s.RIP = 0x121d68) (addR32R32Effect 0x121d68 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[410, 684]
    (.letOp (n := 714) (.out 0x121d6a (movR32R32Effect 0x121d6a 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[712]
    (.letOp (n := 715) (.exec 0x121d6a (fun s => s.RIP = 0x121d6a) (movR32R32Effect 0x121d6a 2 3 7) (Reg.operands [.gpr 7] [])) #v[712]
    (b_l121930_17))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_16 : List UInt8 :=
  [0x44, 0x01, 0xD3, 0x45, 0x89, 0xDA, 0x41, 0xC1, 0xC2, 0x1E, 0x01, 0xDA, 0x81, 0xC2, 0xD5, 0x5E,
    0x1C, 0xAB, 0x44, 0x89, 0xDB, 0xC1, 0xC3, 0x13, 0x44, 0x31, 0xD3, 0x44, 0x89, 0xDD, 0xC1, 0xC5,
    0x0A, 0x31, 0xDD, 0x44, 0x89, 0xC3, 0x44, 0x21, 0xCB, 0x45, 0x89, 0xC2, 0x45, 0x31, 0xCA, 0x45,
    0x21, 0xDA, 0x41, 0x31, 0xDA, 0x41, 0x01, 0xEA, 0x01, 0xD7, 0x89, 0xFB] ++ bytes_l121930_17

theorem code_l121930_16 : ∀ x ∈ codeRange 0x121d30 bytes_l121930_16, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21d30 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_17

def b_l121930_15 : Block Op Label signature Reg.count 637 :=
  .letOp (n := 637) (.out 0x121cf3 (addR32R32Effect 0x121cf3 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[633, 603]
    (.letOp (n := 638) (.exec 0x121cf3 (fun s => s.RIP = 0x121cf3) (addR32R32Effect 0x121cf3 3 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[633, 603]
    (.letOp (n := 639) (.out 0x121cf6 (movR32R32Effect 0x121cf6 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[635]
    (.letOp (n := 640) (.exec 0x121cf6 (fun s => s.RIP = 0x121cf6) (movR32R32Effect 0x121cf6 2 2 6) (Reg.operands [.gpr 6] [])) #v[635]
    (.letOp (n := 641) (.out 0x121cf8 (rolR32Effect 0x121cf8 3 2 26) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[639]
    (.letOp (n := 642) (.exec 0x121cf8 (fun s => s.RIP = 0x121cf8) (rolR32Effect 0x121cf8 3 2 26) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[639]
    (.letOp (n := 643) (.out 0x121cfb (movR32R32Effect 0x121cfb 3 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[635]
    (.letOp (n := 644) (.exec 0x121cfb (fun s => s.RIP = 0x121cfb) (movR32R32Effect 0x121cfb 3 10 6) (Reg.operands [.gpr 6] [])) #v[635]
    (.letOp (n := 645) (.out 0x121cfe (rolR32Effect 0x121cfe 4 10 21) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[643]
    (.letOp (n := 646) (.exec 0x121cfe (fun s => s.RIP = 0x121cfe) (rolR32Effect 0x121cfe 4 10 21) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[643]
    (.letOp (n := 647) (.out 0x121d02 (xorR32R32Effect 0x121d02 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[645, 641]
    (.letOp (n := 648) (.exec 0x121d02 (fun s => s.RIP = 0x121d02) (xorR32R32Effect 0x121d02 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[645, 641]
    (.letOp (n := 649) (.out 0x121d05 (movR32R32Effect 0x121d05 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[635]
    (.letOp (n := 650) (.exec 0x121d05 (fun s => s.RIP = 0x121d05) (movR32R32Effect 0x121d05 2 2 6) (Reg.operands [.gpr 6] [])) #v[635]
    (.letOp (n := 651) (.out 0x121d07 (rolR32Effect 0x121d07 3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[649]
    (.letOp (n := 652) (.exec 0x121d07 (fun s => s.RIP = 0x121d07) (rolR32Effect 0x121d07 3 2 7) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[649]
    (.letOp (n := 653) (.out 0x121d0a (xorR32R32Effect 0x121d0a 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[651, 647]
    (.letOp (n := 654) (.exec 0x121d0a (fun s => s.RIP = 0x121d0a) (xorR32R32Effect 0x121d0a 3 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[651, 647]
    (.letOp (n := 655) (.out 0x121d0d (movR64M64Effect 0x121d0d 10 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 656) (.exec 0x121d0d (LoadPre 0x121d0d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121d0d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121d0d 10 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 657) (.out 0x121d12 (movR32M32Effect 0x121d12 5 (.base 10 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 10] []) (.reg (.gpr 5))) #v[655]
    (.letOp (n := 658) (.exec 0x121d12 (LoadPre 0x121d12 (fun s => AddrMode.addr (.base 10 (.d8 0x1c)) s (0x121d12 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x121d12 5 (.base 10 (.d8 0x1c))) (Reg.operands [.gpr 10] [])) #v[655]
    (.letOp (n := 659) (.out 0x121d16 (bswapR32Effect 0x121d16 2 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[657]
    (.letOp (n := 660) (.exec 0x121d16 (fun s => s.RIP = 0x121d16) (bswapR32Effect 0x121d16 2 5) (Reg.operands [.gpr 5] [])) #v[657]
    (.letOp (n := 661) (.exec 0x121d18 (StorePre 0x121d18 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x121d18 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x121d18 5 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[659, 4]
    (.letOp (n := 662) (.out 0x121d1c (movR32R32Effect 0x121d1c 3 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[635]
    (.letOp (n := 663) (.exec 0x121d1c (fun s => s.RIP = 0x121d1c) (movR32R32Effect 0x121d1c 3 10 6) (Reg.operands [.gpr 6] [])) #v[635]
    (.letOp (n := 664) (.out 0x121d1f (andR32R32Effect 0x121d1f 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[662, 558]
    (.letOp (n := 665) (.exec 0x121d1f (fun s => s.RIP = 0x121d1f) (andR32R32Effect 0x121d1f 3 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[662, 558]
    (.letOp (n := 666) (.out 0x121d22 (addR32R32Effect 0x121d22 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[404, 659]
    (.letOp (n := 667) (.exec 0x121d22 (fun s => s.RIP = 0x121d22) (addR32R32Effect 0x121d22 2 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[404, 659]
    (.letOp (n := 668) (.out 0x121d24 (addR32R32Effect 0x121d24 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[666, 664]
    (.letOp (n := 669) (.exec 0x121d24 (fun s => s.RIP = 0x121d24) (addR32R32Effect 0x121d24 3 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[666, 664]
    (.letOp (n := 670) (.out 0x121d27 (movR32R32Effect 0x121d27 3 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[635]
    (.letOp (n := 671) (.exec 0x121d27 (fun s => s.RIP = 0x121d27) (movR32R32Effect 0x121d27 3 10 6) (Reg.operands [.gpr 6] [])) #v[635]
    (.letOp (n := 672) (.out 0x121d2a (notR32Effect 0x121d2a 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[670]
    (.letOp (n := 673) (.exec 0x121d2a (fun s => s.RIP = 0x121d2a) (notR32Effect 0x121d2a 3 10) (Reg.operands [.gpr 10] [])) #v[670]
    (.letOp (n := 674) (.out 0x121d2d (andR32R32Effect 0x121d2d 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[672, 481]
    (.letOp (n := 675) (.exec 0x121d2d (fun s => s.RIP = 0x121d2d) (andR32R32Effect 0x121d2d 3 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[672, 481]
    (b_l121930_16)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_15 : List UInt8 :=
  [0x41, 0x01, 0xD3, 0x89, 0xF2, 0xC1, 0xC2, 0x1A, 0x41, 0x89, 0xF2, 0x41, 0xC1, 0xC2, 0x15, 0x41,
    0x31, 0xD2, 0x89, 0xF2, 0xC1, 0xC2, 0x07, 0x44, 0x31, 0xD2, 0x4C, 0x8B, 0x54, 0x24, 0x18, 0x41,
    0x8B, 0x6A, 0x1C, 0x0F, 0xCD, 0x89, 0x6C, 0x24, 0x14, 0x41, 0x89, 0xF2, 0x41, 0x21, 0xCA, 0x01,
    0xEB, 0x44, 0x01, 0xD3, 0x41, 0x89, 0xF2, 0x41, 0xF7, 0xD2, 0x41, 0x21, 0xC2] ++ bytes_l121930_16

theorem code_l121930_15 : ∀ x ∈ codeRange 0x121cf3 bytes_l121930_15, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21cf3 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_16

def b_l121930_14 : Block Op Label signature Reg.count 597 :=
  .letOp (n := 597) (.out 0x121cb3 (andR32R32Effect 0x121cb3 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[595, 404]
    (.letOp (n := 598) (.exec 0x121cb3 (fun s => s.RIP = 0x121cb3) (andR32R32Effect 0x121cb3 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[595, 404]
    (.letOp (n := 599) (.out 0x121cb5 (addR32R32Effect 0x121cb5 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[591, 597]
    (.letOp (n := 600) (.exec 0x121cb5 (fun s => s.RIP = 0x121cb5) (addR32R32Effect 0x121cb5 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[591, 597]
    (.letOp (n := 601) (.out 0x121cb8 (leaR32Effect 0x121cb8 4 2 (.sib 11 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 10] []) (.reg (.gpr 2))) #v[576, 599]
    (.letOp (n := 602) (.exec 0x121cb8 (fun s => s.RIP = 0x121cb8) (leaR32Effect 0x121cb8 4 2 (.sib 11 (some 10) 0 .none)) (Reg.operands [.gpr 11, .gpr 10] [])) #v[576, 599]
    (.letOp (n := 603) (.out 0x121cbc (addR32Imm32Effect 0x121cbc 6 2 0x923f82a4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[601]
    (.letOp (n := 604) (.exec 0x121cbc (fun s => s.RIP = 0x121cbc) (addR32Imm32Effect 0x121cbc 6 2 0x923f82a4) (Reg.operands [.gpr 2] [])) #v[601]
    (.letOp (n := 605) (.out 0x121cc2 (movR32R32Effect 0x121cc2 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[564]
    (.letOp (n := 606) (.exec 0x121cc2 (fun s => s.RIP = 0x121cc2) (movR32R32Effect 0x121cc2 3 10 8) (Reg.operands [.gpr 8] [])) #v[564]
    (.letOp (n := 607) (.out 0x121cc5 (rolR32Effect 0x121cc5 4 10 30) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[605]
    (.letOp (n := 608) (.exec 0x121cc5 (fun s => s.RIP = 0x121cc5) (rolR32Effect 0x121cc5 4 10 30) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[605]
    (.letOp (n := 609) (.out 0x121cc9 (movR32R32Effect 0x121cc9 3 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 8] []) (.reg (.gpr 11))) #v[564]
    (.letOp (n := 610) (.exec 0x121cc9 (fun s => s.RIP = 0x121cc9) (movR32R32Effect 0x121cc9 3 11 8) (Reg.operands [.gpr 8] [])) #v[564]
    (.letOp (n := 611) (.out 0x121ccc (rolR32Effect 0x121ccc 4 11 19) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[609]
    (.letOp (n := 612) (.exec 0x121ccc (fun s => s.RIP = 0x121ccc) (rolR32Effect 0x121ccc 4 11 19) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[609]
    (.letOp (n := 613) (.out 0x121cd0 (xorR32R32Effect 0x121cd0 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[611, 607]
    (.letOp (n := 614) (.exec 0x121cd0 (fun s => s.RIP = 0x121cd0) (xorR32R32Effect 0x121cd0 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[611, 607]
    (.letOp (n := 615) (.out 0x121cd3 (movR32R32Effect 0x121cd3 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[564]
    (.letOp (n := 616) (.exec 0x121cd3 (fun s => s.RIP = 0x121cd3) (movR32R32Effect 0x121cd3 3 10 8) (Reg.operands [.gpr 8] [])) #v[564]
    (.letOp (n := 617) (.out 0x121cd6 (rolR32Effect 0x121cd6 4 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[615]
    (.letOp (n := 618) (.exec 0x121cd6 (fun s => s.RIP = 0x121cd6) (rolR32Effect 0x121cd6 4 10 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[615]
    (.letOp (n := 619) (.out 0x121cda (xorR32R32Effect 0x121cda 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[617, 613]
    (.letOp (n := 620) (.exec 0x121cda (fun s => s.RIP = 0x121cda) (xorR32R32Effect 0x121cda 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[617, 613]
    (.letOp (n := 621) (.out 0x121cdd (movR32R32Effect 0x121cdd 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[483]
    (.letOp (n := 622) (.exec 0x121cdd (fun s => s.RIP = 0x121cdd) (movR32R32Effect 0x121cdd 3 5 9) (Reg.operands [.gpr 9] [])) #v[483]
    (.letOp (n := 623) (.out 0x121ce0 (andR32R32Effect 0x121ce0 2 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 7] []) (.reg (.gpr 5))) #v[621, 410]
    (.letOp (n := 624) (.exec 0x121ce0 (fun s => s.RIP = 0x121ce0) (andR32R32Effect 0x121ce0 2 5 7) (Reg.operands [.gpr 5, .gpr 7] [])) #v[621, 410]
    (.letOp (n := 625) (.out 0x121ce2 (movR32R32Effect 0x121ce2 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[483]
    (.letOp (n := 626) (.exec 0x121ce2 (fun s => s.RIP = 0x121ce2) (movR32R32Effect 0x121ce2 3 11 9) (Reg.operands [.gpr 9] [])) #v[483]
    (.letOp (n := 627) (.out 0x121ce5 (xorR32R32Effect 0x121ce5 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[625, 410]
    (.letOp (n := 628) (.exec 0x121ce5 (fun s => s.RIP = 0x121ce5) (xorR32R32Effect 0x121ce5 3 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[625, 410]
    (.letOp (n := 629) (.out 0x121ce8 (andR32R32Effect 0x121ce8 3 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[627, 564]
    (.letOp (n := 630) (.exec 0x121ce8 (fun s => s.RIP = 0x121ce8) (andR32R32Effect 0x121ce8 3 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[627, 564]
    (.letOp (n := 631) (.out 0x121ceb (xorR32R32Effect 0x121ceb 3 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[629, 623]
    (.letOp (n := 632) (.exec 0x121ceb (fun s => s.RIP = 0x121ceb) (xorR32R32Effect 0x121ceb 3 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[629, 623]
    (.letOp (n := 633) (.out 0x121cee (addR32R32Effect 0x121cee 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[631, 619]
    (.letOp (n := 634) (.exec 0x121cee (fun s => s.RIP = 0x121cee) (addR32R32Effect 0x121cee 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[631, 619]
    (.letOp (n := 635) (.out 0x121cf1 (addR32R32Effect 0x121cf1 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[333, 603]
    (.letOp (n := 636) (.exec 0x121cf1 (fun s => s.RIP = 0x121cf1) (addR32R32Effect 0x121cf1 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[333, 603]
    (b_l121930_15))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_14 : List UInt8 :=
  [0x21, 0xDA, 0x41, 0x01, 0xD2, 0x43, 0x8D, 0x14, 0x13, 0x81, 0xC2, 0xA4, 0x82, 0x3F, 0x92, 0x45,
    0x89, 0xC2, 0x41, 0xC1, 0xC2, 0x1E, 0x45, 0x89, 0xC3, 0x41, 0xC1, 0xC3, 0x13, 0x45, 0x31, 0xD3,
    0x45, 0x89, 0xC2, 0x41, 0xC1, 0xC2, 0x0A, 0x45, 0x31, 0xDA, 0x44, 0x89, 0xCD, 0x21, 0xFD, 0x45,
    0x89, 0xCB, 0x41, 0x31, 0xFB, 0x45, 0x21, 0xC3, 0x41, 0x31, 0xEB, 0x45, 0x01, 0xD3, 0x01, 0xD6] ++ bytes_l121930_15

theorem code_l121930_14 : ∀ x ∈ codeRange 0x121cb3 bytes_l121930_14, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21cb3 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_15

def b_l121930_13 : Block Op Label signature Reg.count 558 :=
  .letOp (n := 558) (.out 0x121c79 (addR32R32Effect 0x121c79 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[232, 530]
    (.letOp (n := 559) (.exec 0x121c79 (fun s => s.RIP = 0x121c79) (addR32R32Effect 0x121c79 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[232, 530]
    (.letOp (n := 560) (.out 0x121c7b (movR32R32Effect 0x121c7b 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[558]
    (.letOp (n := 561) (.exec 0x121c7b (fun s => s.RIP = 0x121c7b) (movR32R32Effect 0x121c7b 3 11 1) (Reg.operands [.gpr 1] [])) #v[558]
    (.letOp (n := 562) (.out 0x121c7e (rolR32Effect 0x121c7e 4 11 26) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[560]
    (.letOp (n := 563) (.exec 0x121c7e (fun s => s.RIP = 0x121c7e) (rolR32Effect 0x121c7e 4 11 26) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[560]
    (.letOp (n := 564) (.out 0x121c82 (addR32R32Effect 0x121c82 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[556, 530]
    (.letOp (n := 565) (.exec 0x121c82 (fun s => s.RIP = 0x121c82) (addR32R32Effect 0x121c82 3 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[556, 530]
    (.letOp (n := 566) (.out 0x121c85 (movR32R32Effect 0x121c85 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[558]
    (.letOp (n := 567) (.exec 0x121c85 (fun s => s.RIP = 0x121c85) (movR32R32Effect 0x121c85 2 2 1) (Reg.operands [.gpr 1] [])) #v[558]
    (.letOp (n := 568) (.out 0x121c87 (rolR32Effect 0x121c87 3 2 21) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[566]
    (.letOp (n := 569) (.exec 0x121c87 (fun s => s.RIP = 0x121c87) (rolR32Effect 0x121c87 3 2 21) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[566]
    (.letOp (n := 570) (.out 0x121c8a (xorR32R32Effect 0x121c8a 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[568, 562]
    (.letOp (n := 571) (.exec 0x121c8a (fun s => s.RIP = 0x121c8a) (xorR32R32Effect 0x121c8a 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[568, 562]
    (.letOp (n := 572) (.out 0x121c8d (movR32R32Effect 0x121c8d 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[558]
    (.letOp (n := 573) (.exec 0x121c8d (fun s => s.RIP = 0x121c8d) (movR32R32Effect 0x121c8d 3 11 1) (Reg.operands [.gpr 1] [])) #v[558]
    (.letOp (n := 574) (.out 0x121c90 (rolR32Effect 0x121c90 4 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[572]
    (.letOp (n := 575) (.exec 0x121c90 (fun s => s.RIP = 0x121c90) (rolR32Effect 0x121c90 4 11 7) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[572]
    (.letOp (n := 576) (.out 0x121c94 (xorR32R32Effect 0x121c94 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[574, 570]
    (.letOp (n := 577) (.exec 0x121c94 (fun s => s.RIP = 0x121c94) (xorR32R32Effect 0x121c94 3 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[574, 570]
    (.letOp (n := 578) (.out 0x121c97 (movR64M64Effect 0x121c97 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 579) (.exec 0x121c97 (LoadPre 0x121c97 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121c97 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121c97 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 580) (.out 0x121c9c (movR32M32LowEffect 0x121c9c 5 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[578]
    (.letOp (n := 581) (.exec 0x121c9c (LoadPre 0x121c9c (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x121c9c + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x121c9c 5 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[578]
    (.letOp (n := 582) (.out 0x121c9f (bswapR32Effect 0x121c9f 2 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[580]
    (.letOp (n := 583) (.exec 0x121c9f (fun s => s.RIP = 0x121c9f) (bswapR32Effect 0x121c9f 2 5) (Reg.operands [.gpr 5] [])) #v[580]
    (.letOp (n := 584) (.exec 0x121ca1 (StorePre 0x121ca1 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x121ca1 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x121ca1 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[582, 4]
    (.letOp (n := 585) (.out 0x121ca5 (movR32R32Effect 0x121ca5 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[558]
    (.letOp (n := 586) (.exec 0x121ca5 (fun s => s.RIP = 0x121ca5) (movR32R32Effect 0x121ca5 2 2 1) (Reg.operands [.gpr 1] [])) #v[558]
    (.letOp (n := 587) (.out 0x121ca7 (andR32R32Effect 0x121ca7 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[585, 481]
    (.letOp (n := 588) (.exec 0x121ca7 (fun s => s.RIP = 0x121ca7) (andR32R32Effect 0x121ca7 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[585, 481]
    (.letOp (n := 589) (.out 0x121ca9 (addR32R32Effect 0x121ca9 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[321, 582]
    (.letOp (n := 590) (.exec 0x121ca9 (fun s => s.RIP = 0x121ca9) (addR32R32Effect 0x121ca9 3 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[321, 582]
    (.letOp (n := 591) (.out 0x121cac (addR32R32Effect 0x121cac 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[589, 587]
    (.letOp (n := 592) (.exec 0x121cac (fun s => s.RIP = 0x121cac) (addR32R32Effect 0x121cac 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[589, 587]
    (.letOp (n := 593) (.out 0x121caf (movR32R32Effect 0x121caf 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[558]
    (.letOp (n := 594) (.exec 0x121caf (fun s => s.RIP = 0x121caf) (movR32R32Effect 0x121caf 2 2 1) (Reg.operands [.gpr 1] [])) #v[558]
    (.letOp (n := 595) (.out 0x121cb1 (notR32Effect 0x121cb1 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[593]
    (.letOp (n := 596) (.exec 0x121cb1 (fun s => s.RIP = 0x121cb1) (notR32Effect 0x121cb1 2 2) (Reg.operands [.gpr 2] [])) #v[593]
    (b_l121930_14)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_13 : List UInt8 :=
  [0x01, 0xD1, 0x41, 0x89, 0xCB, 0x41, 0xC1, 0xC3, 0x1A, 0x41, 0x01, 0xD0, 0x89, 0xCA, 0xC1, 0xC2,
    0x15, 0x44, 0x31, 0xDA, 0x41, 0x89, 0xCB, 0x41, 0xC1, 0xC3, 0x07, 0x41, 0x31, 0xD3, 0x48, 0x8B,
    0x54, 0x24, 0x18, 0x8B, 0x6A, 0x18, 0x0F, 0xCD, 0x89, 0x6C, 0x24, 0x28, 0x89, 0xCA, 0x21, 0xC2,
    0x41, 0x01, 0xEA, 0x41, 0x01, 0xD2, 0x89, 0xCA, 0xF7, 0xD2] ++ bytes_l121930_14

theorem code_l121930_13 : ∀ x ∈ codeRange 0x121c79 bytes_l121930_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21c79 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_14

def b_l121930_12 : Block Op Label signature Reg.count 518 :=
  .letOp (n := 518) (.out 0x121c39 (notR32Effect 0x121c39 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[516]
    (.letOp (n := 519) (.exec 0x121c39 (fun s => s.RIP = 0x121c39) (notR32Effect 0x121c39 3 11) (Reg.operands [.gpr 11] [])) #v[516]
    (.letOp (n := 520) (.out 0x121c3c (andR32R32Effect 0x121c3c 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[518, 321]
    (.letOp (n := 521) (.exec 0x121c3c (fun s => s.RIP = 0x121c3c) (andR32R32Effect 0x121c3c 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[518, 321]
    (.letOp (n := 522) (.out 0x121c3f (addR32R32Effect 0x121c3f 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[514, 520]
    (.letOp (n := 523) (.exec 0x121c3f (fun s => s.RIP = 0x121c3f) (addR32R32Effect 0x121c3f 3 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[514, 520]
    (.letOp (n := 524) (.out 0x121c42 (movR32R32Effect 0x121c42 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[483]
    (.letOp (n := 525) (.exec 0x121c42 (fun s => s.RIP = 0x121c42) (movR32R32Effect 0x121c42 3 11 9) (Reg.operands [.gpr 9] [])) #v[483]
    (.letOp (n := 526) (.out 0x121c45 (rolR32Effect 0x121c45 4 11 30) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[524]
    (.letOp (n := 527) (.exec 0x121c45 (fun s => s.RIP = 0x121c45) (rolR32Effect 0x121c45 4 11 30) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[524]
    (.letOp (n := 528) (.out 0x121c49 (addR32R32Effect 0x121c49 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[499, 522]
    (.letOp (n := 529) (.exec 0x121c49 (fun s => s.RIP = 0x121c49) (addR32R32Effect 0x121c49 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[499, 522]
    (.letOp (n := 530) (.out 0x121c4c (addR32Imm32Effect 0x121c4c 6 2 0x59f111f1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[528]
    (.letOp (n := 531) (.exec 0x121c4c (fun s => s.RIP = 0x121c4c) (addR32Imm32Effect 0x121c4c 6 2 0x59f111f1) (Reg.operands [.gpr 2] [])) #v[528]
    (.letOp (n := 532) (.out 0x121c52 (movR32R32Effect 0x121c52 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[483]
    (.letOp (n := 533) (.exec 0x121c52 (fun s => s.RIP = 0x121c52) (movR32R32Effect 0x121c52 3 8 9) (Reg.operands [.gpr 9] [])) #v[483]
    (.letOp (n := 534) (.out 0x121c55 (rolR32Effect 0x121c55 4 8 19) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[532]
    (.letOp (n := 535) (.exec 0x121c55 (fun s => s.RIP = 0x121c55) (rolR32Effect 0x121c55 4 8 19) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[532]
    (.letOp (n := 536) (.out 0x121c59 (xorR32R32Effect 0x121c59 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[534, 526]
    (.letOp (n := 537) (.exec 0x121c59 (fun s => s.RIP = 0x121c59) (xorR32R32Effect 0x121c59 3 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[534, 526]
    (.letOp (n := 538) (.out 0x121c5c (movR32R32Effect 0x121c5c 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[483]
    (.letOp (n := 539) (.exec 0x121c5c (fun s => s.RIP = 0x121c5c) (movR32R32Effect 0x121c5c 3 11 9) (Reg.operands [.gpr 9] [])) #v[483]
    (.letOp (n := 540) (.out 0x121c5f (rolR32Effect 0x121c5f 4 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[538]
    (.letOp (n := 541) (.exec 0x121c5f (fun s => s.RIP = 0x121c5f) (rolR32Effect 0x121c5f 4 11 10) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[538]
    (.letOp (n := 542) (.out 0x121c63 (xorR32R32Effect 0x121c63 3 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[540, 536]
    (.letOp (n := 543) (.exec 0x121c63 (fun s => s.RIP = 0x121c63) (xorR32R32Effect 0x121c63 3 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[540, 536]
    (.letOp (n := 544) (.out 0x121c66 (movR32R32Effect 0x121c66 2 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 7] []) (.reg (.gpr 5))) #v[410]
    (.letOp (n := 545) (.exec 0x121c66 (fun s => s.RIP = 0x121c66) (movR32R32Effect 0x121c66 2 5 7) (Reg.operands [.gpr 7] [])) #v[410]
    (.letOp (n := 546) (.out 0x121c68 (andR32R32Effect 0x121c68 2 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 6] []) (.reg (.gpr 5))) #v[544, 333]
    (.letOp (n := 547) (.exec 0x121c68 (fun s => s.RIP = 0x121c68) (andR32R32Effect 0x121c68 2 5 6) (Reg.operands [.gpr 5, .gpr 6] [])) #v[544, 333]
    (.letOp (n := 548) (.out 0x121c6a (movR32R32Effect 0x121c6a 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[410]
    (.letOp (n := 549) (.exec 0x121c6a (fun s => s.RIP = 0x121c6a) (movR32R32Effect 0x121c6a 3 8 7) (Reg.operands [.gpr 7] [])) #v[410]
    (.letOp (n := 550) (.out 0x121c6d (xorR32R32Effect 0x121c6d 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[548, 333]
    (.letOp (n := 551) (.exec 0x121c6d (fun s => s.RIP = 0x121c6d) (xorR32R32Effect 0x121c6d 3 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[548, 333]
    (.letOp (n := 552) (.out 0x121c70 (andR32R32Effect 0x121c70 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[550, 483]
    (.letOp (n := 553) (.exec 0x121c70 (fun s => s.RIP = 0x121c70) (andR32R32Effect 0x121c70 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[550, 483]
    (.letOp (n := 554) (.out 0x121c73 (xorR32R32Effect 0x121c73 3 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[552, 546]
    (.letOp (n := 555) (.exec 0x121c73 (fun s => s.RIP = 0x121c73) (xorR32R32Effect 0x121c73 3 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[552, 546]
    (.letOp (n := 556) (.out 0x121c76 (addR32R32Effect 0x121c76 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[554, 542]
    (.letOp (n := 557) (.exec 0x121c76 (fun s => s.RIP = 0x121c76) (addR32R32Effect 0x121c76 3 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[554, 542]
    (b_l121930_13))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_12 : List UInt8 :=
  [0x41, 0xF7, 0xD3, 0x45, 0x21, 0xD3, 0x45, 0x01, 0xD8, 0x45, 0x89, 0xCB, 0x41, 0xC1, 0xC3, 0x1E,
    0x44, 0x01, 0xC2, 0x81, 0xC2, 0xF1, 0x11, 0xF1, 0x59, 0x45, 0x89, 0xC8, 0x41, 0xC1, 0xC0, 0x13,
    0x45, 0x31, 0xD8, 0x45, 0x89, 0xCB, 0x41, 0xC1, 0xC3, 0x0A, 0x45, 0x31, 0xC3, 0x89, 0xFD, 0x21,
    0xF5, 0x41, 0x89, 0xF8, 0x41, 0x31, 0xF0, 0x45, 0x21, 0xC8, 0x41, 0x31, 0xE8, 0x45, 0x01, 0xD8] ++ bytes_l121930_13

theorem code_l121930_12 : ∀ x ∈ codeRange 0x121c39 bytes_l121930_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21c39 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_13

def b_l121930_11 : Block Op Label signature Reg.count 479 :=
  .letOp (n := 479) (.out 0x121bfc (addR32R32Effect 0x121bfc 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[477, 465]
    (.letOp (n := 480) (.exec 0x121bfc (fun s => s.RIP = 0x121bfc) (addR32R32Effect 0x121bfc 3 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[477, 465]
    (.letOp (n := 481) (.out 0x121bff (addR32R32Effect 0x121bff 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[168, 449]
    (.letOp (n := 482) (.exec 0x121bff (fun s => s.RIP = 0x121bff) (addR32R32Effect 0x121bff 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[168, 449]
    (.letOp (n := 483) (.out 0x121c01 (addR32R32Effect 0x121c01 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[479, 449]
    (.letOp (n := 484) (.exec 0x121c01 (fun s => s.RIP = 0x121c01) (addR32R32Effect 0x121c01 3 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[479, 449]
    (.letOp (n := 485) (.out 0x121c04 (movR32R32Effect 0x121c04 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[481]
    (.letOp (n := 486) (.exec 0x121c04 (fun s => s.RIP = 0x121c04) (movR32R32Effect 0x121c04 2 2 0) (Reg.operands [.gpr 0] [])) #v[481]
    (.letOp (n := 487) (.out 0x121c06 (rolR32Effect 0x121c06 3 2 26) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[485]
    (.letOp (n := 488) (.exec 0x121c06 (fun s => s.RIP = 0x121c06) (rolR32Effect 0x121c06 3 2 26) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[485]
    (.letOp (n := 489) (.out 0x121c09 (movR32R32Effect 0x121c09 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[481]
    (.letOp (n := 490) (.exec 0x121c09 (fun s => s.RIP = 0x121c09) (movR32R32Effect 0x121c09 3 11 0) (Reg.operands [.gpr 0] [])) #v[481]
    (.letOp (n := 491) (.out 0x121c0c (rolR32Effect 0x121c0c 4 11 21) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[489]
    (.letOp (n := 492) (.exec 0x121c0c (fun s => s.RIP = 0x121c0c) (rolR32Effect 0x121c0c 4 11 21) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[489]
    (.letOp (n := 493) (.out 0x121c10 (xorR32R32Effect 0x121c10 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[491, 487]
    (.letOp (n := 494) (.exec 0x121c10 (fun s => s.RIP = 0x121c10) (xorR32R32Effect 0x121c10 3 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[491, 487]
    (.letOp (n := 495) (.out 0x121c13 (movR32R32Effect 0x121c13 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[481]
    (.letOp (n := 496) (.exec 0x121c13 (fun s => s.RIP = 0x121c13) (movR32R32Effect 0x121c13 2 2 0) (Reg.operands [.gpr 0] [])) #v[481]
    (.letOp (n := 497) (.out 0x121c15 (rolR32Effect 0x121c15 3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[495]
    (.letOp (n := 498) (.exec 0x121c15 (fun s => s.RIP = 0x121c15) (rolR32Effect 0x121c15 3 2 7) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[495]
    (.letOp (n := 499) (.out 0x121c18 (xorR32R32Effect 0x121c18 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[497, 493]
    (.letOp (n := 500) (.exec 0x121c18 (fun s => s.RIP = 0x121c18) (xorR32R32Effect 0x121c18 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[497, 493]
    (.letOp (n := 501) (.out 0x121c1b (movR64M64Effect 0x121c1b 11 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 502) (.exec 0x121c1b (LoadPre 0x121c1b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121c1b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121c1b 11 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 503) (.out 0x121c20 (movR32M32Effect 0x121c20 5 (.base 11 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 11] []) (.reg (.gpr 5))) #v[501]
    (.letOp (n := 504) (.exec 0x121c20 (LoadPre 0x121c20 (fun s => AddrMode.addr (.base 11 (.d8 0x14)) s (0x121c20 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x121c20 5 (.base 11 (.d8 0x14))) (Reg.operands [.gpr 11] [])) #v[501]
    (.letOp (n := 505) (.out 0x121c24 (bswapR32Effect 0x121c24 2 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[503]
    (.letOp (n := 506) (.exec 0x121c24 (fun s => s.RIP = 0x121c24) (bswapR32Effect 0x121c24 2 5) (Reg.operands [.gpr 5] [])) #v[503]
    (.letOp (n := 507) (.exec 0x121c26 (StorePre 0x121c26 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x121c26 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x121c26 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[505, 4]
    (.letOp (n := 508) (.out 0x121c2a (movR32R32Effect 0x121c2a 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[481]
    (.letOp (n := 509) (.exec 0x121c2a (fun s => s.RIP = 0x121c2a) (movR32R32Effect 0x121c2a 3 11 0) (Reg.operands [.gpr 0] [])) #v[481]
    (.letOp (n := 510) (.out 0x121c2d (andR32R32Effect 0x121c2d 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[508, 404]
    (.letOp (n := 511) (.exec 0x121c2d (fun s => s.RIP = 0x121c2d) (andR32R32Effect 0x121c2d 3 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[508, 404]
    (.letOp (n := 512) (.out 0x121c30 (addR32R32Effect 0x121c30 3 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[236, 505]
    (.letOp (n := 513) (.exec 0x121c30 (fun s => s.RIP = 0x121c30) (addR32R32Effect 0x121c30 3 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[236, 505]
    (.letOp (n := 514) (.out 0x121c33 (addR32R32Effect 0x121c33 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[512, 510]
    (.letOp (n := 515) (.exec 0x121c33 (fun s => s.RIP = 0x121c33) (addR32R32Effect 0x121c33 3 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[512, 510]
    (.letOp (n := 516) (.out 0x121c36 (movR32R32Effect 0x121c36 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[481]
    (.letOp (n := 517) (.exec 0x121c36 (fun s => s.RIP = 0x121c36) (movR32R32Effect 0x121c36 3 11 0) (Reg.operands [.gpr 0] [])) #v[481]
    (b_l121930_12)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_11 : List UInt8 :=
  [0x41, 0x01, 0xE9, 0x01, 0xD0, 0x41, 0x01, 0xD1, 0x89, 0xC2, 0xC1, 0xC2, 0x1A, 0x41, 0x89, 0xC3,
    0x41, 0xC1, 0xC3, 0x15, 0x41, 0x31, 0xD3, 0x89, 0xC2, 0xC1, 0xC2, 0x07, 0x44, 0x31, 0xDA, 0x4C,
    0x8B, 0x5C, 0x24, 0x18, 0x41, 0x8B, 0x6B, 0x14, 0x0F, 0xCD, 0x89, 0x6C, 0x24, 0x40, 0x41, 0x89,
    0xC3, 0x41, 0x21, 0xDB, 0x41, 0x01, 0xE8, 0x45, 0x01, 0xD8, 0x41, 0x89, 0xC3] ++ bytes_l121930_12

theorem code_l121930_11 : ∀ x ∈ codeRange 0x121bfc bytes_l121930_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21bfc 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_12

def b_l121930_10 : Block Op Label signature Reg.count 439 :=
  .letOp (n := 439) (.out 0x121bbc (movR32R32Effect 0x121bbc 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[404]
    (.letOp (n := 440) (.exec 0x121bbc (fun s => s.RIP = 0x121bbc) (movR32R32Effect 0x121bbc 3 9 3) (Reg.operands [.gpr 3] [])) #v[404]
    (.letOp (n := 441) (.out 0x121bbf (notR32Effect 0x121bbf 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[439]
    (.letOp (n := 442) (.exec 0x121bbf (fun s => s.RIP = 0x121bbf) (notR32Effect 0x121bbf 3 9) (Reg.operands [.gpr 9] [])) #v[439]
    (.letOp (n := 443) (.out 0x121bc2 (andR32R32Effect 0x121bc2 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[441, 236]
    (.letOp (n := 444) (.exec 0x121bc2 (fun s => s.RIP = 0x121bc2) (andR32R32Effect 0x121bc2 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[441, 236]
    (.letOp (n := 445) (.out 0x121bc5 (addR32R32Effect 0x121bc5 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[437, 443]
    (.letOp (n := 446) (.exec 0x121bc5 (fun s => s.RIP = 0x121bc5) (addR32R32Effect 0x121bc5 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[437, 443]
    (.letOp (n := 447) (.out 0x121bc8 (addR32R32Effect 0x121bc8 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[445, 422]
    (.letOp (n := 448) (.exec 0x121bc8 (fun s => s.RIP = 0x121bc8) (addR32R32Effect 0x121bc8 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[445, 422]
    (.letOp (n := 449) (.out 0x121bcb (addR32Imm32Effect 0x121bcb 6 2 0x3956c25b) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[447]
    (.letOp (n := 450) (.exec 0x121bcb (fun s => s.RIP = 0x121bcb) (addR32Imm32Effect 0x121bcb 6 2 0x3956c25b) (Reg.operands [.gpr 2] [])) #v[447]
    (.letOp (n := 451) (.out 0x121bd1 (movR32R32Effect 0x121bd1 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[410]
    (.letOp (n := 452) (.exec 0x121bd1 (fun s => s.RIP = 0x121bd1) (movR32R32Effect 0x121bd1 3 9 7) (Reg.operands [.gpr 7] [])) #v[410]
    (.letOp (n := 453) (.out 0x121bd4 (rolR32Effect 0x121bd4 4 9 30) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[451]
    (.letOp (n := 454) (.exec 0x121bd4 (fun s => s.RIP = 0x121bd4) (rolR32Effect 0x121bd4 4 9 30) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[451]
    (.letOp (n := 455) (.out 0x121bd8 (movR32R32Effect 0x121bd8 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[410]
    (.letOp (n := 456) (.exec 0x121bd8 (fun s => s.RIP = 0x121bd8) (movR32R32Effect 0x121bd8 3 11 7) (Reg.operands [.gpr 7] [])) #v[410]
    (.letOp (n := 457) (.out 0x121bdb (rolR32Effect 0x121bdb 4 11 19) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[455]
    (.letOp (n := 458) (.exec 0x121bdb (fun s => s.RIP = 0x121bdb) (rolR32Effect 0x121bdb 4 11 19) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[455]
    (.letOp (n := 459) (.out 0x121bdf (xorR32R32Effect 0x121bdf 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[457, 453]
    (.letOp (n := 460) (.exec 0x121bdf (fun s => s.RIP = 0x121bdf) (xorR32R32Effect 0x121bdf 3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[457, 453]
    (.letOp (n := 461) (.out 0x121be2 (movR32R32Effect 0x121be2 2 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 7] []) (.reg (.gpr 5))) #v[410]
    (.letOp (n := 462) (.exec 0x121be2 (fun s => s.RIP = 0x121be2) (movR32R32Effect 0x121be2 2 5 7) (Reg.operands [.gpr 7] [])) #v[410]
    (.letOp (n := 463) (.out 0x121be4 (rolR32Effect 0x121be4 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[461]
    (.letOp (n := 464) (.exec 0x121be4 (fun s => s.RIP = 0x121be4) (rolR32Effect 0x121be4 3 5 10) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[461]
    (.letOp (n := 465) (.out 0x121be7 (xorR32R32Effect 0x121be7 3 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[463, 459]
    (.letOp (n := 466) (.exec 0x121be7 (fun s => s.RIP = 0x121be7) (xorR32R32Effect 0x121be7 3 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[463, 459]
    (.letOp (n := 467) (.out 0x121bea (movR32R32Effect 0x121bea 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[333]
    (.letOp (n := 468) (.exec 0x121bea (fun s => s.RIP = 0x121bea) (movR32R32Effect 0x121bea 3 11 6) (Reg.operands [.gpr 6] [])) #v[333]
    (.letOp (n := 469) (.out 0x121bed (andR32R32Effect 0x121bed 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[467, 232]
    (.letOp (n := 470) (.exec 0x121bed (fun s => s.RIP = 0x121bed) (andR32R32Effect 0x121bed 3 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[467, 232]
    (.letOp (n := 471) (.out 0x121bf0 (movR32R32Effect 0x121bf0 3 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[333]
    (.letOp (n := 472) (.exec 0x121bf0 (fun s => s.RIP = 0x121bf0) (movR32R32Effect 0x121bf0 3 9 6) (Reg.operands [.gpr 6] [])) #v[333]
    (.letOp (n := 473) (.out 0x121bf3 (xorR32R32Effect 0x121bf3 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[471, 232]
    (.letOp (n := 474) (.exec 0x121bf3 (fun s => s.RIP = 0x121bf3) (xorR32R32Effect 0x121bf3 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[471, 232]
    (.letOp (n := 475) (.out 0x121bf6 (andR32R32Effect 0x121bf6 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[473, 410]
    (.letOp (n := 476) (.exec 0x121bf6 (fun s => s.RIP = 0x121bf6) (andR32R32Effect 0x121bf6 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[473, 410]
    (.letOp (n := 477) (.out 0x121bf9 (xorR32R32Effect 0x121bf9 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[475, 469]
    (.letOp (n := 478) (.exec 0x121bf9 (fun s => s.RIP = 0x121bf9) (xorR32R32Effect 0x121bf9 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[475, 469]
    (b_l121930_11))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_10 : List UInt8 :=
  [0x41, 0x89, 0xD9, 0x41, 0xF7, 0xD1, 0x45, 0x21, 0xC1, 0x44, 0x01, 0xCA, 0x44, 0x01, 0xDA, 0x81,
    0xC2, 0x5B, 0xC2, 0x56, 0x39, 0x41, 0x89, 0xF9, 0x41, 0xC1, 0xC1, 0x1E, 0x41, 0x89, 0xFB, 0x41,
    0xC1, 0xC3, 0x13, 0x45, 0x31, 0xCB, 0x89, 0xFD, 0xC1, 0xC5, 0x0A, 0x44, 0x31, 0xDD, 0x41, 0x89,
    0xF3, 0x41, 0x21, 0xCB, 0x41, 0x89, 0xF1, 0x41, 0x31, 0xC9, 0x41, 0x21, 0xF9, 0x45, 0x31, 0xD9] ++ bytes_l121930_11

theorem code_l121930_10 : ∀ x ∈ codeRange 0x121bbc bytes_l121930_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21bbc 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_11

def b_l121930_9 : Block Op Label signature Reg.count 400 :=
  .letOp (n := 400) (.out 0x121b78 (addR32R32Effect 0x121b78 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[398, 386]
    (.letOp (n := 401) (.exec 0x121b78 (fun s => s.RIP = 0x121b78) (addR32R32Effect 0x121b78 3 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[398, 386]
    (.letOp (n := 402) (.out 0x121b7b (addR32R32Effect 0x121b7b 3 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[370, 312]
    (.letOp (n := 403) (.exec 0x121b7b (fun s => s.RIP = 0x121b7b) (addR32R32Effect 0x121b7b 3 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[370, 312]
    (.letOp (n := 404) (.out 0x121b7e (addR32Imm32Effect 0x121b7e 6 3 0xe9b5dba5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[402]
    (.letOp (n := 405) (.exec 0x121b7e (fun s => s.RIP = 0x121b7e) (addR32Imm32Effect 0x121b7e 6 3 0xe9b5dba5) (Reg.operands [.gpr 3] [])) #v[402]
    (.letOp (n := 406) (.out 0x121b84 (movR32R32Effect 0x121b84 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[404]
    (.letOp (n := 407) (.exec 0x121b84 (fun s => s.RIP = 0x121b84) (movR32R32Effect 0x121b84 3 11 3) (Reg.operands [.gpr 3] [])) #v[404]
    (.letOp (n := 408) (.out 0x121b87 (rolR32Effect 0x121b87 4 11 26) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[406]
    (.letOp (n := 409) (.exec 0x121b87 (fun s => s.RIP = 0x121b87) (rolR32Effect 0x121b87 4 11 26) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[406]
    (.letOp (n := 410) (.out 0x121b8b (addR32R32Effect 0x121b8b 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[400, 374]
    (.letOp (n := 411) (.exec 0x121b8b (fun s => s.RIP = 0x121b8b) (addR32R32Effect 0x121b8b 3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[400, 374]
    (.letOp (n := 412) (.out 0x121b8e (movR32R32Effect 0x121b8e 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[404]
    (.letOp (n := 413) (.exec 0x121b8e (fun s => s.RIP = 0x121b8e) (movR32R32Effect 0x121b8e 3 9 3) (Reg.operands [.gpr 3] [])) #v[404]
    (.letOp (n := 414) (.out 0x121b91 (rolR32Effect 0x121b91 4 9 21) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[412]
    (.letOp (n := 415) (.exec 0x121b91 (fun s => s.RIP = 0x121b91) (rolR32Effect 0x121b91 4 9 21) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[412]
    (.letOp (n := 416) (.out 0x121b95 (xorR32R32Effect 0x121b95 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[414, 408]
    (.letOp (n := 417) (.exec 0x121b95 (fun s => s.RIP = 0x121b95) (xorR32R32Effect 0x121b95 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[414, 408]
    (.letOp (n := 418) (.out 0x121b98 (movR32R32Effect 0x121b98 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[404]
    (.letOp (n := 419) (.exec 0x121b98 (fun s => s.RIP = 0x121b98) (movR32R32Effect 0x121b98 3 11 3) (Reg.operands [.gpr 3] [])) #v[404]
    (.letOp (n := 420) (.out 0x121b9b (rolR32Effect 0x121b9b 4 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[418]
    (.letOp (n := 421) (.exec 0x121b9b (fun s => s.RIP = 0x121b9b) (rolR32Effect 0x121b9b 4 11 7) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[418]
    (.letOp (n := 422) (.out 0x121b9f (xorR32R32Effect 0x121b9f 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[420, 416]
    (.letOp (n := 423) (.exec 0x121b9f (fun s => s.RIP = 0x121b9f) (xorR32R32Effect 0x121b9f 3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[420, 416]
    (.letOp (n := 424) (.out 0x121ba2 (movR64M64Effect 0x121ba2 9 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 425) (.exec 0x121ba2 (LoadPre 0x121ba2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121ba2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121ba2 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 426) (.out 0x121ba7 (movR32M32Effect 0x121ba7 5 (.base 9 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[424]
    (.letOp (n := 427) (.exec 0x121ba7 (LoadPre 0x121ba7 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x121ba7 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x121ba7 5 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 9] [])) #v[424]
    (.letOp (n := 428) (.out 0x121bab (bswapR32Effect 0x121bab 2 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[426]
    (.letOp (n := 429) (.exec 0x121bab (fun s => s.RIP = 0x121bab) (bswapR32Effect 0x121bab 2 5) (Reg.operands [.gpr 5] [])) #v[426]
    (.letOp (n := 430) (.exec 0x121bad (StorePre 0x121bad 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x121bad + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x121bad 5 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[428, 4]
    (.letOp (n := 431) (.out 0x121bb1 (movR32R32Effect 0x121bb1 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[404]
    (.letOp (n := 432) (.exec 0x121bb1 (fun s => s.RIP = 0x121bb1) (movR32R32Effect 0x121bb1 3 9 3) (Reg.operands [.gpr 3] [])) #v[404]
    (.letOp (n := 433) (.out 0x121bb4 (andR32R32Effect 0x121bb4 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[431, 321]
    (.letOp (n := 434) (.exec 0x121bb4 (fun s => s.RIP = 0x121bb4) (andR32R32Effect 0x121bb4 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[431, 321]
    (.letOp (n := 435) (.out 0x121bb7 (addR32R32Effect 0x121bb7 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[156, 428]
    (.letOp (n := 436) (.exec 0x121bb7 (fun s => s.RIP = 0x121bb7) (addR32R32Effect 0x121bb7 2 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[156, 428]
    (.letOp (n := 437) (.out 0x121bb9 (addR32R32Effect 0x121bb9 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[435, 433]
    (.letOp (n := 438) (.exec 0x121bb9 (fun s => s.RIP = 0x121bb9) (addR32R32Effect 0x121bb9 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[435, 433]
    (b_l121930_10)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_9 : List UInt8 :=
  [0x44, 0x01, 0xDF, 0x44, 0x01, 0xF3, 0x81, 0xC3, 0xA5, 0xDB, 0xB5, 0xE9, 0x41, 0x89, 0xDB, 0x41,
    0xC1, 0xC3, 0x1A, 0x44, 0x01, 0xCF, 0x41, 0x89, 0xD9, 0x41, 0xC1, 0xC1, 0x15, 0x45, 0x31, 0xD9,
    0x41, 0x89, 0xDB, 0x41, 0xC1, 0xC3, 0x07, 0x45, 0x31, 0xCB, 0x4C, 0x8B, 0x4C, 0x24, 0x18, 0x41,
    0x8B, 0x69, 0x10, 0x0F, 0xCD, 0x89, 0x6C, 0x24, 0x24, 0x41, 0x89, 0xD9, 0x45, 0x21, 0xD1, 0x01,
    0xEA, 0x44, 0x01, 0xCA] ++ bytes_l121930_10

theorem code_l121930_9 : ∀ x ∈ codeRange 0x121b78 bytes_l121930_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21b78 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_10

def b_l121930_8 : Block Op Label signature Reg.count 360 :=
  .letOp (n := 360) (.out 0x121b3c (notR32Effect 0x121b3c 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[358]
    (.letOp (n := 361) (.exec 0x121b3c (fun s => s.RIP = 0x121b3c) (notR32Effect 0x121b3c 3 11) (Reg.operands [.gpr 11] [])) #v[358]
    (.letOp (n := 362) (.out 0x121b3f (andR32R32Effect 0x121b3f 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[360, 156]
    (.letOp (n := 363) (.exec 0x121b3f (fun s => s.RIP = 0x121b3f) (andR32R32Effect 0x121b3f 3 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[360, 156]
    (.letOp (n := 364) (.out 0x121b42 (addR32R32Effect 0x121b42 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[356, 362]
    (.letOp (n := 365) (.exec 0x121b42 (fun s => s.RIP = 0x121b42) (addR32R32Effect 0x121b42 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[356, 362]
    (.letOp (n := 366) (.out 0x121b45 (movR32R32Effect 0x121b45 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[333]
    (.letOp (n := 367) (.exec 0x121b45 (fun s => s.RIP = 0x121b45) (movR32R32Effect 0x121b45 3 11 6) (Reg.operands [.gpr 6] [])) #v[333]
    (.letOp (n := 368) (.out 0x121b48 (rolR32Effect 0x121b48 4 11 30) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[366]
    (.letOp (n := 369) (.exec 0x121b48 (fun s => s.RIP = 0x121b48) (rolR32Effect 0x121b48 4 11 30) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[366]
    (.letOp (n := 370) (.out 0x121b4c (leaR32Effect 0x121b4c 4 3 (.sib 9 (some 7) 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9, .gpr 7] []) (.reg (.gpr 3))) #v[364, 341]
    (.letOp (n := 371) (.exec 0x121b4c (fun s => s.RIP = 0x121b4c) (leaR32Effect 0x121b4c 4 3 (.sib 9 (some 7) 0 .none)) (Reg.operands [.gpr 9, .gpr 7] [])) #v[364, 341]
    (.letOp (n := 372) (.out 0x121b50 (addR32R32Effect 0x121b50 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[364, 341]
    (.letOp (n := 373) (.exec 0x121b50 (fun s => s.RIP = 0x121b50) (addR32R32Effect 0x121b50 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[364, 341]
    (.letOp (n := 374) (.out 0x121b53 (addR32Imm32Effect 0x121b53 7 9 0xe9b5dba5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[372]
    (.letOp (n := 375) (.exec 0x121b53 (fun s => s.RIP = 0x121b53) (addR32Imm32Effect 0x121b53 7 9 0xe9b5dba5) (Reg.operands [.gpr 9] [])) #v[372]
    (.letOp (n := 376) (.out 0x121b5a (movR32R32Effect 0x121b5a 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[333]
    (.letOp (n := 377) (.exec 0x121b5a (fun s => s.RIP = 0x121b5a) (movR32R32Effect 0x121b5a 2 7 6) (Reg.operands [.gpr 6] [])) #v[333]
    (.letOp (n := 378) (.out 0x121b5c (rolR32Effect 0x121b5c 3 7 19) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[376]
    (.letOp (n := 379) (.exec 0x121b5c (fun s => s.RIP = 0x121b5c) (rolR32Effect 0x121b5c 3 7 19) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[376]
    (.letOp (n := 380) (.out 0x121b5f (xorR32R32Effect 0x121b5f 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[378, 368]
    (.letOp (n := 381) (.exec 0x121b5f (fun s => s.RIP = 0x121b5f) (xorR32R32Effect 0x121b5f 3 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[378, 368]
    (.letOp (n := 382) (.out 0x121b62 (movR32R32Effect 0x121b62 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[333]
    (.letOp (n := 383) (.exec 0x121b62 (fun s => s.RIP = 0x121b62) (movR32R32Effect 0x121b62 3 11 6) (Reg.operands [.gpr 6] [])) #v[333]
    (.letOp (n := 384) (.out 0x121b65 (rolR32Effect 0x121b65 4 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[382]
    (.letOp (n := 385) (.exec 0x121b65 (fun s => s.RIP = 0x121b65) (rolR32Effect 0x121b65 4 11 10) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[382]
    (.letOp (n := 386) (.out 0x121b69 (xorR32R32Effect 0x121b69 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[384, 380]
    (.letOp (n := 387) (.exec 0x121b69 (fun s => s.RIP = 0x121b69) (xorR32R32Effect 0x121b69 3 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[384, 380]
    (.letOp (n := 388) (.out 0x121b6c (movR32R32Effect 0x121b6c 2 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[232]
    (.letOp (n := 389) (.exec 0x121b6c (fun s => s.RIP = 0x121b6c) (movR32R32Effect 0x121b6c 2 5 1) (Reg.operands [.gpr 1] [])) #v[232]
    (.letOp (n := 390) (.out 0x121b6e (andR32R32Effect 0x121b6e 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[388, 168]
    (.letOp (n := 391) (.exec 0x121b6e (fun s => s.RIP = 0x121b6e) (andR32R32Effect 0x121b6e 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[388, 168]
    (.letOp (n := 392) (.out 0x121b70 (movR32R32Effect 0x121b70 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[232]
    (.letOp (n := 393) (.exec 0x121b70 (fun s => s.RIP = 0x121b70) (movR32R32Effect 0x121b70 2 7 1) (Reg.operands [.gpr 1] [])) #v[232]
    (.letOp (n := 394) (.out 0x121b72 (xorR32R32Effect 0x121b72 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[392, 168]
    (.letOp (n := 395) (.exec 0x121b72 (fun s => s.RIP = 0x121b72) (xorR32R32Effect 0x121b72 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[392, 168]
    (.letOp (n := 396) (.out 0x121b74 (andR32R32Effect 0x121b74 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[394, 333]
    (.letOp (n := 397) (.exec 0x121b74 (fun s => s.RIP = 0x121b74) (andR32R32Effect 0x121b74 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[394, 333]
    (.letOp (n := 398) (.out 0x121b76 (xorR32R32Effect 0x121b76 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[396, 390]
    (.letOp (n := 399) (.exec 0x121b76 (fun s => s.RIP = 0x121b76) (xorR32R32Effect 0x121b76 2 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[396, 390]
    (b_l121930_9))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_8 : List UInt8 :=
  [0x41, 0xF7, 0xD3, 0x41, 0x21, 0xD3, 0x45, 0x01, 0xD9, 0x41, 0x89, 0xF3, 0x41, 0xC1, 0xC3, 0x1E,
    0x41, 0x8D, 0x1C, 0x39, 0x41, 0x01, 0xF9, 0x41, 0x81, 0xC1, 0xA5, 0xDB, 0xB5, 0xE9, 0x89, 0xF7,
    0xC1, 0xC7, 0x13, 0x44, 0x31, 0xDF, 0x41, 0x89, 0xF3, 0x41, 0xC1, 0xC3, 0x0A, 0x41, 0x31, 0xFB,
    0x89, 0xCD, 0x21, 0xC5, 0x89, 0xCF, 0x31, 0xC7, 0x21, 0xF7, 0x31, 0xEF] ++ bytes_l121930_9

theorem code_l121930_8 : ∀ x ∈ codeRange 0x121b3c bytes_l121930_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21b3c 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_9

def b_l121930_7 : Block Op Label signature Reg.count 321 :=
  .letOp (n := 321) (.out 0x121af7 (addR32Imm32Effect 0x121af7 7 10 0xb5c0fbcf) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[319]
    (.letOp (n := 322) (.exec 0x121af7 (fun s => s.RIP = 0x121af7) (addR32Imm32Effect 0x121af7 7 10 0xb5c0fbcf) (Reg.operands [.gpr 10] [])) #v[319]
    (.letOp (n := 323) (.out 0x121afe (movR32R32Effect 0x121afe 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[321]
    (.letOp (n := 324) (.exec 0x121afe (fun s => s.RIP = 0x121afe) (movR32R32Effect 0x121afe 3 9 10) (Reg.operands [.gpr 10] [])) #v[321]
    (.letOp (n := 325) (.out 0x121b01 (rolR32Effect 0x121b01 4 9 26) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[323]
    (.letOp (n := 326) (.exec 0x121b01 (fun s => s.RIP = 0x121b01) (rolR32Effect 0x121b01 4 9 26) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[323]
    (.letOp (n := 327) (.out 0x121b05 (addR32R32Effect 0x121b05 2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[317, 300]
    (.letOp (n := 328) (.exec 0x121b05 (fun s => s.RIP = 0x121b05) (addR32R32Effect 0x121b05 2 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[317, 300]
    (.letOp (n := 329) (.out 0x121b07 (movR32R32Effect 0x121b07 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[321]
    (.letOp (n := 330) (.exec 0x121b07 (fun s => s.RIP = 0x121b07) (movR32R32Effect 0x121b07 3 11 10) (Reg.operands [.gpr 10] [])) #v[321]
    (.letOp (n := 331) (.out 0x121b0a (rolR32Effect 0x121b0a 4 11 21) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[329]
    (.letOp (n := 332) (.exec 0x121b0a (fun s => s.RIP = 0x121b0a) (rolR32Effect 0x121b0a 4 11 21) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[329]
    (.letOp (n := 333) (.out 0x121b0e (addR32R32Effect 0x121b0e 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[327, 290]
    (.letOp (n := 334) (.exec 0x121b0e (fun s => s.RIP = 0x121b0e) (addR32R32Effect 0x121b0e 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[327, 290]
    (.letOp (n := 335) (.out 0x121b10 (movR32R32Effect 0x121b10 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 10] []) (.reg (.gpr 7))) #v[321]
    (.letOp (n := 336) (.exec 0x121b10 (fun s => s.RIP = 0x121b10) (movR32R32Effect 0x121b10 3 7 10) (Reg.operands [.gpr 10] [])) #v[321]
    (.letOp (n := 337) (.out 0x121b13 (rolR32Effect 0x121b13 3 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[335]
    (.letOp (n := 338) (.exec 0x121b13 (fun s => s.RIP = 0x121b13) (rolR32Effect 0x121b13 3 7 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[335]
    (.letOp (n := 339) (.out 0x121b16 (xorR32R32Effect 0x121b16 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[331, 325]
    (.letOp (n := 340) (.exec 0x121b16 (fun s => s.RIP = 0x121b16) (xorR32R32Effect 0x121b16 3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[331, 325]
    (.letOp (n := 341) (.out 0x121b19 (xorR32R32Effect 0x121b19 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[337, 339]
    (.letOp (n := 342) (.exec 0x121b19 (fun s => s.RIP = 0x121b19) (xorR32R32Effect 0x121b19 3 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[337, 339]
    (.letOp (n := 343) (.out 0x121b1c (movR64M64Effect 0x121b1c 9 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 344) (.exec 0x121b1c (LoadPre 0x121b1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121b1c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121b1c 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 345) (.out 0x121b21 (movR32M32Effect 0x121b21 11 (.base 9 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[343]
    (.letOp (n := 346) (.exec 0x121b21 (LoadPre 0x121b21 (fun s => AddrMode.addr (.base 9 (.d8 0xc)) s (0x121b21 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x121b21 11 (.base 9 (.d8 0xc))) (Reg.operands [.gpr 9] [])) #v[343]
    (.letOp (n := 347) (.out 0x121b25 (bswapR32Effect 0x121b25 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[345]
    (.letOp (n := 348) (.exec 0x121b25 (fun s => s.RIP = 0x121b25) (bswapR32Effect 0x121b25 3 11) (Reg.operands [.gpr 11] [])) #v[345]
    (.letOp (n := 349) (.exec 0x121b28 (StorePre 0x121b28 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x121b28 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121b28 11 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[347, 4]
    (.letOp (n := 350) (.out 0x121b2d (movR32R32Effect 0x121b2d 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[321]
    (.letOp (n := 351) (.exec 0x121b2d (fun s => s.RIP = 0x121b2d) (movR32R32Effect 0x121b2d 3 9 10) (Reg.operands [.gpr 10] [])) #v[321]
    (.letOp (n := 352) (.out 0x121b30 (andR32R32Effect 0x121b30 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[350, 236]
    (.letOp (n := 353) (.exec 0x121b30 (fun s => s.RIP = 0x121b30) (andR32R32Effect 0x121b30 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[350, 236]
    (.letOp (n := 354) (.out 0x121b33 (addR32R32Effect 0x121b33 3 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 12] []) (.reg (.gpr 11))) #v[347, 131]
    (.letOp (n := 355) (.exec 0x121b33 (fun s => s.RIP = 0x121b33) (addR32R32Effect 0x121b33 3 11 12) (Reg.operands [.gpr 11, .gpr 12] [])) #v[347, 131]
    (.letOp (n := 356) (.out 0x121b36 (addR32R32Effect 0x121b36 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[352, 354]
    (.letOp (n := 357) (.exec 0x121b36 (fun s => s.RIP = 0x121b36) (addR32R32Effect 0x121b36 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[352, 354]
    (.letOp (n := 358) (.out 0x121b39 (movR32R32Effect 0x121b39 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[321]
    (.letOp (n := 359) (.exec 0x121b39 (fun s => s.RIP = 0x121b39) (movR32R32Effect 0x121b39 3 11 10) (Reg.operands [.gpr 10] [])) #v[321]
    (b_l121930_8)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_7 : List UInt8 :=
  [0x41, 0x81, 0xC2, 0xCF, 0xFB, 0xC0, 0xB5, 0x45, 0x89, 0xD1, 0x41, 0xC1, 0xC1, 0x1A, 0x01, 0xDE,
    0x45, 0x89, 0xD3, 0x41, 0xC1, 0xC3, 0x15, 0x01, 0xFE, 0x44, 0x89, 0xD7, 0xC1, 0xC7, 0x07, 0x45,
    0x31, 0xCB, 0x44, 0x31, 0xDF, 0x4C, 0x8B, 0x4C, 0x24, 0x18, 0x45, 0x8B, 0x59, 0x0C, 0x41, 0x0F,
    0xCB, 0x4C, 0x89, 0x5C, 0x24, 0x48, 0x45, 0x89, 0xD1, 0x45, 0x21, 0xC1, 0x45, 0x01, 0xE3, 0x45,
    0x01, 0xD9, 0x45, 0x89, 0xD3] ++ bytes_l121930_8

theorem code_l121930_7 : ∀ x ∈ codeRange 0x121af7 bytes_l121930_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21af7 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_8

def b_l121930_6 : Block Op Label signature Reg.count 282 :=
  .letOp (n := 282) (.out 0x121ab4 (movR32R32Effect 0x121ab4 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[232]
    (.letOp (n := 283) (.exec 0x121ab4 (fun s => s.RIP = 0x121ab4) (movR32R32Effect 0x121ab4 3 10 1) (Reg.operands [.gpr 1] [])) #v[232]
    (.letOp (n := 284) (.out 0x121ab7 (rolR32Effect 0x121ab7 4 10 19) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[282]
    (.letOp (n := 285) (.exec 0x121ab7 (fun s => s.RIP = 0x121ab7) (rolR32Effect 0x121ab7 4 10 19) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[282]
    (.letOp (n := 286) (.out 0x121abb (leaR32Effect 0x121abb 4 11 (.sib 7 (some 6) 0 .none)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7, .gpr 6] []) (.reg (.gpr 11))) #v[276, 252]
    (.letOp (n := 287) (.exec 0x121abb (fun s => s.RIP = 0x121abb) (leaR32Effect 0x121abb 4 11 (.sib 7 (some 6) 0 .none)) (Reg.operands [.gpr 7, .gpr 6] [])) #v[276, 252]
    (.letOp (n := 288) (.out 0x121abf (addR32R32Effect 0x121abf 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[276, 252]
    (.letOp (n := 289) (.exec 0x121abf (fun s => s.RIP = 0x121abf) (addR32R32Effect 0x121abf 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[276, 252]
    (.letOp (n := 290) (.out 0x121ac1 (addR32Imm32Effect 0x121ac1 6 7 0xb5c0fbcf) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[288]
    (.letOp (n := 291) (.exec 0x121ac1 (fun s => s.RIP = 0x121ac1) (addR32Imm32Effect 0x121ac1 6 7 0xb5c0fbcf) (Reg.operands [.gpr 7] [])) #v[288]
    (.letOp (n := 292) (.out 0x121ac7 (movR64R64Effect 0x121ac7 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 293) (.exec 0x121ac7 (fun s => s.RIP = 0x121ac7) (movR64R64Effect 0x121ac7 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 294) (.out 0x121aca (movR32R32Effect 0x121aca 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[232]
    (.letOp (n := 295) (.exec 0x121aca (fun s => s.RIP = 0x121aca) (movR32R32Effect 0x121aca 2 3 1) (Reg.operands [.gpr 1] [])) #v[232]
    (.letOp (n := 296) (.out 0x121acc (rolR32Effect 0x121acc 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[294]
    (.letOp (n := 297) (.exec 0x121acc (fun s => s.RIP = 0x121acc) (rolR32Effect 0x121acc 3 3 10) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[294]
    (.letOp (n := 298) (.out 0x121acf (xorR32R32Effect 0x121acf 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[284, 280]
    (.letOp (n := 299) (.exec 0x121acf (fun s => s.RIP = 0x121acf) (xorR32R32Effect 0x121acf 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[284, 280]
    (.letOp (n := 300) (.out 0x121ad2 (xorR32R32Effect 0x121ad2 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[296, 298]
    (.letOp (n := 301) (.exec 0x121ad2 (fun s => s.RIP = 0x121ad2) (xorR32R32Effect 0x121ad2 3 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[296, 298]
    (.letOp (n := 302) (.out 0x121ad5 (movR32R32Effect 0x121ad5 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[168]
    (.letOp (n := 303) (.exec 0x121ad5 (fun s => s.RIP = 0x121ad5) (movR32R32Effect 0x121ad5 3 9 0) (Reg.operands [.gpr 0] [])) #v[168]
    (.letOp (n := 304) (.out 0x121ad8 (movR64R64Effect 0x121ad8 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[292]
    (.letOp (n := 305) (.exec 0x121ad8 (fun s => s.RIP = 0x121ad8) (movR64R64Effect 0x121ad8 10 6) (Reg.operands [.gpr 6] [])) #v[292]
    (.letOp (n := 306) (.out 0x121adb (andR32R32Effect 0x121adb 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[302, 304]
    (.letOp (n := 307) (.exec 0x121adb (fun s => s.RIP = 0x121adb) (andR32R32Effect 0x121adb 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[302, 304]
    (.letOp (n := 308) (.out 0x121ade (movR32R32Effect 0x121ade 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[168]
    (.letOp (n := 309) (.exec 0x121ade (fun s => s.RIP = 0x121ade) (movR32R32Effect 0x121ade 2 6 0) (Reg.operands [.gpr 0] [])) #v[168]
    (.letOp (n := 310) (.out 0x121ae0 (xorR32R32Effect 0x121ae0 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[308, 304]
    (.letOp (n := 311) (.exec 0x121ae0 (fun s => s.RIP = 0x121ae0) (xorR32R32Effect 0x121ae0 3 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[308, 304]
    (.letOp (n := 312) (.out 0x121ae3 (movR64R64Effect 0x121ae3 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 10] []) (.reg (.gpr 14))) #v[304]
    (.letOp (n := 313) (.exec 0x121ae3 (fun s => s.RIP = 0x121ae3) (movR64R64Effect 0x121ae3 14 10) (Reg.operands [.gpr 10] [])) #v[304]
    (.letOp (n := 314) (.exec 0x121ae6 (StorePre 0x121ae6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x121ae6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x121ae6 10 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[304, 4]
    (.letOp (n := 315) (.out 0x121aee (andR32R32Effect 0x121aee 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[310, 232]
    (.letOp (n := 316) (.exec 0x121aee (fun s => s.RIP = 0x121aee) (andR32R32Effect 0x121aee 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[310, 232]
    (.letOp (n := 317) (.out 0x121af0 (xorR32R32Effect 0x121af0 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[315, 306]
    (.letOp (n := 318) (.exec 0x121af0 (fun s => s.RIP = 0x121af0) (xorR32R32Effect 0x121af0 3 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[315, 306]
    (.letOp (n := 319) (.out 0x121af3 (leaR32Effect 0x121af3 4 10 (.sib 15 (some 11) 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 15, .gpr 11] []) (.reg (.gpr 10))) #v[54, 286]
    (.letOp (n := 320) (.exec 0x121af3 (fun s => s.RIP = 0x121af3) (leaR32Effect 0x121af3 4 10 (.sib 15 (some 11) 0 .none)) (Reg.operands [.gpr 15, .gpr 11] [])) #v[54, 286]
    (b_l121930_7)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_6 : List UInt8 :=
  [0x41, 0x89, 0xCA, 0x41, 0xC1, 0xC2, 0x13, 0x44, 0x8D, 0x1C, 0x37, 0x01, 0xF7, 0x81, 0xC7, 0xCF,
    0xFB, 0xC0, 0xB5, 0x48, 0x89, 0xDE, 0x89, 0xCB, 0xC1, 0xC3, 0x0A, 0x45, 0x31, 0xCA, 0x44, 0x31,
    0xD3, 0x41, 0x89, 0xC1, 0x49, 0x89, 0xF2, 0x45, 0x21, 0xD1, 0x89, 0xC6, 0x44, 0x31, 0xD6, 0x4D,
    0x89, 0xD6, 0x4C, 0x89, 0x94, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x21, 0xCE, 0x44, 0x31, 0xCE, 0x47,
    0x8D, 0x14, 0x1F] ++ bytes_l121930_7

theorem code_l121930_6 : ∀ x ∈ codeRange 0x121ab4 bytes_l121930_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21ab4 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_7

def b_l121930_5 : Block Op Label signature Reg.count 244 :=
  .letOp (n := 244) (.out 0x121a70 (rolR32Effect 0x121a70 3 7 21) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[242]
    (.letOp (n := 245) (.exec 0x121a70 (fun s => s.RIP = 0x121a70) (rolR32Effect 0x121a70 3 7 21) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[242]
    (.letOp (n := 246) (.out 0x121a73 (xorR32R32Effect 0x121a73 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[244, 240]
    (.letOp (n := 247) (.exec 0x121a73 (fun s => s.RIP = 0x121a73) (xorR32R32Effect 0x121a73 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[244, 240]
    (.letOp (n := 248) (.out 0x121a75 (movR32R32Effect 0x121a75 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[236]
    (.letOp (n := 249) (.exec 0x121a75 (fun s => s.RIP = 0x121a75) (movR32R32Effect 0x121a75 3 6 8) (Reg.operands [.gpr 8] [])) #v[236]
    (.letOp (n := 250) (.out 0x121a78 (rolR32Effect 0x121a78 3 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[248]
    (.letOp (n := 251) (.exec 0x121a78 (fun s => s.RIP = 0x121a78) (rolR32Effect 0x121a78 3 6 7) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[248]
    (.letOp (n := 252) (.out 0x121a7b (xorR32R32Effect 0x121a7b 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[250, 246]
    (.letOp (n := 253) (.exec 0x121a7b (fun s => s.RIP = 0x121a7b) (xorR32R32Effect 0x121a7b 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[250, 246]
    (.letOp (n := 254) (.out 0x121a7d (movR64M64Effect 0x121a7d 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 255) (.exec 0x121a7d (LoadPre 0x121a7d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121a7d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121a7d 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 256) (.out 0x121a82 (movR32M32Effect 0x121a82 9 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[254]
    (.letOp (n := 257) (.exec 0x121a82 (LoadPre 0x121a82 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x121a82 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x121a82 9 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[254]
    (.letOp (n := 258) (.out 0x121a86 (bswapR32Effect 0x121a86 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[256]
    (.letOp (n := 259) (.exec 0x121a86 (fun s => s.RIP = 0x121a86) (bswapR32Effect 0x121a86 3 9) (Reg.operands [.gpr 9] [])) #v[256]
    (.letOp (n := 260) (.exec 0x121a89 (StorePre 0x121a89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x121a89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121a89 9 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[258, 4]
    (.letOp (n := 261) (.out 0x121a8e (movR32R32Effect 0x121a8e 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[236]
    (.letOp (n := 262) (.exec 0x121a8e (fun s => s.RIP = 0x121a8e) (movR32R32Effect 0x121a8e 3 7 8) (Reg.operands [.gpr 8] [])) #v[236]
    (.letOp (n := 263) (.out 0x121a91 (andR32R32Effect 0x121a91 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[261, 156]
    (.letOp (n := 264) (.exec 0x121a91 (fun s => s.RIP = 0x121a91) (andR32R32Effect 0x121a91 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[261, 156]
    (.letOp (n := 265) (.out 0x121a93 (addR32R32Effect 0x121a93 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[258, 10]
    (.letOp (n := 266) (.exec 0x121a93 (fun s => s.RIP = 0x121a93) (addR32R32Effect 0x121a93 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[258, 10]
    (.letOp (n := 267) (.out 0x121a96 (addR32R32Effect 0x121a96 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[263, 265]
    (.letOp (n := 268) (.exec 0x121a96 (fun s => s.RIP = 0x121a96) (addR32R32Effect 0x121a96 3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[263, 265]
    (.letOp (n := 269) (.out 0x121a99 (movR32R32Effect 0x121a99 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[236]
    (.letOp (n := 270) (.exec 0x121a99 (fun s => s.RIP = 0x121a99) (movR32R32Effect 0x121a99 3 9 8) (Reg.operands [.gpr 8] [])) #v[236]
    (.letOp (n := 271) (.out 0x121a9c (notR32Effect 0x121a9c 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[269]
    (.letOp (n := 272) (.exec 0x121a9c (fun s => s.RIP = 0x121a9c) (notR32Effect 0x121a9c 3 9) (Reg.operands [.gpr 9] [])) #v[269]
    (.letOp (n := 273) (.exec 0x121a9f (StorePre 0x121a9f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x121a9f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x121a9f 12 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[131, 4]
    (.letOp (n := 274) (.out 0x121aa7 (andR32R32Effect 0x121aa7 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[271, 131]
    (.letOp (n := 275) (.exec 0x121aa7 (fun s => s.RIP = 0x121aa7) (andR32R32Effect 0x121aa7 3 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[271, 131]
    (.letOp (n := 276) (.out 0x121aaa (addR32R32Effect 0x121aaa 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[267, 274]
    (.letOp (n := 277) (.exec 0x121aaa (fun s => s.RIP = 0x121aaa) (addR32R32Effect 0x121aaa 3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[267, 274]
    (.letOp (n := 278) (.out 0x121aad (movR32R32Effect 0x121aad 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[232]
    (.letOp (n := 279) (.exec 0x121aad (fun s => s.RIP = 0x121aad) (movR32R32Effect 0x121aad 3 9 1) (Reg.operands [.gpr 1] [])) #v[232]
    (.letOp (n := 280) (.out 0x121ab0 (rolR32Effect 0x121ab0 4 9 30) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[278]
    (.letOp (n := 281) (.exec 0x121ab0 (fun s => s.RIP = 0x121ab0) (rolR32Effect 0x121ab0 4 9 30) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[278]
    (b_l121930_6))))))))))))))))))))))))))))))))))))))

def bytes_l121930_5 : List UInt8 :=
  [0xC1, 0xC7, 0x15, 0x31, 0xF7, 0x44, 0x89, 0xC6, 0xC1, 0xC6, 0x07, 0x31, 0xFE, 0x48, 0x8B, 0x7C,
    0x24, 0x18, 0x44, 0x8B, 0x4F, 0x08, 0x41, 0x0F, 0xC9, 0x4C, 0x89, 0x4C, 0x24, 0x68, 0x44, 0x89,
    0xC7, 0x21, 0xD7, 0x45, 0x01, 0xD1, 0x44, 0x01, 0xCF, 0x45, 0x89, 0xC1, 0x41, 0xF7, 0xD1, 0x4C,
    0x89, 0xA4, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x45, 0x21, 0xE1, 0x44, 0x01, 0xCF, 0x41, 0x89, 0xC9,
    0x41, 0xC1, 0xC1, 0x1E] ++ bytes_l121930_6

theorem code_l121930_5 : ∀ x ∈ codeRange 0x121a70 bytes_l121930_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21a70 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_6

def b_l121930_4 : Block Op Label signature Reg.count 205 :=
  .letOp (n := 205) (.out 0x121a2b (movR32R32Effect 0x121a2b 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[168]
    (.letOp (n := 206) (.exec 0x121a2b (fun s => s.RIP = 0x121a2b) (movR32R32Effect 0x121a2b 3 8 0) (Reg.operands [.gpr 0] [])) #v[168]
    (.letOp (n := 207) (.out 0x121a2e (rolR32Effect 0x121a2e 4 8 19) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[205]
    (.letOp (n := 208) (.exec 0x121a2e (fun s => s.RIP = 0x121a2e) (rolR32Effect 0x121a2e 4 8 19) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[205]
    (.letOp (n := 209) (.out 0x121a32 (xorR32R32Effect 0x121a32 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[207, 203]
    (.letOp (n := 210) (.exec 0x121a32 (fun s => s.RIP = 0x121a32) (xorR32R32Effect 0x121a32 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[207, 203]
    (.letOp (n := 211) (.out 0x121a35 (movR32R32Effect 0x121a35 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[168]
    (.letOp (n := 212) (.exec 0x121a35 (fun s => s.RIP = 0x121a35) (movR32R32Effect 0x121a35 3 9 0) (Reg.operands [.gpr 0] [])) #v[168]
    (.letOp (n := 213) (.out 0x121a38 (rolR32Effect 0x121a38 4 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[211]
    (.letOp (n := 214) (.exec 0x121a38 (fun s => s.RIP = 0x121a38) (rolR32Effect 0x121a38 4 9 10) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[211]
    (.letOp (n := 215) (.out 0x121a3c (xorR32R32Effect 0x121a3c 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[213, 209]
    (.letOp (n := 216) (.exec 0x121a3c (fun s => s.RIP = 0x121a3c) (xorR32R32Effect 0x121a3c 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[213, 209]
    (.letOp (n := 217) (.out 0x121a3f (movR32R32Effect 0x121a3f 3 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[3]
    (.letOp (n := 218) (.exec 0x121a3f (fun s => s.RIP = 0x121a3f) (movR32R32Effect 0x121a3f 3 8 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 219) (.out 0x121a42 (andR32R32Effect 0x121a42 3 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[217, 54]
    (.letOp (n := 220) (.exec 0x121a42 (fun s => s.RIP = 0x121a42) (andR32R32Effect 0x121a42 3 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[217, 54]
    (.letOp (n := 221) (.out 0x121a45 (movR32R32Effect 0x121a45 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 222) (.exec 0x121a45 (fun s => s.RIP = 0x121a45) (movR32R32Effect 0x121a45 2 1 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 223) (.out 0x121a47 (xorR32R32Effect 0x121a47 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[221, 54]
    (.letOp (n := 224) (.exec 0x121a47 (fun s => s.RIP = 0x121a47) (xorR32R32Effect 0x121a47 3 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[221, 54]
    (.letOp (n := 225) (.exec 0x121a4a (StorePre 0x121a4a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x121a4a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x121a4a 15 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 226) (.out 0x121a52 (andR32R32Effect 0x121a52 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[223, 168]
    (.letOp (n := 227) (.exec 0x121a52 (fun s => s.RIP = 0x121a52) (andR32R32Effect 0x121a52 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[223, 168]
    (.letOp (n := 228) (.out 0x121a54 (xorR32R32Effect 0x121a54 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[226, 219]
    (.letOp (n := 229) (.exec 0x121a54 (fun s => s.RIP = 0x121a54) (xorR32R32Effect 0x121a54 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[226, 219]
    (.letOp (n := 230) (.out 0x121a57 (addR32R32Effect 0x121a57 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[228, 215]
    (.letOp (n := 231) (.exec 0x121a57 (fun s => s.RIP = 0x121a57) (addR32R32Effect 0x121a57 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[228, 215]
    (.letOp (n := 232) (.out 0x121a5a (addR32R32Effect 0x121a5a 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[230, 199]
    (.letOp (n := 233) (.exec 0x121a5a (fun s => s.RIP = 0x121a5a) (addR32R32Effect 0x121a5a 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[230, 199]
    (.letOp (n := 234) (.out 0x121a5c (leaR32Effect 0x121a5c 4 8 (.sib 14 (some 6) 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14, .gpr 6] []) (.reg (.gpr 8))) #v[56, 195]
    (.letOp (n := 235) (.exec 0x121a5c (fun s => s.RIP = 0x121a5c) (leaR32Effect 0x121a5c 4 8 (.sib 14 (some 6) 0 .none)) (Reg.operands [.gpr 14, .gpr 6] [])) #v[56, 195]
    (.letOp (n := 236) (.out 0x121a60 (addR32Imm32Effect 0x121a60 7 8 0x71374491) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[234]
    (.letOp (n := 237) (.exec 0x121a60 (fun s => s.RIP = 0x121a60) (addR32Imm32Effect 0x121a60 7 8 0x71374491) (Reg.operands [.gpr 8] [])) #v[234]
    (.letOp (n := 238) (.out 0x121a67 (movR32R32Effect 0x121a67 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[236]
    (.letOp (n := 239) (.exec 0x121a67 (fun s => s.RIP = 0x121a67) (movR32R32Effect 0x121a67 3 6 8) (Reg.operands [.gpr 8] [])) #v[236]
    (.letOp (n := 240) (.out 0x121a6a (rolR32Effect 0x121a6a 3 6 26) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[238]
    (.letOp (n := 241) (.exec 0x121a6a (fun s => s.RIP = 0x121a6a) (rolR32Effect 0x121a6a 3 6 26) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[238]
    (.letOp (n := 242) (.out 0x121a6d (movR32R32Effect 0x121a6d 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[236]
    (.letOp (n := 243) (.exec 0x121a6d (fun s => s.RIP = 0x121a6d) (movR32R32Effect 0x121a6d 3 7 8) (Reg.operands [.gpr 8] [])) #v[236]
    (b_l121930_5)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_4 : List UInt8 :=
  [0x41, 0x89, 0xC0, 0x41, 0xC1, 0xC0, 0x13, 0x41, 0x31, 0xC8, 0x41, 0x89, 0xC1, 0x41, 0xC1, 0xC1,
    0x0A, 0x45, 0x31, 0xC1, 0x41, 0x89, 0xD8, 0x45, 0x21, 0xF8, 0x89, 0xD9, 0x44, 0x31, 0xF9, 0x4C,
    0x89, 0xBC, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x21, 0xC1, 0x44, 0x31, 0xC1, 0x44, 0x01, 0xC9, 0x01,
    0xF9, 0x45, 0x8D, 0x04, 0x36, 0x41, 0x81, 0xC0, 0x91, 0x44, 0x37, 0x71, 0x44, 0x89, 0xC6, 0xC1,
    0xC6, 0x1A, 0x44, 0x89, 0xC7] ++ bytes_l121930_5

theorem code_l121930_4 : ∀ x ∈ codeRange 0x121a2b bytes_l121930_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21a2b 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_5

def b_l121930_3 : Block Op Label signature Reg.count 166 :=
  .letOp (n := 166) (.out 0x1219f1 (rolR32Effect 0x1219f1 3 6 21) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[164]
    (.letOp (n := 167) (.exec 0x1219f1 (fun s => s.RIP = 0x1219f1) (rolR32Effect 0x1219f1 3 6 21) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[164]
    (.letOp (n := 168) (.out 0x1219f4 (addR32R32Effect 0x1219f4 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[162, 129]
    (.letOp (n := 169) (.exec 0x1219f4 (fun s => s.RIP = 0x1219f4) (addR32R32Effect 0x1219f4 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[162, 129]
    (.letOp (n := 170) (.out 0x1219f6 (movR32R32Effect 0x1219f6 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[156]
    (.letOp (n := 171) (.exec 0x1219f6 (fun s => s.RIP = 0x1219f6) (movR32R32Effect 0x1219f6 2 7 2) (Reg.operands [.gpr 2] [])) #v[156]
    (.letOp (n := 172) (.out 0x1219f8 (rolR32Effect 0x1219f8 3 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[170]
    (.letOp (n := 173) (.exec 0x1219f8 (fun s => s.RIP = 0x1219f8) (rolR32Effect 0x1219f8 3 7 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[170]
    (.letOp (n := 174) (.out 0x1219fb (xorR32R32Effect 0x1219fb 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[166, 160]
    (.letOp (n := 175) (.exec 0x1219fb (fun s => s.RIP = 0x1219fb) (xorR32R32Effect 0x1219fb 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[166, 160]
    (.letOp (n := 176) (.out 0x1219fd (xorR32R32Effect 0x1219fd 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[172, 174]
    (.letOp (n := 177) (.exec 0x1219fd (fun s => s.RIP = 0x1219fd) (xorR32R32Effect 0x1219fd 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[172, 174]
    (.letOp (n := 178) (.out 0x1219ff (movR32R32Effect 0x1219ff 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[156]
    (.letOp (n := 179) (.exec 0x1219ff (fun s => s.RIP = 0x1219ff) (movR32R32Effect 0x1219ff 2 1 2) (Reg.operands [.gpr 2] [])) #v[156]
    (.letOp (n := 180) (.out 0x121a01 (andR32R32Effect 0x121a01 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[178, 131]
    (.letOp (n := 181) (.exec 0x121a01 (fun s => s.RIP = 0x121a01) (andR32R32Effect 0x121a01 3 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[178, 131]
    (.letOp (n := 182) (.out 0x121a04 (addR32R32Effect 0x121a04 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[180, 61]
    (.letOp (n := 183) (.exec 0x121a04 (fun s => s.RIP = 0x121a04) (addR32R32Effect 0x121a04 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[180, 61]
    (.letOp (n := 184) (.out 0x121a07 (addR32R32Effect 0x121a07 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[182, 76]
    (.letOp (n := 185) (.exec 0x121a07 (fun s => s.RIP = 0x121a07) (addR32R32Effect 0x121a07 3 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[182, 76]
    (.letOp (n := 186) (.out 0x121a0a (movR32R32Effect 0x121a0a 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[156]
    (.letOp (n := 187) (.exec 0x121a0a (fun s => s.RIP = 0x121a0a) (movR32R32Effect 0x121a0a 2 6 2) (Reg.operands [.gpr 2] [])) #v[156]
    (.letOp (n := 188) (.out 0x121a0c (notR32Effect 0x121a0c 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[186]
    (.letOp (n := 189) (.exec 0x121a0c (fun s => s.RIP = 0x121a0c) (notR32Effect 0x121a0c 2 6) (Reg.operands [.gpr 6] [])) #v[186]
    (.letOp (n := 190) (.exec 0x121a0e (StorePre 0x121a0e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x121a0e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x121a0e 10 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 191) (.out 0x121a16 (andR32R32Effect 0x121a16 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[188, 10]
    (.letOp (n := 192) (.exec 0x121a16 (fun s => s.RIP = 0x121a16) (andR32R32Effect 0x121a16 3 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[188, 10]
    (.letOp (n := 193) (.out 0x121a19 (addR32R32Effect 0x121a19 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[184, 191]
    (.letOp (n := 194) (.exec 0x121a19 (fun s => s.RIP = 0x121a19) (addR32R32Effect 0x121a19 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[184, 191]
    (.letOp (n := 195) (.out 0x121a1b (leaR32Effect 0x121a1b 3 6 (.sib 1 (some 7) 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1, .gpr 7] []) (.reg (.gpr 6))) #v[193, 176]
    (.letOp (n := 196) (.exec 0x121a1b (fun s => s.RIP = 0x121a1b) (leaR32Effect 0x121a1b 3 6 (.sib 1 (some 7) 0 .none)) (Reg.operands [.gpr 1, .gpr 7] [])) #v[193, 176]
    (.letOp (n := 197) (.out 0x121a1e (addR32R32Effect 0x121a1e 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[176, 193]
    (.letOp (n := 198) (.exec 0x121a1e (fun s => s.RIP = 0x121a1e) (addR32R32Effect 0x121a1e 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[176, 193]
    (.letOp (n := 199) (.out 0x121a20 (addR32Imm32Effect 0x121a20 6 7 0x71374491) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[197]
    (.letOp (n := 200) (.exec 0x121a20 (fun s => s.RIP = 0x121a20) (addR32Imm32Effect 0x121a20 6 7 0x71374491) (Reg.operands [.gpr 7] [])) #v[197]
    (.letOp (n := 201) (.out 0x121a26 (movR32R32Effect 0x121a26 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[168]
    (.letOp (n := 202) (.exec 0x121a26 (fun s => s.RIP = 0x121a26) (movR32R32Effect 0x121a26 2 1 0) (Reg.operands [.gpr 0] [])) #v[168]
    (.letOp (n := 203) (.out 0x121a28 (rolR32Effect 0x121a28 3 1 30) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[201]
    (.letOp (n := 204) (.exec 0x121a28 (fun s => s.RIP = 0x121a28) (rolR32Effect 0x121a28 3 1 30) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[201]
    (b_l121930_4)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_3 : List UInt8 :=
  [0xC1, 0xC6, 0x15, 0x01, 0xF8, 0x89, 0xD7, 0xC1, 0xC7, 0x07, 0x31, 0xCE, 0x31, 0xF7, 0x89, 0xD1,
    0x44, 0x21, 0xE1, 0x44, 0x01, 0xC9, 0x44, 0x01, 0xE9, 0x89, 0xD6, 0xF7, 0xD6, 0x4C, 0x89, 0x94,
    0x24, 0x00, 0x01, 0x00, 0x00, 0x44, 0x21, 0xD6, 0x01, 0xF1, 0x8D, 0x34, 0x39, 0x01, 0xCF, 0x81,
    0xC7, 0x91, 0x44, 0x37, 0x71, 0x89, 0xC1, 0xC1, 0xC1, 0x1E] ++ bytes_l121930_4

theorem code_l121930_3 : ∀ x ∈ codeRange 0x1219f1 bytes_l121930_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x219f1 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_4

def b_l121930_2 : Block Op Label signature Reg.count 127 :=
  .letOp (n := 127) (.out 0x1219ae (addR32R32Effect 0x1219ae 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[118, 112]
    (.letOp (n := 128) (.exec 0x1219ae (fun s => s.RIP = 0x1219ae) (addR32R32Effect 0x1219ae 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[118, 112]
    (.letOp (n := 129) (.out 0x1219b0 (addR32Imm32Effect 0x1219b0 6 7 0x428a2f98) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[127]
    (.letOp (n := 130) (.exec 0x1219b0 (fun s => s.RIP = 0x1219b0) (addR32Imm32Effect 0x1219b0 6 7 0x428a2f98) (Reg.operands [.gpr 7] [])) #v[127]
    (.letOp (n := 131) (.out 0x1219b6 (movR64R64Effect 0x1219b6 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 8] []) (.reg (.gpr 12))) #v[8]
    (.letOp (n := 132) (.exec 0x1219b6 (fun s => s.RIP = 0x1219b6) (movR64R64Effect 0x1219b6 12 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 133) (.out 0x1219b9 (movR32R32Effect 0x1219b9 3 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[3]
    (.letOp (n := 134) (.exec 0x1219b9 (fun s => s.RIP = 0x1219b9) (movR32R32Effect 0x1219b9 3 8 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 135) (.out 0x1219bc (rolR32Effect 0x1219bc 4 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[133]
    (.letOp (n := 136) (.exec 0x1219bc (fun s => s.RIP = 0x1219bc) (rolR32Effect 0x1219bc 4 8 10) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[133]
    (.letOp (n := 137) (.out 0x1219c0 (xorR32R32Effect 0x1219c0 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[125, 116]
    (.letOp (n := 138) (.exec 0x1219c0 (fun s => s.RIP = 0x1219c0) (xorR32R32Effect 0x1219c0 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[125, 116]
    (.letOp (n := 139) (.out 0x1219c2 (xorR32R32Effect 0x1219c2 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[135, 137]
    (.letOp (n := 140) (.exec 0x1219c2 (fun s => s.RIP = 0x1219c2) (xorR32R32Effect 0x1219c2 3 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[135, 137]
    (.letOp (n := 141) (.out 0x1219c5 (movR32R32Effect 0x1219c5 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[54]
    (.letOp (n := 142) (.exec 0x1219c5 (fun s => s.RIP = 0x1219c5) (movR32R32Effect 0x1219c5 3 2 15) (Reg.operands [.gpr 15] [])) #v[54]
    (.letOp (n := 143) (.out 0x1219c8 (xorR32R32Effect 0x1219c8 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[141, 56]
    (.letOp (n := 144) (.exec 0x1219c8 (fun s => s.RIP = 0x1219c8) (xorR32R32Effect 0x1219c8 3 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[141, 56]
    (.letOp (n := 145) (.out 0x1219cb (andR32R32Effect 0x1219cb 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[143, 3]
    (.letOp (n := 146) (.exec 0x1219cb (fun s => s.RIP = 0x1219cb) (andR32R32Effect 0x1219cb 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[143, 3]
    (.letOp (n := 147) (.out 0x1219cd (movR32R32Effect 0x1219cd 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 148) (.exec 0x1219cd (fun s => s.RIP = 0x1219cd) (movR32R32Effect 0x1219cd 3 0 15) (Reg.operands [.gpr 15] [])) #v[54]
    (.letOp (n := 149) (.out 0x1219d0 (andR32R32Effect 0x1219d0 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[147, 56]
    (.letOp (n := 150) (.exec 0x1219d0 (fun s => s.RIP = 0x1219d0) (andR32R32Effect 0x1219d0 3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[147, 56]
    (.letOp (n := 151) (.exec 0x1219d3 (StorePre 0x1219d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1219d3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1219d3 14 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 152) (.out 0x1219db (xorR32R32Effect 0x1219db 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[149, 145]
    (.letOp (n := 153) (.exec 0x1219db (fun s => s.RIP = 0x1219db) (xorR32R32Effect 0x1219db 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[149, 145]
    (.letOp (n := 154) (.out 0x1219dd (leaR32Effect 0x1219dd 4 2 (.sib 11 (some 1) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 1] []) (.reg (.gpr 2))) #v[58, 121]
    (.letOp (n := 155) (.exec 0x1219dd (fun s => s.RIP = 0x1219dd) (leaR32Effect 0x1219dd 4 2 (.sib 11 (some 1) 0 .none)) (Reg.operands [.gpr 11, .gpr 1] [])) #v[58, 121]
    (.letOp (n := 156) (.out 0x1219e1 (addR32Imm32Effect 0x1219e1 6 2 0x428a2f98) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[154]
    (.letOp (n := 157) (.exec 0x1219e1 (fun s => s.RIP = 0x1219e1) (addR32Imm32Effect 0x1219e1 6 2 0x428a2f98) (Reg.operands [.gpr 2] [])) #v[154]
    (.letOp (n := 158) (.out 0x1219e7 (movR32R32Effect 0x1219e7 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[156]
    (.letOp (n := 159) (.exec 0x1219e7 (fun s => s.RIP = 0x1219e7) (movR32R32Effect 0x1219e7 2 1 2) (Reg.operands [.gpr 2] [])) #v[156]
    (.letOp (n := 160) (.out 0x1219e9 (rolR32Effect 0x1219e9 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[158]
    (.letOp (n := 161) (.exec 0x1219e9 (fun s => s.RIP = 0x1219e9) (rolR32Effect 0x1219e9 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[158]
    (.letOp (n := 162) (.out 0x1219ec (addR32R32Effect 0x1219ec 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[152, 139]
    (.letOp (n := 163) (.exec 0x1219ec (fun s => s.RIP = 0x1219ec) (addR32R32Effect 0x1219ec 3 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[152, 139]
    (.letOp (n := 164) (.out 0x1219ef (movR32R32Effect 0x1219ef 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[156]
    (.letOp (n := 165) (.exec 0x1219ef (fun s => s.RIP = 0x1219ef) (movR32R32Effect 0x1219ef 2 6 2) (Reg.operands [.gpr 2] [])) #v[156]
    (b_l121930_3)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_2 : List UInt8 :=
  [0x01, 0xC7, 0x81, 0xC7, 0x98, 0x2F, 0x8A, 0x42, 0x4D, 0x89, 0xC4, 0x41, 0x89, 0xD8, 0x41, 0xC1,
    0xC0, 0x0A, 0x31, 0xD6, 0x41, 0x31, 0xF0, 0x44, 0x89, 0xFA, 0x44, 0x31, 0xF2, 0x21, 0xDA, 0x44,
    0x89, 0xF8, 0x44, 0x21, 0xF0, 0x4C, 0x89, 0xB4, 0x24, 0x08, 0x01, 0x00, 0x00, 0x31, 0xD0, 0x41,
    0x8D, 0x14, 0x0B, 0x81, 0xC2, 0x98, 0x2F, 0x8A, 0x42, 0x89, 0xD1, 0xC1, 0xC1, 0x1A, 0x44, 0x01,
    0xC0, 0x89, 0xD6] ++ bytes_l121930_3

theorem code_l121930_2 : ∀ x ∈ codeRange 0x1219ae bytes_l121930_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x219ae 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_3

def b_l121930_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x121974 (movR32R32Effect 0x121974 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 90) (.exec 0x121974 (fun s => s.RIP = 0x121974) (movR32R32Effect 0x121974 3 0 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 91) (.out 0x121977 (rolR32Effect 0x121977 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[89]
    (.letOp (n := 92) (.exec 0x121977 (fun s => s.RIP = 0x121977) (rolR32Effect 0x121977 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[89]
    (.letOp (n := 93) (.out 0x12197a (xorR32R32Effect 0x12197a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[91, 87]
    (.letOp (n := 94) (.exec 0x12197a (fun s => s.RIP = 0x12197a) (xorR32R32Effect 0x12197a 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[91, 87]
    (.letOp (n := 95) (.out 0x12197c (movR32R32Effect 0x12197c 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 96) (.exec 0x12197c (fun s => s.RIP = 0x12197c) (movR32R32Effect 0x12197c 3 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 97) (.out 0x12197f (andR32R32Effect 0x12197f 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[95, 10]
    (.letOp (n := 98) (.exec 0x12197f (fun s => s.RIP = 0x12197f) (andR32R32Effect 0x12197f 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[95, 10]
    (.letOp (n := 99) (.out 0x121982 (movR32R32Effect 0x121982 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[8]
    (.letOp (n := 100) (.exec 0x121982 (fun s => s.RIP = 0x121982) (movR32R32Effect 0x121982 3 2 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 101) (.out 0x121985 (notR32Effect 0x121985 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[99]
    (.letOp (n := 102) (.exec 0x121985 (fun s => s.RIP = 0x121985) (notR32Effect 0x121985 2 2) (Reg.operands [.gpr 2] [])) #v[99]
    (.letOp (n := 103) (.out 0x121987 (andR32R32Effect 0x121987 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[101, 61]
    (.letOp (n := 104) (.exec 0x121987 (fun s => s.RIP = 0x121987) (andR32R32Effect 0x121987 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[101, 61]
    (.letOp (n := 105) (.exec 0x12198a (StorePre 0x12198a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x12198a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12198a 9 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 106) (.out 0x121992 (addR32R32Effect 0x121992 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[97, 63]
    (.letOp (n := 107) (.exec 0x121992 (fun s => s.RIP = 0x121992) (addR32R32Effect 0x121992 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[97, 63]
    (.letOp (n := 108) (.out 0x121994 (addR32R32Effect 0x121994 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[106, 103]
    (.letOp (n := 109) (.exec 0x121994 (fun s => s.RIP = 0x121994) (addR32R32Effect 0x121994 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[106, 103]
    (.letOp (n := 110) (.out 0x121996 (addR32R32Effect 0x121996 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[108, 93]
    (.letOp (n := 111) (.exec 0x121996 (fun s => s.RIP = 0x121996) (addR32R32Effect 0x121996 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[108, 93]
    (.letOp (n := 112) (.out 0x121998 (movR32R32Effect 0x121998 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[110]
    (.letOp (n := 113) (.exec 0x121998 (fun s => s.RIP = 0x121998) (movR32R32Effect 0x121998 2 0 1) (Reg.operands [.gpr 1] [])) #v[110]
    (.letOp (n := 114) (.out 0x12199a (movR32R32Effect 0x12199a 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 115) (.exec 0x12199a (fun s => s.RIP = 0x12199a) (movR32R32Effect 0x12199a 2 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 116) (.out 0x12199c (rolR32Effect 0x12199c 3 2 30) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[114]
    (.letOp (n := 117) (.exec 0x12199c (fun s => s.RIP = 0x12199c) (rolR32Effect 0x12199c 3 2 30) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[114]
    (.letOp (n := 118) (.out 0x12199f (movR64R64Effect 0x12199f 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[72]
    (.letOp (n := 119) (.exec 0x12199f (fun s => s.RIP = 0x12199f) (movR64R64Effect 0x12199f 7 6) (Reg.operands [.gpr 6] [])) #v[72]
    (.letOp (n := 120) (.exec 0x1219a2 (StorePre 0x1219a2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1219a2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1219a2 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 121) (.out 0x1219a7 (addR32R32Effect 0x1219a7 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[110, 118]
    (.letOp (n := 122) (.exec 0x1219a7 (fun s => s.RIP = 0x1219a7) (addR32R32Effect 0x1219a7 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[110, 118]
    (.letOp (n := 123) (.out 0x1219a9 (movR32R32Effect 0x1219a9 2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 124) (.exec 0x1219a9 (fun s => s.RIP = 0x1219a9) (movR32R32Effect 0x1219a9 2 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 125) (.out 0x1219ab (rolR32Effect 0x1219ab 3 6 19) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[123]
    (.letOp (n := 126) (.exec 0x1219ab (fun s => s.RIP = 0x1219ab) (rolR32Effect 0x1219ab 3 6 19) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[123]
    (b_l121930_2))))))))))))))))))))))))))))))))))))))

def bytes_l121930_1 : List UInt8 :=
  [0x44, 0x89, 0xC0, 0xC1, 0xC0, 0x07, 0x31, 0xC8, 0x44, 0x89, 0xC1, 0x44, 0x21, 0xD1, 0x44, 0x89,
    0xC2, 0xF7, 0xD2, 0x44, 0x21, 0xCA, 0x4C, 0x89, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00, 0x01, 0xF9,
    0x01, 0xD1, 0x01, 0xC1, 0x89, 0xC8, 0x89, 0xDA, 0xC1, 0xC2, 0x1E, 0x48, 0x89, 0xF7, 0x48, 0x89,
    0x74, 0x24, 0x50, 0x01, 0xF9, 0x89, 0xDE, 0xC1, 0xC6, 0x13] ++ bytes_l121930_2

theorem code_l121930_1 : ∀ x ∈ codeRange 0x121974 bytes_l121930_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21974 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_2

def b_l121930 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x121930 (StorePre 0x121930 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121930 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121930 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 54) (.out 0x121935 (movR32R32Effect 0x121935 3 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 55) (.exec 0x121935 (fun s => s.RIP = 0x121935) (movR32R32Effect 0x121935 3 15 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.out 0x121938 (movR32R32Effect 0x121938 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[0]
    (.letOp (n := 57) (.exec 0x121938 (fun s => s.RIP = 0x121938) (movR32R32Effect 0x121938 3 14 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 58) (.out 0x12193b (movR32R32Effect 0x12193b 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[9]
    (.letOp (n := 59) (.exec 0x12193b (fun s => s.RIP = 0x12193b) (movR32R32Effect 0x12193b 3 11 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 60) (.exec 0x12193e (StorePre 0x12193e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x12193e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12193e 11 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x121946 (movR32R32Effect 0x121946 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2]
    (.letOp (n := 62) (.exec 0x121946 (fun s => s.RIP = 0x121946) (movR32R32Effect 0x121946 3 9 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 63) (.out 0x121949 (movR32R32Effect 0x121949 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1]
    (.letOp (n := 64) (.exec 0x121949 (fun s => s.RIP = 0x121949) (movR32R32Effect 0x121949 2 7 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 65) (.exec 0x12194b (StorePre 0x12194b 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x12194b + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x12194b 1 (.sib 4 none 0 (.d32 0xbc))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 66) (.out 0x121952 (movR32M32LowEffect 0x121952 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 67) (.exec 0x121952 (LoadPre 0x121952 (fun s => AddrMode.addr (.base 6 .none) s (0x121952 + BitVec.ofNat 64 2)) 4) (movR32M32LowEffect 0x121952 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 68) (.out 0x121954 (movR32M32LowEffect 0x121954 1 (.base 6 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 69) (.exec 0x121954 (LoadPre 0x121954 (fun s => AddrMode.addr (.base 6 (.d8 0x4)) s (0x121954 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x121954 1 (.base 6 (.d8 0x4))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 70) (.out 0x121957 (bswapR32Effect 0x121957 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 71) (.exec 0x121957 (fun s => s.RIP = 0x121957) (bswapR32Effect 0x121957 2 0) (Reg.operands [.gpr 0] [])) #v[66]
    (.letOp (n := 72) (.out 0x121959 (movR64R64Effect 0x121959 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[70]
    (.letOp (n := 73) (.exec 0x121959 (fun s => s.RIP = 0x121959) (movR64R64Effect 0x121959 6 0) (Reg.operands [.gpr 0] [])) #v[70]
    (.letOp (n := 74) (.out 0x12195c (bswapR32Effect 0x12195c 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[68]
    (.letOp (n := 75) (.exec 0x12195c (fun s => s.RIP = 0x12195c) (bswapR32Effect 0x12195c 2 1) (Reg.operands [.gpr 1] [])) #v[68]
    (.letOp (n := 76) (.out 0x12195e (movR64R64Effect 0x12195e 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[74]
    (.letOp (n := 77) (.exec 0x12195e (fun s => s.RIP = 0x12195e) (movR64R64Effect 0x12195e 13 1) (Reg.operands [.gpr 1] [])) #v[74]
    (.letOp (n := 78) (.exec 0x121961 (StorePre 0x121961 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x121961 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121961 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 79) (.out 0x121966 (movR32R32Effect 0x121966 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 80) (.exec 0x121966 (fun s => s.RIP = 0x121966) (movR32R32Effect 0x121966 3 0 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 81) (.out 0x121969 (rolR32Effect 0x121969 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[79]
    (.letOp (n := 82) (.exec 0x121969 (fun s => s.RIP = 0x121969) (rolR32Effect 0x121969 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 83) (.out 0x12196c (movR32R32Effect 0x12196c 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 84) (.exec 0x12196c (fun s => s.RIP = 0x12196c) (movR32R32Effect 0x12196c 3 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 85) (.out 0x12196f (rolR32Effect 0x12196f 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[83]
    (.letOp (n := 86) (.exec 0x12196f (fun s => s.RIP = 0x12196f) (rolR32Effect 0x12196f 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[83]
    (.letOp (n := 87) (.out 0x121972 (xorR32R32Effect 0x121972 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[85, 81]
    (.letOp (n := 88) (.exec 0x121972 (fun s => s.RIP = 0x121972) (xorR32R32Effect 0x121972 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[85, 81]
    (b_l121930_1))))))))))))))))))))))))))))))))))))

def bytes_l121930 : List UInt8 :=
  [0x48, 0x89, 0x74, 0x24, 0x18, 0x45, 0x89, 0xF7, 0x41, 0x89, 0xC6, 0x45, 0x89, 0xCB, 0x4C, 0x89,
    0x9C, 0x24, 0x18, 0x01, 0x00, 0x00, 0x41, 0x89, 0xD1, 0x89, 0xCF, 0x89, 0x8C, 0x24, 0xBC, 0x00,
    0x00, 0x00, 0x8B, 0x06, 0x8B, 0x4E, 0x04, 0x0F, 0xC8, 0x48, 0x89, 0xC6, 0x0F, 0xC9, 0x49, 0x89,
    0xCD, 0x48, 0x89, 0x4C, 0x24, 0x38, 0x44, 0x89, 0xC0, 0xC1, 0xC0, 0x1A, 0x44, 0x89, 0xC1, 0xC1,
    0xC1, 0x15, 0x31, 0xC1] ++ bytes_l121930_1

theorem code_l121930 : ∀ x ∈ codeRange 0x121930 bytes_l121930, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21930 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_1

end K256.Proofs.Verify.LIR
