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

def b_l121930_166 : Block Op Label signature Reg.count 6562 :=
  .letOp (n := 6562) (.out 0x124082 (addR32M32Effect 0x124082 8 9 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[6298, 4]
    (.letOp (n := 6563) (.exec 0x124082 (LoadPre 0x124082 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x124082 + BitVec.ofNat 64 8)) 4) (addR32M32Effect 0x124082 8 9 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[6298, 4]
    (.letOp (n := 6564) (.out 0x12408a (addR32M32Effect 0x12408a 8 11 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4] []) (.reg (.gpr 11))) #v[6212, 4]
    (.letOp (n := 6565) (.exec 0x12408a (LoadPre 0x12408a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x12408a + BitVec.ofNat 64 8)) 4) (addR32M32Effect 0x12408a 8 11 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[6212, 4]
    (.letOp (n := 6566) (.out 0x124092 (movR32R32Effect 0x124092 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 5] []) (.reg (.gpr 3))) #v[6554]
    (.letOp (n := 6567) (.exec 0x124092 (fun s => s.RIP = 0x124092) (movR32R32Effect 0x124092 2 3 5) (Reg.operands [.gpr 5] [])) #v[6554]
    (.letOp (n := 6568) (.out 0x124094 (addR32R32Effect 0x124094 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[6566, 6522]
    (.letOp (n := 6569) (.exec 0x124094 (fun s => s.RIP = 0x124094) (addR32R32Effect 0x124094 2 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[6566, 6522]
    (.letOp (n := 6570) (.out 0x124096 (movR32R32Effect 0x124096 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[6564]
    (.letOp (n := 6571) (.exec 0x124096 (fun s => s.RIP = 0x124096) (movR32R32Effect 0x124096 3 8 11) (Reg.operands [.gpr 11] [])) #v[6564]
    (.letOp (n := 6572) (.out 0x124099 (addR32R32Effect 0x124099 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[6570, 6522]
    (.letOp (n := 6573) (.exec 0x124099 (fun s => s.RIP = 0x124099) (addR32R32Effect 0x124099 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[6570, 6522]
    (.letOp (n := 6574) (.out 0x12409c (addR32M32Effect 0x12409c 8 10 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[6468, 4]
    (.letOp (n := 6575) (.exec 0x12409c (LoadPre 0x12409c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x12409c + BitVec.ofNat 64 8)) 4) (addR32M32Effect 0x12409c 8 10 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[6468, 4]
    (.letOp (n := 6576) (.out 0x1240a4 (addR32M32Effect 0x1240a4 7 2 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[6382, 4]
    (.letOp (n := 6577) (.exec 0x1240a4 (LoadPre 0x1240a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1240a4 + BitVec.ofNat 64 7)) 4) (addR32M32Effect 0x1240a4 7 2 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[6382, 4]
    (.letOp (n := 6578) (.out 0x1240ab (addR32M32Effect 0x1240ab 7 1 (.sib 4 none 0 (.d32 0xbc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[6296, 4]
    (.letOp (n := 6579) (.exec 0x1240ab (LoadPre 0x1240ab (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x1240ab + BitVec.ofNat 64 7)) 4) (addR32M32Effect 0x1240ab 7 1 (.sib 4 none 0 (.d32 0xbc))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[6296, 4]
    (.letOp (n := 6580) (.out 0x1240b2 (addR64Imm8Effect 0x1240b2 6 0x40) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6556]
    (.letOp (n := 6581) (.exec 0x1240b2 (fun s => s.RIP = 0x1240b2) (addR64Imm8Effect 0x1240b2 6 0x40) (Reg.operands [.gpr 6] [])) #v[6556]
    (.letOp (n := 6582) (.out 0x1240b6 (cmpR64M64Effect 0x1240b6 6 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 4] []) (.flag .ZF)) #v[6580, 4]
    (.letOp (n := 6583) (.exec 0x1240b6 (LoadPre 0x1240b6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1240b6 + BitVec.ofNat 64 8)) 8) (cmpR64M64Effect 0x1240b6 6 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6580, 4]
    (.letOp (n := 6584) (.pure (condOp 5)) #v[6582]
    (.terminate (.condBr (Fin.last 6584) ⟨.l121930, RegMap.args [(0, 6560), (1, 6578), (2, 6576), (3, 6568), (4, 4), (5, 6554), (6, 6580), (7, 6522), (8, 6572), (9, 6562), (10, 6574), (11, 6564), (12, 6236), (13, 6260), (14, 6558), (15, 6322), (19, 6582), (22, 22), (39, 39), (50, 50), (51, 51)] 6585⟩ ⟨.l1240c4, RegMap.args [(0, 6560), (1, 6578), (2, 6576), (3, 6568), (4, 4), (5, 6554), (6, 6580), (7, 6522), (8, 6572), (9, 6562), (10, 6574), (11, 6564), (12, 6236), (13, 6260), (14, 6558), (15, 6322), (19, 6582), (22, 22), (39, 39), (50, 50), (51, 51)] 6585⟩))))))))))))))))))))))))

def bytes_l121930_166 : List UInt8 :=
  [0x44, 0x03, 0x8C, 0x24, 0x18, 0x01, 0x00, 0x00, 0x44, 0x03, 0x9C, 0x24, 0xF0, 0x00, 0x00, 0x00,
    0x89, 0xEB, 0x01, 0xFB, 0x45, 0x89, 0xD8, 0x41, 0x01, 0xF8, 0x44, 0x03, 0x94, 0x24, 0x00, 0x01,
    0x00, 0x00, 0x03, 0x94, 0x24, 0x10, 0x01, 0x00, 0x00, 0x03, 0x8C, 0x24, 0xBC, 0x00, 0x00, 0x00,
    0x48, 0x83, 0xC6, 0x40, 0x48, 0x3B, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x0F, 0x85, 0x6C, 0xD8,
    0xFF, 0xFF]

theorem code_l121930_166 : ∀ x ∈ codeRange 0x124082 bytes_l121930_166, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24082 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l121930_165 : Block Op Label signature Reg.count 6522 :=
  .letOp (n := 6522) (.out 0x124035 (addR32Imm32Effect 0x124035 6 7 0xc67178f2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[6520]
    (.letOp (n := 6523) (.exec 0x124035 (fun s => s.RIP = 0x124035) (addR32Imm32Effect 0x124035 6 7 0xc67178f2) (Reg.operands [.gpr 7] [])) #v[6520]
    (.letOp (n := 6524) (.out 0x12403b (movR32R32Effect 0x12403b 3 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[6470]
    (.letOp (n := 6525) (.exec 0x12403b (fun s => s.RIP = 0x12403b) (movR32R32Effect 0x12403b 3 8 14) (Reg.operands [.gpr 14] [])) #v[6470]
    (.letOp (n := 6526) (.out 0x12403e (rolR32Effect 0x12403e 4 8 30) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[6524]
    (.letOp (n := 6527) (.exec 0x12403e (fun s => s.RIP = 0x12403e) (rolR32Effect 0x12403e 4 8 30) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6524]
    (.letOp (n := 6528) (.out 0x124042 (movR32R32Effect 0x124042 3 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 14] []) (.reg (.gpr 3))) #v[6470]
    (.letOp (n := 6529) (.exec 0x124042 (fun s => s.RIP = 0x124042) (movR32R32Effect 0x124042 3 3 14) (Reg.operands [.gpr 14] [])) #v[6470]
    (.letOp (n := 6530) (.out 0x124045 (rolR32Effect 0x124045 3 3 19) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6528]
    (.letOp (n := 6531) (.exec 0x124045 (fun s => s.RIP = 0x124045) (rolR32Effect 0x124045 3 3 19) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6528]
    (.letOp (n := 6532) (.out 0x124048 (xorR32R32Effect 0x124048 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[6530, 6526]
    (.letOp (n := 6533) (.exec 0x124048 (fun s => s.RIP = 0x124048) (xorR32R32Effect 0x124048 3 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[6530, 6526]
    (.letOp (n := 6534) (.out 0x12404b (movR32R32Effect 0x12404b 3 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[6470]
    (.letOp (n := 6535) (.exec 0x12404b (fun s => s.RIP = 0x12404b) (movR32R32Effect 0x12404b 3 8 14) (Reg.operands [.gpr 14] [])) #v[6470]
    (.letOp (n := 6536) (.out 0x12404e (rolR32Effect 0x12404e 4 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[6534]
    (.letOp (n := 6537) (.exec 0x12404e (fun s => s.RIP = 0x12404e) (rolR32Effect 0x12404e 4 8 10) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6534]
    (.letOp (n := 6538) (.out 0x124052 (xorR32R32Effect 0x124052 3 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[6536, 6532]
    (.letOp (n := 6539) (.exec 0x124052 (fun s => s.RIP = 0x124052) (xorR32R32Effect 0x124052 3 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[6536, 6532]
    (.letOp (n := 6540) (.out 0x124055 (movR32R32Effect 0x124055 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[6384]
    (.letOp (n := 6541) (.exec 0x124055 (fun s => s.RIP = 0x124055) (movR32R32Effect 0x124055 2 3 0) (Reg.operands [.gpr 0] [])) #v[6384]
    (.letOp (n := 6542) (.out 0x124057 (andR32R32Effect 0x124057 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[6540, 6298]
    (.letOp (n := 6543) (.exec 0x124057 (fun s => s.RIP = 0x124057) (andR32R32Effect 0x124057 3 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[6540, 6298]
    (.letOp (n := 6544) (.out 0x12405a (movR32R32Effect 0x12405a 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[6384]
    (.letOp (n := 6545) (.exec 0x12405a (fun s => s.RIP = 0x12405a) (movR32R32Effect 0x12405a 2 5 0) (Reg.operands [.gpr 0] [])) #v[6384]
    (.letOp (n := 6546) (.out 0x12405c (xorR32R32Effect 0x12405c 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[6544, 6298]
    (.letOp (n := 6547) (.exec 0x12405c (fun s => s.RIP = 0x12405c) (xorR32R32Effect 0x12405c 3 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[6544, 6298]
    (.letOp (n := 6548) (.out 0x12405f (andR32R32Effect 0x12405f 3 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[6546, 6470]
    (.letOp (n := 6549) (.exec 0x12405f (fun s => s.RIP = 0x12405f) (andR32R32Effect 0x12405f 3 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[6546, 6470]
    (.letOp (n := 6550) (.out 0x124062 (xorR32R32Effect 0x124062 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[6548, 6542]
    (.letOp (n := 6551) (.exec 0x124062 (fun s => s.RIP = 0x124062) (xorR32R32Effect 0x124062 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[6548, 6542]
    (.letOp (n := 6552) (.out 0x124064 (addR32M32Effect 0x124064 7 5 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[6550, 4]
    (.letOp (n := 6553) (.exec 0x124064 (LoadPre 0x124064 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x124064 + BitVec.ofNat 64 7)) 4) (addR32M32Effect 0x124064 7 5 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[6550, 4]
    (.letOp (n := 6554) (.out 0x12406b (addR32R32Effect 0x12406b 3 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[6552, 6538]
    (.letOp (n := 6555) (.exec 0x12406b (fun s => s.RIP = 0x12406b) (addR32R32Effect 0x12406b 3 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[6552, 6538]
    (.letOp (n := 6556) (.out 0x12406e (movR64M64Effect 0x12406e 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 6557) (.exec 0x12406e (LoadPre 0x12406e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12406e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12406e 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 6558) (.out 0x124073 (addR32M32Effect 0x124073 8 14 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[6470, 4]
    (.letOp (n := 6559) (.exec 0x124073 (LoadPre 0x124073 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x124073 + BitVec.ofNat 64 8)) 4) (addR32M32Effect 0x124073 8 14 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[6470, 4]
    (.letOp (n := 6560) (.out 0x12407b (addR32M32Effect 0x12407b 7 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[6384, 4]
    (.letOp (n := 6561) (.exec 0x12407b (LoadPre 0x12407b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x12407b + BitVec.ofNat 64 7)) 4) (addR32M32Effect 0x12407b 7 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[6384, 4]
    (b_l121930_166))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_165 : List UInt8 :=
  [0x81, 0xC7, 0xF2, 0x78, 0x71, 0xC6, 0x45, 0x89, 0xF0, 0x41, 0xC1, 0xC0, 0x1E, 0x44, 0x89, 0xF3,
    0xC1, 0xC3, 0x13, 0x44, 0x31, 0xC3, 0x45, 0x89, 0xF0, 0x41, 0xC1, 0xC0, 0x0A, 0x41, 0x31, 0xD8,
    0x89, 0xC3, 0x44, 0x21, 0xCB, 0x89, 0xC5, 0x44, 0x31, 0xCD, 0x44, 0x21, 0xF5, 0x31, 0xDD, 0x03,
    0xAC, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x44, 0x01, 0xC5, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x44, 0x03,
    0xB4, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x03, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] ++ bytes_l121930_166

theorem code_l121930_165 : ∀ x ∈ codeRange 0x124035 bytes_l121930_165, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x24035 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_166

def b_l121930_164 : Block Op Label signature Reg.count 6482 :=
  .letOp (n := 6482) (.out 0x123ffd (xorR32R32Effect 0x123ffd 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[6480, 6476]
    (.letOp (n := 6483) (.exec 0x123ffd (fun s => s.RIP = 0x123ffd) (xorR32R32Effect 0x123ffd 2 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[6480, 6476]
    (.letOp (n := 6484) (.out 0x123fff (shrR32Effect 0x123fff 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[6472]
    (.letOp (n := 6485) (.exec 0x123fff (fun s => s.RIP = 0x123fff) (shrR32Effect 0x123fff 3 6 10) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6472]
    (.letOp (n := 6486) (.out 0x124002 (xorR32R32Effect 0x124002 2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[6484, 6482]
    (.letOp (n := 6487) (.exec 0x124002 (fun s => s.RIP = 0x124002) (xorR32R32Effect 0x124002 2 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6484, 6482]
    (.letOp (n := 6488) (.out 0x124004 (movR32R32Effect 0x124004 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 10] []) (.reg (.gpr 7))) #v[6468]
    (.letOp (n := 6489) (.exec 0x124004 (fun s => s.RIP = 0x124004) (movR32R32Effect 0x124004 3 7 10) (Reg.operands [.gpr 10] [])) #v[6468]
    (.letOp (n := 6490) (.out 0x124007 (rolR32Effect 0x124007 3 7 26) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6488]
    (.letOp (n := 6491) (.exec 0x124007 (fun s => s.RIP = 0x124007) (rolR32Effect 0x124007 3 7 26) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6488]
    (.letOp (n := 6492) (.out 0x12400a (movR32R32Effect 0x12400a 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 10] []) (.reg (.gpr 3))) #v[6468]
    (.letOp (n := 6493) (.exec 0x12400a (fun s => s.RIP = 0x12400a) (movR32R32Effect 0x12400a 3 3 10) (Reg.operands [.gpr 10] [])) #v[6468]
    (.letOp (n := 6494) (.out 0x12400d (rolR32Effect 0x12400d 3 3 21) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6492]
    (.letOp (n := 6495) (.exec 0x12400d (fun s => s.RIP = 0x12400d) (rolR32Effect 0x12400d 3 3 21) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6492]
    (.letOp (n := 6496) (.out 0x124010 (xorR32R32Effect 0x124010 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[6494, 6490]
    (.letOp (n := 6497) (.exec 0x124010 (fun s => s.RIP = 0x124010) (xorR32R32Effect 0x124010 2 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[6494, 6490]
    (.letOp (n := 6498) (.out 0x124012 (movR32R32Effect 0x124012 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 10] []) (.reg (.gpr 7))) #v[6468]
    (.letOp (n := 6499) (.exec 0x124012 (fun s => s.RIP = 0x124012) (movR32R32Effect 0x124012 3 7 10) (Reg.operands [.gpr 10] [])) #v[6468]
    (.letOp (n := 6500) (.out 0x124015 (rolR32Effect 0x124015 3 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6498]
    (.letOp (n := 6501) (.exec 0x124015 (fun s => s.RIP = 0x124015) (rolR32Effect 0x124015 3 7 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6498]
    (.letOp (n := 6502) (.out 0x124018 (xorR32R32Effect 0x124018 2 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[6500, 6496]
    (.letOp (n := 6503) (.exec 0x124018 (fun s => s.RIP = 0x124018) (xorR32R32Effect 0x124018 2 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[6500, 6496]
    (.letOp (n := 6504) (.out 0x12401a (movR64M64Effect 0x12401a 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 6505) (.exec 0x12401a (LoadPre 0x12401a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12401a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12401a 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 6506) (.out 0x12401f (addR32R32Effect 0x12401f 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[6504, 6486]
    (.letOp (n := 6507) (.exec 0x12401f (fun s => s.RIP = 0x12401f) (addR32R32Effect 0x12401f 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[6504, 6486]
    (.letOp (n := 6508) (.out 0x124021 (addR32R32Effect 0x124021 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[6506, 6210]
    (.letOp (n := 6509) (.exec 0x124021 (fun s => s.RIP = 0x124021) (addR32R32Effect 0x124021 3 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[6506, 6210]
    (.letOp (n := 6510) (.out 0x124024 (movR32R32Effect 0x124024 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[6382]
    (.letOp (n := 6511) (.exec 0x124024 (fun s => s.RIP = 0x124024) (movR32R32Effect 0x124024 3 8 2) (Reg.operands [.gpr 2] [])) #v[6382]
    (.letOp (n := 6512) (.out 0x124027 (xorR32R32Effect 0x124027 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[6510, 6296]
    (.letOp (n := 6513) (.exec 0x124027 (fun s => s.RIP = 0x124027) (xorR32R32Effect 0x124027 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[6510, 6296]
    (.letOp (n := 6514) (.out 0x12402a (andR32R32Effect 0x12402a 3 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[6512, 6468]
    (.letOp (n := 6515) (.exec 0x12402a (fun s => s.RIP = 0x12402a) (andR32R32Effect 0x12402a 3 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[6512, 6468]
    (.letOp (n := 6516) (.out 0x12402d (xorR32R32Effect 0x12402d 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[6514, 6296]
    (.letOp (n := 6517) (.exec 0x12402d (fun s => s.RIP = 0x12402d) (xorR32R32Effect 0x12402d 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[6514, 6296]
    (.letOp (n := 6518) (.out 0x124030 (addR32R32Effect 0x124030 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[6508, 6516]
    (.letOp (n := 6519) (.exec 0x124030 (fun s => s.RIP = 0x124030) (addR32R32Effect 0x124030 3 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[6508, 6516]
    (.letOp (n := 6520) (.out 0x124033 (addR32R32Effect 0x124033 2 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[6502, 6518]
    (.letOp (n := 6521) (.exec 0x124033 (fun s => s.RIP = 0x124033) (addR32R32Effect 0x124033 2 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[6502, 6518]
    (b_l121930_165))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_164 : List UInt8 :=
  [0x31, 0xFB, 0xC1, 0xEE, 0x0A, 0x31, 0xDE, 0x44, 0x89, 0xD7, 0xC1, 0xC7, 0x1A, 0x44, 0x89, 0xD3,
    0xC1, 0xC3, 0x15, 0x31, 0xFB, 0x44, 0x89, 0xD7, 0xC1, 0xC7, 0x07, 0x31, 0xDF, 0x48, 0x8B, 0x5C,
    0x24, 0x28, 0x01, 0xF3, 0x44, 0x01, 0xC3, 0x41, 0x89, 0xD0, 0x41, 0x31, 0xC8, 0x45, 0x21, 0xD0,
    0x41, 0x31, 0xC8, 0x44, 0x01, 0xC3, 0x01, 0xDF] ++ bytes_l121930_165

theorem code_l121930_164 : ∀ x ∈ codeRange 0x123ffd bytes_l121930_164, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23ffd 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_165

def b_l121930_163 : Block Op Label signature Reg.count 6442 :=
  .letOp (n := 6442) (.out 0x123fc5 (movR32R32Effect 0x123fc5 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[6384]
    (.letOp (n := 6443) (.exec 0x123fc5 (fun s => s.RIP = 0x123fc5) (movR32R32Effect 0x123fc5 2 3 0) (Reg.operands [.gpr 0] [])) #v[6384]
    (.letOp (n := 6444) (.out 0x123fc7 (rolR32Effect 0x123fc7 3 3 19) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6442]
    (.letOp (n := 6445) (.exec 0x123fc7 (fun s => s.RIP = 0x123fc7) (rolR32Effect 0x123fc7 3 3 19) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6442]
    (.letOp (n := 6446) (.out 0x123fca (xorR32R32Effect 0x123fca 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[6444, 6440]
    (.letOp (n := 6447) (.exec 0x123fca (fun s => s.RIP = 0x123fca) (xorR32R32Effect 0x123fca 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[6444, 6440]
    (.letOp (n := 6448) (.out 0x123fcc (movR32R32Effect 0x123fcc 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[6384]
    (.letOp (n := 6449) (.exec 0x123fcc (fun s => s.RIP = 0x123fcc) (movR32R32Effect 0x123fcc 2 5 0) (Reg.operands [.gpr 0] [])) #v[6384]
    (.letOp (n := 6450) (.out 0x123fce (rolR32Effect 0x123fce 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[6448]
    (.letOp (n := 6451) (.exec 0x123fce (fun s => s.RIP = 0x123fce) (rolR32Effect 0x123fce 3 5 10) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6448]
    (.letOp (n := 6452) (.out 0x123fd1 (xorR32R32Effect 0x123fd1 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[6450, 6446]
    (.letOp (n := 6453) (.exec 0x123fd1 (fun s => s.RIP = 0x123fd1) (xorR32R32Effect 0x123fd1 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[6450, 6446]
    (.letOp (n := 6454) (.out 0x123fd3 (movR32R32Effect 0x123fd3 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[6298]
    (.letOp (n := 6455) (.exec 0x123fd3 (fun s => s.RIP = 0x123fd3) (movR32R32Effect 0x123fd3 3 3 9) (Reg.operands [.gpr 9] [])) #v[6298]
    (.letOp (n := 6456) (.out 0x123fd6 (andR32R32Effect 0x123fd6 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[6454, 6212]
    (.letOp (n := 6457) (.exec 0x123fd6 (fun s => s.RIP = 0x123fd6) (andR32R32Effect 0x123fd6 3 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[6454, 6212]
    (.letOp (n := 6458) (.out 0x123fd9 (movR32R32Effect 0x123fd9 3 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 9] []) (.reg (.gpr 14))) #v[6298]
    (.letOp (n := 6459) (.exec 0x123fd9 (fun s => s.RIP = 0x123fd9) (movR32R32Effect 0x123fd9 3 14 9) (Reg.operands [.gpr 9] [])) #v[6298]
    (.letOp (n := 6460) (.out 0x123fdc (xorR32R32Effect 0x123fdc 3 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[6458, 6212]
    (.letOp (n := 6461) (.exec 0x123fdc (fun s => s.RIP = 0x123fdc) (xorR32R32Effect 0x123fdc 3 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[6458, 6212]
    (.letOp (n := 6462) (.out 0x123fdf (andR32R32Effect 0x123fdf 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[6460, 6384]
    (.letOp (n := 6463) (.exec 0x123fdf (fun s => s.RIP = 0x123fdf) (andR32R32Effect 0x123fdf 3 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[6460, 6384]
    (.letOp (n := 6464) (.out 0x123fe2 (xorR32R32Effect 0x123fe2 3 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[6462, 6456]
    (.letOp (n := 6465) (.exec 0x123fe2 (fun s => s.RIP = 0x123fe2) (xorR32R32Effect 0x123fe2 3 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[6462, 6456]
    (.letOp (n := 6466) (.out 0x123fe5 (addR32R32Effect 0x123fe5 3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[6464, 6452]
    (.letOp (n := 6467) (.exec 0x123fe5 (fun s => s.RIP = 0x123fe5) (addR32R32Effect 0x123fe5 3 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[6464, 6452]
    (.letOp (n := 6468) (.out 0x123fe8 (addR32R32Effect 0x123fe8 3 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[6126, 6436]
    (.letOp (n := 6469) (.exec 0x123fe8 (fun s => s.RIP = 0x123fe8) (addR32R32Effect 0x123fe8 3 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[6126, 6436]
    (.letOp (n := 6470) (.out 0x123feb (addR32R32Effect 0x123feb 3 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[6466, 6436]
    (.letOp (n := 6471) (.exec 0x123feb (fun s => s.RIP = 0x123feb) (addR32R32Effect 0x123feb 3 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[6466, 6436]
    (.letOp (n := 6472) (.out 0x123fee (movR32R32Effect 0x123fee 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[6322]
    (.letOp (n := 6473) (.exec 0x123fee (fun s => s.RIP = 0x123fee) (movR32R32Effect 0x123fee 3 6 15) (Reg.operands [.gpr 15] [])) #v[6322]
    (.letOp (n := 6474) (.out 0x123ff1 (movR32R32Effect 0x123ff1 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[6322]
    (.letOp (n := 6475) (.exec 0x123ff1 (fun s => s.RIP = 0x123ff1) (movR32R32Effect 0x123ff1 3 7 15) (Reg.operands [.gpr 15] [])) #v[6322]
    (.letOp (n := 6476) (.out 0x123ff4 (rolR32Effect 0x123ff4 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6474]
    (.letOp (n := 6477) (.exec 0x123ff4 (fun s => s.RIP = 0x123ff4) (rolR32Effect 0x123ff4 3 7 15) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6474]
    (.letOp (n := 6478) (.out 0x123ff7 (movR32R32Effect 0x123ff7 3 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[6322]
    (.letOp (n := 6479) (.exec 0x123ff7 (fun s => s.RIP = 0x123ff7) (movR32R32Effect 0x123ff7 3 3 15) (Reg.operands [.gpr 15] [])) #v[6322]
    (.letOp (n := 6480) (.out 0x123ffa (rolR32Effect 0x123ffa 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6478]
    (.letOp (n := 6481) (.exec 0x123ffa (fun s => s.RIP = 0x123ffa) (rolR32Effect 0x123ffa 3 3 13) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6478]
    (b_l121930_164))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_163 : List UInt8 :=
  [0x89, 0xC3, 0xC1, 0xC3, 0x13, 0x31, 0xF3, 0x89, 0xC5, 0xC1, 0xC5, 0x0A, 0x31, 0xDD, 0x44, 0x89,
    0xCB, 0x44, 0x21, 0xDB, 0x45, 0x89, 0xCE, 0x45, 0x31, 0xDE, 0x41, 0x21, 0xC6, 0x41, 0x31, 0xDE,
    0x41, 0x01, 0xEE, 0x41, 0x01, 0xFA, 0x41, 0x01, 0xFE, 0x44, 0x89, 0xFE, 0x44, 0x89, 0xFF, 0xC1,
    0xC7, 0x0F, 0x44, 0x89, 0xFB, 0xC1, 0xC3, 0x0D] ++ bytes_l121930_164

theorem code_l121930_163 : ∀ x ∈ codeRange 0x123fc5 bytes_l121930_163, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23fc5 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_164

def b_l121930_162 : Block Op Label signature Reg.count 6402 :=
  .letOp (n := 6402) (.out 0x123f90 (movR32R32Effect 0x123f90 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[6382]
    (.letOp (n := 6403) (.exec 0x123f90 (fun s => s.RIP = 0x123f90) (movR32R32Effect 0x123f90 2 7 2) (Reg.operands [.gpr 2] [])) #v[6382]
    (.letOp (n := 6404) (.out 0x123f92 (rolR32Effect 0x123f92 3 7 26) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6402]
    (.letOp (n := 6405) (.exec 0x123f92 (fun s => s.RIP = 0x123f92) (rolR32Effect 0x123f92 3 7 26) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6402]
    (.letOp (n := 6406) (.out 0x123f95 (movR32R32Effect 0x123f95 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[6382]
    (.letOp (n := 6407) (.exec 0x123f95 (fun s => s.RIP = 0x123f95) (movR32R32Effect 0x123f95 2 3 2) (Reg.operands [.gpr 2] [])) #v[6382]
    (.letOp (n := 6408) (.out 0x123f97 (rolR32Effect 0x123f97 3 3 21) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6406]
    (.letOp (n := 6409) (.exec 0x123f97 (fun s => s.RIP = 0x123f97) (rolR32Effect 0x123f97 3 3 21) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6406]
    (.letOp (n := 6410) (.out 0x123f9a (xorR32R32Effect 0x123f9a 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[6408, 6404]
    (.letOp (n := 6411) (.exec 0x123f9a (fun s => s.RIP = 0x123f9a) (xorR32R32Effect 0x123f9a 2 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[6408, 6404]
    (.letOp (n := 6412) (.out 0x123f9c (movR32R32Effect 0x123f9c 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[6382]
    (.letOp (n := 6413) (.exec 0x123f9c (fun s => s.RIP = 0x123f9c) (movR32R32Effect 0x123f9c 2 7 2) (Reg.operands [.gpr 2] [])) #v[6382]
    (.letOp (n := 6414) (.out 0x123f9e (rolR32Effect 0x123f9e 3 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6412]
    (.letOp (n := 6415) (.exec 0x123f9e (fun s => s.RIP = 0x123f9e) (rolR32Effect 0x123f9e 3 7 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6412]
    (.letOp (n := 6416) (.out 0x123fa1 (xorR32R32Effect 0x123fa1 2 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[6414, 6410]
    (.letOp (n := 6417) (.exec 0x123fa1 (fun s => s.RIP = 0x123fa1) (xorR32R32Effect 0x123fa1 2 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[6414, 6410]
    (.letOp (n := 6418) (.out 0x123fa3 (movR64M64Effect 0x123fa3 3 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 6419) (.exec 0x123fa3 (LoadPre 0x123fa3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x123fa3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x123fa3 3 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 6420) (.out 0x123fa8 (addR32R32Effect 0x123fa8 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[6418, 6400]
    (.letOp (n := 6421) (.exec 0x123fa8 (fun s => s.RIP = 0x123fa8) (addR32R32Effect 0x123fa8 2 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[6418, 6400]
    (.letOp (n := 6422) (.out 0x123faa (addR32R32Effect 0x123faa 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[6420, 6124]
    (.letOp (n := 6423) (.exec 0x123faa (fun s => s.RIP = 0x123faa) (addR32R32Effect 0x123faa 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[6420, 6124]
    (.letOp (n := 6424) (.out 0x123fac (movR32R32Effect 0x123fac 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[6296]
    (.letOp (n := 6425) (.exec 0x123fac (fun s => s.RIP = 0x123fac) (movR32R32Effect 0x123fac 2 6 1) (Reg.operands [.gpr 1] [])) #v[6296]
    (.letOp (n := 6426) (.out 0x123fae (xorR32R32Effect 0x123fae 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[6424, 6210]
    (.letOp (n := 6427) (.exec 0x123fae (fun s => s.RIP = 0x123fae) (xorR32R32Effect 0x123fae 3 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[6424, 6210]
    (.letOp (n := 6428) (.out 0x123fb1 (andR32R32Effect 0x123fb1 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[6426, 6382]
    (.letOp (n := 6429) (.exec 0x123fb1 (fun s => s.RIP = 0x123fb1) (andR32R32Effect 0x123fb1 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6426, 6382]
    (.letOp (n := 6430) (.out 0x123fb3 (xorR32R32Effect 0x123fb3 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[6428, 6210]
    (.letOp (n := 6431) (.exec 0x123fb3 (fun s => s.RIP = 0x123fb3) (xorR32R32Effect 0x123fb3 3 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[6428, 6210]
    (.letOp (n := 6432) (.out 0x123fb6 (addR32R32Effect 0x123fb6 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[6422, 6430]
    (.letOp (n := 6433) (.exec 0x123fb6 (fun s => s.RIP = 0x123fb6) (addR32R32Effect 0x123fb6 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[6422, 6430]
    (.letOp (n := 6434) (.out 0x123fb8 (addR32R32Effect 0x123fb8 2 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[6416, 6432]
    (.letOp (n := 6435) (.exec 0x123fb8 (fun s => s.RIP = 0x123fb8) (addR32R32Effect 0x123fb8 2 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[6416, 6432]
    (.letOp (n := 6436) (.out 0x123fba (addR32Imm32Effect 0x123fba 6 7 0xbef9a3f7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[6434]
    (.letOp (n := 6437) (.exec 0x123fba (fun s => s.RIP = 0x123fba) (addR32Imm32Effect 0x123fba 6 7 0xbef9a3f7) (Reg.operands [.gpr 7] [])) #v[6434]
    (.letOp (n := 6438) (.out 0x123fc0 (movR32R32Effect 0x123fc0 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[6384]
    (.letOp (n := 6439) (.exec 0x123fc0 (fun s => s.RIP = 0x123fc0) (movR32R32Effect 0x123fc0 2 6 0) (Reg.operands [.gpr 0] [])) #v[6384]
    (.letOp (n := 6440) (.out 0x123fc2 (rolR32Effect 0x123fc2 3 6 30) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[6438]
    (.letOp (n := 6441) (.exec 0x123fc2 (fun s => s.RIP = 0x123fc2) (rolR32Effect 0x123fc2 3 6 30) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6438]
    (b_l121930_163))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_162 : List UInt8 :=
  [0x89, 0xD7, 0xC1, 0xC7, 0x1A, 0x89, 0xD3, 0xC1, 0xC3, 0x15, 0x31, 0xFB, 0x89, 0xD7, 0xC1, 0xC7,
    0x07, 0x31, 0xDF, 0x48, 0x8B, 0x5C, 0x24, 0x40, 0x01, 0xEB, 0x01, 0xF3, 0x89, 0xCE, 0x44, 0x31,
    0xC6, 0x21, 0xD6, 0x44, 0x31, 0xC6, 0x01, 0xF3, 0x01, 0xDF, 0x81, 0xC7, 0xF7, 0xA3, 0xF9, 0xBE,
    0x89, 0xC6, 0xC1, 0xC6, 0x1E] ++ bytes_l121930_163

theorem code_l121930_162 : ∀ x ∈ codeRange 0x123f90 bytes_l121930_162, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23f90 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_163

def b_l121930_161 : Block Op Label signature Reg.count 6362 :=
  .letOp (n := 6362) (.out 0x123f58 (movR32R32Effect 0x123f58 3 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 9] []) (.reg (.gpr 14))) #v[6298]
    (.letOp (n := 6363) (.exec 0x123f58 (fun s => s.RIP = 0x123f58) (movR32R32Effect 0x123f58 3 14 9) (Reg.operands [.gpr 9] [])) #v[6298]
    (.letOp (n := 6364) (.out 0x123f5b (rolR32Effect 0x123f5b 4 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[6362]
    (.letOp (n := 6365) (.exec 0x123f5b (fun s => s.RIP = 0x123f5b) (rolR32Effect 0x123f5b 4 14 10) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6362]
    (.letOp (n := 6366) (.out 0x123f5f (xorR32R32Effect 0x123f5f 3 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[6364, 6360]
    (.letOp (n := 6367) (.exec 0x123f5f (fun s => s.RIP = 0x123f5f) (xorR32R32Effect 0x123f5f 3 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[6364, 6360]
    (.letOp (n := 6368) (.out 0x123f62 (movR32R32Effect 0x123f62 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[6212]
    (.letOp (n := 6369) (.exec 0x123f62 (fun s => s.RIP = 0x123f62) (movR32R32Effect 0x123f62 3 3 11) (Reg.operands [.gpr 11] [])) #v[6212]
    (.letOp (n := 6370) (.out 0x123f65 (andR32R32Effect 0x123f65 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[6368, 6126]
    (.letOp (n := 6371) (.exec 0x123f65 (fun s => s.RIP = 0x123f65) (andR32R32Effect 0x123f65 3 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[6368, 6126]
    (.letOp (n := 6372) (.out 0x123f68 (movR32R32Effect 0x123f68 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[6212]
    (.letOp (n := 6373) (.exec 0x123f68 (fun s => s.RIP = 0x123f68) (movR32R32Effect 0x123f68 3 0 11) (Reg.operands [.gpr 11] [])) #v[6212]
    (.letOp (n := 6374) (.out 0x123f6b (xorR32R32Effect 0x123f6b 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[6372, 6126]
    (.letOp (n := 6375) (.exec 0x123f6b (fun s => s.RIP = 0x123f6b) (xorR32R32Effect 0x123f6b 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[6372, 6126]
    (.letOp (n := 6376) (.out 0x123f6e (andR32R32Effect 0x123f6e 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[6374, 6298]
    (.letOp (n := 6377) (.exec 0x123f6e (fun s => s.RIP = 0x123f6e) (andR32R32Effect 0x123f6e 3 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[6374, 6298]
    (.letOp (n := 6378) (.out 0x123f71 (xorR32R32Effect 0x123f71 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[6376, 6370]
    (.letOp (n := 6379) (.exec 0x123f71 (fun s => s.RIP = 0x123f71) (xorR32R32Effect 0x123f71 2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[6376, 6370]
    (.letOp (n := 6380) (.out 0x123f73 (addR32R32Effect 0x123f73 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[6378, 6366]
    (.letOp (n := 6381) (.exec 0x123f73 (fun s => s.RIP = 0x123f73) (addR32R32Effect 0x123f73 3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[6378, 6366]
    (.letOp (n := 6382) (.out 0x123f76 (addR32R32Effect 0x123f76 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[6039, 6350]
    (.letOp (n := 6383) (.exec 0x123f76 (fun s => s.RIP = 0x123f76) (addR32R32Effect 0x123f76 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[6039, 6350]
    (.letOp (n := 6384) (.out 0x123f78 (addR32R32Effect 0x123f78 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[6380, 6350]
    (.letOp (n := 6385) (.exec 0x123f78 (fun s => s.RIP = 0x123f78) (addR32R32Effect 0x123f78 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[6380, 6350]
    (.letOp (n := 6386) (.out 0x123f7a (movR32R32Effect 0x123f7a 3 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 12] []) (.reg (.gpr 5))) #v[6236]
    (.letOp (n := 6387) (.exec 0x123f7a (fun s => s.RIP = 0x123f7a) (movR32R32Effect 0x123f7a 3 5 12) (Reg.operands [.gpr 12] [])) #v[6236]
    (.letOp (n := 6388) (.out 0x123f7d (movR32R32Effect 0x123f7d 3 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[6236]
    (.letOp (n := 6389) (.exec 0x123f7d (fun s => s.RIP = 0x123f7d) (movR32R32Effect 0x123f7d 3 7 12) (Reg.operands [.gpr 12] [])) #v[6236]
    (.letOp (n := 6390) (.out 0x123f80 (rolR32Effect 0x123f80 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6388]
    (.letOp (n := 6391) (.exec 0x123f80 (fun s => s.RIP = 0x123f80) (rolR32Effect 0x123f80 3 7 15) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6388]
    (.letOp (n := 6392) (.out 0x123f83 (movR32R32Effect 0x123f83 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[6236]
    (.letOp (n := 6393) (.exec 0x123f83 (fun s => s.RIP = 0x123f83) (movR32R32Effect 0x123f83 3 3 12) (Reg.operands [.gpr 12] [])) #v[6236]
    (.letOp (n := 6394) (.out 0x123f86 (rolR32Effect 0x123f86 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6392]
    (.letOp (n := 6395) (.exec 0x123f86 (fun s => s.RIP = 0x123f86) (rolR32Effect 0x123f86 3 3 13) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6392]
    (.letOp (n := 6396) (.out 0x123f89 (xorR32R32Effect 0x123f89 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[6394, 6390]
    (.letOp (n := 6397) (.exec 0x123f89 (fun s => s.RIP = 0x123f89) (xorR32R32Effect 0x123f89 2 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[6394, 6390]
    (.letOp (n := 6398) (.out 0x123f8b (shrR32Effect 0x123f8b 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[6386]
    (.letOp (n := 6399) (.exec 0x123f8b (fun s => s.RIP = 0x123f8b) (shrR32Effect 0x123f8b 3 5 10) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6386]
    (.letOp (n := 6400) (.out 0x123f8e (xorR32R32Effect 0x123f8e 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[6398, 6396]
    (.letOp (n := 6401) (.exec 0x123f8e (fun s => s.RIP = 0x123f8e) (xorR32R32Effect 0x123f8e 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[6398, 6396]
    (b_l121930_162))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_161 : List UInt8 :=
  [0x45, 0x89, 0xCE, 0x41, 0xC1, 0xC6, 0x0A, 0x41, 0x31, 0xDE, 0x44, 0x89, 0xDB, 0x44, 0x21, 0xD3,
    0x44, 0x89, 0xD8, 0x44, 0x31, 0xD0, 0x44, 0x21, 0xC8, 0x31, 0xD8, 0x44, 0x01, 0xF0, 0x01, 0xFA,
    0x01, 0xF8, 0x44, 0x89, 0xE5, 0x44, 0x89, 0xE7, 0xC1, 0xC7, 0x0F, 0x44, 0x89, 0xE3, 0xC1, 0xC3,
    0x0D, 0x31, 0xFB, 0xC1, 0xED, 0x0A, 0x31, 0xDD] ++ bytes_l121930_162

theorem code_l121930_161 : ∀ x ∈ codeRange 0x123f58 bytes_l121930_161, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23f58 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_162

def b_l121930_160 : Block Op Label signature Reg.count 6322 :=
  .letOp (n := 6322) (.out 0x123f23 (addR32R32Effect 0x123f23 3 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 5] []) (.reg (.gpr 15))) #v[6320, 6314]
    (.letOp (n := 6323) (.exec 0x123f23 (fun s => s.RIP = 0x123f23) (addR32R32Effect 0x123f23 3 15 5) (Reg.operands [.gpr 15, .gpr 5] [])) #v[6320, 6314]
    (.letOp (n := 6324) (.out 0x123f26 (movR32R32Effect 0x123f26 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[6296]
    (.letOp (n := 6325) (.exec 0x123f26 (fun s => s.RIP = 0x123f26) (movR32R32Effect 0x123f26 2 3 1) (Reg.operands [.gpr 1] [])) #v[6296]
    (.letOp (n := 6326) (.out 0x123f28 (rolR32Effect 0x123f28 3 3 21) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6324]
    (.letOp (n := 6327) (.exec 0x123f28 (fun s => s.RIP = 0x123f28) (rolR32Effect 0x123f28 3 3 21) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6324]
    (.letOp (n := 6328) (.out 0x123f2b (xorR32R32Effect 0x123f2b 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[6326, 6318]
    (.letOp (n := 6329) (.exec 0x123f2b (fun s => s.RIP = 0x123f2b) (xorR32R32Effect 0x123f2b 2 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[6326, 6318]
    (.letOp (n := 6330) (.out 0x123f2d (movR32R32Effect 0x123f2d 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[6296]
    (.letOp (n := 6331) (.exec 0x123f2d (fun s => s.RIP = 0x123f2d) (movR32R32Effect 0x123f2d 2 7 1) (Reg.operands [.gpr 1] [])) #v[6296]
    (.letOp (n := 6332) (.out 0x123f2f (rolR32Effect 0x123f2f 3 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6330]
    (.letOp (n := 6333) (.exec 0x123f2f (fun s => s.RIP = 0x123f2f) (rolR32Effect 0x123f2f 3 7 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6330]
    (.letOp (n := 6334) (.out 0x123f32 (xorR32R32Effect 0x123f32 2 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[6332, 6328]
    (.letOp (n := 6335) (.exec 0x123f32 (fun s => s.RIP = 0x123f32) (xorR32R32Effect 0x123f32 2 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[6332, 6328]
    (.letOp (n := 6336) (.out 0x123f34 (movR32R32Effect 0x123f34 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[6210]
    (.letOp (n := 6337) (.exec 0x123f34 (fun s => s.RIP = 0x123f34) (movR32R32Effect 0x123f34 3 3 8) (Reg.operands [.gpr 8] [])) #v[6210]
    (.letOp (n := 6338) (.out 0x123f37 (xorR32R32Effect 0x123f37 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[6336, 6124]
    (.letOp (n := 6339) (.exec 0x123f37 (fun s => s.RIP = 0x123f37) (xorR32R32Effect 0x123f37 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[6336, 6124]
    (.letOp (n := 6340) (.out 0x123f39 (andR32R32Effect 0x123f39 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[6338, 6296]
    (.letOp (n := 6341) (.exec 0x123f39 (fun s => s.RIP = 0x123f39) (andR32R32Effect 0x123f39 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[6338, 6296]
    (.letOp (n := 6342) (.out 0x123f3b (xorR32R32Effect 0x123f3b 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[6340, 6124]
    (.letOp (n := 6343) (.exec 0x123f3b (fun s => s.RIP = 0x123f3b) (xorR32R32Effect 0x123f3b 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[6340, 6124]
    (.letOp (n := 6344) (.out 0x123f3d (addR32R32Effect 0x123f3d 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[6033, 6322]
    (.letOp (n := 6345) (.exec 0x123f3d (fun s => s.RIP = 0x123f3d) (addR32R32Effect 0x123f3d 3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[6033, 6322]
    (.letOp (n := 6346) (.out 0x123f40 (addR32R32Effect 0x123f40 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[6344, 6342]
    (.letOp (n := 6347) (.exec 0x123f40 (fun s => s.RIP = 0x123f40) (addR32R32Effect 0x123f40 2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[6344, 6342]
    (.letOp (n := 6348) (.out 0x123f42 (addR32R32Effect 0x123f42 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[6334, 6346]
    (.letOp (n := 6349) (.exec 0x123f42 (fun s => s.RIP = 0x123f42) (addR32R32Effect 0x123f42 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[6334, 6346]
    (.letOp (n := 6350) (.out 0x123f44 (addR32Imm32Effect 0x123f44 6 7 0xa4506ceb) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[6348]
    (.letOp (n := 6351) (.exec 0x123f44 (fun s => s.RIP = 0x123f44) (addR32Imm32Effect 0x123f44 6 7 0xa4506ceb) (Reg.operands [.gpr 7] [])) #v[6348]
    (.letOp (n := 6352) (.out 0x123f4a (movR32R32Effect 0x123f4a 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[6298]
    (.letOp (n := 6353) (.exec 0x123f4a (fun s => s.RIP = 0x123f4a) (movR32R32Effect 0x123f4a 3 0 9) (Reg.operands [.gpr 9] [])) #v[6298]
    (.letOp (n := 6354) (.out 0x123f4d (rolR32Effect 0x123f4d 3 0 30) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[6352]
    (.letOp (n := 6355) (.exec 0x123f4d (fun s => s.RIP = 0x123f4d) (rolR32Effect 0x123f4d 3 0 30) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6352]
    (.letOp (n := 6356) (.out 0x123f50 (movR32R32Effect 0x123f50 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[6298]
    (.letOp (n := 6357) (.exec 0x123f50 (fun s => s.RIP = 0x123f50) (movR32R32Effect 0x123f50 3 3 9) (Reg.operands [.gpr 9] [])) #v[6298]
    (.letOp (n := 6358) (.out 0x123f53 (rolR32Effect 0x123f53 3 3 19) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6356]
    (.letOp (n := 6359) (.exec 0x123f53 (fun s => s.RIP = 0x123f53) (rolR32Effect 0x123f53 3 3 19) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6356]
    (.letOp (n := 6360) (.out 0x123f56 (xorR32R32Effect 0x123f56 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[6358, 6354]
    (.letOp (n := 6361) (.exec 0x123f56 (fun s => s.RIP = 0x123f56) (xorR32R32Effect 0x123f56 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[6358, 6354]
    (b_l121930_161))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_160 : List UInt8 :=
  [0x41, 0x01, 0xEF, 0x89, 0xCB, 0xC1, 0xC3, 0x15, 0x31, 0xFB, 0x89, 0xCF, 0xC1, 0xC7, 0x07, 0x31,
    0xDF, 0x44, 0x89, 0xC3, 0x31, 0xF3, 0x21, 0xCB, 0x31, 0xF3, 0x44, 0x01, 0xF8, 0x01, 0xD8, 0x01,
    0xC7, 0x81, 0xC7, 0xEB, 0x6C, 0x50, 0xA4, 0x44, 0x89, 0xC8, 0xC1, 0xC0, 0x1E, 0x44, 0x89, 0xCB,
    0xC1, 0xC3, 0x13, 0x31, 0xC3] ++ bytes_l121930_161

theorem code_l121930_160 : ∀ x ∈ codeRange 0x123f23 bytes_l121930_160, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23f23 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_161

def b_l121930_159 : Block Op Label signature Reg.count 6282 :=
  .letOp (n := 6282) (.out 0x123eea (movR32R32Effect 0x123eea 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 10] []) (.reg (.gpr 3))) #v[6126]
    (.letOp (n := 6283) (.exec 0x123eea (fun s => s.RIP = 0x123eea) (movR32R32Effect 0x123eea 3 3 10) (Reg.operands [.gpr 10] [])) #v[6126]
    (.letOp (n := 6284) (.out 0x123eed (andR32R32Effect 0x123eed 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[6282, 6039]
    (.letOp (n := 6285) (.exec 0x123eed (fun s => s.RIP = 0x123eed) (andR32R32Effect 0x123eed 2 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[6282, 6039]
    (.letOp (n := 6286) (.out 0x123eef (movR32R32Effect 0x123eef 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[6126]
    (.letOp (n := 6287) (.exec 0x123eef (fun s => s.RIP = 0x123eef) (movR32R32Effect 0x123eef 3 9 10) (Reg.operands [.gpr 10] [])) #v[6126]
    (.letOp (n := 6288) (.out 0x123ef2 (xorR32R32Effect 0x123ef2 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[6286, 6039]
    (.letOp (n := 6289) (.exec 0x123ef2 (fun s => s.RIP = 0x123ef2) (xorR32R32Effect 0x123ef2 3 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[6286, 6039]
    (.letOp (n := 6290) (.out 0x123ef5 (andR32R32Effect 0x123ef5 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[6288, 6212]
    (.letOp (n := 6291) (.exec 0x123ef5 (fun s => s.RIP = 0x123ef5) (andR32R32Effect 0x123ef5 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[6288, 6212]
    (.letOp (n := 6292) (.out 0x123ef8 (xorR32R32Effect 0x123ef8 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[6290, 6284]
    (.letOp (n := 6293) (.exec 0x123ef8 (fun s => s.RIP = 0x123ef8) (xorR32R32Effect 0x123ef8 3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[6290, 6284]
    (.letOp (n := 6294) (.out 0x123efb (addR32R32Effect 0x123efb 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[6292, 6280]
    (.letOp (n := 6295) (.exec 0x123efb (fun s => s.RIP = 0x123efb) (addR32R32Effect 0x123efb 3 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[6292, 6280]
    (.letOp (n := 6296) (.out 0x123efe (addR32R32Effect 0x123efe 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[5944, 6264]
    (.letOp (n := 6297) (.exec 0x123efe (fun s => s.RIP = 0x123efe) (addR32R32Effect 0x123efe 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[5944, 6264]
    (.letOp (n := 6298) (.out 0x123f00 (addR32R32Effect 0x123f00 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[6294, 6264]
    (.letOp (n := 6299) (.exec 0x123f00 (fun s => s.RIP = 0x123f00) (addR32R32Effect 0x123f00 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[6294, 6264]
    (.letOp (n := 6300) (.out 0x123f03 (movR32R32Effect 0x123f03 3 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 15] []) (.reg (.gpr 5))) #v[6150]
    (.letOp (n := 6301) (.exec 0x123f03 (fun s => s.RIP = 0x123f03) (movR32R32Effect 0x123f03 3 5 15) (Reg.operands [.gpr 15] [])) #v[6150]
    (.letOp (n := 6302) (.out 0x123f06 (movR32R32Effect 0x123f06 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[6150]
    (.letOp (n := 6303) (.exec 0x123f06 (fun s => s.RIP = 0x123f06) (movR32R32Effect 0x123f06 3 7 15) (Reg.operands [.gpr 15] [])) #v[6150]
    (.letOp (n := 6304) (.out 0x123f09 (rolR32Effect 0x123f09 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6302]
    (.letOp (n := 6305) (.exec 0x123f09 (fun s => s.RIP = 0x123f09) (rolR32Effect 0x123f09 3 7 15) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6302]
    (.letOp (n := 6306) (.out 0x123f0c (movR32R32Effect 0x123f0c 3 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[6150]
    (.letOp (n := 6307) (.exec 0x123f0c (fun s => s.RIP = 0x123f0c) (movR32R32Effect 0x123f0c 3 3 15) (Reg.operands [.gpr 15] [])) #v[6150]
    (.letOp (n := 6308) (.out 0x123f0f (rolR32Effect 0x123f0f 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6306]
    (.letOp (n := 6309) (.exec 0x123f0f (fun s => s.RIP = 0x123f0f) (rolR32Effect 0x123f0f 3 3 13) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6306]
    (.letOp (n := 6310) (.out 0x123f12 (xorR32R32Effect 0x123f12 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[6308, 6304]
    (.letOp (n := 6311) (.exec 0x123f12 (fun s => s.RIP = 0x123f12) (xorR32R32Effect 0x123f12 2 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[6308, 6304]
    (.letOp (n := 6312) (.out 0x123f14 (shrR32Effect 0x123f14 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[6300]
    (.letOp (n := 6313) (.exec 0x123f14 (fun s => s.RIP = 0x123f14) (shrR32Effect 0x123f14 3 5 10) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6300]
    (.letOp (n := 6314) (.out 0x123f17 (xorR32R32Effect 0x123f17 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[6312, 6310]
    (.letOp (n := 6315) (.exec 0x123f17 (fun s => s.RIP = 0x123f17) (xorR32R32Effect 0x123f17 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[6312, 6310]
    (.letOp (n := 6316) (.out 0x123f19 (movR32R32Effect 0x123f19 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[6296]
    (.letOp (n := 6317) (.exec 0x123f19 (fun s => s.RIP = 0x123f19) (movR32R32Effect 0x123f19 2 7 1) (Reg.operands [.gpr 1] [])) #v[6296]
    (.letOp (n := 6318) (.out 0x123f1b (rolR32Effect 0x123f1b 3 7 26) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6316]
    (.letOp (n := 6319) (.exec 0x123f1b (fun s => s.RIP = 0x123f1b) (rolR32Effect 0x123f1b 3 7 26) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6316]
    (.letOp (n := 6320) (.out 0x123f1e (movR32M32Effect 0x123f1e 15 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 6321) (.exec 0x123f1e (LoadPre 0x123f1e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x123f1e + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x123f1e 15 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l121930_160))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_159 : List UInt8 :=
  [0x44, 0x89, 0xD3, 0x21, 0xD3, 0x45, 0x89, 0xD1, 0x41, 0x31, 0xD1, 0x45, 0x21, 0xD9, 0x41, 0x31,
    0xD9, 0x45, 0x01, 0xF1, 0x01, 0xF9, 0x41, 0x01, 0xF9, 0x44, 0x89, 0xFD, 0x44, 0x89, 0xFF, 0xC1,
    0xC7, 0x0F, 0x44, 0x89, 0xFB, 0xC1, 0xC3, 0x0D, 0x31, 0xFB, 0xC1, 0xED, 0x0A, 0x31, 0xDD, 0x89,
    0xCF, 0xC1, 0xC7, 0x1A, 0x44, 0x8B, 0x7C, 0x24, 0x04] ++ bytes_l121930_160

theorem code_l121930_159 : ∀ x ∈ codeRange 0x123eea bytes_l121930_159, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23eea 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_160

def b_l121930_158 : Block Op Label signature Reg.count 6242 :=
  .letOp (n := 6242) (.out 0x123ea9 (xorR32R32Effect 0x123ea9 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[6240, 6232]
    (.letOp (n := 6243) (.exec 0x123ea9 (fun s => s.RIP = 0x123ea9) (xorR32R32Effect 0x123ea9 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[6240, 6232]
    (.letOp (n := 6244) (.out 0x123eac (movR32R32Effect 0x123eac 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[6210]
    (.letOp (n := 6245) (.exec 0x123eac (fun s => s.RIP = 0x123eac) (movR32R32Effect 0x123eac 3 7 8) (Reg.operands [.gpr 8] [])) #v[6210]
    (.letOp (n := 6246) (.out 0x123eaf (rolR32Effect 0x123eaf 3 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6244]
    (.letOp (n := 6247) (.exec 0x123eaf (fun s => s.RIP = 0x123eaf) (rolR32Effect 0x123eaf 3 7 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6244]
    (.letOp (n := 6248) (.out 0x123eb2 (xorR32R32Effect 0x123eb2 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[6246, 6242]
    (.letOp (n := 6249) (.exec 0x123eb2 (fun s => s.RIP = 0x123eb2) (xorR32R32Effect 0x123eb2 3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[6246, 6242]
    (.letOp (n := 6250) (.out 0x123eb5 (movR32R32Effect 0x123eb5 3 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6124]
    (.letOp (n := 6251) (.exec 0x123eb5 (fun s => s.RIP = 0x123eb5) (movR32R32Effect 0x123eb5 3 9 6) (Reg.operands [.gpr 6] [])) #v[6124]
    (.letOp (n := 6252) (.out 0x123eb8 (xorR32R32Effect 0x123eb8 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[6250, 6033]
    (.letOp (n := 6253) (.exec 0x123eb8 (fun s => s.RIP = 0x123eb8) (xorR32R32Effect 0x123eb8 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[6250, 6033]
    (.letOp (n := 6254) (.out 0x123ebb (andR32R32Effect 0x123ebb 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[6252, 6210]
    (.letOp (n := 6255) (.exec 0x123ebb (fun s => s.RIP = 0x123ebb) (andR32R32Effect 0x123ebb 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[6252, 6210]
    (.letOp (n := 6256) (.out 0x123ebe (xorR32R32Effect 0x123ebe 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[6254, 6033]
    (.letOp (n := 6257) (.exec 0x123ebe (fun s => s.RIP = 0x123ebe) (xorR32R32Effect 0x123ebe 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[6254, 6033]
    (.letOp (n := 6258) (.out 0x123ec1 (addR32R32Effect 0x123ec1 3 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[5942, 6236]
    (.letOp (n := 6259) (.exec 0x123ec1 (fun s => s.RIP = 0x123ec1) (addR32R32Effect 0x123ec1 3 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[5942, 6236]
    (.letOp (n := 6260) (.out 0x123ec4 (addR32R32Effect 0x123ec4 3 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[6258, 6256]
    (.letOp (n := 6261) (.exec 0x123ec4 (fun s => s.RIP = 0x123ec4) (addR32R32Effect 0x123ec4 3 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[6258, 6256]
    (.letOp (n := 6262) (.out 0x123ec7 (addR32R32Effect 0x123ec7 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[6248, 6260]
    (.letOp (n := 6263) (.exec 0x123ec7 (fun s => s.RIP = 0x123ec7) (addR32R32Effect 0x123ec7 3 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[6248, 6260]
    (.letOp (n := 6264) (.out 0x123eca (addR32Imm32Effect 0x123eca 6 7 0x90befffa) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[6262]
    (.letOp (n := 6265) (.exec 0x123eca (fun s => s.RIP = 0x123eca) (addR32Imm32Effect 0x123eca 6 7 0x90befffa) (Reg.operands [.gpr 7] [])) #v[6262]
    (.letOp (n := 6266) (.out 0x123ed0 (movR32R32Effect 0x123ed0 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 11] []) (.reg (.gpr 9))) #v[6212]
    (.letOp (n := 6267) (.exec 0x123ed0 (fun s => s.RIP = 0x123ed0) (movR32R32Effect 0x123ed0 3 9 11) (Reg.operands [.gpr 11] [])) #v[6212]
    (.letOp (n := 6268) (.out 0x123ed3 (rolR32Effect 0x123ed3 4 9 30) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[6266]
    (.letOp (n := 6269) (.exec 0x123ed3 (fun s => s.RIP = 0x123ed3) (rolR32Effect 0x123ed3 4 9 30) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6266]
    (.letOp (n := 6270) (.out 0x123ed7 (movR32R32Effect 0x123ed7 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[6212]
    (.letOp (n := 6271) (.exec 0x123ed7 (fun s => s.RIP = 0x123ed7) (movR32R32Effect 0x123ed7 3 3 11) (Reg.operands [.gpr 11] [])) #v[6212]
    (.letOp (n := 6272) (.out 0x123eda (rolR32Effect 0x123eda 3 3 19) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6270]
    (.letOp (n := 6273) (.exec 0x123eda (fun s => s.RIP = 0x123eda) (rolR32Effect 0x123eda 3 3 19) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6270]
    (.letOp (n := 6274) (.out 0x123edd (xorR32R32Effect 0x123edd 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[6272, 6268]
    (.letOp (n := 6275) (.exec 0x123edd (fun s => s.RIP = 0x123edd) (xorR32R32Effect 0x123edd 3 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[6272, 6268]
    (.letOp (n := 6276) (.out 0x123ee0 (movR32R32Effect 0x123ee0 3 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 11] []) (.reg (.gpr 14))) #v[6212]
    (.letOp (n := 6277) (.exec 0x123ee0 (fun s => s.RIP = 0x123ee0) (movR32R32Effect 0x123ee0 3 14 11) (Reg.operands [.gpr 11] [])) #v[6212]
    (.letOp (n := 6278) (.out 0x123ee3 (rolR32Effect 0x123ee3 4 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[6276]
    (.letOp (n := 6279) (.exec 0x123ee3 (fun s => s.RIP = 0x123ee3) (rolR32Effect 0x123ee3 4 14 10) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6276]
    (.letOp (n := 6280) (.out 0x123ee7 (xorR32R32Effect 0x123ee7 3 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[6278, 6274]
    (.letOp (n := 6281) (.exec 0x123ee7 (fun s => s.RIP = 0x123ee7) (xorR32R32Effect 0x123ee7 3 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[6278, 6274]
    (b_l121930_159))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_158 : List UInt8 :=
  [0x41, 0x31, 0xF9, 0x44, 0x89, 0xC7, 0xC1, 0xC7, 0x07, 0x44, 0x31, 0xCF, 0x41, 0x89, 0xF1, 0x41,
    0x31, 0xC1, 0x45, 0x21, 0xC1, 0x41, 0x31, 0xC1, 0x45, 0x01, 0xE5, 0x45, 0x01, 0xCD, 0x44, 0x01,
    0xEF, 0x81, 0xC7, 0xFA, 0xFF, 0xBE, 0x90, 0x45, 0x89, 0xD9, 0x41, 0xC1, 0xC1, 0x1E, 0x44, 0x89,
    0xDB, 0xC1, 0xC3, 0x13, 0x44, 0x31, 0xCB, 0x45, 0x89, 0xDE, 0x41, 0xC1, 0xC6, 0x0A, 0x41, 0x31,
    0xDE] ++ bytes_l121930_159

theorem code_l121930_158 : ∀ x ∈ codeRange 0x123ea9 bytes_l121930_158, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23ea9 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_159

def b_l121930_157 : Block Op Label signature Reg.count 6202 :=
  .letOp (n := 6202) (.out 0x123e6c (xorR32R32Effect 0x123e6c 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[6200, 5944]
    (.letOp (n := 6203) (.exec 0x123e6c (fun s => s.RIP = 0x123e6c) (xorR32R32Effect 0x123e6c 3 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[6200, 5944]
    (.letOp (n := 6204) (.out 0x123e6f (andR32R32Effect 0x123e6f 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[6202, 6126]
    (.letOp (n := 6205) (.exec 0x123e6f (fun s => s.RIP = 0x123e6f) (andR32R32Effect 0x123e6f 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[6202, 6126]
    (.letOp (n := 6206) (.out 0x123e72 (xorR32R32Effect 0x123e72 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[6204, 6198]
    (.letOp (n := 6207) (.exec 0x123e72 (fun s => s.RIP = 0x123e72) (xorR32R32Effect 0x123e72 3 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[6204, 6198]
    (.letOp (n := 6208) (.out 0x123e75 (addR32R32Effect 0x123e75 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[6206, 6194]
    (.letOp (n := 6209) (.exec 0x123e75 (fun s => s.RIP = 0x123e75) (addR32R32Effect 0x123e75 3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[6206, 6194]
    (.letOp (n := 6210) (.out 0x123e78 (addR32R32Effect 0x123e78 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[5861, 6178]
    (.letOp (n := 6211) (.exec 0x123e78 (fun s => s.RIP = 0x123e78) (addR32R32Effect 0x123e78 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[5861, 6178]
    (.letOp (n := 6212) (.out 0x123e7b (addR32R32Effect 0x123e7b 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[6208, 6178]
    (.letOp (n := 6213) (.exec 0x123e7b (fun s => s.RIP = 0x123e7b) (addR32R32Effect 0x123e7b 3 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[6208, 6178]
    (.letOp (n := 6214) (.out 0x123e7e (movR32R32Effect 0x123e7e 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 5] []) (.reg (.gpr 3))) #v[6064]
    (.letOp (n := 6215) (.exec 0x123e7e (fun s => s.RIP = 0x123e7e) (movR32R32Effect 0x123e7e 2 3 5) (Reg.operands [.gpr 5] [])) #v[6064]
    (.letOp (n := 6216) (.out 0x123e80 (movR32R32Effect 0x123e80 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[6064]
    (.letOp (n := 6217) (.exec 0x123e80 (fun s => s.RIP = 0x123e80) (movR32R32Effect 0x123e80 2 7 5) (Reg.operands [.gpr 5] [])) #v[6064]
    (.letOp (n := 6218) (.out 0x123e82 (rolR32Effect 0x123e82 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6216]
    (.letOp (n := 6219) (.exec 0x123e82 (fun s => s.RIP = 0x123e82) (rolR32Effect 0x123e82 3 7 15) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6216]
    (.letOp (n := 6220) (.out 0x123e85 (movR32R32Effect 0x123e85 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[6064]
    (.letOp (n := 6221) (.exec 0x123e85 (fun s => s.RIP = 0x123e85) (movR32R32Effect 0x123e85 3 9 5) (Reg.operands [.gpr 5] [])) #v[6064]
    (.letOp (n := 6222) (.out 0x123e88 (rolR32Effect 0x123e88 4 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[6220]
    (.letOp (n := 6223) (.exec 0x123e88 (fun s => s.RIP = 0x123e88) (rolR32Effect 0x123e88 4 9 13) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6220]
    (.letOp (n := 6224) (.out 0x123e8c (xorR32R32Effect 0x123e8c 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[6222, 6218]
    (.letOp (n := 6225) (.exec 0x123e8c (fun s => s.RIP = 0x123e8c) (xorR32R32Effect 0x123e8c 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[6222, 6218]
    (.letOp (n := 6226) (.out 0x123e8f (shrR32Effect 0x123e8f 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6214]
    (.letOp (n := 6227) (.exec 0x123e8f (fun s => s.RIP = 0x123e8f) (shrR32Effect 0x123e8f 3 3 10) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6214]
    (.letOp (n := 6228) (.out 0x123e92 (xorR32R32Effect 0x123e92 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[6226, 6224]
    (.letOp (n := 6229) (.exec 0x123e92 (fun s => s.RIP = 0x123e92) (xorR32R32Effect 0x123e92 3 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[6226, 6224]
    (.letOp (n := 6230) (.out 0x123e95 (movR32R32Effect 0x123e95 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[6210]
    (.letOp (n := 6231) (.exec 0x123e95 (fun s => s.RIP = 0x123e95) (movR32R32Effect 0x123e95 3 7 8) (Reg.operands [.gpr 8] [])) #v[6210]
    (.letOp (n := 6232) (.out 0x123e98 (rolR32Effect 0x123e98 3 7 26) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6230]
    (.letOp (n := 6233) (.exec 0x123e98 (fun s => s.RIP = 0x123e98) (rolR32Effect 0x123e98 3 7 26) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6230]
    (.letOp (n := 6234) (.out 0x123e9b (movR32M32Effect 0x123e9b 12 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 6235) (.exec 0x123e9b (LoadPre 0x123e9b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x123e9b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x123e9b 12 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 6236) (.out 0x123e9f (addR32R32Effect 0x123e9f 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[6234, 6228]
    (.letOp (n := 6237) (.exec 0x123e9f (fun s => s.RIP = 0x123e9f) (addR32R32Effect 0x123e9f 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[6234, 6228]
    (.letOp (n := 6238) (.out 0x123ea2 (movR32R32Effect 0x123ea2 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[6210]
    (.letOp (n := 6239) (.exec 0x123ea2 (fun s => s.RIP = 0x123ea2) (movR32R32Effect 0x123ea2 3 9 8) (Reg.operands [.gpr 8] [])) #v[6210]
    (.letOp (n := 6240) (.out 0x123ea5 (rolR32Effect 0x123ea5 4 9 21) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[6238]
    (.letOp (n := 6241) (.exec 0x123ea5 (fun s => s.RIP = 0x123ea5) (rolR32Effect 0x123ea5 4 9 21) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6238]
    (b_l121930_158))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_157 : List UInt8 :=
  [0x41, 0x31, 0xCB, 0x45, 0x21, 0xD3, 0x41, 0x31, 0xDB, 0x45, 0x01, 0xCB, 0x41, 0x01, 0xF8, 0x41,
    0x01, 0xFB, 0x89, 0xEB, 0x89, 0xEF, 0xC1, 0xC7, 0x0F, 0x41, 0x89, 0xE9, 0x41, 0xC1, 0xC1, 0x0D,
    0x41, 0x31, 0xF9, 0xC1, 0xEB, 0x0A, 0x44, 0x31, 0xCB, 0x44, 0x89, 0xC7, 0xC1, 0xC7, 0x1A, 0x44,
    0x8B, 0x24, 0x24, 0x41, 0x01, 0xDC, 0x45, 0x89, 0xC1, 0x41, 0xC1, 0xC1, 0x15] ++ bytes_l121930_158

theorem code_l121930_157 : ∀ x ∈ codeRange 0x123e6c bytes_l121930_157, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23e6c 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_158

def b_l121930_156 : Block Op Label signature Reg.count 6162 :=
  .letOp (n := 6162) (.out 0x123e2c (xorR32R32Effect 0x123e2c 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[6160, 6156]
    (.letOp (n := 6163) (.exec 0x123e2c (fun s => s.RIP = 0x123e2c) (xorR32R32Effect 0x123e2c 3 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[6160, 6156]
    (.letOp (n := 6164) (.out 0x123e2f (movR32R32Effect 0x123e2f 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[6033]
    (.letOp (n := 6165) (.exec 0x123e2f (fun s => s.RIP = 0x123e2f) (movR32R32Effect 0x123e2f 3 11 0) (Reg.operands [.gpr 0] [])) #v[6033]
    (.letOp (n := 6166) (.out 0x123e32 (xorR32R32Effect 0x123e32 3 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13] []) (.reg (.gpr 11))) #v[6164, 5942]
    (.letOp (n := 6167) (.exec 0x123e32 (fun s => s.RIP = 0x123e32) (xorR32R32Effect 0x123e32 3 11 13) (Reg.operands [.gpr 11, .gpr 13] [])) #v[6164, 5942]
    (.letOp (n := 6168) (.out 0x123e35 (andR32R32Effect 0x123e35 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[6166, 6124]
    (.letOp (n := 6169) (.exec 0x123e35 (fun s => s.RIP = 0x123e35) (andR32R32Effect 0x123e35 3 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[6166, 6124]
    (.letOp (n := 6170) (.out 0x123e38 (xorR32R32Effect 0x123e38 3 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13] []) (.reg (.gpr 11))) #v[6168, 5942]
    (.letOp (n := 6171) (.exec 0x123e38 (fun s => s.RIP = 0x123e38) (xorR32R32Effect 0x123e38 3 11 13) (Reg.operands [.gpr 11, .gpr 13] [])) #v[6168, 5942]
    (.letOp (n := 6172) (.out 0x123e3b (addR32R32Effect 0x123e3b 3 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[5855, 6150]
    (.letOp (n := 6173) (.exec 0x123e3b (fun s => s.RIP = 0x123e3b) (addR32R32Effect 0x123e3b 3 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[5855, 6150]
    (.letOp (n := 6174) (.out 0x123e3e (addR32R32Effect 0x123e3e 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[6172, 6170]
    (.letOp (n := 6175) (.exec 0x123e3e (fun s => s.RIP = 0x123e3e) (addR32R32Effect 0x123e3e 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[6172, 6170]
    (.letOp (n := 6176) (.out 0x123e41 (addR32R32Effect 0x123e41 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[6162, 6174]
    (.letOp (n := 6177) (.exec 0x123e41 (fun s => s.RIP = 0x123e41) (addR32R32Effect 0x123e41 3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[6162, 6174]
    (.letOp (n := 6178) (.out 0x123e44 (addR32Imm32Effect 0x123e44 6 7 0x8cc70208) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[6176]
    (.letOp (n := 6179) (.exec 0x123e44 (fun s => s.RIP = 0x123e44) (addR32Imm32Effect 0x123e44 6 7 0x8cc70208) (Reg.operands [.gpr 7] [])) #v[6176]
    (.letOp (n := 6180) (.out 0x123e4a (movR32R32Effect 0x123e4a 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[6126]
    (.letOp (n := 6181) (.exec 0x123e4a (fun s => s.RIP = 0x123e4a) (movR32R32Effect 0x123e4a 3 9 10) (Reg.operands [.gpr 10] [])) #v[6126]
    (.letOp (n := 6182) (.out 0x123e4d (rolR32Effect 0x123e4d 4 9 30) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[6180]
    (.letOp (n := 6183) (.exec 0x123e4d (fun s => s.RIP = 0x123e4d) (rolR32Effect 0x123e4d 4 9 30) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6180]
    (.letOp (n := 6184) (.out 0x123e51 (movR32R32Effect 0x123e51 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[6126]
    (.letOp (n := 6185) (.exec 0x123e51 (fun s => s.RIP = 0x123e51) (movR32R32Effect 0x123e51 3 11 10) (Reg.operands [.gpr 10] [])) #v[6126]
    (.letOp (n := 6186) (.out 0x123e54 (rolR32Effect 0x123e54 4 11 19) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[6184]
    (.letOp (n := 6187) (.exec 0x123e54 (fun s => s.RIP = 0x123e54) (rolR32Effect 0x123e54 4 11 19) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6184]
    (.letOp (n := 6188) (.out 0x123e58 (xorR32R32Effect 0x123e58 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[6186, 6182]
    (.letOp (n := 6189) (.exec 0x123e58 (fun s => s.RIP = 0x123e58) (xorR32R32Effect 0x123e58 3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[6186, 6182]
    (.letOp (n := 6190) (.out 0x123e5b (movR32R32Effect 0x123e5b 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[6126]
    (.letOp (n := 6191) (.exec 0x123e5b (fun s => s.RIP = 0x123e5b) (movR32R32Effect 0x123e5b 3 9 10) (Reg.operands [.gpr 10] [])) #v[6126]
    (.letOp (n := 6192) (.out 0x123e5e (rolR32Effect 0x123e5e 4 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[6190]
    (.letOp (n := 6193) (.exec 0x123e5e (fun s => s.RIP = 0x123e5e) (rolR32Effect 0x123e5e 4 9 10) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6190]
    (.letOp (n := 6194) (.out 0x123e62 (xorR32R32Effect 0x123e62 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[6192, 6188]
    (.letOp (n := 6195) (.exec 0x123e62 (fun s => s.RIP = 0x123e62) (xorR32R32Effect 0x123e62 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[6192, 6188]
    (.letOp (n := 6196) (.out 0x123e65 (movR32R32Effect 0x123e65 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[6039]
    (.letOp (n := 6197) (.exec 0x123e65 (fun s => s.RIP = 0x123e65) (movR32R32Effect 0x123e65 2 3 2) (Reg.operands [.gpr 2] [])) #v[6039]
    (.letOp (n := 6198) (.out 0x123e67 (andR32R32Effect 0x123e67 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[6196, 5944]
    (.letOp (n := 6199) (.exec 0x123e67 (fun s => s.RIP = 0x123e67) (andR32R32Effect 0x123e67 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[6196, 5944]
    (.letOp (n := 6200) (.out 0x123e69 (movR32R32Effect 0x123e69 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[6039]
    (.letOp (n := 6201) (.exec 0x123e69 (fun s => s.RIP = 0x123e69) (movR32R32Effect 0x123e69 3 11 2) (Reg.operands [.gpr 2] [])) #v[6039]
    (b_l121930_157))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_156 : List UInt8 :=
  [0x44, 0x31, 0xDF, 0x41, 0x89, 0xC3, 0x45, 0x31, 0xEB, 0x41, 0x21, 0xF3, 0x45, 0x31, 0xEB, 0x45,
    0x01, 0xF9, 0x45, 0x01, 0xD9, 0x44, 0x01, 0xCF, 0x81, 0xC7, 0x08, 0x02, 0xC7, 0x8C, 0x45, 0x89,
    0xD1, 0x41, 0xC1, 0xC1, 0x1E, 0x45, 0x89, 0xD3, 0x41, 0xC1, 0xC3, 0x13, 0x45, 0x31, 0xCB, 0x45,
    0x89, 0xD1, 0x41, 0xC1, 0xC1, 0x0A, 0x45, 0x31, 0xD9, 0x89, 0xD3, 0x21, 0xCB, 0x41, 0x89, 0xD3] ++ bytes_l121930_157

theorem code_l121930_156 : ∀ x ∈ codeRange 0x123e2c bytes_l121930_156, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23e2c 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_157

def b_l121930_155 : Block Op Label signature Reg.count 6122 :=
  .letOp (n := 6122) (.out 0x123df1 (addR32R32Effect 0x123df1 3 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[6120, 6108]
    (.letOp (n := 6123) (.exec 0x123df1 (fun s => s.RIP = 0x123df1) (addR32R32Effect 0x123df1 3 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[6120, 6108]
    (.letOp (n := 6124) (.out 0x123df4 (addR32R32Effect 0x123df4 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[5770, 6092]
    (.letOp (n := 6125) (.exec 0x123df4 (fun s => s.RIP = 0x123df4) (addR32R32Effect 0x123df4 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[5770, 6092]
    (.letOp (n := 6126) (.out 0x123df6 (addR32R32Effect 0x123df6 3 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[6122, 6092]
    (.letOp (n := 6127) (.exec 0x123df6 (fun s => s.RIP = 0x123df6) (addR32R32Effect 0x123df6 3 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[6122, 6092]
    (.letOp (n := 6128) (.out 0x123df9 (movR32R32Effect 0x123df9 3 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 14] []) (.reg (.gpr 3))) #v[5969]
    (.letOp (n := 6129) (.exec 0x123df9 (fun s => s.RIP = 0x123df9) (movR32R32Effect 0x123df9 3 3 14) (Reg.operands [.gpr 14] [])) #v[5969]
    (.letOp (n := 6130) (.out 0x123dfc (movR32R32Effect 0x123dfc 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[5969]
    (.letOp (n := 6131) (.exec 0x123dfc (fun s => s.RIP = 0x123dfc) (movR32R32Effect 0x123dfc 3 7 14) (Reg.operands [.gpr 14] [])) #v[5969]
    (.letOp (n := 6132) (.out 0x123dff (rolR32Effect 0x123dff 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6130]
    (.letOp (n := 6133) (.exec 0x123dff (fun s => s.RIP = 0x123dff) (rolR32Effect 0x123dff 3 7 15) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6130]
    (.letOp (n := 6134) (.out 0x123e02 (movR32R32Effect 0x123e02 3 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 14] []) (.reg (.gpr 11))) #v[5969]
    (.letOp (n := 6135) (.exec 0x123e02 (fun s => s.RIP = 0x123e02) (movR32R32Effect 0x123e02 3 11 14) (Reg.operands [.gpr 14] [])) #v[5969]
    (.letOp (n := 6136) (.out 0x123e05 (rolR32Effect 0x123e05 4 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[6134]
    (.letOp (n := 6137) (.exec 0x123e05 (fun s => s.RIP = 0x123e05) (rolR32Effect 0x123e05 4 11 13) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6134]
    (.letOp (n := 6138) (.out 0x123e09 (xorR32R32Effect 0x123e09 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[6136, 6132]
    (.letOp (n := 6139) (.exec 0x123e09 (fun s => s.RIP = 0x123e09) (xorR32R32Effect 0x123e09 3 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[6136, 6132]
    (.letOp (n := 6140) (.out 0x123e0c (shrR32Effect 0x123e0c 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6128]
    (.letOp (n := 6141) (.exec 0x123e0c (fun s => s.RIP = 0x123e0c) (shrR32Effect 0x123e0c 3 3 10) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6128]
    (.letOp (n := 6142) (.out 0x123e0f (xorR32R32Effect 0x123e0f 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[6140, 6138]
    (.letOp (n := 6143) (.exec 0x123e0f (fun s => s.RIP = 0x123e0f) (xorR32R32Effect 0x123e0f 3 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[6140, 6138]
    (.letOp (n := 6144) (.out 0x123e12 (movR32R32Effect 0x123e12 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6124]
    (.letOp (n := 6145) (.exec 0x123e12 (fun s => s.RIP = 0x123e12) (movR32R32Effect 0x123e12 2 7 6) (Reg.operands [.gpr 6] [])) #v[6124]
    (.letOp (n := 6146) (.out 0x123e14 (rolR32Effect 0x123e14 3 7 26) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6144]
    (.letOp (n := 6147) (.exec 0x123e14 (fun s => s.RIP = 0x123e14) (rolR32Effect 0x123e14 3 7 26) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6144]
    (.letOp (n := 6148) (.out 0x123e17 (movR32R32Effect 0x123e17 3 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[5694]
    (.letOp (n := 6149) (.exec 0x123e17 (fun s => s.RIP = 0x123e17) (movR32R32Effect 0x123e17 3 15 12) (Reg.operands [.gpr 12] [])) #v[5694]
    (.letOp (n := 6150) (.out 0x123e1a (addR32R32Effect 0x123e1a 3 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[6148, 6142]
    (.letOp (n := 6151) (.exec 0x123e1a (fun s => s.RIP = 0x123e1a) (addR32R32Effect 0x123e1a 3 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[6148, 6142]
    (.letOp (n := 6152) (.out 0x123e1d (movR32R32Effect 0x123e1d 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[6124]
    (.letOp (n := 6153) (.exec 0x123e1d (fun s => s.RIP = 0x123e1d) (movR32R32Effect 0x123e1d 3 11 6) (Reg.operands [.gpr 6] [])) #v[6124]
    (.letOp (n := 6154) (.out 0x123e20 (rolR32Effect 0x123e20 4 11 21) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[6152]
    (.letOp (n := 6155) (.exec 0x123e20 (fun s => s.RIP = 0x123e20) (rolR32Effect 0x123e20 4 11 21) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6152]
    (.letOp (n := 6156) (.out 0x123e24 (xorR32R32Effect 0x123e24 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[6154, 6146]
    (.letOp (n := 6157) (.exec 0x123e24 (fun s => s.RIP = 0x123e24) (xorR32R32Effect 0x123e24 3 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[6154, 6146]
    (.letOp (n := 6158) (.out 0x123e27 (movR32R32Effect 0x123e27 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6124]
    (.letOp (n := 6159) (.exec 0x123e27 (fun s => s.RIP = 0x123e27) (movR32R32Effect 0x123e27 2 7 6) (Reg.operands [.gpr 6] [])) #v[6124]
    (.letOp (n := 6160) (.out 0x123e29 (rolR32Effect 0x123e29 3 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6158]
    (.letOp (n := 6161) (.exec 0x123e29 (fun s => s.RIP = 0x123e29) (rolR32Effect 0x123e29 3 7 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6158]
    (b_l121930_156))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_155 : List UInt8 :=
  [0x41, 0x01, 0xDA, 0x01, 0xFE, 0x41, 0x01, 0xFA, 0x44, 0x89, 0xF3, 0x44, 0x89, 0xF7, 0xC1, 0xC7,
    0x0F, 0x45, 0x89, 0xF3, 0x41, 0xC1, 0xC3, 0x0D, 0x41, 0x31, 0xFB, 0xC1, 0xEB, 0x0A, 0x44, 0x31,
    0xDB, 0x89, 0xF7, 0xC1, 0xC7, 0x1A, 0x45, 0x89, 0xE7, 0x41, 0x01, 0xDF, 0x41, 0x89, 0xF3, 0x41,
    0xC1, 0xC3, 0x15, 0x41, 0x31, 0xFB, 0x89, 0xF7, 0xC1, 0xC7, 0x07] ++ bytes_l121930_156

theorem code_l121930_155 : ∀ x ∈ codeRange 0x123df1 bytes_l121930_155, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23df1 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_156

def b_l121930_154 : Block Op Label signature Reg.count 6082 :=
  .letOp (n := 6082) (.out 0x123db1 (andR32R32Effect 0x123db1 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[6080, 6033]
    (.letOp (n := 6083) (.exec 0x123db1 (fun s => s.RIP = 0x123db1) (andR32R32Effect 0x123db1 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[6080, 6033]
    (.letOp (n := 6084) (.out 0x123db3 (xorR32R32Effect 0x123db3 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[6082, 5855]
    (.letOp (n := 6085) (.exec 0x123db3 (fun s => s.RIP = 0x123db3) (xorR32R32Effect 0x123db3 3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[6082, 5855]
    (.letOp (n := 6086) (.out 0x123db6 (addR32R32Effect 0x123db6 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[5768, 6064]
    (.letOp (n := 6087) (.exec 0x123db6 (fun s => s.RIP = 0x123db6) (addR32R32Effect 0x123db6 3 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[5768, 6064]
    (.letOp (n := 6088) (.out 0x123db9 (addR32R32Effect 0x123db9 3 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[6086, 6084]
    (.letOp (n := 6089) (.exec 0x123db9 (fun s => s.RIP = 0x123db9) (addR32R32Effect 0x123db9 3 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[6086, 6084]
    (.letOp (n := 6090) (.out 0x123dbc (leaR32Effect 0x123dbc 4 7 (.sib 11 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 11, .gpr 10] []) (.reg (.gpr 7))) #v[6076, 6088]
    (.letOp (n := 6091) (.exec 0x123dbc (fun s => s.RIP = 0x123dbc) (leaR32Effect 0x123dbc 4 7 (.sib 11 (some 10) 0 .none)) (Reg.operands [.gpr 11, .gpr 10] [])) #v[6076, 6088]
    (.letOp (n := 6092) (.out 0x123dc0 (addR32Imm32Effect 0x123dc0 6 7 0x84c87814) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[6090]
    (.letOp (n := 6093) (.exec 0x123dc0 (fun s => s.RIP = 0x123dc0) (addR32Imm32Effect 0x123dc0 6 7 0x84c87814) (Reg.operands [.gpr 7] [])) #v[6090]
    (.letOp (n := 6094) (.out 0x123dc6 (movR32R32Effect 0x123dc6 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[6039]
    (.letOp (n := 6095) (.exec 0x123dc6 (fun s => s.RIP = 0x123dc6) (movR32R32Effect 0x123dc6 3 10 2) (Reg.operands [.gpr 2] [])) #v[6039]
    (.letOp (n := 6096) (.out 0x123dc9 (rolR32Effect 0x123dc9 4 10 30) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[6094]
    (.letOp (n := 6097) (.exec 0x123dc9 (fun s => s.RIP = 0x123dc9) (rolR32Effect 0x123dc9 4 10 30) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6094]
    (.letOp (n := 6098) (.out 0x123dcd (movR32R32Effect 0x123dcd 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[6039]
    (.letOp (n := 6099) (.exec 0x123dcd (fun s => s.RIP = 0x123dcd) (movR32R32Effect 0x123dcd 3 11 2) (Reg.operands [.gpr 2] [])) #v[6039]
    (.letOp (n := 6100) (.out 0x123dd0 (rolR32Effect 0x123dd0 4 11 19) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[6098]
    (.letOp (n := 6101) (.exec 0x123dd0 (fun s => s.RIP = 0x123dd0) (rolR32Effect 0x123dd0 4 11 19) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6098]
    (.letOp (n := 6102) (.out 0x123dd4 (xorR32R32Effect 0x123dd4 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[6100, 6096]
    (.letOp (n := 6103) (.exec 0x123dd4 (fun s => s.RIP = 0x123dd4) (xorR32R32Effect 0x123dd4 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[6100, 6096]
    (.letOp (n := 6104) (.out 0x123dd7 (movR32R32Effect 0x123dd7 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[6039]
    (.letOp (n := 6105) (.exec 0x123dd7 (fun s => s.RIP = 0x123dd7) (movR32R32Effect 0x123dd7 2 3 2) (Reg.operands [.gpr 2] [])) #v[6039]
    (.letOp (n := 6106) (.out 0x123dd9 (rolR32Effect 0x123dd9 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[6104]
    (.letOp (n := 6107) (.exec 0x123dd9 (fun s => s.RIP = 0x123dd9) (rolR32Effect 0x123dd9 3 3 10) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6104]
    (.letOp (n := 6108) (.out 0x123ddc (xorR32R32Effect 0x123ddc 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[6106, 6102]
    (.letOp (n := 6109) (.exec 0x123ddc (fun s => s.RIP = 0x123ddc) (xorR32R32Effect 0x123ddc 3 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[6106, 6102]
    (.letOp (n := 6110) (.out 0x123ddf (movR32R32Effect 0x123ddf 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[5944]
    (.letOp (n := 6111) (.exec 0x123ddf (fun s => s.RIP = 0x123ddf) (movR32R32Effect 0x123ddf 3 11 1) (Reg.operands [.gpr 1] [])) #v[5944]
    (.letOp (n := 6112) (.out 0x123de2 (andR32R32Effect 0x123de2 3 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[6110, 5861]
    (.letOp (n := 6113) (.exec 0x123de2 (fun s => s.RIP = 0x123de2) (andR32R32Effect 0x123de2 3 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[6110, 5861]
    (.letOp (n := 6114) (.out 0x123de5 (movR32R32Effect 0x123de5 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[5944]
    (.letOp (n := 6115) (.exec 0x123de5 (fun s => s.RIP = 0x123de5) (movR32R32Effect 0x123de5 3 10 1) (Reg.operands [.gpr 1] [])) #v[5944]
    (.letOp (n := 6116) (.out 0x123de8 (xorR32R32Effect 0x123de8 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[6114, 5861]
    (.letOp (n := 6117) (.exec 0x123de8 (fun s => s.RIP = 0x123de8) (xorR32R32Effect 0x123de8 3 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[6114, 5861]
    (.letOp (n := 6118) (.out 0x123deb (andR32R32Effect 0x123deb 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[6116, 6039]
    (.letOp (n := 6119) (.exec 0x123deb (fun s => s.RIP = 0x123deb) (andR32R32Effect 0x123deb 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[6116, 6039]
    (.letOp (n := 6120) (.out 0x123dee (xorR32R32Effect 0x123dee 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[6118, 6112]
    (.letOp (n := 6121) (.exec 0x123dee (fun s => s.RIP = 0x123dee) (xorR32R32Effect 0x123dee 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[6118, 6112]
    (b_l121930_155))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_154 : List UInt8 :=
  [0x21, 0xC7, 0x44, 0x31, 0xCF, 0x41, 0x01, 0xEA, 0x41, 0x01, 0xFA, 0x43, 0x8D, 0x3C, 0x13, 0x81,
    0xC7, 0x14, 0x78, 0xC8, 0x84, 0x41, 0x89, 0xD2, 0x41, 0xC1, 0xC2, 0x1E, 0x41, 0x89, 0xD3, 0x41,
    0xC1, 0xC3, 0x13, 0x45, 0x31, 0xD3, 0x89, 0xD3, 0xC1, 0xC3, 0x0A, 0x44, 0x31, 0xDB, 0x41, 0x89,
    0xCB, 0x45, 0x21, 0xC3, 0x41, 0x89, 0xCA, 0x45, 0x31, 0xC2, 0x41, 0x21, 0xD2, 0x45, 0x31, 0xDA] ++ bytes_l121930_155

theorem code_l121930_154 : ∀ x ∈ codeRange 0x123db1 bytes_l121930_154, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23db1 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_155

def b_l121930_153 : Block Op Label signature Reg.count 6043 :=
  .letOp (n := 6043) (.out 0x123d71 (rolR32Effect 0x123d71 4 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[6041]
    (.letOp (n := 6044) (.exec 0x123d71 (fun s => s.RIP = 0x123d71) (rolR32Effect 0x123d71 4 11 13) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6041]
    (.letOp (n := 6045) (.out 0x123d75 (xorR32R32Effect 0x123d75 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[6043, 6037]
    (.letOp (n := 6046) (.exec 0x123d75 (fun s => s.RIP = 0x123d75) (xorR32R32Effect 0x123d75 3 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[6043, 6037]
    (.letOp (n := 6047) (.out 0x123d78 (movR64M64Effect 0x123d78 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 6048) (.exec 0x123d78 (LoadPre 0x123d78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x123d78 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x123d78 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 6049) (.out 0x123d7d (addR32R32Effect 0x123d7d 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[6047, 5882]
    (.letOp (n := 6050) (.exec 0x123d7d (fun s => s.RIP = 0x123d7d) (addR32R32Effect 0x123d7d 2 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[6047, 5882]
    (.letOp (n := 6051) (.exec 0x123d7f (StorePre 0x123d7f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x123d7f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x123d7f 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[6049, 4]
    (.letOp (n := 6052) (.out 0x123d84 (movR32R32Effect 0x123d84 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5882]
    (.letOp (n := 6053) (.exec 0x123d84 (fun s => s.RIP = 0x123d84) (movR32R32Effect 0x123d84 2 7 5) (Reg.operands [.gpr 5] [])) #v[5882]
    (.letOp (n := 6054) (.out 0x123d86 (shrR32Effect 0x123d86 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6052]
    (.letOp (n := 6055) (.exec 0x123d86 (fun s => s.RIP = 0x123d86) (shrR32Effect 0x123d86 3 7 10) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6052]
    (.letOp (n := 6056) (.out 0x123d89 (xorR32R32Effect 0x123d89 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[6054, 6045]
    (.letOp (n := 6057) (.exec 0x123d89 (fun s => s.RIP = 0x123d89) (xorR32R32Effect 0x123d89 3 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[6054, 6045]
    (.letOp (n := 6058) (.out 0x123d8c (movR32R32Effect 0x123d8c 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[6033]
    (.letOp (n := 6059) (.exec 0x123d8c (fun s => s.RIP = 0x123d8c) (movR32R32Effect 0x123d8c 3 11 0) (Reg.operands [.gpr 0] [])) #v[6033]
    (.letOp (n := 6060) (.out 0x123d8f (rolR32Effect 0x123d8f 4 11 26) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[6058]
    (.letOp (n := 6061) (.exec 0x123d8f (fun s => s.RIP = 0x123d8f) (rolR32Effect 0x123d8f 4 11 26) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6058]
    (.letOp (n := 6062) (.out 0x123d93 (movR32M32LowEffect 0x123d93 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 6063) (.exec 0x123d93 (LoadPre 0x123d93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x123d93 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x123d93 5 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 6064) (.out 0x123d97 (addR32R32Effect 0x123d97 2 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 7] []) (.reg (.gpr 5))) #v[6062, 6056]
    (.letOp (n := 6065) (.exec 0x123d97 (fun s => s.RIP = 0x123d97) (addR32R32Effect 0x123d97 2 5 7) (Reg.operands [.gpr 5, .gpr 7] [])) #v[6062, 6056]
    (.letOp (n := 6066) (.out 0x123d99 (movR32R32Effect 0x123d99 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[6033]
    (.letOp (n := 6067) (.exec 0x123d99 (fun s => s.RIP = 0x123d99) (movR32R32Effect 0x123d99 2 7 0) (Reg.operands [.gpr 0] [])) #v[6033]
    (.letOp (n := 6068) (.out 0x123d9b (rolR32Effect 0x123d9b 3 7 21) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6066]
    (.letOp (n := 6069) (.exec 0x123d9b (fun s => s.RIP = 0x123d9b) (rolR32Effect 0x123d9b 3 7 21) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6066]
    (.letOp (n := 6070) (.out 0x123d9e (xorR32R32Effect 0x123d9e 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[6068, 6060]
    (.letOp (n := 6071) (.exec 0x123d9e (fun s => s.RIP = 0x123d9e) (xorR32R32Effect 0x123d9e 3 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[6068, 6060]
    (.letOp (n := 6072) (.out 0x123da1 (movR32R32Effect 0x123da1 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[6033]
    (.letOp (n := 6073) (.exec 0x123da1 (fun s => s.RIP = 0x123da1) (movR32R32Effect 0x123da1 3 11 0) (Reg.operands [.gpr 0] [])) #v[6033]
    (.letOp (n := 6074) (.out 0x123da4 (rolR32Effect 0x123da4 4 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[6072]
    (.letOp (n := 6075) (.exec 0x123da4 (fun s => s.RIP = 0x123da4) (rolR32Effect 0x123da4 4 11 7) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6072]
    (.letOp (n := 6076) (.out 0x123da8 (xorR32R32Effect 0x123da8 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[6074, 6070]
    (.letOp (n := 6077) (.exec 0x123da8 (fun s => s.RIP = 0x123da8) (xorR32R32Effect 0x123da8 3 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[6074, 6070]
    (.letOp (n := 6078) (.out 0x123dab (movR32R32Effect 0x123dab 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[5942]
    (.letOp (n := 6079) (.exec 0x123dab (fun s => s.RIP = 0x123dab) (movR32R32Effect 0x123dab 3 7 13) (Reg.operands [.gpr 13] [])) #v[5942]
    (.letOp (n := 6080) (.out 0x123dae (xorR32R32Effect 0x123dae 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[6078, 5855]
    (.letOp (n := 6081) (.exec 0x123dae (fun s => s.RIP = 0x123dae) (xorR32R32Effect 0x123dae 3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[6078, 5855]
    (b_l121930_154)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_153 : List UInt8 :=
  [0x41, 0xC1, 0xC3, 0x0D, 0x41, 0x31, 0xFB, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x01, 0xEF, 0x48, 0x89,
    0x7C, 0x24, 0x28, 0x89, 0xEF, 0xC1, 0xEF, 0x0A, 0x44, 0x31, 0xDF, 0x41, 0x89, 0xC3, 0x41, 0xC1,
    0xC3, 0x1A, 0x8B, 0x6C, 0x24, 0x58, 0x01, 0xFD, 0x89, 0xC7, 0xC1, 0xC7, 0x15, 0x44, 0x31, 0xDF,
    0x41, 0x89, 0xC3, 0x41, 0xC1, 0xC3, 0x07, 0x41, 0x31, 0xFB, 0x44, 0x89, 0xEF, 0x44, 0x31, 0xCF] ++ bytes_l121930_154

theorem code_l121930_153 : ∀ x ∈ codeRange 0x123d71 bytes_l121930_153, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23d71 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_154

def b_l121930_152 : Block Op Label signature Reg.count 6003 :=
  .letOp (n := 6003) (.out 0x123d3b (addR32R32Effect 0x123d3b 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[5997, 5985]
    (.letOp (n := 6004) (.exec 0x123d3b (fun s => s.RIP = 0x123d3b) (addR32R32Effect 0x123d3b 3 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[5997, 5985]
    (.letOp (n := 6005) (.out 0x123d3e (addR32Imm32Effect 0x123d3e 7 11 0x78a5636f) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[6003]
    (.letOp (n := 6006) (.exec 0x123d3e (fun s => s.RIP = 0x123d3e) (addR32Imm32Effect 0x123d3e 7 11 0x78a5636f) (Reg.operands [.gpr 11] [])) #v[6003]
    (.letOp (n := 6007) (.out 0x123d45 (movR32R32Effect 0x123d45 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[5944]
    (.letOp (n := 6008) (.exec 0x123d45 (fun s => s.RIP = 0x123d45) (movR32R32Effect 0x123d45 2 2 1) (Reg.operands [.gpr 1] [])) #v[5944]
    (.letOp (n := 6009) (.out 0x123d47 (rolR32Effect 0x123d47 3 2 19) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[6007]
    (.letOp (n := 6010) (.exec 0x123d47 (fun s => s.RIP = 0x123d47) (rolR32Effect 0x123d47 3 2 19) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6007]
    (.letOp (n := 6011) (.out 0x123d4a (xorR32R32Effect 0x123d4a 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[6009, 6001]
    (.letOp (n := 6012) (.exec 0x123d4a (fun s => s.RIP = 0x123d4a) (xorR32R32Effect 0x123d4a 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[6009, 6001]
    (.letOp (n := 6013) (.out 0x123d4c (movR32R32Effect 0x123d4c 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[5944]
    (.letOp (n := 6014) (.exec 0x123d4c (fun s => s.RIP = 0x123d4c) (movR32R32Effect 0x123d4c 2 7 1) (Reg.operands [.gpr 1] [])) #v[5944]
    (.letOp (n := 6015) (.out 0x123d4e (rolR32Effect 0x123d4e 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6013]
    (.letOp (n := 6016) (.exec 0x123d4e (fun s => s.RIP = 0x123d4e) (rolR32Effect 0x123d4e 3 7 10) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6013]
    (.letOp (n := 6017) (.out 0x123d51 (xorR32R32Effect 0x123d51 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[6015, 6011]
    (.letOp (n := 6018) (.exec 0x123d51 (fun s => s.RIP = 0x123d51) (xorR32R32Effect 0x123d51 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[6015, 6011]
    (.letOp (n := 6019) (.out 0x123d53 (movR32R32Effect 0x123d53 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[5861]
    (.letOp (n := 6020) (.exec 0x123d53 (fun s => s.RIP = 0x123d53) (movR32R32Effect 0x123d53 3 3 8) (Reg.operands [.gpr 8] [])) #v[5861]
    (.letOp (n := 6021) (.out 0x123d56 (andR32R32Effect 0x123d56 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[6019, 5770]
    (.letOp (n := 6022) (.exec 0x123d56 (fun s => s.RIP = 0x123d56) (andR32R32Effect 0x123d56 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[6019, 5770]
    (.letOp (n := 6023) (.out 0x123d58 (movR32R32Effect 0x123d58 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[5861]
    (.letOp (n := 6024) (.exec 0x123d58 (fun s => s.RIP = 0x123d58) (movR32R32Effect 0x123d58 3 2 8) (Reg.operands [.gpr 8] [])) #v[5861]
    (.letOp (n := 6025) (.out 0x123d5b (xorR32R32Effect 0x123d5b 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[6023, 5770]
    (.letOp (n := 6026) (.exec 0x123d5b (fun s => s.RIP = 0x123d5b) (xorR32R32Effect 0x123d5b 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[6023, 5770]
    (.letOp (n := 6027) (.out 0x123d5d (andR32R32Effect 0x123d5d 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[6025, 5944]
    (.letOp (n := 6028) (.exec 0x123d5d (fun s => s.RIP = 0x123d5d) (andR32R32Effect 0x123d5d 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[6025, 5944]
    (.letOp (n := 6029) (.out 0x123d5f (xorR32R32Effect 0x123d5f 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[6027, 6021]
    (.letOp (n := 6030) (.exec 0x123d5f (fun s => s.RIP = 0x123d5f) (xorR32R32Effect 0x123d5f 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[6027, 6021]
    (.letOp (n := 6031) (.out 0x123d61 (addR32R32Effect 0x123d61 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[6029, 6017]
    (.letOp (n := 6032) (.exec 0x123d61 (fun s => s.RIP = 0x123d61) (addR32R32Effect 0x123d61 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[6029, 6017]
    (.letOp (n := 6033) (.out 0x123d63 (addR32R32Effect 0x123d63 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[5684, 6005]
    (.letOp (n := 6034) (.exec 0x123d63 (fun s => s.RIP = 0x123d63) (addR32R32Effect 0x123d63 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[5684, 6005]
    (.letOp (n := 6035) (.out 0x123d66 (movR32R32Effect 0x123d66 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5882]
    (.letOp (n := 6036) (.exec 0x123d66 (fun s => s.RIP = 0x123d66) (movR32R32Effect 0x123d66 2 7 5) (Reg.operands [.gpr 5] [])) #v[5882]
    (.letOp (n := 6037) (.out 0x123d68 (rolR32Effect 0x123d68 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[6035]
    (.letOp (n := 6038) (.exec 0x123d68 (fun s => s.RIP = 0x123d68) (rolR32Effect 0x123d68 3 7 15) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6035]
    (.letOp (n := 6039) (.out 0x123d6b (addR32R32Effect 0x123d6b 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[6031, 6005]
    (.letOp (n := 6040) (.exec 0x123d6b (fun s => s.RIP = 0x123d6b) (addR32R32Effect 0x123d6b 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[6031, 6005]
    (.letOp (n := 6041) (.out 0x123d6e (movR32R32Effect 0x123d6e 3 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 5] []) (.reg (.gpr 11))) #v[5882]
    (.letOp (n := 6042) (.exec 0x123d6e (fun s => s.RIP = 0x123d6e) (movR32R32Effect 0x123d6e 3 11 5) (Reg.operands [.gpr 5] [])) #v[5882]
    (b_l121930_153))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_152 : List UInt8 :=
  [0x41, 0x01, 0xD3, 0x41, 0x81, 0xC3, 0x6F, 0x63, 0xA5, 0x78, 0x89, 0xCA, 0xC1, 0xC2, 0x13, 0x31,
    0xFA, 0x89, 0xCF, 0xC1, 0xC7, 0x0A, 0x31, 0xD7, 0x44, 0x89, 0xC3, 0x21, 0xF3, 0x44, 0x89, 0xC2,
    0x31, 0xF2, 0x21, 0xCA, 0x31, 0xDA, 0x01, 0xFA, 0x44, 0x01, 0xD8, 0x89, 0xEF, 0xC1, 0xC7, 0x0F,
    0x44, 0x01, 0xDA, 0x41, 0x89, 0xEB] ++ bytes_l121930_153

theorem code_l121930_152 : ∀ x ∈ codeRange 0x123d3b bytes_l121930_152, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23d3b 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_153

def b_l121930_151 : Block Op Label signature Reg.count 5963 :=
  .letOp (n := 5963) (.out 0x123cfe (shrR32Effect 0x123cfe 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5961]
    (.letOp (n := 5964) (.exec 0x123cfe (fun s => s.RIP = 0x123cfe) (shrR32Effect 0x123cfe 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5961]
    (.letOp (n := 5965) (.out 0x123d01 (xorR32R32Effect 0x123d01 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[5963, 5954]
    (.letOp (n := 5966) (.exec 0x123d01 (fun s => s.RIP = 0x123d01) (xorR32R32Effect 0x123d01 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[5963, 5954]
    (.letOp (n := 5967) (.out 0x123d03 (movR32M32Effect 0x123d03 14 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 5968) (.exec 0x123d03 (LoadPre 0x123d03 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x123d03 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x123d03 14 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5969) (.out 0x123d0b (addR32R32Effect 0x123d0b 3 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[5967, 5965]
    (.letOp (n := 5970) (.exec 0x123d0b (fun s => s.RIP = 0x123d0b) (addR32R32Effect 0x123d0b 3 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[5967, 5965]
    (.letOp (n := 5971) (.out 0x123d0e (movR32R32Effect 0x123d0e 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[5942]
    (.letOp (n := 5972) (.exec 0x123d0e (fun s => s.RIP = 0x123d0e) (movR32R32Effect 0x123d0e 3 2 13) (Reg.operands [.gpr 13] [])) #v[5942]
    (.letOp (n := 5973) (.out 0x123d11 (rolR32Effect 0x123d11 3 2 26) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5971]
    (.letOp (n := 5974) (.exec 0x123d11 (fun s => s.RIP = 0x123d11) (rolR32Effect 0x123d11 3 2 26) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5971]
    (.letOp (n := 5975) (.out 0x123d14 (movR32R32Effect 0x123d14 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[5942]
    (.letOp (n := 5976) (.exec 0x123d14 (fun s => s.RIP = 0x123d14) (movR32R32Effect 0x123d14 3 7 13) (Reg.operands [.gpr 13] [])) #v[5942]
    (.letOp (n := 5977) (.out 0x123d17 (rolR32Effect 0x123d17 3 7 21) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[5975]
    (.letOp (n := 5978) (.exec 0x123d17 (fun s => s.RIP = 0x123d17) (rolR32Effect 0x123d17 3 7 21) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5975]
    (.letOp (n := 5979) (.out 0x123d1a (xorR32R32Effect 0x123d1a 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[5977, 5973]
    (.letOp (n := 5980) (.exec 0x123d1a (fun s => s.RIP = 0x123d1a) (xorR32R32Effect 0x123d1a 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[5977, 5973]
    (.letOp (n := 5981) (.out 0x123d1c (movR32R32Effect 0x123d1c 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[5942]
    (.letOp (n := 5982) (.exec 0x123d1c (fun s => s.RIP = 0x123d1c) (movR32R32Effect 0x123d1c 3 2 13) (Reg.operands [.gpr 13] [])) #v[5942]
    (.letOp (n := 5983) (.out 0x123d1f (rolR32Effect 0x123d1f 3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5981]
    (.letOp (n := 5984) (.exec 0x123d1f (fun s => s.RIP = 0x123d1f) (rolR32Effect 0x123d1f 3 2 7) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5981]
    (.letOp (n := 5985) (.out 0x123d22 (xorR32R32Effect 0x123d22 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[5983, 5979]
    (.letOp (n := 5986) (.exec 0x123d22 (fun s => s.RIP = 0x123d22) (xorR32R32Effect 0x123d22 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[5983, 5979]
    (.letOp (n := 5987) (.out 0x123d24 (movR32R32Effect 0x123d24 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[5855]
    (.letOp (n := 5988) (.exec 0x123d24 (fun s => s.RIP = 0x123d24) (movR32R32Effect 0x123d24 3 7 9) (Reg.operands [.gpr 9] [])) #v[5855]
    (.letOp (n := 5989) (.out 0x123d27 (xorR32R32Effect 0x123d27 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[5987, 5768]
    (.letOp (n := 5990) (.exec 0x123d27 (fun s => s.RIP = 0x123d27) (xorR32R32Effect 0x123d27 3 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[5987, 5768]
    (.letOp (n := 5991) (.out 0x123d2a (andR32R32Effect 0x123d2a 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[5989, 5942]
    (.letOp (n := 5992) (.exec 0x123d2a (fun s => s.RIP = 0x123d2a) (andR32R32Effect 0x123d2a 3 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[5989, 5942]
    (.letOp (n := 5993) (.out 0x123d2d (xorR32R32Effect 0x123d2d 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[5991, 5768]
    (.letOp (n := 5994) (.exec 0x123d2d (fun s => s.RIP = 0x123d2d) (xorR32R32Effect 0x123d2d 3 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[5991, 5768]
    (.letOp (n := 5995) (.out 0x123d30 (addR32R32Effect 0x123d30 3 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[5678, 5969]
    (.letOp (n := 5996) (.exec 0x123d30 (fun s => s.RIP = 0x123d30) (addR32R32Effect 0x123d30 3 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[5678, 5969]
    (.letOp (n := 5997) (.out 0x123d33 (addR32R32Effect 0x123d33 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[5995, 5993]
    (.letOp (n := 5998) (.exec 0x123d33 (fun s => s.RIP = 0x123d33) (addR32R32Effect 0x123d33 3 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[5995, 5993]
    (.letOp (n := 5999) (.out 0x123d36 (movR32R32Effect 0x123d36 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[5944]
    (.letOp (n := 6000) (.exec 0x123d36 (fun s => s.RIP = 0x123d36) (movR32R32Effect 0x123d36 2 7 1) (Reg.operands [.gpr 1] [])) #v[5944]
    (.letOp (n := 6001) (.out 0x123d38 (rolR32Effect 0x123d38 3 7 30) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[5999]
    (.letOp (n := 6002) (.exec 0x123d38 (fun s => s.RIP = 0x123d38) (rolR32Effect 0x123d38 3 7 30) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5999]
    (b_l121930_152))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_151 : List UInt8 :=
  [0xC1, 0xEA, 0x0A, 0x31, 0xFA, 0x44, 0x8B, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x41, 0x01, 0xD6,
    0x44, 0x89, 0xEA, 0xC1, 0xC2, 0x1A, 0x44, 0x89, 0xEF, 0xC1, 0xC7, 0x15, 0x31, 0xD7, 0x44, 0x89,
    0xEA, 0xC1, 0xC2, 0x07, 0x31, 0xFA, 0x44, 0x89, 0xCF, 0x44, 0x31, 0xD7, 0x44, 0x21, 0xEF, 0x44,
    0x31, 0xD7, 0x45, 0x01, 0xF3, 0x41, 0x01, 0xFB, 0x89, 0xCF, 0xC1, 0xC7, 0x1E] ++ bytes_l121930_152

theorem code_l121930_151 : ∀ x ∈ codeRange 0x123cfe bytes_l121930_151, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23cfe 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_152

def b_l121930_150 : Block Op Label signature Reg.count 5924 :=
  .letOp (n := 5924) (.out 0x123cc7 (rolR32Effect 0x123cc7 3 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[5922]
    (.letOp (n := 5925) (.exec 0x123cc7 (fun s => s.RIP = 0x123cc7) (rolR32Effect 0x123cc7 3 3 10) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5922]
    (.letOp (n := 5926) (.out 0x123cca (xorR32R32Effect 0x123cca 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[5924, 5920]
    (.letOp (n := 5927) (.exec 0x123cca (fun s => s.RIP = 0x123cca) (xorR32R32Effect 0x123cca 2 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[5924, 5920]
    (.letOp (n := 5928) (.out 0x123ccc (movR32R32Effect 0x123ccc 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[5770]
    (.letOp (n := 5929) (.exec 0x123ccc (fun s => s.RIP = 0x123ccc) (movR32R32Effect 0x123ccc 2 7 6) (Reg.operands [.gpr 6] [])) #v[5770]
    (.letOp (n := 5930) (.out 0x123cce (andR32R32Effect 0x123cce 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[5928, 5684]
    (.letOp (n := 5931) (.exec 0x123cce (fun s => s.RIP = 0x123cce) (andR32R32Effect 0x123cce 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[5928, 5684]
    (.letOp (n := 5932) (.out 0x123cd0 (movR32R32Effect 0x123cd0 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[5770]
    (.letOp (n := 5933) (.exec 0x123cd0 (fun s => s.RIP = 0x123cd0) (movR32R32Effect 0x123cd0 2 1 6) (Reg.operands [.gpr 6] [])) #v[5770]
    (.letOp (n := 5934) (.out 0x123cd2 (xorR32R32Effect 0x123cd2 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[5932, 5684]
    (.letOp (n := 5935) (.exec 0x123cd2 (fun s => s.RIP = 0x123cd2) (xorR32R32Effect 0x123cd2 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5932, 5684]
    (.letOp (n := 5936) (.out 0x123cd4 (andR32R32Effect 0x123cd4 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[5934, 5861]
    (.letOp (n := 5937) (.exec 0x123cd4 (fun s => s.RIP = 0x123cd4) (andR32R32Effect 0x123cd4 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[5934, 5861]
    (.letOp (n := 5938) (.out 0x123cd7 (xorR32R32Effect 0x123cd7 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[5936, 5930]
    (.letOp (n := 5939) (.exec 0x123cd7 (fun s => s.RIP = 0x123cd7) (xorR32R32Effect 0x123cd7 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[5936, 5930]
    (.letOp (n := 5940) (.out 0x123cd9 (addR32R32Effect 0x123cd9 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[5938, 5926]
    (.letOp (n := 5941) (.exec 0x123cd9 (fun s => s.RIP = 0x123cd9) (addR32R32Effect 0x123cd9 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[5938, 5926]
    (.letOp (n := 5942) (.out 0x123cdb (addR32R32Effect 0x123cdb 3 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[5593, 5910]
    (.letOp (n := 5943) (.exec 0x123cdb (fun s => s.RIP = 0x123cdb) (addR32R32Effect 0x123cdb 3 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[5593, 5910]
    (.letOp (n := 5944) (.out 0x123cde (addR32R32Effect 0x123cde 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[5940, 5910]
    (.letOp (n := 5945) (.exec 0x123cde (fun s => s.RIP = 0x123cde) (addR32R32Effect 0x123cde 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[5940, 5910]
    (.letOp (n := 5946) (.out 0x123ce0 (movR32R32Effect 0x123ce0 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[5791]
    (.letOp (n := 5947) (.exec 0x123ce0 (fun s => s.RIP = 0x123ce0) (movR32R32Effect 0x123ce0 3 2 14) (Reg.operands [.gpr 14] [])) #v[5791]
    (.letOp (n := 5948) (.out 0x123ce3 (rolR32Effect 0x123ce3 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5946]
    (.letOp (n := 5949) (.exec 0x123ce3 (fun s => s.RIP = 0x123ce3) (rolR32Effect 0x123ce3 3 2 15) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5946]
    (.letOp (n := 5950) (.out 0x123ce6 (movR32R32Effect 0x123ce6 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[5791]
    (.letOp (n := 5951) (.exec 0x123ce6 (fun s => s.RIP = 0x123ce6) (movR32R32Effect 0x123ce6 3 7 14) (Reg.operands [.gpr 14] [])) #v[5791]
    (.letOp (n := 5952) (.out 0x123ce9 (rolR32Effect 0x123ce9 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[5950]
    (.letOp (n := 5953) (.exec 0x123ce9 (fun s => s.RIP = 0x123ce9) (rolR32Effect 0x123ce9 3 7 13) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5950]
    (.letOp (n := 5954) (.out 0x123cec (xorR32R32Effect 0x123cec 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[5952, 5948]
    (.letOp (n := 5955) (.exec 0x123cec (fun s => s.RIP = 0x123cec) (xorR32R32Effect 0x123cec 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[5952, 5948]
    (.letOp (n := 5956) (.out 0x123cee (movR64M64Effect 0x123cee 2 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 5957) (.exec 0x123cee (LoadPre 0x123cee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x123cee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x123cee 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5958) (.out 0x123cf3 (addR32R32Effect 0x123cf3 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[5956, 5791]
    (.letOp (n := 5959) (.exec 0x123cf3 (fun s => s.RIP = 0x123cf3) (addR32R32Effect 0x123cf3 3 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[5956, 5791]
    (.letOp (n := 5960) (.exec 0x123cf6 (StorePre 0x123cf6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x123cf6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x123cf6 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5958, 4]
    (.letOp (n := 5961) (.out 0x123cfb (movR32R32Effect 0x123cfb 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[5791]
    (.letOp (n := 5962) (.exec 0x123cfb (fun s => s.RIP = 0x123cfb) (movR32R32Effect 0x123cfb 3 2 14) (Reg.operands [.gpr 14] [])) #v[5791]
    (b_l121930_151)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_150 : List UInt8 :=
  [0xC1, 0xC3, 0x0A, 0x31, 0xFB, 0x89, 0xF7, 0x21, 0xC7, 0x89, 0xF1, 0x31, 0xC1, 0x44, 0x21, 0xC1,
    0x31, 0xF9, 0x01, 0xD9, 0x41, 0x01, 0xD5, 0x01, 0xD1, 0x44, 0x89, 0xF2, 0xC1, 0xC2, 0x0F, 0x44,
    0x89, 0xF7, 0xC1, 0xC7, 0x0D, 0x31, 0xD7, 0x48, 0x8B, 0x54, 0x24, 0x40, 0x44, 0x01, 0xF2, 0x48,
    0x89, 0x54, 0x24, 0x40, 0x44, 0x89, 0xF2] ++ bytes_l121930_151

theorem code_l121930_150 : ∀ x ∈ codeRange 0x123cc7 bytes_l121930_150, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23cc7 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_151

def b_l121930_149 : Block Op Label signature Reg.count 5884 :=
  .letOp (n := 5884) (.out 0x123c8d (movR32R32Effect 0x123c8d 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[5855]
    (.letOp (n := 5885) (.exec 0x123c8d (fun s => s.RIP = 0x123c8d) (movR32R32Effect 0x123c8d 3 2 9) (Reg.operands [.gpr 9] [])) #v[5855]
    (.letOp (n := 5886) (.out 0x123c90 (rolR32Effect 0x123c90 3 2 21) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5884]
    (.letOp (n := 5887) (.exec 0x123c90 (fun s => s.RIP = 0x123c90) (rolR32Effect 0x123c90 3 2 21) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5884]
    (.letOp (n := 5888) (.out 0x123c93 (xorR32R32Effect 0x123c93 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[5886, 5878]
    (.letOp (n := 5889) (.exec 0x123c93 (fun s => s.RIP = 0x123c93) (xorR32R32Effect 0x123c93 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[5886, 5878]
    (.letOp (n := 5890) (.out 0x123c95 (movR32R32Effect 0x123c95 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[5855]
    (.letOp (n := 5891) (.exec 0x123c95 (fun s => s.RIP = 0x123c95) (movR32R32Effect 0x123c95 3 1 9) (Reg.operands [.gpr 9] [])) #v[5855]
    (.letOp (n := 5892) (.out 0x123c98 (rolR32Effect 0x123c98 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5890]
    (.letOp (n := 5893) (.exec 0x123c98 (fun s => s.RIP = 0x123c98) (rolR32Effect 0x123c98 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5890]
    (.letOp (n := 5894) (.out 0x123c9b (xorR32R32Effect 0x123c9b 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[5892, 5888]
    (.letOp (n := 5895) (.exec 0x123c9b (fun s => s.RIP = 0x123c9b) (xorR32R32Effect 0x123c9b 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[5892, 5888]
    (.letOp (n := 5896) (.out 0x123c9d (movR32R32Effect 0x123c9d 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[5768]
    (.letOp (n := 5897) (.exec 0x123c9d (fun s => s.RIP = 0x123c9d) (movR32R32Effect 0x123c9d 3 2 10) (Reg.operands [.gpr 10] [])) #v[5768]
    (.letOp (n := 5898) (.out 0x123ca0 (xorR32R32Effect 0x123ca0 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[5896, 5678]
    (.letOp (n := 5899) (.exec 0x123ca0 (fun s => s.RIP = 0x123ca0) (xorR32R32Effect 0x123ca0 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[5896, 5678]
    (.letOp (n := 5900) (.out 0x123ca3 (andR32R32Effect 0x123ca3 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[5898, 5855]
    (.letOp (n := 5901) (.exec 0x123ca3 (fun s => s.RIP = 0x123ca3) (andR32R32Effect 0x123ca3 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[5898, 5855]
    (.letOp (n := 5902) (.out 0x123ca6 (xorR32R32Effect 0x123ca6 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[5900, 5678]
    (.letOp (n := 5903) (.exec 0x123ca6 (fun s => s.RIP = 0x123ca6) (xorR32R32Effect 0x123ca6 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[5900, 5678]
    (.letOp (n := 5904) (.out 0x123ca9 (addR32R32Effect 0x123ca9 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[5591, 5882]
    (.letOp (n := 5905) (.exec 0x123ca9 (fun s => s.RIP = 0x123ca9) (addR32R32Effect 0x123ca9 2 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[5591, 5882]
    (.letOp (n := 5906) (.out 0x123cab (addR32R32Effect 0x123cab 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[5904, 5902]
    (.letOp (n := 5907) (.exec 0x123cab (fun s => s.RIP = 0x123cab) (addR32R32Effect 0x123cab 2 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[5904, 5902]
    (.letOp (n := 5908) (.out 0x123cad (leaR32Effect 0x123cad 3 2 (.sib 1 (some 3) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 3] []) (.reg (.gpr 2))) #v[5894, 5906]
    (.letOp (n := 5909) (.exec 0x123cad (fun s => s.RIP = 0x123cad) (leaR32Effect 0x123cad 3 2 (.sib 1 (some 3) 0 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[5894, 5906]
    (.letOp (n := 5910) (.out 0x123cb0 (addR32Imm32Effect 0x123cb0 6 2 0x748f82ee) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[5908]
    (.letOp (n := 5911) (.exec 0x123cb0 (fun s => s.RIP = 0x123cb0) (addR32Imm32Effect 0x123cb0 6 2 0x748f82ee) (Reg.operands [.gpr 2] [])) #v[5908]
    (.letOp (n := 5912) (.out 0x123cb6 (movR32R32Effect 0x123cb6 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[5861]
    (.letOp (n := 5913) (.exec 0x123cb6 (fun s => s.RIP = 0x123cb6) (movR32R32Effect 0x123cb6 3 1 8) (Reg.operands [.gpr 8] [])) #v[5861]
    (.letOp (n := 5914) (.out 0x123cb9 (rolR32Effect 0x123cb9 3 1 30) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5912]
    (.letOp (n := 5915) (.exec 0x123cb9 (fun s => s.RIP = 0x123cb9) (rolR32Effect 0x123cb9 3 1 30) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5912]
    (.letOp (n := 5916) (.out 0x123cbc (movR32R32Effect 0x123cbc 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[5861]
    (.letOp (n := 5917) (.exec 0x123cbc (fun s => s.RIP = 0x123cbc) (movR32R32Effect 0x123cbc 3 7 8) (Reg.operands [.gpr 8] [])) #v[5861]
    (.letOp (n := 5918) (.out 0x123cbf (rolR32Effect 0x123cbf 3 7 19) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[5916]
    (.letOp (n := 5919) (.exec 0x123cbf (fun s => s.RIP = 0x123cbf) (rolR32Effect 0x123cbf 3 7 19) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5916]
    (.letOp (n := 5920) (.out 0x123cc2 (xorR32R32Effect 0x123cc2 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[5918, 5914]
    (.letOp (n := 5921) (.exec 0x123cc2 (fun s => s.RIP = 0x123cc2) (xorR32R32Effect 0x123cc2 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[5918, 5914]
    (.letOp (n := 5922) (.out 0x123cc4 (movR32R32Effect 0x123cc4 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[5861]
    (.letOp (n := 5923) (.exec 0x123cc4 (fun s => s.RIP = 0x123cc4) (movR32R32Effect 0x123cc4 3 3 8) (Reg.operands [.gpr 8] [])) #v[5861]
    (b_l121930_150))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_149 : List UInt8 :=
  [0x44, 0x89, 0xCA, 0xC1, 0xC2, 0x15, 0x31, 0xCA, 0x44, 0x89, 0xC9, 0xC1, 0xC1, 0x07, 0x31, 0xD1,
    0x44, 0x89, 0xD2, 0x44, 0x31, 0xDA, 0x44, 0x21, 0xCA, 0x44, 0x31, 0xDA, 0x01, 0xEB, 0x01, 0xD3,
    0x8D, 0x14, 0x19, 0x81, 0xC2, 0xEE, 0x82, 0x8F, 0x74, 0x44, 0x89, 0xC1, 0xC1, 0xC1, 0x1E, 0x44,
    0x89, 0xC7, 0xC1, 0xC7, 0x13, 0x31, 0xCF, 0x44, 0x89, 0xC3] ++ bytes_l121930_150

theorem code_l121930_149 : ∀ x ∈ codeRange 0x123c8d bytes_l121930_149, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23c8d 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_150

def b_l121930_148 : Block Op Label signature Reg.count 5845 :=
  .letOp (n := 5845) (.out 0x123c55 (movR32R32Effect 0x123c55 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[5684]
    (.letOp (n := 5846) (.exec 0x123c55 (fun s => s.RIP = 0x123c55) (movR32R32Effect 0x123c55 3 8 0) (Reg.operands [.gpr 0] [])) #v[5684]
    (.letOp (n := 5847) (.out 0x123c58 (xorR32R32Effect 0x123c58 3 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[5845, 5593]
    (.letOp (n := 5848) (.exec 0x123c58 (fun s => s.RIP = 0x123c58) (xorR32R32Effect 0x123c58 3 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[5845, 5593]
    (.letOp (n := 5849) (.out 0x123c5b (andR32R32Effect 0x123c5b 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[5847, 5770]
    (.letOp (n := 5850) (.exec 0x123c5b (fun s => s.RIP = 0x123c5b) (andR32R32Effect 0x123c5b 3 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[5847, 5770]
    (.letOp (n := 5851) (.out 0x123c5e (xorR32R32Effect 0x123c5e 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[5849, 5843]
    (.letOp (n := 5852) (.exec 0x123c5e (fun s => s.RIP = 0x123c5e) (xorR32R32Effect 0x123c5e 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[5849, 5843]
    (.letOp (n := 5853) (.out 0x123c61 (addR32R32Effect 0x123c61 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[5851, 5839]
    (.letOp (n := 5854) (.exec 0x123c61 (fun s => s.RIP = 0x123c61) (addR32R32Effect 0x123c61 3 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[5851, 5839]
    (.letOp (n := 5855) (.out 0x123c64 (addR32R32Effect 0x123c64 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[5510, 5827]
    (.letOp (n := 5856) (.exec 0x123c64 (fun s => s.RIP = 0x123c64) (addR32R32Effect 0x123c64 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[5510, 5827]
    (.letOp (n := 5857) (.out 0x123c67 (movR32R32Effect 0x123c67 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5708]
    (.letOp (n := 5858) (.exec 0x123c67 (fun s => s.RIP = 0x123c67) (movR32R32Effect 0x123c67 2 2 5) (Reg.operands [.gpr 5] [])) #v[5708]
    (.letOp (n := 5859) (.out 0x123c69 (rolR32Effect 0x123c69 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5857]
    (.letOp (n := 5860) (.exec 0x123c69 (fun s => s.RIP = 0x123c69) (rolR32Effect 0x123c69 3 2 15) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5857]
    (.letOp (n := 5861) (.out 0x123c6c (addR32R32Effect 0x123c6c 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[5853, 5827]
    (.letOp (n := 5862) (.exec 0x123c6c (fun s => s.RIP = 0x123c6c) (addR32R32Effect 0x123c6c 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[5853, 5827]
    (.letOp (n := 5863) (.out 0x123c6f (movR32R32Effect 0x123c6f 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5708]
    (.letOp (n := 5864) (.exec 0x123c6f (fun s => s.RIP = 0x123c6f) (movR32R32Effect 0x123c6f 2 1 5) (Reg.operands [.gpr 5] [])) #v[5708]
    (.letOp (n := 5865) (.out 0x123c71 (rolR32Effect 0x123c71 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5863]
    (.letOp (n := 5866) (.exec 0x123c71 (fun s => s.RIP = 0x123c71) (rolR32Effect 0x123c71 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5863]
    (.letOp (n := 5867) (.out 0x123c74 (xorR32R32Effect 0x123c74 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[5865, 5859]
    (.letOp (n := 5868) (.exec 0x123c74 (fun s => s.RIP = 0x123c74) (xorR32R32Effect 0x123c74 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[5865, 5859]
    (.letOp (n := 5869) (.exec 0x123c76 (StorePre 0x123c76 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x123c76 + BitVec.ofNat 64 4)) 4) (addMREffect 0x123c76 4 32 5 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5708, 4]
    (.letOp (n := 5870) (.out 0x123c7a (movR32R32Effect 0x123c7a 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5708]
    (.letOp (n := 5871) (.exec 0x123c7a (fun s => s.RIP = 0x123c7a) (movR32R32Effect 0x123c7a 2 2 5) (Reg.operands [.gpr 5] [])) #v[5708]
    (.letOp (n := 5872) (.out 0x123c7c (shrR32Effect 0x123c7c 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5870]
    (.letOp (n := 5873) (.exec 0x123c7c (fun s => s.RIP = 0x123c7c) (shrR32Effect 0x123c7c 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5870]
    (.letOp (n := 5874) (.out 0x123c7f (xorR32R32Effect 0x123c7f 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[5872, 5867]
    (.letOp (n := 5875) (.exec 0x123c7f (fun s => s.RIP = 0x123c7f) (xorR32R32Effect 0x123c7f 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[5872, 5867]
    (.letOp (n := 5876) (.out 0x123c81 (movR32R32Effect 0x123c81 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[5855]
    (.letOp (n := 5877) (.exec 0x123c81 (fun s => s.RIP = 0x123c81) (movR32R32Effect 0x123c81 3 1 9) (Reg.operands [.gpr 9] [])) #v[5855]
    (.letOp (n := 5878) (.out 0x123c84 (rolR32Effect 0x123c84 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5876]
    (.letOp (n := 5879) (.exec 0x123c84 (fun s => s.RIP = 0x123c84) (rolR32Effect 0x123c84 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5876]
    (.letOp (n := 5880) (.out 0x123c87 (movR32M32LowEffect 0x123c87 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 5881) (.exec 0x123c87 (LoadPre 0x123c87 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x123c87 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x123c87 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5882) (.out 0x123c8b (addR32R32Effect 0x123c8b 2 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[5880, 5874]
    (.letOp (n := 5883) (.exec 0x123c8b (fun s => s.RIP = 0x123c8b) (addR32R32Effect 0x123c8b 2 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[5880, 5874]
    (b_l121930_149)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_148 : List UInt8 :=
  [0x41, 0x89, 0xC0, 0x45, 0x31, 0xE8, 0x41, 0x21, 0xF0, 0x41, 0x31, 0xF8, 0x41, 0x01, 0xD0, 0x41,
    0x01, 0xC9, 0x89, 0xEA, 0xC1, 0xC2, 0x0F, 0x41, 0x01, 0xC8, 0x89, 0xE9, 0xC1, 0xC1, 0x0D, 0x31,
    0xD1, 0x01, 0x6C, 0x24, 0x04, 0x89, 0xEA, 0xC1, 0xEA, 0x0A, 0x31, 0xCA, 0x44, 0x89, 0xC9, 0xC1,
    0xC1, 0x1A, 0x8B, 0x6C, 0x24, 0x68, 0x01, 0xD5] ++ bytes_l121930_149

theorem code_l121930_148 : ∀ x ∈ codeRange 0x123c55 bytes_l121930_148, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23c55 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_149

def b_l121930_147 : Block Op Label signature Reg.count 5805 :=
  .letOp (n := 5805) (.out 0x123c1f (rolR32Effect 0x123c1f 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5803]
    (.letOp (n := 5806) (.exec 0x123c1f (fun s => s.RIP = 0x123c1f) (rolR32Effect 0x123c1f 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5803]
    (.letOp (n := 5807) (.out 0x123c22 (xorR32R32Effect 0x123c22 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[5805, 5801]
    (.letOp (n := 5808) (.exec 0x123c22 (fun s => s.RIP = 0x123c22) (xorR32R32Effect 0x123c22 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[5805, 5801]
    (.letOp (n := 5809) (.out 0x123c24 (movR32R32Effect 0x123c24 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11] []) (.reg (.gpr 2))) #v[5678]
    (.letOp (n := 5810) (.exec 0x123c24 (fun s => s.RIP = 0x123c24) (movR32R32Effect 0x123c24 3 2 11) (Reg.operands [.gpr 11] [])) #v[5678]
    (.letOp (n := 5811) (.out 0x123c27 (xorR32R32Effect 0x123c27 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[5809, 5591]
    (.letOp (n := 5812) (.exec 0x123c27 (fun s => s.RIP = 0x123c27) (xorR32R32Effect 0x123c27 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[5809, 5591]
    (.letOp (n := 5813) (.out 0x123c29 (andR32R32Effect 0x123c29 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[5811, 5768]
    (.letOp (n := 5814) (.exec 0x123c29 (fun s => s.RIP = 0x123c29) (andR32R32Effect 0x123c29 3 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[5811, 5768]
    (.letOp (n := 5815) (.out 0x123c2c (xorR32R32Effect 0x123c2c 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[5813, 5591]
    (.letOp (n := 5816) (.exec 0x123c2c (fun s => s.RIP = 0x123c2c) (xorR32R32Effect 0x123c2c 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[5813, 5591]
    (.letOp (n := 5817) (.out 0x123c2e (addR32R32Effect 0x123c2e 3 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[5504, 5791]
    (.letOp (n := 5818) (.exec 0x123c2e (fun s => s.RIP = 0x123c2e) (addR32R32Effect 0x123c2e 3 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[5504, 5791]
    (.letOp (n := 5819) (.out 0x123c31 (addR32R32Effect 0x123c31 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[5817, 5815]
    (.letOp (n := 5820) (.exec 0x123c31 (fun s => s.RIP = 0x123c31) (addR32R32Effect 0x123c31 3 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[5817, 5815]
    (.letOp (n := 5821) (.out 0x123c34 (movR32R32Effect 0x123c34 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[5770]
    (.letOp (n := 5822) (.exec 0x123c34 (fun s => s.RIP = 0x123c34) (movR32R32Effect 0x123c34 2 2 6) (Reg.operands [.gpr 6] [])) #v[5770]
    (.letOp (n := 5823) (.out 0x123c36 (rolR32Effect 0x123c36 3 2 30) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5821]
    (.letOp (n := 5824) (.exec 0x123c36 (fun s => s.RIP = 0x123c36) (rolR32Effect 0x123c36 3 2 30) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5821]
    (.letOp (n := 5825) (.out 0x123c39 (addR32R32Effect 0x123c39 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[5807, 5819]
    (.letOp (n := 5826) (.exec 0x123c39 (fun s => s.RIP = 0x123c39) (addR32R32Effect 0x123c39 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[5807, 5819]
    (.letOp (n := 5827) (.out 0x123c3c (addR32Imm32Effect 0x123c3c 6 1 0x682e6ff3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[5825]
    (.letOp (n := 5828) (.exec 0x123c3c (fun s => s.RIP = 0x123c3c) (addR32Imm32Effect 0x123c3c 6 1 0x682e6ff3) (Reg.operands [.gpr 1] [])) #v[5825]
    (.letOp (n := 5829) (.out 0x123c42 (movR32R32Effect 0x123c42 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[5770]
    (.letOp (n := 5830) (.exec 0x123c42 (fun s => s.RIP = 0x123c42) (movR32R32Effect 0x123c42 2 7 6) (Reg.operands [.gpr 6] [])) #v[5770]
    (.letOp (n := 5831) (.out 0x123c44 (rolR32Effect 0x123c44 3 7 19) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[5829]
    (.letOp (n := 5832) (.exec 0x123c44 (fun s => s.RIP = 0x123c44) (rolR32Effect 0x123c44 3 7 19) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5829]
    (.letOp (n := 5833) (.out 0x123c47 (xorR32R32Effect 0x123c47 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[5831, 5823]
    (.letOp (n := 5834) (.exec 0x123c47 (fun s => s.RIP = 0x123c47) (xorR32R32Effect 0x123c47 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[5831, 5823]
    (.letOp (n := 5835) (.out 0x123c49 (movR32R32Effect 0x123c49 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[5770]
    (.letOp (n := 5836) (.exec 0x123c49 (fun s => s.RIP = 0x123c49) (movR32R32Effect 0x123c49 2 2 6) (Reg.operands [.gpr 6] [])) #v[5770]
    (.letOp (n := 5837) (.out 0x123c4b (rolR32Effect 0x123c4b 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5835]
    (.letOp (n := 5838) (.exec 0x123c4b (fun s => s.RIP = 0x123c4b) (rolR32Effect 0x123c4b 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5835]
    (.letOp (n := 5839) (.out 0x123c4e (xorR32R32Effect 0x123c4e 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[5837, 5833]
    (.letOp (n := 5840) (.exec 0x123c4e (fun s => s.RIP = 0x123c4e) (xorR32R32Effect 0x123c4e 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[5837, 5833]
    (.letOp (n := 5841) (.out 0x123c50 (movR32R32Effect 0x123c50 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[5684]
    (.letOp (n := 5842) (.exec 0x123c50 (fun s => s.RIP = 0x123c50) (movR32R32Effect 0x123c50 2 7 0) (Reg.operands [.gpr 0] [])) #v[5684]
    (.letOp (n := 5843) (.out 0x123c52 (andR32R32Effect 0x123c52 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[5841, 5593]
    (.letOp (n := 5844) (.exec 0x123c52 (fun s => s.RIP = 0x123c52) (andR32R32Effect 0x123c52 3 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[5841, 5593]
    (b_l121930_148))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_147 : List UInt8 :=
  [0xC1, 0xC1, 0x07, 0x31, 0xD1, 0x44, 0x89, 0xDA, 0x31, 0xDA, 0x44, 0x21, 0xD2, 0x31, 0xDA, 0x45,
    0x01, 0xF0, 0x41, 0x01, 0xD0, 0x89, 0xF2, 0xC1, 0xC2, 0x1E, 0x44, 0x01, 0xC1, 0x81, 0xC1, 0xF3,
    0x6F, 0x2E, 0x68, 0x89, 0xF7, 0xC1, 0xC7, 0x13, 0x31, 0xD7, 0x89, 0xF2, 0xC1, 0xC2, 0x0A, 0x31,
    0xFA, 0x89, 0xC7, 0x44, 0x21, 0xEF] ++ bytes_l121930_148

theorem code_l121930_147 : ∀ x ∈ codeRange 0x123c1f bytes_l121930_147, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23c1f 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_148

def b_l121930_146 : Block Op Label signature Reg.count 5766 :=
  .letOp (n := 5766) (.out 0x123be5 (addR32R32Effect 0x123be5 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[5764, 5752]
    (.letOp (n := 5767) (.exec 0x123be5 (fun s => s.RIP = 0x123be5) (addR32R32Effect 0x123be5 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[5764, 5752]
    (.letOp (n := 5768) (.out 0x123be7 (addR32R32Effect 0x123be7 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[5421, 5736]
    (.letOp (n := 5769) (.exec 0x123be7 (fun s => s.RIP = 0x123be7) (addR32R32Effect 0x123be7 3 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[5421, 5736]
    (.letOp (n := 5770) (.out 0x123bea (addR32R32Effect 0x123bea 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[5766, 5736]
    (.letOp (n := 5771) (.exec 0x123bea (fun s => s.RIP = 0x123bea) (addR32R32Effect 0x123bea 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[5766, 5736]
    (.letOp (n := 5772) (.out 0x123bec (movR32R32Effect 0x123bec 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[5614]
    (.letOp (n := 5773) (.exec 0x123bec (fun s => s.RIP = 0x123bec) (movR32R32Effect 0x123bec 3 1 15) (Reg.operands [.gpr 15] [])) #v[5614]
    (.letOp (n := 5774) (.out 0x123bef (rolR32Effect 0x123bef 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5772]
    (.letOp (n := 5775) (.exec 0x123bef (fun s => s.RIP = 0x123bef) (rolR32Effect 0x123bef 3 1 15) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5772]
    (.letOp (n := 5776) (.out 0x123bf2 (movR32R32Effect 0x123bf2 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[5614]
    (.letOp (n := 5777) (.exec 0x123bf2 (fun s => s.RIP = 0x123bf2) (movR32R32Effect 0x123bf2 3 2 15) (Reg.operands [.gpr 15] [])) #v[5614]
    (.letOp (n := 5778) (.out 0x123bf5 (rolR32Effect 0x123bf5 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5776]
    (.letOp (n := 5779) (.exec 0x123bf5 (fun s => s.RIP = 0x123bf5) (rolR32Effect 0x123bf5 3 2 13) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5776]
    (.letOp (n := 5780) (.out 0x123bf8 (xorR32R32Effect 0x123bf8 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[5778, 5774]
    (.letOp (n := 5781) (.exec 0x123bf8 (fun s => s.RIP = 0x123bf8) (xorR32R32Effect 0x123bf8 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[5778, 5774]
    (.letOp (n := 5782) (.exec 0x123bfa (StorePre 0x123bfa 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x123bfa + BitVec.ofNat 64 4)) 4) (addMREffect 0x123bfa 4 32 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 15, .gpr 4] [])) #v[5614, 4]
    (.letOp (n := 5783) (.out 0x123bfe (movR32R32Effect 0x123bfe 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[5614]
    (.letOp (n := 5784) (.exec 0x123bfe (fun s => s.RIP = 0x123bfe) (movR32R32Effect 0x123bfe 3 1 15) (Reg.operands [.gpr 15] [])) #v[5614]
    (.letOp (n := 5785) (.out 0x123c01 (shrR32Effect 0x123c01 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5783]
    (.letOp (n := 5786) (.exec 0x123c01 (fun s => s.RIP = 0x123c01) (shrR32Effect 0x123c01 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5783]
    (.letOp (n := 5787) (.out 0x123c04 (xorR32R32Effect 0x123c04 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[5785, 5780]
    (.letOp (n := 5788) (.exec 0x123c04 (fun s => s.RIP = 0x123c04) (xorR32R32Effect 0x123c04 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[5785, 5780]
    (.letOp (n := 5789) (.out 0x123c06 (movR32M32Effect 0x123c06 14 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 5790) (.exec 0x123c06 (LoadPre 0x123c06 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x123c06 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x123c06 14 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5791) (.out 0x123c0b (addR32R32Effect 0x123c0b 3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[5789, 5787]
    (.letOp (n := 5792) (.exec 0x123c0b (fun s => s.RIP = 0x123c0b) (addR32R32Effect 0x123c0b 3 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[5789, 5787]
    (.letOp (n := 5793) (.out 0x123c0e (movR32R32Effect 0x123c0e 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[5768]
    (.letOp (n := 5794) (.exec 0x123c0e (fun s => s.RIP = 0x123c0e) (movR32R32Effect 0x123c0e 3 1 10) (Reg.operands [.gpr 10] [])) #v[5768]
    (.letOp (n := 5795) (.out 0x123c11 (rolR32Effect 0x123c11 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5793]
    (.letOp (n := 5796) (.exec 0x123c11 (fun s => s.RIP = 0x123c11) (rolR32Effect 0x123c11 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5793]
    (.letOp (n := 5797) (.out 0x123c14 (movR32R32Effect 0x123c14 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[5768]
    (.letOp (n := 5798) (.exec 0x123c14 (fun s => s.RIP = 0x123c14) (movR32R32Effect 0x123c14 3 2 10) (Reg.operands [.gpr 10] [])) #v[5768]
    (.letOp (n := 5799) (.out 0x123c17 (rolR32Effect 0x123c17 3 2 21) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5797]
    (.letOp (n := 5800) (.exec 0x123c17 (fun s => s.RIP = 0x123c17) (rolR32Effect 0x123c17 3 2 21) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5797]
    (.letOp (n := 5801) (.out 0x123c1a (xorR32R32Effect 0x123c1a 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[5799, 5795]
    (.letOp (n := 5802) (.exec 0x123c1a (fun s => s.RIP = 0x123c1a) (xorR32R32Effect 0x123c1a 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[5799, 5795]
    (.letOp (n := 5803) (.out 0x123c1c (movR32R32Effect 0x123c1c 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[5768]
    (.letOp (n := 5804) (.exec 0x123c1c (fun s => s.RIP = 0x123c1c) (movR32R32Effect 0x123c1c 3 1 10) (Reg.operands [.gpr 10] [])) #v[5768]
    (b_l121930_147)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_146 : List UInt8 :=
  [0x01, 0xD6, 0x41, 0x01, 0xCA, 0x01, 0xCE, 0x44, 0x89, 0xF9, 0xC1, 0xC1, 0x0F, 0x44, 0x89, 0xFA,
    0xC1, 0xC2, 0x0D, 0x31, 0xCA, 0x44, 0x01, 0x3C, 0x24, 0x44, 0x89, 0xF9, 0xC1, 0xE9, 0x0A, 0x31,
    0xD1, 0x44, 0x8B, 0x74, 0x24, 0x70, 0x41, 0x01, 0xCE, 0x44, 0x89, 0xD1, 0xC1, 0xC1, 0x1A, 0x44,
    0x89, 0xD2, 0xC1, 0xC2, 0x15, 0x31, 0xCA, 0x44, 0x89, 0xD1] ++ bytes_l121930_147

theorem code_l121930_146 : ∀ x ∈ codeRange 0x123be5 bytes_l121930_146, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23be5 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_147

def b_l121930_145 : Block Op Label signature Reg.count 5726 :=
  .letOp (n := 5726) (.out 0x123bac (andR32R32Effect 0x123bac 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[5724, 5678]
    (.letOp (n := 5727) (.exec 0x123bac (fun s => s.RIP = 0x123bac) (andR32R32Effect 0x123bac 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[5724, 5678]
    (.letOp (n := 5728) (.out 0x123baf (xorR32R32Effect 0x123baf 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[5726, 5504]
    (.letOp (n := 5729) (.exec 0x123baf (fun s => s.RIP = 0x123baf) (xorR32R32Effect 0x123baf 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[5726, 5504]
    (.letOp (n := 5730) (.out 0x123bb2 (addR32R32Effect 0x123bb2 3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[5419, 5708]
    (.letOp (n := 5731) (.exec 0x123bb2 (fun s => s.RIP = 0x123bb2) (addR32R32Effect 0x123bb2 3 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[5419, 5708]
    (.letOp (n := 5732) (.out 0x123bb5 (addR32R32Effect 0x123bb5 3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[5730, 5728]
    (.letOp (n := 5733) (.exec 0x123bb5 (fun s => s.RIP = 0x123bb5) (addR32R32Effect 0x123bb5 3 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[5730, 5728]
    (.letOp (n := 5734) (.out 0x123bb8 (leaR32Effect 0x123bb8 4 1 (.sib 2 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 14] []) (.reg (.gpr 1))) #v[5720, 5732]
    (.letOp (n := 5735) (.exec 0x123bb8 (fun s => s.RIP = 0x123bb8) (leaR32Effect 0x123bb8 4 1 (.sib 2 (some 14) 0 .none)) (Reg.operands [.gpr 2, .gpr 14] [])) #v[5720, 5732]
    (.letOp (n := 5736) (.out 0x123bbc (addR32Imm32Effect 0x123bbc 6 1 0x5b9cca4f) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[5734]
    (.letOp (n := 5737) (.exec 0x123bbc (fun s => s.RIP = 0x123bbc) (addR32Imm32Effect 0x123bbc 6 1 0x5b9cca4f) (Reg.operands [.gpr 1] [])) #v[5734]
    (.letOp (n := 5738) (.out 0x123bc2 (movR32R32Effect 0x123bc2 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[5684]
    (.letOp (n := 5739) (.exec 0x123bc2 (fun s => s.RIP = 0x123bc2) (movR32R32Effect 0x123bc2 2 2 0) (Reg.operands [.gpr 0] [])) #v[5684]
    (.letOp (n := 5740) (.out 0x123bc4 (rolR32Effect 0x123bc4 3 2 30) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5738]
    (.letOp (n := 5741) (.exec 0x123bc4 (fun s => s.RIP = 0x123bc4) (rolR32Effect 0x123bc4 3 2 30) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5738]
    (.letOp (n := 5742) (.out 0x123bc7 (movR32R32Effect 0x123bc7 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[5684]
    (.letOp (n := 5743) (.exec 0x123bc7 (fun s => s.RIP = 0x123bc7) (movR32R32Effect 0x123bc7 2 6 0) (Reg.operands [.gpr 0] [])) #v[5684]
    (.letOp (n := 5744) (.out 0x123bc9 (rolR32Effect 0x123bc9 3 6 19) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5742]
    (.letOp (n := 5745) (.exec 0x123bc9 (fun s => s.RIP = 0x123bc9) (rolR32Effect 0x123bc9 3 6 19) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5742]
    (.letOp (n := 5746) (.out 0x123bcc (xorR32R32Effect 0x123bcc 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[5744, 5740]
    (.letOp (n := 5747) (.exec 0x123bcc (fun s => s.RIP = 0x123bcc) (xorR32R32Effect 0x123bcc 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[5744, 5740]
    (.letOp (n := 5748) (.out 0x123bce (movR32R32Effect 0x123bce 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[5684]
    (.letOp (n := 5749) (.exec 0x123bce (fun s => s.RIP = 0x123bce) (movR32R32Effect 0x123bce 2 2 0) (Reg.operands [.gpr 0] [])) #v[5684]
    (.letOp (n := 5750) (.out 0x123bd0 (rolR32Effect 0x123bd0 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5748]
    (.letOp (n := 5751) (.exec 0x123bd0 (fun s => s.RIP = 0x123bd0) (rolR32Effect 0x123bd0 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5748]
    (.letOp (n := 5752) (.out 0x123bd3 (xorR32R32Effect 0x123bd3 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[5750, 5746]
    (.letOp (n := 5753) (.exec 0x123bd3 (fun s => s.RIP = 0x123bd3) (xorR32R32Effect 0x123bd3 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[5750, 5746]
    (.letOp (n := 5754) (.out 0x123bd5 (movR32R32Effect 0x123bd5 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[5593]
    (.letOp (n := 5755) (.exec 0x123bd5 (fun s => s.RIP = 0x123bd5) (movR32R32Effect 0x123bd5 3 7 13) (Reg.operands [.gpr 13] [])) #v[5593]
    (.letOp (n := 5756) (.out 0x123bd8 (andR32R32Effect 0x123bd8 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[5754, 5510]
    (.letOp (n := 5757) (.exec 0x123bd8 (fun s => s.RIP = 0x123bd8) (andR32R32Effect 0x123bd8 3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[5754, 5510]
    (.letOp (n := 5758) (.out 0x123bdb (movR32R32Effect 0x123bdb 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[5593]
    (.letOp (n := 5759) (.exec 0x123bdb (fun s => s.RIP = 0x123bdb) (movR32R32Effect 0x123bdb 3 6 13) (Reg.operands [.gpr 13] [])) #v[5593]
    (.letOp (n := 5760) (.out 0x123bde (xorR32R32Effect 0x123bde 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[5758, 5510]
    (.letOp (n := 5761) (.exec 0x123bde (fun s => s.RIP = 0x123bde) (xorR32R32Effect 0x123bde 3 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[5758, 5510]
    (.letOp (n := 5762) (.out 0x123be1 (andR32R32Effect 0x123be1 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[5760, 5684]
    (.letOp (n := 5763) (.exec 0x123be1 (fun s => s.RIP = 0x123be1) (andR32R32Effect 0x123be1 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[5760, 5684]
    (.letOp (n := 5764) (.out 0x123be3 (xorR32R32Effect 0x123be3 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[5762, 5756]
    (.letOp (n := 5765) (.exec 0x123be3 (fun s => s.RIP = 0x123be3) (xorR32R32Effect 0x123be3 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[5762, 5756]
    (b_l121930_146))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_145 : List UInt8 :=
  [0x44, 0x21, 0xD9, 0x44, 0x31, 0xC1, 0x41, 0x01, 0xEE, 0x41, 0x01, 0xCE, 0x42, 0x8D, 0x0C, 0x32,
    0x81, 0xC1, 0x4F, 0xCA, 0x9C, 0x5B, 0x89, 0xC2, 0xC1, 0xC2, 0x1E, 0x89, 0xC6, 0xC1, 0xC6, 0x13,
    0x31, 0xD6, 0x89, 0xC2, 0xC1, 0xC2, 0x0A, 0x31, 0xF2, 0x44, 0x89, 0xEF, 0x44, 0x21, 0xCF, 0x44,
    0x89, 0xEE, 0x44, 0x31, 0xCE, 0x21, 0xC6, 0x31, 0xFE] ++ bytes_l121930_146

theorem code_l121930_145 : ∀ x ∈ codeRange 0x123bac bytes_l121930_145, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23bac 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_146

def b_l121930_144 : Block Op Label signature Reg.count 5686 :=
  .letOp (n := 5686) (.out 0x123b75 (movR32R32Effect 0x123b75 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5531]
    (.letOp (n := 5687) (.exec 0x123b75 (fun s => s.RIP = 0x123b75) (movR32R32Effect 0x123b75 2 2 5) (Reg.operands [.gpr 5] [])) #v[5531]
    (.letOp (n := 5688) (.out 0x123b77 (rolR32Effect 0x123b77 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5686]
    (.letOp (n := 5689) (.exec 0x123b77 (fun s => s.RIP = 0x123b77) (rolR32Effect 0x123b77 3 2 13) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5686]
    (.letOp (n := 5690) (.out 0x123b7a (xorR32R32Effect 0x123b7a 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[5688, 5682]
    (.letOp (n := 5691) (.exec 0x123b7a (fun s => s.RIP = 0x123b7a) (xorR32R32Effect 0x123b7a 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[5688, 5682]
    (.letOp (n := 5692) (.out 0x123b7c (movR32M32Effect 0x123b7c 12 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 5693) (.exec 0x123b7c (LoadPre 0x123b7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x123b7c + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x123b7c 12 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5694) (.out 0x123b81 (addR32R32Effect 0x123b81 3 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[5692, 5531]
    (.letOp (n := 5695) (.exec 0x123b81 (fun s => s.RIP = 0x123b81) (addR32R32Effect 0x123b81 3 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[5692, 5531]
    (.letOp (n := 5696) (.out 0x123b84 (movR32R32Effect 0x123b84 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5531]
    (.letOp (n := 5697) (.exec 0x123b84 (fun s => s.RIP = 0x123b84) (movR32R32Effect 0x123b84 2 1 5) (Reg.operands [.gpr 5] [])) #v[5531]
    (.letOp (n := 5698) (.out 0x123b86 (shrR32Effect 0x123b86 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5696]
    (.letOp (n := 5699) (.exec 0x123b86 (fun s => s.RIP = 0x123b86) (shrR32Effect 0x123b86 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5696]
    (.letOp (n := 5700) (.out 0x123b89 (xorR32R32Effect 0x123b89 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[5698, 5690]
    (.letOp (n := 5701) (.exec 0x123b89 (fun s => s.RIP = 0x123b89) (xorR32R32Effect 0x123b89 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[5698, 5690]
    (.letOp (n := 5702) (.out 0x123b8b (movR32R32Effect 0x123b8b 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11] []) (.reg (.gpr 2))) #v[5678]
    (.letOp (n := 5703) (.exec 0x123b8b (fun s => s.RIP = 0x123b8b) (movR32R32Effect 0x123b8b 3 2 11) (Reg.operands [.gpr 11] [])) #v[5678]
    (.letOp (n := 5704) (.out 0x123b8e (rolR32Effect 0x123b8e 3 2 26) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5702]
    (.letOp (n := 5705) (.exec 0x123b8e (fun s => s.RIP = 0x123b8e) (rolR32Effect 0x123b8e 3 2 26) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5702]
    (.letOp (n := 5706) (.out 0x123b91 (movR32M32LowEffect 0x123b91 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 5707) (.exec 0x123b91 (LoadPre 0x123b91 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x123b91 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x123b91 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5708) (.out 0x123b95 (addR32R32Effect 0x123b95 2 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[5706, 5700]
    (.letOp (n := 5709) (.exec 0x123b95 (fun s => s.RIP = 0x123b95) (addR32R32Effect 0x123b95 2 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[5706, 5700]
    (.letOp (n := 5710) (.out 0x123b97 (movR32R32Effect 0x123b97 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11] []) (.reg (.gpr 1))) #v[5678]
    (.letOp (n := 5711) (.exec 0x123b97 (fun s => s.RIP = 0x123b97) (movR32R32Effect 0x123b97 3 1 11) (Reg.operands [.gpr 11] [])) #v[5678]
    (.letOp (n := 5712) (.out 0x123b9a (rolR32Effect 0x123b9a 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5710]
    (.letOp (n := 5713) (.exec 0x123b9a (fun s => s.RIP = 0x123b9a) (rolR32Effect 0x123b9a 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5710]
    (.letOp (n := 5714) (.out 0x123b9d (xorR32R32Effect 0x123b9d 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[5712, 5704]
    (.letOp (n := 5715) (.exec 0x123b9d (fun s => s.RIP = 0x123b9d) (xorR32R32Effect 0x123b9d 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[5712, 5704]
    (.letOp (n := 5716) (.out 0x123b9f (movR32R32Effect 0x123b9f 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11] []) (.reg (.gpr 2))) #v[5678]
    (.letOp (n := 5717) (.exec 0x123b9f (fun s => s.RIP = 0x123b9f) (movR32R32Effect 0x123b9f 3 2 11) (Reg.operands [.gpr 11] [])) #v[5678]
    (.letOp (n := 5718) (.out 0x123ba2 (rolR32Effect 0x123ba2 3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5716]
    (.letOp (n := 5719) (.exec 0x123ba2 (fun s => s.RIP = 0x123ba2) (rolR32Effect 0x123ba2 3 2 7) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5716]
    (.letOp (n := 5720) (.out 0x123ba5 (xorR32R32Effect 0x123ba5 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[5718, 5714]
    (.letOp (n := 5721) (.exec 0x123ba5 (fun s => s.RIP = 0x123ba5) (xorR32R32Effect 0x123ba5 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[5718, 5714]
    (.letOp (n := 5722) (.out 0x123ba7 (movR32R32Effect 0x123ba7 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[5591]
    (.letOp (n := 5723) (.exec 0x123ba7 (fun s => s.RIP = 0x123ba7) (movR32R32Effect 0x123ba7 2 1 3) (Reg.operands [.gpr 3] [])) #v[5591]
    (.letOp (n := 5724) (.out 0x123ba9 (xorR32R32Effect 0x123ba9 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[5722, 5504]
    (.letOp (n := 5725) (.exec 0x123ba9 (fun s => s.RIP = 0x123ba9) (xorR32R32Effect 0x123ba9 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[5722, 5504]
    (b_l121930_145))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_144 : List UInt8 :=
  [0x89, 0xEA, 0xC1, 0xC2, 0x0D, 0x31, 0xCA, 0x44, 0x8B, 0x64, 0x24, 0x10, 0x41, 0x01, 0xEC, 0x89,
    0xE9, 0xC1, 0xE9, 0x0A, 0x31, 0xD1, 0x44, 0x89, 0xDA, 0xC1, 0xC2, 0x1A, 0x8B, 0x6C, 0x24, 0x48,
    0x01, 0xCD, 0x44, 0x89, 0xD9, 0xC1, 0xC1, 0x15, 0x31, 0xD1, 0x44, 0x89, 0xDA, 0xC1, 0xC2, 0x07,
    0x31, 0xCA, 0x89, 0xD9, 0x44, 0x31, 0xC1] ++ bytes_l121930_145

theorem code_l121930_144 : ∀ x ∈ codeRange 0x123b75 bytes_l121930_144, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23b75 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_145

def b_l121930_143 : Block Op Label signature Reg.count 5646 :=
  .letOp (n := 5646) (.out 0x123b3b (rolR32Effect 0x123b3b 3 1 30) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5644]
    (.letOp (n := 5647) (.exec 0x123b3b (fun s => s.RIP = 0x123b3b) (rolR32Effect 0x123b3b 3 1 30) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5644]
    (.letOp (n := 5648) (.out 0x123b3e (leaR32Effect 0x123b3e 4 2 (.sib 0 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 12] []) (.reg (.gpr 2))) #v[5630, 5642]
    (.letOp (n := 5649) (.exec 0x123b3e (fun s => s.RIP = 0x123b3e) (leaR32Effect 0x123b3e 4 2 (.sib 0 (some 12) 0 .none)) (Reg.operands [.gpr 0, .gpr 12] [])) #v[5630, 5642]
    (.letOp (n := 5650) (.out 0x123b42 (addR32Imm32Effect 0x123b42 6 2 0x4ed8aa4a) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[5648]
    (.letOp (n := 5651) (.exec 0x123b42 (fun s => s.RIP = 0x123b42) (addR32Imm32Effect 0x123b42 6 2 0x4ed8aa4a) (Reg.operands [.gpr 2] [])) #v[5648]
    (.letOp (n := 5652) (.out 0x123b48 (movR32R32Effect 0x123b48 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[5593]
    (.letOp (n := 5653) (.exec 0x123b48 (fun s => s.RIP = 0x123b48) (movR32R32Effect 0x123b48 3 0 13) (Reg.operands [.gpr 13] [])) #v[5593]
    (.letOp (n := 5654) (.out 0x123b4b (rolR32Effect 0x123b4b 3 0 19) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5652]
    (.letOp (n := 5655) (.exec 0x123b4b (fun s => s.RIP = 0x123b4b) (rolR32Effect 0x123b4b 3 0 19) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5652]
    (.letOp (n := 5656) (.out 0x123b4e (xorR32R32Effect 0x123b4e 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[5654, 5646]
    (.letOp (n := 5657) (.exec 0x123b4e (fun s => s.RIP = 0x123b4e) (xorR32R32Effect 0x123b4e 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[5654, 5646]
    (.letOp (n := 5658) (.out 0x123b50 (movR32R32Effect 0x123b50 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[5593]
    (.letOp (n := 5659) (.exec 0x123b50 (fun s => s.RIP = 0x123b50) (movR32R32Effect 0x123b50 3 1 13) (Reg.operands [.gpr 13] [])) #v[5593]
    (.letOp (n := 5660) (.out 0x123b53 (rolR32Effect 0x123b53 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5658]
    (.letOp (n := 5661) (.exec 0x123b53 (fun s => s.RIP = 0x123b53) (rolR32Effect 0x123b53 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5658]
    (.letOp (n := 5662) (.out 0x123b56 (xorR32R32Effect 0x123b56 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[5660, 5656]
    (.letOp (n := 5663) (.exec 0x123b56 (fun s => s.RIP = 0x123b56) (xorR32R32Effect 0x123b56 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5660, 5656]
    (.letOp (n := 5664) (.out 0x123b58 (movR32R32Effect 0x123b58 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[5510]
    (.letOp (n := 5665) (.exec 0x123b58 (fun s => s.RIP = 0x123b58) (movR32R32Effect 0x123b58 3 6 9) (Reg.operands [.gpr 9] [])) #v[5510]
    (.letOp (n := 5666) (.out 0x123b5b (andR32R32Effect 0x123b5b 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[5664, 5421]
    (.letOp (n := 5667) (.exec 0x123b5b (fun s => s.RIP = 0x123b5b) (andR32R32Effect 0x123b5b 3 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[5664, 5421]
    (.letOp (n := 5668) (.out 0x123b5e (movR32R32Effect 0x123b5e 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[5510]
    (.letOp (n := 5669) (.exec 0x123b5e (fun s => s.RIP = 0x123b5e) (movR32R32Effect 0x123b5e 3 0 9) (Reg.operands [.gpr 9] [])) #v[5510]
    (.letOp (n := 5670) (.out 0x123b61 (xorR32R32Effect 0x123b61 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[5668, 5421]
    (.letOp (n := 5671) (.exec 0x123b61 (fun s => s.RIP = 0x123b61) (xorR32R32Effect 0x123b61 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[5668, 5421]
    (.letOp (n := 5672) (.out 0x123b64 (andR32R32Effect 0x123b64 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[5670, 5593]
    (.letOp (n := 5673) (.exec 0x123b64 (fun s => s.RIP = 0x123b64) (andR32R32Effect 0x123b64 3 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[5670, 5593]
    (.letOp (n := 5674) (.out 0x123b67 (xorR32R32Effect 0x123b67 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[5672, 5666]
    (.letOp (n := 5675) (.exec 0x123b67 (fun s => s.RIP = 0x123b67) (xorR32R32Effect 0x123b67 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[5672, 5666]
    (.letOp (n := 5676) (.out 0x123b69 (addR32R32Effect 0x123b69 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[5674, 5662]
    (.letOp (n := 5677) (.exec 0x123b69 (fun s => s.RIP = 0x123b69) (addR32R32Effect 0x123b69 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[5674, 5662]
    (.letOp (n := 5678) (.out 0x123b6b (addR32R32Effect 0x123b6b 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[5339, 5650]
    (.letOp (n := 5679) (.exec 0x123b6b (fun s => s.RIP = 0x123b6b) (addR32R32Effect 0x123b6b 3 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[5339, 5650]
    (.letOp (n := 5680) (.out 0x123b6e (movR32R32Effect 0x123b6e 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5531]
    (.letOp (n := 5681) (.exec 0x123b6e (fun s => s.RIP = 0x123b6e) (movR32R32Effect 0x123b6e 2 1 5) (Reg.operands [.gpr 5] [])) #v[5531]
    (.letOp (n := 5682) (.out 0x123b70 (rolR32Effect 0x123b70 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5680]
    (.letOp (n := 5683) (.exec 0x123b70 (fun s => s.RIP = 0x123b70) (rolR32Effect 0x123b70 3 1 15) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5680]
    (.letOp (n := 5684) (.out 0x123b73 (addR32R32Effect 0x123b73 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[5676, 5650]
    (.letOp (n := 5685) (.exec 0x123b73 (fun s => s.RIP = 0x123b73) (addR32R32Effect 0x123b73 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[5676, 5650]
    (b_l121930_144))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_143 : List UInt8 :=
  [0xC1, 0xC1, 0x1E, 0x42, 0x8D, 0x14, 0x20, 0x81, 0xC2, 0x4A, 0xAA, 0xD8, 0x4E, 0x44, 0x89, 0xE8,
    0xC1, 0xC0, 0x13, 0x31, 0xC8, 0x44, 0x89, 0xE9, 0xC1, 0xC1, 0x0A, 0x31, 0xC1, 0x44, 0x89, 0xCE,
    0x44, 0x21, 0xD6, 0x44, 0x89, 0xC8, 0x44, 0x31, 0xD0, 0x44, 0x21, 0xE8, 0x31, 0xF0, 0x01, 0xC8,
    0x41, 0x01, 0xD3, 0x89, 0xE9, 0xC1, 0xC1, 0x0F, 0x01, 0xD0] ++ bytes_l121930_144

theorem code_l121930_143 : ∀ x ∈ codeRange 0x123b3b bytes_l121930_143, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23b3b 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_144

def b_l121930_142 : Block Op Label signature Reg.count 5606 :=
  .letOp (n := 5606) (.out 0x123b05 (movR32R32Effect 0x123b05 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[5440]
    (.letOp (n := 5607) (.exec 0x123b05 (fun s => s.RIP = 0x123b05) (movR32R32Effect 0x123b05 2 0 7) (Reg.operands [.gpr 7] [])) #v[5440]
    (.letOp (n := 5608) (.out 0x123b07 (shrR32Effect 0x123b07 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5606]
    (.letOp (n := 5609) (.exec 0x123b07 (fun s => s.RIP = 0x123b07) (shrR32Effect 0x123b07 3 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5606]
    (.letOp (n := 5610) (.out 0x123b0a (xorR32R32Effect 0x123b0a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[5608, 5603]
    (.letOp (n := 5611) (.exec 0x123b0a (fun s => s.RIP = 0x123b0a) (xorR32R32Effect 0x123b0a 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[5608, 5603]
    (.letOp (n := 5612) (.out 0x123b0c (movR32M32Effect 0x123b0c 15 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 5613) (.exec 0x123b0c (LoadPre 0x123b0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x123b0c + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x123b0c 15 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5614) (.out 0x123b11 (addR32R32Effect 0x123b11 3 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[5612, 5610]
    (.letOp (n := 5615) (.exec 0x123b11 (fun s => s.RIP = 0x123b11) (addR32R32Effect 0x123b11 3 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[5612, 5610]
    (.letOp (n := 5616) (.out 0x123b14 (movR32R32Effect 0x123b14 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[5591]
    (.letOp (n := 5617) (.exec 0x123b14 (fun s => s.RIP = 0x123b14) (movR32R32Effect 0x123b14 2 0 3) (Reg.operands [.gpr 3] [])) #v[5591]
    (.letOp (n := 5618) (.out 0x123b16 (rolR32Effect 0x123b16 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5616]
    (.letOp (n := 5619) (.exec 0x123b16 (fun s => s.RIP = 0x123b16) (rolR32Effect 0x123b16 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5616]
    (.letOp (n := 5620) (.out 0x123b19 (movR32R32Effect 0x123b19 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[5591]
    (.letOp (n := 5621) (.exec 0x123b19 (fun s => s.RIP = 0x123b19) (movR32R32Effect 0x123b19 2 1 3) (Reg.operands [.gpr 3] [])) #v[5591]
    (.letOp (n := 5622) (.out 0x123b1b (rolR32Effect 0x123b1b 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5620]
    (.letOp (n := 5623) (.exec 0x123b1b (fun s => s.RIP = 0x123b1b) (rolR32Effect 0x123b1b 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5620]
    (.letOp (n := 5624) (.out 0x123b1e (xorR32R32Effect 0x123b1e 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[5622, 5618]
    (.letOp (n := 5625) (.exec 0x123b1e (fun s => s.RIP = 0x123b1e) (xorR32R32Effect 0x123b1e 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5622, 5618]
    (.letOp (n := 5626) (.out 0x123b20 (movR32R32Effect 0x123b20 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[5591]
    (.letOp (n := 5627) (.exec 0x123b20 (fun s => s.RIP = 0x123b20) (movR32R32Effect 0x123b20 2 0 3) (Reg.operands [.gpr 3] [])) #v[5591]
    (.letOp (n := 5628) (.out 0x123b22 (rolR32Effect 0x123b22 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5626]
    (.letOp (n := 5629) (.exec 0x123b22 (fun s => s.RIP = 0x123b22) (rolR32Effect 0x123b22 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5626]
    (.letOp (n := 5630) (.out 0x123b25 (xorR32R32Effect 0x123b25 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[5628, 5624]
    (.letOp (n := 5631) (.exec 0x123b25 (fun s => s.RIP = 0x123b25) (xorR32R32Effect 0x123b25 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[5628, 5624]
    (.letOp (n := 5632) (.out 0x123b27 (movR32R32Effect 0x123b27 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[5504]
    (.letOp (n := 5633) (.exec 0x123b27 (fun s => s.RIP = 0x123b27) (movR32R32Effect 0x123b27 3 1 8) (Reg.operands [.gpr 8] [])) #v[5504]
    (.letOp (n := 5634) (.out 0x123b2a (xorR32R32Effect 0x123b2a 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[5632, 5419]
    (.letOp (n := 5635) (.exec 0x123b2a (fun s => s.RIP = 0x123b2a) (xorR32R32Effect 0x123b2a 3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[5632, 5419]
    (.letOp (n := 5636) (.out 0x123b2d (andR32R32Effect 0x123b2d 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[5634, 5591]
    (.letOp (n := 5637) (.exec 0x123b2d (fun s => s.RIP = 0x123b2d) (andR32R32Effect 0x123b2d 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[5634, 5591]
    (.letOp (n := 5638) (.out 0x123b2f (xorR32R32Effect 0x123b2f 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[5636, 5419]
    (.letOp (n := 5639) (.exec 0x123b2f (fun s => s.RIP = 0x123b2f) (xorR32R32Effect 0x123b2f 3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[5636, 5419]
    (.letOp (n := 5640) (.out 0x123b32 (addR32R32Effect 0x123b32 3 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[5337, 5614]
    (.letOp (n := 5641) (.exec 0x123b32 (fun s => s.RIP = 0x123b32) (addR32R32Effect 0x123b32 3 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[5337, 5614]
    (.letOp (n := 5642) (.out 0x123b35 (addR32R32Effect 0x123b35 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[5640, 5638]
    (.letOp (n := 5643) (.exec 0x123b35 (fun s => s.RIP = 0x123b35) (addR32R32Effect 0x123b35 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[5640, 5638]
    (.letOp (n := 5644) (.out 0x123b38 (movR32R32Effect 0x123b38 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[5593]
    (.letOp (n := 5645) (.exec 0x123b38 (fun s => s.RIP = 0x123b38) (movR32R32Effect 0x123b38 3 1 13) (Reg.operands [.gpr 13] [])) #v[5593]
    (b_l121930_143))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_142 : List UInt8 :=
  [0x89, 0xF8, 0xC1, 0xE8, 0x0A, 0x31, 0xC8, 0x44, 0x8B, 0x7C, 0x24, 0x14, 0x41, 0x01, 0xC7, 0x89,
    0xD8, 0xC1, 0xC0, 0x1A, 0x89, 0xD9, 0xC1, 0xC1, 0x15, 0x31, 0xC1, 0x89, 0xD8, 0xC1, 0xC0, 0x07,
    0x31, 0xC8, 0x44, 0x89, 0xC1, 0x44, 0x31, 0xF1, 0x21, 0xD9, 0x44, 0x31, 0xF1, 0x45, 0x01, 0xFC,
    0x41, 0x01, 0xCC, 0x44, 0x89, 0xE9] ++ bytes_l121930_143

theorem code_l121930_142 : ∀ x ∈ codeRange 0x123b05 bytes_l121930_142, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23b05 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_143

def b_l121930_141 : Block Op Label signature Reg.count 5567 :=
  .letOp (n := 5567) (.out 0x123ace (rolR32Effect 0x123ace 3 2 19) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5565]
    (.letOp (n := 5568) (.exec 0x123ace (fun s => s.RIP = 0x123ace) (rolR32Effect 0x123ace 3 2 19) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5565]
    (.letOp (n := 5569) (.out 0x123ad1 (xorR32R32Effect 0x123ad1 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[5567, 5563]
    (.letOp (n := 5570) (.exec 0x123ad1 (fun s => s.RIP = 0x123ad1) (xorR32R32Effect 0x123ad1 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[5567, 5563]
    (.letOp (n := 5571) (.out 0x123ad3 (movR32R32Effect 0x123ad3 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[5510]
    (.letOp (n := 5572) (.exec 0x123ad3 (fun s => s.RIP = 0x123ad3) (movR32R32Effect 0x123ad3 3 1 9) (Reg.operands [.gpr 9] [])) #v[5510]
    (.letOp (n := 5573) (.out 0x123ad6 (rolR32Effect 0x123ad6 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5571]
    (.letOp (n := 5574) (.exec 0x123ad6 (fun s => s.RIP = 0x123ad6) (rolR32Effect 0x123ad6 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5571]
    (.letOp (n := 5575) (.out 0x123ad9 (xorR32R32Effect 0x123ad9 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[5573, 5569]
    (.letOp (n := 5576) (.exec 0x123ad9 (fun s => s.RIP = 0x123ad9) (xorR32R32Effect 0x123ad9 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[5573, 5569]
    (.letOp (n := 5577) (.out 0x123adb (movR32R32Effect 0x123adb 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[5421]
    (.letOp (n := 5578) (.exec 0x123adb (fun s => s.RIP = 0x123adb) (movR32R32Effect 0x123adb 3 2 10) (Reg.operands [.gpr 10] [])) #v[5421]
    (.letOp (n := 5579) (.out 0x123ade (andR32R32Effect 0x123ade 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[5577, 5339]
    (.letOp (n := 5580) (.exec 0x123ade (fun s => s.RIP = 0x123ade) (andR32R32Effect 0x123ade 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[5577, 5339]
    (.letOp (n := 5581) (.out 0x123ae1 (movR32R32Effect 0x123ae1 3 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 10] []) (.reg (.gpr 13))) #v[5421]
    (.letOp (n := 5582) (.exec 0x123ae1 (fun s => s.RIP = 0x123ae1) (movR32R32Effect 0x123ae1 3 13 10) (Reg.operands [.gpr 10] [])) #v[5421]
    (.letOp (n := 5583) (.out 0x123ae4 (xorR32R32Effect 0x123ae4 3 13 11) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 11] []) (.reg (.gpr 13))) #v[5581, 5339]
    (.letOp (n := 5584) (.exec 0x123ae4 (fun s => s.RIP = 0x123ae4) (xorR32R32Effect 0x123ae4 3 13 11) (Reg.operands [.gpr 13, .gpr 11] [])) #v[5581, 5339]
    (.letOp (n := 5585) (.out 0x123ae7 (andR32R32Effect 0x123ae7 3 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[5583, 5510]
    (.letOp (n := 5586) (.exec 0x123ae7 (fun s => s.RIP = 0x123ae7) (andR32R32Effect 0x123ae7 3 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[5583, 5510]
    (.letOp (n := 5587) (.out 0x123aea (xorR32R32Effect 0x123aea 3 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[5585, 5579]
    (.letOp (n := 5588) (.exec 0x123aea (fun s => s.RIP = 0x123aea) (xorR32R32Effect 0x123aea 3 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[5585, 5579]
    (.letOp (n := 5589) (.out 0x123aed (addR32R32Effect 0x123aed 3 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[5587, 5575]
    (.letOp (n := 5590) (.exec 0x123aed (fun s => s.RIP = 0x123aed) (addR32R32Effect 0x123aed 3 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[5587, 5575]
    (.letOp (n := 5591) (.out 0x123af0 (addR32R32Effect 0x123af0 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[5232, 5559]
    (.letOp (n := 5592) (.exec 0x123af0 (fun s => s.RIP = 0x123af0) (addR32R32Effect 0x123af0 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[5232, 5559]
    (.letOp (n := 5593) (.out 0x123af2 (addR32R32Effect 0x123af2 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[5589, 5559]
    (.letOp (n := 5594) (.exec 0x123af2 (fun s => s.RIP = 0x123af2) (addR32R32Effect 0x123af2 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[5589, 5559]
    (.letOp (n := 5595) (.out 0x123af5 (movR32R32Effect 0x123af5 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[5440]
    (.letOp (n := 5596) (.exec 0x123af5 (fun s => s.RIP = 0x123af5) (movR32R32Effect 0x123af5 2 0 7) (Reg.operands [.gpr 7] [])) #v[5440]
    (.letOp (n := 5597) (.out 0x123af7 (rolR32Effect 0x123af7 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5595]
    (.letOp (n := 5598) (.exec 0x123af7 (fun s => s.RIP = 0x123af7) (rolR32Effect 0x123af7 3 0 15) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5595]
    (.letOp (n := 5599) (.out 0x123afa (movR32R32Effect 0x123afa 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[5440]
    (.letOp (n := 5600) (.exec 0x123afa (fun s => s.RIP = 0x123afa) (movR32R32Effect 0x123afa 2 1 7) (Reg.operands [.gpr 7] [])) #v[5440]
    (.letOp (n := 5601) (.out 0x123afc (rolR32Effect 0x123afc 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5599]
    (.letOp (n := 5602) (.exec 0x123afc (fun s => s.RIP = 0x123afc) (rolR32Effect 0x123afc 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5599]
    (.letOp (n := 5603) (.out 0x123aff (xorR32R32Effect 0x123aff 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[5601, 5597]
    (.letOp (n := 5604) (.exec 0x123aff (fun s => s.RIP = 0x123aff) (xorR32R32Effect 0x123aff 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5601, 5597]
    (.letOp (n := 5605) (.exec 0x123b01 (StorePre 0x123b01 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x123b01 + BitVec.ofNat 64 4)) 4) (addMREffect 0x123b01 4 32 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[5440, 4]
    (b_l121930_142)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_141 : List UInt8 :=
  [0xC1, 0xC2, 0x13, 0x31, 0xCA, 0x44, 0x89, 0xC9, 0xC1, 0xC1, 0x0A, 0x31, 0xD1, 0x44, 0x89, 0xD2,
    0x44, 0x21, 0xDA, 0x45, 0x89, 0xD5, 0x45, 0x31, 0xDD, 0x45, 0x21, 0xCD, 0x41, 0x31, 0xD5, 0x41,
    0x01, 0xCD, 0x01, 0xC3, 0x41, 0x01, 0xC5, 0x89, 0xF8, 0xC1, 0xC0, 0x0F, 0x89, 0xF9, 0xC1, 0xC1,
    0x0D, 0x31, 0xC1, 0x01, 0x7C, 0x24, 0x58] ++ bytes_l121930_142

theorem code_l121930_141 : ∀ x ∈ codeRange 0x123ace bytes_l121930_141, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23ace 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_142

def b_l121930_140 : Block Op Label signature Reg.count 5527 :=
  .letOp (n := 5527) (.out 0x123a92 (rolR32Effect 0x123a92 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5525]
    (.letOp (n := 5528) (.exec 0x123a92 (fun s => s.RIP = 0x123a92) (rolR32Effect 0x123a92 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5525]
    (.letOp (n := 5529) (.out 0x123a95 (movR32M32LowEffect 0x123a95 5 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 5530) (.exec 0x123a95 (LoadPre 0x123a95 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x123a95 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x123a95 5 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5531) (.out 0x123a99 (addR32R32Effect 0x123a99 2 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[5529, 5523]
    (.letOp (n := 5532) (.exec 0x123a99 (fun s => s.RIP = 0x123a99) (addR32R32Effect 0x123a99 2 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[5529, 5523]
    (.letOp (n := 5533) (.out 0x123a9b (movR32R32Effect 0x123a9b 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[5504]
    (.letOp (n := 5534) (.exec 0x123a9b (fun s => s.RIP = 0x123a9b) (movR32R32Effect 0x123a9b 3 1 8) (Reg.operands [.gpr 8] [])) #v[5504]
    (.letOp (n := 5535) (.out 0x123a9e (rolR32Effect 0x123a9e 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5533]
    (.letOp (n := 5536) (.exec 0x123a9e (fun s => s.RIP = 0x123a9e) (rolR32Effect 0x123a9e 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5533]
    (.letOp (n := 5537) (.out 0x123aa1 (xorR32R32Effect 0x123aa1 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[5535, 5527]
    (.letOp (n := 5538) (.exec 0x123aa1 (fun s => s.RIP = 0x123aa1) (xorR32R32Effect 0x123aa1 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5535, 5527]
    (.letOp (n := 5539) (.out 0x123aa3 (movR32R32Effect 0x123aa3 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[5504]
    (.letOp (n := 5540) (.exec 0x123aa3 (fun s => s.RIP = 0x123aa3) (movR32R32Effect 0x123aa3 3 0 8) (Reg.operands [.gpr 8] [])) #v[5504]
    (.letOp (n := 5541) (.out 0x123aa6 (rolR32Effect 0x123aa6 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5539]
    (.letOp (n := 5542) (.exec 0x123aa6 (fun s => s.RIP = 0x123aa6) (rolR32Effect 0x123aa6 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5539]
    (.letOp (n := 5543) (.out 0x123aa9 (xorR32R32Effect 0x123aa9 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[5541, 5537]
    (.letOp (n := 5544) (.exec 0x123aa9 (fun s => s.RIP = 0x123aa9) (xorR32R32Effect 0x123aa9 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[5541, 5537]
    (.letOp (n := 5545) (.out 0x123aab (movR32R32Effect 0x123aab 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[5419]
    (.letOp (n := 5546) (.exec 0x123aab (fun s => s.RIP = 0x123aab) (movR32R32Effect 0x123aab 3 1 14) (Reg.operands [.gpr 14] [])) #v[5419]
    (.letOp (n := 5547) (.out 0x123aae (xorR32R32Effect 0x123aae 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[5545, 5337]
    (.letOp (n := 5548) (.exec 0x123aae (fun s => s.RIP = 0x123aae) (xorR32R32Effect 0x123aae 3 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[5545, 5337]
    (.letOp (n := 5549) (.out 0x123ab1 (andR32R32Effect 0x123ab1 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[5547, 5504]
    (.letOp (n := 5550) (.exec 0x123ab1 (fun s => s.RIP = 0x123ab1) (andR32R32Effect 0x123ab1 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[5547, 5504]
    (.letOp (n := 5551) (.out 0x123ab4 (xorR32R32Effect 0x123ab4 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[5549, 5337]
    (.letOp (n := 5552) (.exec 0x123ab4 (fun s => s.RIP = 0x123ab4) (xorR32R32Effect 0x123ab4 3 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[5549, 5337]
    (.letOp (n := 5553) (.out 0x123ab7 (addR32R32Effect 0x123ab7 3 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[5226, 5531]
    (.letOp (n := 5554) (.exec 0x123ab7 (fun s => s.RIP = 0x123ab7) (addR32R32Effect 0x123ab7 3 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[5226, 5531]
    (.letOp (n := 5555) (.out 0x123aba (addR32R32Effect 0x123aba 3 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[5553, 5551]
    (.letOp (n := 5556) (.exec 0x123aba (fun s => s.RIP = 0x123aba) (addR32R32Effect 0x123aba 3 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[5553, 5551]
    (.letOp (n := 5557) (.out 0x123abd (addR32R32Effect 0x123abd 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[5543, 5555]
    (.letOp (n := 5558) (.exec 0x123abd (fun s => s.RIP = 0x123abd) (addR32R32Effect 0x123abd 3 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[5543, 5555]
    (.letOp (n := 5559) (.out 0x123ac0 (addEaxImm32Effect 0x123ac0 0x391c0cb3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[5557]
    (.letOp (n := 5560) (.exec 0x123ac0 (fun s => s.RIP = 0x123ac0) (addEaxImm32Effect 0x123ac0 0x391c0cb3) (Reg.operands [.gpr 0] [])) #v[5557]
    (.letOp (n := 5561) (.out 0x123ac5 (movR32R32Effect 0x123ac5 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[5510]
    (.letOp (n := 5562) (.exec 0x123ac5 (fun s => s.RIP = 0x123ac5) (movR32R32Effect 0x123ac5 3 1 9) (Reg.operands [.gpr 9] [])) #v[5510]
    (.letOp (n := 5563) (.out 0x123ac8 (rolR32Effect 0x123ac8 3 1 30) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5561]
    (.letOp (n := 5564) (.exec 0x123ac8 (fun s => s.RIP = 0x123ac8) (rolR32Effect 0x123ac8 3 1 30) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5561]
    (.letOp (n := 5565) (.out 0x123acb (movR32R32Effect 0x123acb 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[5510]
    (.letOp (n := 5566) (.exec 0x123acb (fun s => s.RIP = 0x123acb) (movR32R32Effect 0x123acb 3 2 9) (Reg.operands [.gpr 9] [])) #v[5510]
    (b_l121930_141))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_140 : List UInt8 :=
  [0xC1, 0xC0, 0x1A, 0x8B, 0x6C, 0x24, 0x78, 0x01, 0xCD, 0x44, 0x89, 0xC1, 0xC1, 0xC1, 0x15, 0x31,
    0xC1, 0x44, 0x89, 0xC0, 0xC1, 0xC0, 0x07, 0x31, 0xC8, 0x44, 0x89, 0xF1, 0x44, 0x31, 0xE1, 0x44,
    0x21, 0xC1, 0x44, 0x31, 0xE1, 0x41, 0x01, 0xED, 0x41, 0x01, 0xCD, 0x44, 0x01, 0xE8, 0x05, 0xB3,
    0x0C, 0x1C, 0x39, 0x44, 0x89, 0xC9, 0xC1, 0xC1, 0x1E, 0x44, 0x89, 0xCA] ++ bytes_l121930_141

theorem code_l121930_140 : ∀ x ∈ codeRange 0x123a92 bytes_l121930_140, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23a92 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_141

def b_l121930_139 : Block Op Label signature Reg.count 5488 :=
  .letOp (n := 5488) (.out 0x123a59 (xorR32R32Effect 0x123a59 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[5486, 5482]
    (.letOp (n := 5489) (.exec 0x123a59 (fun s => s.RIP = 0x123a59) (xorR32R32Effect 0x123a59 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[5486, 5482]
    (.letOp (n := 5490) (.out 0x123a5b (movR32R32Effect 0x123a5b 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11] []) (.reg (.gpr 2))) #v[5339]
    (.letOp (n := 5491) (.exec 0x123a5b (fun s => s.RIP = 0x123a5b) (movR32R32Effect 0x123a5b 3 2 11) (Reg.operands [.gpr 11] [])) #v[5339]
    (.letOp (n := 5492) (.out 0x123a5e (andR32R32Effect 0x123a5e 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[5490, 5232]
    (.letOp (n := 5493) (.exec 0x123a5e (fun s => s.RIP = 0x123a5e) (andR32R32Effect 0x123a5e 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[5490, 5232]
    (.letOp (n := 5494) (.out 0x123a60 (movR32R32Effect 0x123a60 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 11] []) (.reg (.gpr 9))) #v[5339]
    (.letOp (n := 5495) (.exec 0x123a60 (fun s => s.RIP = 0x123a60) (movR32R32Effect 0x123a60 3 9 11) (Reg.operands [.gpr 11] [])) #v[5339]
    (.letOp (n := 5496) (.out 0x123a63 (xorR32R32Effect 0x123a63 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[5494, 5232]
    (.letOp (n := 5497) (.exec 0x123a63 (fun s => s.RIP = 0x123a63) (xorR32R32Effect 0x123a63 3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[5494, 5232]
    (.letOp (n := 5498) (.out 0x123a66 (andR32R32Effect 0x123a66 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[5496, 5421]
    (.letOp (n := 5499) (.exec 0x123a66 (fun s => s.RIP = 0x123a66) (andR32R32Effect 0x123a66 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[5496, 5421]
    (.letOp (n := 5500) (.out 0x123a69 (xorR32R32Effect 0x123a69 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[5498, 5492]
    (.letOp (n := 5501) (.exec 0x123a69 (fun s => s.RIP = 0x123a69) (xorR32R32Effect 0x123a69 3 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[5498, 5492]
    (.letOp (n := 5502) (.out 0x123a6c (addR32R32Effect 0x123a6c 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[5500, 5488]
    (.letOp (n := 5503) (.exec 0x123a6c (fun s => s.RIP = 0x123a6c) (addR32R32Effect 0x123a6c 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[5500, 5488]
    (.letOp (n := 5504) (.out 0x123a6f (addR32R32Effect 0x123a6f 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[5122, 5476]
    (.letOp (n := 5505) (.exec 0x123a6f (fun s => s.RIP = 0x123a6f) (addR32R32Effect 0x123a6f 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[5122, 5476]
    (.letOp (n := 5506) (.out 0x123a72 (movR32R32Effect 0x123a72 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[5357]
    (.letOp (n := 5507) (.exec 0x123a72 (fun s => s.RIP = 0x123a72) (movR32R32Effect 0x123a72 2 1 6) (Reg.operands [.gpr 6] [])) #v[5357]
    (.letOp (n := 5508) (.out 0x123a74 (rolR32Effect 0x123a74 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5506]
    (.letOp (n := 5509) (.exec 0x123a74 (fun s => s.RIP = 0x123a74) (rolR32Effect 0x123a74 3 1 15) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5506]
    (.letOp (n := 5510) (.out 0x123a77 (addR32R32Effect 0x123a77 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[5502, 5476]
    (.letOp (n := 5511) (.exec 0x123a77 (fun s => s.RIP = 0x123a77) (addR32R32Effect 0x123a77 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[5502, 5476]
    (.letOp (n := 5512) (.out 0x123a7a (movR32R32Effect 0x123a7a 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[5357]
    (.letOp (n := 5513) (.exec 0x123a7a (fun s => s.RIP = 0x123a7a) (movR32R32Effect 0x123a7a 2 0 6) (Reg.operands [.gpr 6] [])) #v[5357]
    (.letOp (n := 5514) (.out 0x123a7c (rolR32Effect 0x123a7c 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5512]
    (.letOp (n := 5515) (.exec 0x123a7c (fun s => s.RIP = 0x123a7c) (rolR32Effect 0x123a7c 3 0 13) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5512]
    (.letOp (n := 5516) (.out 0x123a7f (xorR32R32Effect 0x123a7f 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[5514, 5508]
    (.letOp (n := 5517) (.exec 0x123a7f (fun s => s.RIP = 0x123a7f) (xorR32R32Effect 0x123a7f 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[5514, 5508]
    (.letOp (n := 5518) (.exec 0x123a81 (StorePre 0x123a81 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x123a81 + BitVec.ofNat 64 7)) 4) (addMREffect 0x123a81 7 32 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[5357, 4]
    (.letOp (n := 5519) (.out 0x123a88 (movR32R32Effect 0x123a88 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[5357]
    (.letOp (n := 5520) (.exec 0x123a88 (fun s => s.RIP = 0x123a88) (movR32R32Effect 0x123a88 2 1 6) (Reg.operands [.gpr 6] [])) #v[5357]
    (.letOp (n := 5521) (.out 0x123a8a (shrR32Effect 0x123a8a 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5519]
    (.letOp (n := 5522) (.exec 0x123a8a (fun s => s.RIP = 0x123a8a) (shrR32Effect 0x123a8a 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5519]
    (.letOp (n := 5523) (.out 0x123a8d (xorR32R32Effect 0x123a8d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[5521, 5516]
    (.letOp (n := 5524) (.exec 0x123a8d (fun s => s.RIP = 0x123a8d) (xorR32R32Effect 0x123a8d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5521, 5516]
    (.letOp (n := 5525) (.out 0x123a8f (movR32R32Effect 0x123a8f 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[5504]
    (.letOp (n := 5526) (.exec 0x123a8f (fun s => s.RIP = 0x123a8f) (movR32R32Effect 0x123a8f 3 0 8) (Reg.operands [.gpr 8] [])) #v[5504]
    (b_l121930_140)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_139 : List UInt8 :=
  [0x31, 0xD1, 0x44, 0x89, 0xDA, 0x21, 0xDA, 0x45, 0x89, 0xD9, 0x41, 0x31, 0xD9, 0x45, 0x21, 0xD1,
    0x41, 0x31, 0xD1, 0x41, 0x01, 0xC9, 0x41, 0x01, 0xC0, 0x89, 0xF1, 0xC1, 0xC1, 0x0F, 0x41, 0x01,
    0xC1, 0x89, 0xF0, 0xC1, 0xC0, 0x0D, 0x31, 0xC8, 0x01, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x89,
    0xF1, 0xC1, 0xE9, 0x0A, 0x31, 0xC1, 0x44, 0x89, 0xC0] ++ bytes_l121930_140

theorem code_l121930_139 : ∀ x ∈ codeRange 0x123a59 bytes_l121930_139, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23a59 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_140

def b_l121930_138 : Block Op Label signature Reg.count 5448 :=
  .letOp (n := 5448) (.out 0x123a1e (rolR32Effect 0x123a1e 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5446]
    (.letOp (n := 5449) (.exec 0x123a1e (fun s => s.RIP = 0x123a1e) (rolR32Effect 0x123a1e 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5446]
    (.letOp (n := 5450) (.out 0x123a21 (xorR32R32Effect 0x123a21 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[5448, 5444]
    (.letOp (n := 5451) (.exec 0x123a21 (fun s => s.RIP = 0x123a21) (xorR32R32Effect 0x123a21 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5448, 5444]
    (.letOp (n := 5452) (.out 0x123a23 (movR32R32Effect 0x123a23 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[5419]
    (.letOp (n := 5453) (.exec 0x123a23 (fun s => s.RIP = 0x123a23) (movR32R32Effect 0x123a23 3 0 14) (Reg.operands [.gpr 14] [])) #v[5419]
    (.letOp (n := 5454) (.out 0x123a26 (rolR32Effect 0x123a26 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5452]
    (.letOp (n := 5455) (.exec 0x123a26 (fun s => s.RIP = 0x123a26) (rolR32Effect 0x123a26 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5452]
    (.letOp (n := 5456) (.out 0x123a29 (xorR32R32Effect 0x123a29 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[5454, 5450]
    (.letOp (n := 5457) (.exec 0x123a29 (fun s => s.RIP = 0x123a29) (xorR32R32Effect 0x123a29 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[5454, 5450]
    (.letOp (n := 5458) (.out 0x123a2b (movR32R32Effect 0x123a2b 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[5337]
    (.letOp (n := 5459) (.exec 0x123a2b (fun s => s.RIP = 0x123a2b) (movR32R32Effect 0x123a2b 3 1 12) (Reg.operands [.gpr 12] [])) #v[5337]
    (.letOp (n := 5460) (.out 0x123a2e (xorR32R32Effect 0x123a2e 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[5458, 5226]
    (.letOp (n := 5461) (.exec 0x123a2e (fun s => s.RIP = 0x123a2e) (xorR32R32Effect 0x123a2e 3 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[5458, 5226]
    (.letOp (n := 5462) (.out 0x123a31 (andR32R32Effect 0x123a31 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[5460, 5419]
    (.letOp (n := 5463) (.exec 0x123a31 (fun s => s.RIP = 0x123a31) (andR32R32Effect 0x123a31 3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[5460, 5419]
    (.letOp (n := 5464) (.out 0x123a34 (xorR32R32Effect 0x123a34 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[5462, 5226]
    (.letOp (n := 5465) (.exec 0x123a34 (fun s => s.RIP = 0x123a34) (xorR32R32Effect 0x123a34 3 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[5462, 5226]
    (.letOp (n := 5466) (.out 0x123a37 (addR32R32Effect 0x123a37 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[5120, 5440]
    (.letOp (n := 5467) (.exec 0x123a37 (fun s => s.RIP = 0x123a37) (addR32R32Effect 0x123a37 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[5120, 5440]
    (.letOp (n := 5468) (.out 0x123a3a (addR32R32Effect 0x123a3a 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[5466, 5464]
    (.letOp (n := 5469) (.exec 0x123a3a (fun s => s.RIP = 0x123a3a) (addR32R32Effect 0x123a3a 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[5466, 5464]
    (.letOp (n := 5470) (.out 0x123a3d (movR32R32Effect 0x123a3d 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[5421]
    (.letOp (n := 5471) (.exec 0x123a3d (fun s => s.RIP = 0x123a3d) (movR32R32Effect 0x123a3d 3 1 10) (Reg.operands [.gpr 10] [])) #v[5421]
    (.letOp (n := 5472) (.out 0x123a40 (rolR32Effect 0x123a40 3 1 30) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5470]
    (.letOp (n := 5473) (.exec 0x123a40 (fun s => s.RIP = 0x123a40) (rolR32Effect 0x123a40 3 1 30) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5470]
    (.letOp (n := 5474) (.out 0x123a43 (addR32R32Effect 0x123a43 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[5456, 5468]
    (.letOp (n := 5475) (.exec 0x123a43 (fun s => s.RIP = 0x123a43) (addR32R32Effect 0x123a43 3 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[5456, 5468]
    (.letOp (n := 5476) (.out 0x123a46 (addEaxImm32Effect 0x123a46 0x34b0bcb5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[5474]
    (.letOp (n := 5477) (.exec 0x123a46 (fun s => s.RIP = 0x123a46) (addEaxImm32Effect 0x123a46 0x34b0bcb5) (Reg.operands [.gpr 0] [])) #v[5474]
    (.letOp (n := 5478) (.out 0x123a4b (movR32R32Effect 0x123a4b 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[5421]
    (.letOp (n := 5479) (.exec 0x123a4b (fun s => s.RIP = 0x123a4b) (movR32R32Effect 0x123a4b 3 2 10) (Reg.operands [.gpr 10] [])) #v[5421]
    (.letOp (n := 5480) (.out 0x123a4e (rolR32Effect 0x123a4e 3 2 19) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5478]
    (.letOp (n := 5481) (.exec 0x123a4e (fun s => s.RIP = 0x123a4e) (rolR32Effect 0x123a4e 3 2 19) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5478]
    (.letOp (n := 5482) (.out 0x123a51 (xorR32R32Effect 0x123a51 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[5480, 5472]
    (.letOp (n := 5483) (.exec 0x123a51 (fun s => s.RIP = 0x123a51) (xorR32R32Effect 0x123a51 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[5480, 5472]
    (.letOp (n := 5484) (.out 0x123a53 (movR32R32Effect 0x123a53 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[5421]
    (.letOp (n := 5485) (.exec 0x123a53 (fun s => s.RIP = 0x123a53) (movR32R32Effect 0x123a53 3 1 10) (Reg.operands [.gpr 10] [])) #v[5421]
    (.letOp (n := 5486) (.out 0x123a56 (rolR32Effect 0x123a56 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5484]
    (.letOp (n := 5487) (.exec 0x123a56 (fun s => s.RIP = 0x123a56) (rolR32Effect 0x123a56 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5484]
    (b_l121930_139))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_138 : List UInt8 :=
  [0xC1, 0xC1, 0x15, 0x31, 0xC1, 0x44, 0x89, 0xF0, 0xC1, 0xC0, 0x07, 0x31, 0xC8, 0x44, 0x89, 0xE1,
    0x44, 0x31, 0xE9, 0x44, 0x21, 0xF1, 0x44, 0x31, 0xE9, 0x41, 0x01, 0xF9, 0x41, 0x01, 0xC9, 0x44,
    0x89, 0xD1, 0xC1, 0xC1, 0x1E, 0x44, 0x01, 0xC8, 0x05, 0xB5, 0xBC, 0xB0, 0x34, 0x44, 0x89, 0xD2,
    0xC1, 0xC2, 0x13, 0x31, 0xCA, 0x44, 0x89, 0xD1, 0xC1, 0xC1, 0x0A] ++ bytes_l121930_139

theorem code_l121930_138 : ∀ x ∈ codeRange 0x123a1e bytes_l121930_138, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23a1e 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_139

def b_l121930_137 : Block Op Label signature Reg.count 5409 :=
  .letOp (n := 5409) (.out 0x1239e5 (movR32R32Effect 0x1239e5 3 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 3] []) (.reg (.gpr 10))) #v[5232]
    (.letOp (n := 5410) (.exec 0x1239e5 (fun s => s.RIP = 0x1239e5) (movR32R32Effect 0x1239e5 3 10 3) (Reg.operands [.gpr 3] [])) #v[5232]
    (.letOp (n := 5411) (.out 0x1239e8 (xorR32R32Effect 0x1239e8 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[5409, 5122]
    (.letOp (n := 5412) (.exec 0x1239e8 (fun s => s.RIP = 0x1239e8) (xorR32R32Effect 0x1239e8 3 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[5409, 5122]
    (.letOp (n := 5413) (.out 0x1239eb (andR32R32Effect 0x1239eb 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[5411, 5339]
    (.letOp (n := 5414) (.exec 0x1239eb (fun s => s.RIP = 0x1239eb) (andR32R32Effect 0x1239eb 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[5411, 5339]
    (.letOp (n := 5415) (.out 0x1239ee (xorR32R32Effect 0x1239ee 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[5413, 5407]
    (.letOp (n := 5416) (.exec 0x1239ee (fun s => s.RIP = 0x1239ee) (xorR32R32Effect 0x1239ee 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[5413, 5407]
    (.letOp (n := 5417) (.out 0x1239f1 (addR32R32Effect 0x1239f1 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[5415, 5403]
    (.letOp (n := 5418) (.exec 0x1239f1 (fun s => s.RIP = 0x1239f1) (addR32R32Effect 0x1239f1 3 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[5415, 5403]
    (.letOp (n := 5419) (.out 0x1239f4 (addR32R32Effect 0x1239f4 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[5025, 5387]
    (.letOp (n := 5420) (.exec 0x1239f4 (fun s => s.RIP = 0x1239f4) (addR32R32Effect 0x1239f4 3 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[5025, 5387]
    (.letOp (n := 5421) (.out 0x1239f7 (addR32R32Effect 0x1239f7 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[5417, 5387]
    (.letOp (n := 5422) (.exec 0x1239f7 (fun s => s.RIP = 0x1239f7) (addR32R32Effect 0x1239f7 3 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[5417, 5387]
    (.letOp (n := 5423) (.out 0x1239fa (movR32R32Effect 0x1239fa 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5271]
    (.letOp (n := 5424) (.exec 0x1239fa (fun s => s.RIP = 0x1239fa) (movR32R32Effect 0x1239fa 2 0 5) (Reg.operands [.gpr 5] [])) #v[5271]
    (.letOp (n := 5425) (.out 0x1239fc (rolR32Effect 0x1239fc 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5423]
    (.letOp (n := 5426) (.exec 0x1239fc (fun s => s.RIP = 0x1239fc) (rolR32Effect 0x1239fc 3 0 15) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5423]
    (.letOp (n := 5427) (.out 0x1239ff (movR32R32Effect 0x1239ff 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5271]
    (.letOp (n := 5428) (.exec 0x1239ff (fun s => s.RIP = 0x1239ff) (movR32R32Effect 0x1239ff 2 1 5) (Reg.operands [.gpr 5] [])) #v[5271]
    (.letOp (n := 5429) (.out 0x123a01 (rolR32Effect 0x123a01 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5427]
    (.letOp (n := 5430) (.exec 0x123a01 (fun s => s.RIP = 0x123a01) (rolR32Effect 0x123a01 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5427]
    (.letOp (n := 5431) (.out 0x123a04 (xorR32R32Effect 0x123a04 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[5429, 5425]
    (.letOp (n := 5432) (.exec 0x123a04 (fun s => s.RIP = 0x123a04) (xorR32R32Effect 0x123a04 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5429, 5425]
    (.letOp (n := 5433) (.exec 0x123a06 (StorePre 0x123a06 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x123a06 + BitVec.ofNat 64 4)) 4) (addMREffect 0x123a06 4 32 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5271, 4]
    (.letOp (n := 5434) (.out 0x123a0a (shrR32Effect 0x123a0a 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5271]
    (.letOp (n := 5435) (.exec 0x123a0a (fun s => s.RIP = 0x123a0a) (shrR32Effect 0x123a0a 3 5 10) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5271]
    (.letOp (n := 5436) (.out 0x123a0d (xorR32R32Effect 0x123a0d 2 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[5434, 5431]
    (.letOp (n := 5437) (.exec 0x123a0d (fun s => s.RIP = 0x123a0d) (xorR32R32Effect 0x123a0d 2 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[5434, 5431]
    (.letOp (n := 5438) (.out 0x123a0f (movR32M32LowEffect 0x123a0f 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 5439) (.exec 0x123a0f (LoadPre 0x123a0f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x123a0f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x123a0f 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5440) (.out 0x123a13 (addR32R32Effect 0x123a13 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[5438, 5436]
    (.letOp (n := 5441) (.exec 0x123a13 (fun s => s.RIP = 0x123a13) (addR32R32Effect 0x123a13 2 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[5438, 5436]
    (.letOp (n := 5442) (.out 0x123a15 (movR32R32Effect 0x123a15 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[5419]
    (.letOp (n := 5443) (.exec 0x123a15 (fun s => s.RIP = 0x123a15) (movR32R32Effect 0x123a15 3 0 14) (Reg.operands [.gpr 14] [])) #v[5419]
    (.letOp (n := 5444) (.out 0x123a18 (rolR32Effect 0x123a18 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5442]
    (.letOp (n := 5445) (.exec 0x123a18 (fun s => s.RIP = 0x123a18) (rolR32Effect 0x123a18 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5442]
    (.letOp (n := 5446) (.out 0x123a1b (movR32R32Effect 0x123a1b 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[5419]
    (.letOp (n := 5447) (.exec 0x123a1b (fun s => s.RIP = 0x123a1b) (movR32R32Effect 0x123a1b 3 1 14) (Reg.operands [.gpr 14] [])) #v[5419]
    (b_l121930_138)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_137 : List UInt8 :=
  [0x41, 0x89, 0xDA, 0x45, 0x31, 0xC2, 0x45, 0x21, 0xDA, 0x41, 0x31, 0xD2, 0x41, 0x01, 0xCA, 0x41,
    0x01, 0xC6, 0x41, 0x01, 0xC2, 0x89, 0xE8, 0xC1, 0xC0, 0x0F, 0x89, 0xE9, 0xC1, 0xC1, 0x0D, 0x31,
    0xC1, 0x01, 0x6C, 0x24, 0x68, 0xC1, 0xED, 0x0A, 0x31, 0xCD, 0x8B, 0x7C, 0x24, 0x50, 0x01, 0xEF,
    0x44, 0x89, 0xF0, 0xC1, 0xC0, 0x1A, 0x44, 0x89, 0xF1] ++ bytes_l121930_138

theorem code_l121930_137 : ∀ x ∈ codeRange 0x1239e5 bytes_l121930_137, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x239e5 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_138

def b_l121930_136 : Block Op Label signature Reg.count 5369 :=
  .letOp (n := 5369) (.out 0x1239ae (xorR32R32Effect 0x1239ae 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[5367, 5363]
    (.letOp (n := 5370) (.exec 0x1239ae (fun s => s.RIP = 0x1239ae) (xorR32R32Effect 0x1239ae 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[5367, 5363]
    (.letOp (n := 5371) (.out 0x1239b0 (movR32R32Effect 0x1239b0 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[5226]
    (.letOp (n := 5372) (.exec 0x1239b0 (fun s => s.RIP = 0x1239b0) (movR32R32Effect 0x1239b0 3 1 13) (Reg.operands [.gpr 13] [])) #v[5226]
    (.letOp (n := 5373) (.out 0x1239b3 (xorR32R32Effect 0x1239b3 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[5371, 5120]
    (.letOp (n := 5374) (.exec 0x1239b3 (fun s => s.RIP = 0x1239b3) (xorR32R32Effect 0x1239b3 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[5371, 5120]
    (.letOp (n := 5375) (.out 0x1239b6 (andR32R32Effect 0x1239b6 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[5373, 5337]
    (.letOp (n := 5376) (.exec 0x1239b6 (fun s => s.RIP = 0x1239b6) (andR32R32Effect 0x1239b6 3 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[5373, 5337]
    (.letOp (n := 5377) (.out 0x1239b9 (xorR32R32Effect 0x1239b9 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[5375, 5120]
    (.letOp (n := 5378) (.exec 0x1239b9 (fun s => s.RIP = 0x1239b9) (xorR32R32Effect 0x1239b9 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[5375, 5120]
    (.letOp (n := 5379) (.out 0x1239bc (movR64R64Effect 0x1239bc 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[5291]
    (.letOp (n := 5380) (.exec 0x1239bc (fun s => s.RIP = 0x1239bc) (movR64R64Effect 0x1239bc 2 10) (Reg.operands [.gpr 10] [])) #v[5291]
    (.letOp (n := 5381) (.out 0x1239bf (addR32R32Effect 0x1239bf 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[5379, 5357]
    (.letOp (n := 5382) (.exec 0x1239bf (fun s => s.RIP = 0x1239bf) (addR32R32Effect 0x1239bf 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[5379, 5357]
    (.letOp (n := 5383) (.out 0x1239c1 (addR32R32Effect 0x1239c1 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[5381, 5377]
    (.letOp (n := 5384) (.exec 0x1239c1 (fun s => s.RIP = 0x1239c1) (addR32R32Effect 0x1239c1 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[5381, 5377]
    (.letOp (n := 5385) (.out 0x1239c3 (addR32R32Effect 0x1239c3 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[5369, 5383]
    (.letOp (n := 5386) (.exec 0x1239c3 (fun s => s.RIP = 0x1239c3) (addR32R32Effect 0x1239c3 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[5369, 5383]
    (.letOp (n := 5387) (.out 0x1239c5 (addEaxImm32Effect 0x1239c5 0x2748774c) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[5385]
    (.letOp (n := 5388) (.exec 0x1239c5 (fun s => s.RIP = 0x1239c5) (addEaxImm32Effect 0x1239c5 0x2748774c) (Reg.operands [.gpr 0] [])) #v[5385]
    (.letOp (n := 5389) (.out 0x1239ca (movR32R32Effect 0x1239ca 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11] []) (.reg (.gpr 1))) #v[5339]
    (.letOp (n := 5390) (.exec 0x1239ca (fun s => s.RIP = 0x1239ca) (movR32R32Effect 0x1239ca 3 1 11) (Reg.operands [.gpr 11] [])) #v[5339]
    (.letOp (n := 5391) (.out 0x1239cd (rolR32Effect 0x1239cd 3 1 30) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5389]
    (.letOp (n := 5392) (.exec 0x1239cd (fun s => s.RIP = 0x1239cd) (rolR32Effect 0x1239cd 3 1 30) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5389]
    (.letOp (n := 5393) (.out 0x1239d0 (movR32R32Effect 0x1239d0 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11] []) (.reg (.gpr 2))) #v[5339]
    (.letOp (n := 5394) (.exec 0x1239d0 (fun s => s.RIP = 0x1239d0) (movR32R32Effect 0x1239d0 3 2 11) (Reg.operands [.gpr 11] [])) #v[5339]
    (.letOp (n := 5395) (.out 0x1239d3 (rolR32Effect 0x1239d3 3 2 19) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5393]
    (.letOp (n := 5396) (.exec 0x1239d3 (fun s => s.RIP = 0x1239d3) (rolR32Effect 0x1239d3 3 2 19) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5393]
    (.letOp (n := 5397) (.out 0x1239d6 (xorR32R32Effect 0x1239d6 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[5395, 5391]
    (.letOp (n := 5398) (.exec 0x1239d6 (fun s => s.RIP = 0x1239d6) (xorR32R32Effect 0x1239d6 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[5395, 5391]
    (.letOp (n := 5399) (.out 0x1239d8 (movR32R32Effect 0x1239d8 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11] []) (.reg (.gpr 1))) #v[5339]
    (.letOp (n := 5400) (.exec 0x1239d8 (fun s => s.RIP = 0x1239d8) (movR32R32Effect 0x1239d8 3 1 11) (Reg.operands [.gpr 11] [])) #v[5339]
    (.letOp (n := 5401) (.out 0x1239db (rolR32Effect 0x1239db 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5399]
    (.letOp (n := 5402) (.exec 0x1239db (fun s => s.RIP = 0x1239db) (rolR32Effect 0x1239db 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5399]
    (.letOp (n := 5403) (.out 0x1239de (xorR32R32Effect 0x1239de 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[5401, 5397]
    (.letOp (n := 5404) (.exec 0x1239de (fun s => s.RIP = 0x1239de) (xorR32R32Effect 0x1239de 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[5401, 5397]
    (.letOp (n := 5405) (.out 0x1239e0 (movR32R32Effect 0x1239e0 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[5232]
    (.letOp (n := 5406) (.exec 0x1239e0 (fun s => s.RIP = 0x1239e0) (movR32R32Effect 0x1239e0 2 2 3) (Reg.operands [.gpr 3] [])) #v[5232]
    (.letOp (n := 5407) (.out 0x1239e2 (andR32R32Effect 0x1239e2 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[5405, 5122]
    (.letOp (n := 5408) (.exec 0x1239e2 (fun s => s.RIP = 0x1239e2) (andR32R32Effect 0x1239e2 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[5405, 5122]
    (b_l121930_137))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_136 : List UInt8 :=
  [0x31, 0xC8, 0x44, 0x89, 0xE9, 0x44, 0x31, 0xC9, 0x44, 0x21, 0xE1, 0x44, 0x31, 0xC9, 0x4C, 0x89,
    0xD2, 0x01, 0xF2, 0x01, 0xCA, 0x01, 0xD0, 0x05, 0x4C, 0x77, 0x48, 0x27, 0x44, 0x89, 0xD9, 0xC1,
    0xC1, 0x1E, 0x44, 0x89, 0xDA, 0xC1, 0xC2, 0x13, 0x31, 0xCA, 0x44, 0x89, 0xD9, 0xC1, 0xC1, 0x0A,
    0x31, 0xD1, 0x89, 0xDA, 0x44, 0x21, 0xC2] ++ bytes_l121930_137

theorem code_l121930_136 : ∀ x ∈ codeRange 0x1239ae bytes_l121930_136, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x239ae 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_137

def b_l121930_135 : Block Op Label signature Reg.count 5329 :=
  .letOp (n := 5329) (.out 0x123975 (xorR32R32Effect 0x123975 3 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[5327, 5025]
    (.letOp (n := 5330) (.exec 0x123975 (fun s => s.RIP = 0x123975) (xorR32R32Effect 0x123975 3 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[5327, 5025]
    (.letOp (n := 5331) (.out 0x123978 (andR32R32Effect 0x123978 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[5329, 5232]
    (.letOp (n := 5332) (.exec 0x123978 (fun s => s.RIP = 0x123978) (andR32R32Effect 0x123978 3 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[5329, 5232]
    (.letOp (n := 5333) (.out 0x12397b (xorR32R32Effect 0x12397b 3 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[5331, 5325]
    (.letOp (n := 5334) (.exec 0x12397b (fun s => s.RIP = 0x12397b) (xorR32R32Effect 0x12397b 3 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[5331, 5325]
    (.letOp (n := 5335) (.out 0x12397e (addR32R32Effect 0x12397e 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[5333, 5321]
    (.letOp (n := 5336) (.exec 0x12397e (fun s => s.RIP = 0x12397e) (addR32R32Effect 0x12397e 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[5333, 5321]
    (.letOp (n := 5337) (.out 0x123981 (addR32R32Effect 0x123981 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[4911, 5309]
    (.letOp (n := 5338) (.exec 0x123981 (fun s => s.RIP = 0x123981) (addR32R32Effect 0x123981 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[4911, 5309]
    (.letOp (n := 5339) (.out 0x123984 (addR32R32Effect 0x123984 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[5335, 5309]
    (.letOp (n := 5340) (.exec 0x123984 (fun s => s.RIP = 0x123984) (addR32R32Effect 0x123984 3 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[5335, 5309]
    (.letOp (n := 5341) (.out 0x123987 (rolR32Effect 0x123987 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[5251]
    (.letOp (n := 5342) (.exec 0x123987 (fun s => s.RIP = 0x123987) (rolR32Effect 0x123987 3 7 15) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5251]
    (.letOp (n := 5343) (.out 0x12398a (rolR32Effect 0x12398a 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5253]
    (.letOp (n := 5344) (.exec 0x12398a (fun s => s.RIP = 0x12398a) (rolR32Effect 0x12398a 3 6 13) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5253]
    (.letOp (n := 5345) (.out 0x12398d (xorR32R32Effect 0x12398d 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[5343, 5341]
    (.letOp (n := 5346) (.exec 0x12398d (fun s => s.RIP = 0x12398d) (xorR32R32Effect 0x12398d 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[5343, 5341]
    (.letOp (n := 5347) (.out 0x12398f (shrR32Effect 0x12398f 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5255]
    (.letOp (n := 5348) (.exec 0x12398f (fun s => s.RIP = 0x12398f) (shrR32Effect 0x12398f 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5255]
    (.letOp (n := 5349) (.out 0x123992 (xorR32R32Effect 0x123992 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[5347, 5345]
    (.letOp (n := 5350) (.exec 0x123992 (fun s => s.RIP = 0x123992) (xorR32R32Effect 0x123992 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[5347, 5345]
    (.letOp (n := 5351) (.out 0x123994 (movR32R32Effect 0x123994 3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[5337]
    (.letOp (n := 5352) (.exec 0x123994 (fun s => s.RIP = 0x123994) (movR32R32Effect 0x123994 3 0 12) (Reg.operands [.gpr 12] [])) #v[5337]
    (.letOp (n := 5353) (.out 0x123997 (rolR32Effect 0x123997 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5351]
    (.letOp (n := 5354) (.exec 0x123997 (fun s => s.RIP = 0x123997) (rolR32Effect 0x123997 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5351]
    (.letOp (n := 5355) (.out 0x12399a (movR32M32LowEffect 0x12399a 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 5356) (.exec 0x12399a (LoadPre 0x12399a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12399a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12399a 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5357) (.out 0x12399e (addR32R32Effect 0x12399e 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[5355, 5349]
    (.letOp (n := 5358) (.exec 0x12399e (fun s => s.RIP = 0x12399e) (addR32R32Effect 0x12399e 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[5355, 5349]
    (.letOp (n := 5359) (.out 0x1239a0 (movR32R32Effect 0x1239a0 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[5337]
    (.letOp (n := 5360) (.exec 0x1239a0 (fun s => s.RIP = 0x1239a0) (movR32R32Effect 0x1239a0 3 1 12) (Reg.operands [.gpr 12] [])) #v[5337]
    (.letOp (n := 5361) (.out 0x1239a3 (rolR32Effect 0x1239a3 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5359]
    (.letOp (n := 5362) (.exec 0x1239a3 (fun s => s.RIP = 0x1239a3) (rolR32Effect 0x1239a3 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5359]
    (.letOp (n := 5363) (.out 0x1239a6 (xorR32R32Effect 0x1239a6 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[5361, 5353]
    (.letOp (n := 5364) (.exec 0x1239a6 (fun s => s.RIP = 0x1239a6) (xorR32R32Effect 0x1239a6 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5361, 5353]
    (.letOp (n := 5365) (.out 0x1239a8 (movR32R32Effect 0x1239a8 3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[5337]
    (.letOp (n := 5366) (.exec 0x1239a8 (fun s => s.RIP = 0x1239a8) (movR32R32Effect 0x1239a8 3 0 12) (Reg.operands [.gpr 12] [])) #v[5337]
    (.letOp (n := 5367) (.out 0x1239ab (rolR32Effect 0x1239ab 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5365]
    (.letOp (n := 5368) (.exec 0x1239ab (fun s => s.RIP = 0x1239ab) (rolR32Effect 0x1239ab 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5365]
    (b_l121930_136))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_135 : List UInt8 :=
  [0x45, 0x31, 0xF3, 0x41, 0x21, 0xDB, 0x45, 0x31, 0xFB, 0x41, 0x01, 0xC3, 0x41, 0x01, 0xCC, 0x41,
    0x01, 0xCB, 0xC1, 0xC7, 0x0F, 0xC1, 0xC6, 0x0D, 0x31, 0xFE, 0xC1, 0xEA, 0x0A, 0x31, 0xF2, 0x44,
    0x89, 0xE0, 0xC1, 0xC0, 0x1A, 0x8B, 0x74, 0x24, 0x08, 0x01, 0xD6, 0x44, 0x89, 0xE1, 0xC1, 0xC1,
    0x15, 0x31, 0xC1, 0x44, 0x89, 0xE0, 0xC1, 0xC0, 0x07] ++ bytes_l121930_136

theorem code_l121930_135 : ∀ x ∈ codeRange 0x123975 bytes_l121930_135, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23975 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_136

def b_l121930_134 : Block Op Label signature Reg.count 5289 :=
  .letOp (n := 5289) (.out 0x123932 (movR32R32Effect 0x123932 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[5120]
    (.letOp (n := 5290) (.exec 0x123932 (fun s => s.RIP = 0x123932) (movR32R32Effect 0x123932 3 11 9) (Reg.operands [.gpr 9] [])) #v[5120]
    (.letOp (n := 5291) (.out 0x123935 (movR64M64Effect 0x123935 10 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 5292) (.exec 0x123935 (LoadPre 0x123935 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x123935 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x123935 10 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5293) (.out 0x12393a (xorR32R32Effect 0x12393a 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[5289, 5291]
    (.letOp (n := 5294) (.exec 0x12393a (fun s => s.RIP = 0x12393a) (xorR32R32Effect 0x12393a 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[5289, 5291]
    (.letOp (n := 5295) (.out 0x12393d (andR32R32Effect 0x12393d 3 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13] []) (.reg (.gpr 11))) #v[5293, 5226]
    (.letOp (n := 5296) (.exec 0x12393d (fun s => s.RIP = 0x12393d) (andR32R32Effect 0x12393d 3 11 13) (Reg.operands [.gpr 11, .gpr 13] [])) #v[5293, 5226]
    (.letOp (n := 5297) (.out 0x123940 (xorR32R32Effect 0x123940 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[5295, 5291]
    (.letOp (n := 5298) (.exec 0x123940 (fun s => s.RIP = 0x123940) (xorR32R32Effect 0x123940 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[5295, 5291]
    (.letOp (n := 5299) (.out 0x123943 (addR32R32Effect 0x123943 3 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 5] []) (.reg (.gpr 15))) #v[4905, 5271]
    (.letOp (n := 5300) (.exec 0x123943 (fun s => s.RIP = 0x123943) (addR32R32Effect 0x123943 3 15 5) (Reg.operands [.gpr 15, .gpr 5] [])) #v[4905, 5271]
    (.letOp (n := 5301) (.out 0x123946 (addR32R32Effect 0x123946 3 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[5299, 5297]
    (.letOp (n := 5302) (.exec 0x123946 (fun s => s.RIP = 0x123946) (addR32R32Effect 0x123946 3 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[5299, 5297]
    (.letOp (n := 5303) (.out 0x123949 (movR32R32Effect 0x123949 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[5232]
    (.letOp (n := 5304) (.exec 0x123949 (fun s => s.RIP = 0x123949) (movR32R32Effect 0x123949 3 11 3) (Reg.operands [.gpr 3] [])) #v[5232]
    (.letOp (n := 5305) (.out 0x12394c (rolR32Effect 0x12394c 4 11 30) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[5303]
    (.letOp (n := 5306) (.exec 0x12394c (fun s => s.RIP = 0x12394c) (rolR32Effect 0x12394c 4 11 30) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5303]
    (.letOp (n := 5307) (.out 0x123950 (leaR32Effect 0x123950 4 1 (.sib 0 (some 15) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0, .gpr 15] []) (.reg (.gpr 1))) #v[5287, 5301]
    (.letOp (n := 5308) (.exec 0x123950 (fun s => s.RIP = 0x123950) (leaR32Effect 0x123950 4 1 (.sib 0 (some 15) 0 .none)) (Reg.operands [.gpr 0, .gpr 15] [])) #v[5287, 5301]
    (.letOp (n := 5309) (.out 0x123954 (addR32Imm32Effect 0x123954 6 1 0x1e376c08) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[5307]
    (.letOp (n := 5310) (.exec 0x123954 (fun s => s.RIP = 0x123954) (addR32Imm32Effect 0x123954 6 1 0x1e376c08) (Reg.operands [.gpr 1] [])) #v[5307]
    (.letOp (n := 5311) (.out 0x12395a (movR32R32Effect 0x12395a 3 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[5232]
    (.letOp (n := 5312) (.exec 0x12395a (fun s => s.RIP = 0x12395a) (movR32R32Effect 0x12395a 3 15 3) (Reg.operands [.gpr 3] [])) #v[5232]
    (.letOp (n := 5313) (.out 0x12395d (rolR32Effect 0x12395d 4 15 19) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[5311]
    (.letOp (n := 5314) (.exec 0x12395d (fun s => s.RIP = 0x12395d) (rolR32Effect 0x12395d 4 15 19) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5311]
    (.letOp (n := 5315) (.out 0x123961 (xorR32R32Effect 0x123961 3 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[5313, 5305]
    (.letOp (n := 5316) (.exec 0x123961 (fun s => s.RIP = 0x123961) (xorR32R32Effect 0x123961 3 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[5313, 5305]
    (.letOp (n := 5317) (.out 0x123964 (movR32R32Effect 0x123964 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[5232]
    (.letOp (n := 5318) (.exec 0x123964 (fun s => s.RIP = 0x123964) (movR32R32Effect 0x123964 2 0 3) (Reg.operands [.gpr 3] [])) #v[5232]
    (.letOp (n := 5319) (.out 0x123966 (rolR32Effect 0x123966 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5317]
    (.letOp (n := 5320) (.exec 0x123966 (fun s => s.RIP = 0x123966) (rolR32Effect 0x123966 3 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5317]
    (.letOp (n := 5321) (.out 0x123969 (xorR32R32Effect 0x123969 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[5319, 5315]
    (.letOp (n := 5322) (.exec 0x123969 (fun s => s.RIP = 0x123969) (xorR32R32Effect 0x123969 3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[5319, 5315]
    (.letOp (n := 5323) (.out 0x12396c (movR32R32Effect 0x12396c 3 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[5122]
    (.letOp (n := 5324) (.exec 0x12396c (fun s => s.RIP = 0x12396c) (movR32R32Effect 0x12396c 3 15 8) (Reg.operands [.gpr 8] [])) #v[5122]
    (.letOp (n := 5325) (.out 0x12396f (andR32R32Effect 0x12396f 3 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[5323, 5025]
    (.letOp (n := 5326) (.exec 0x12396f (fun s => s.RIP = 0x12396f) (andR32R32Effect 0x12396f 3 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[5323, 5025]
    (.letOp (n := 5327) (.out 0x123972 (movR32R32Effect 0x123972 3 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 8] []) (.reg (.gpr 11))) #v[5122]
    (.letOp (n := 5328) (.exec 0x123972 (fun s => s.RIP = 0x123972) (movR32R32Effect 0x123972 3 11 8) (Reg.operands [.gpr 8] [])) #v[5122]
    (b_l121930_135))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_134 : List UInt8 :=
  [0x45, 0x89, 0xCB, 0x4C, 0x8B, 0x54, 0x24, 0x38, 0x45, 0x31, 0xD3, 0x45, 0x21, 0xEB, 0x45, 0x31,
    0xD3, 0x41, 0x01, 0xEF, 0x45, 0x01, 0xDF, 0x41, 0x89, 0xDB, 0x41, 0xC1, 0xC3, 0x1E, 0x42, 0x8D,
    0x0C, 0x38, 0x81, 0xC1, 0x08, 0x6C, 0x37, 0x1E, 0x41, 0x89, 0xDF, 0x41, 0xC1, 0xC7, 0x13, 0x45,
    0x31, 0xDF, 0x89, 0xD8, 0xC1, 0xC0, 0x0A, 0x44, 0x31, 0xF8, 0x45, 0x89, 0xC7, 0x45, 0x21, 0xF7,
    0x45, 0x89, 0xC3] ++ bytes_l121930_135

theorem code_l121930_134 : ∀ x ∈ codeRange 0x123932 bytes_l121930_134, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23932 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_135

def b_l121930_133 : Block Op Label signature Reg.count 5251 :=
  .letOp (n := 5251) (.out 0x1238f3 (movR32R32Effect 0x1238f3 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[5162]
    (.letOp (n := 5252) (.exec 0x1238f3 (fun s => s.RIP = 0x1238f3) (movR32R32Effect 0x1238f3 2 7 1) (Reg.operands [.gpr 1] [])) #v[5162]
    (.letOp (n := 5253) (.out 0x1238f5 (movR32R32Effect 0x1238f5 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[5162]
    (.letOp (n := 5254) (.exec 0x1238f5 (fun s => s.RIP = 0x1238f5) (movR32R32Effect 0x1238f5 2 6 1) (Reg.operands [.gpr 1] [])) #v[5162]
    (.letOp (n := 5255) (.out 0x1238f7 (movR32R32Effect 0x1238f7 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[5162]
    (.letOp (n := 5256) (.exec 0x1238f7 (fun s => s.RIP = 0x1238f7) (movR32R32Effect 0x1238f7 2 2 1) (Reg.operands [.gpr 1] [])) #v[5162]
    (.letOp (n := 5257) (.out 0x1238f9 (shrR32Effect 0x1238f9 3 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[5162]
    (.letOp (n := 5258) (.exec 0x1238f9 (fun s => s.RIP = 0x1238f9) (shrR32Effect 0x1238f9 3 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5162]
    (.letOp (n := 5259) (.out 0x1238fc (xorR32R32Effect 0x1238fc 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[5257, 5248]
    (.letOp (n := 5260) (.exec 0x1238fc (fun s => s.RIP = 0x1238fc) (xorR32R32Effect 0x1238fc 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5257, 5248]
    (.letOp (n := 5261) (.exec 0x1238fe (StorePre 0x1238fe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1238fe + BitVec.ofNat 64 5)) 4) (addMREffect 0x1238fe 5 32 10 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[5063, 4]
    (.letOp (n := 5262) (.out 0x123903 (addR32R32Effect 0x123903 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[5259, 5063]
    (.letOp (n := 5263) (.exec 0x123903 (fun s => s.RIP = 0x123903) (addR32R32Effect 0x123903 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[5259, 5063]
    (.letOp (n := 5264) (.exec 0x123906 (StorePre 0x123906 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x123906 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x123906 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[5262, 4]
    (.letOp (n := 5265) (.out 0x12390b (shrR32Effect 0x12390b 4 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[5063]
    (.letOp (n := 5266) (.exec 0x12390b (fun s => s.RIP = 0x12390b) (shrR32Effect 0x12390b 4 10 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5063]
    (.letOp (n := 5267) (.out 0x12390f (xorR32R32Effect 0x12390f 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[5265, 5238]
    (.letOp (n := 5268) (.exec 0x12390f (fun s => s.RIP = 0x12390f) (xorR32R32Effect 0x12390f 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[5265, 5238]
    (.letOp (n := 5269) (.out 0x123912 (movR32M32LowEffect 0x123912 5 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 5270) (.exec 0x123912 (LoadPre 0x123912 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x123912 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x123912 5 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5271) (.out 0x123916 (addR32R32Effect 0x123916 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[5269, 5267]
    (.letOp (n := 5272) (.exec 0x123916 (fun s => s.RIP = 0x123916) (addR32R32Effect 0x123916 3 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[5269, 5267]
    (.letOp (n := 5273) (.out 0x123919 (movR32R32Effect 0x123919 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[5226]
    (.letOp (n := 5274) (.exec 0x123919 (fun s => s.RIP = 0x123919) (movR32R32Effect 0x123919 3 0 13) (Reg.operands [.gpr 13] [])) #v[5226]
    (.letOp (n := 5275) (.out 0x12391c (rolR32Effect 0x12391c 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5273]
    (.letOp (n := 5276) (.exec 0x12391c (fun s => s.RIP = 0x12391c) (rolR32Effect 0x12391c 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5273]
    (.letOp (n := 5277) (.out 0x12391f (movR32R32Effect 0x12391f 3 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 13] []) (.reg (.gpr 11))) #v[5226]
    (.letOp (n := 5278) (.exec 0x12391f (fun s => s.RIP = 0x12391f) (movR32R32Effect 0x12391f 3 11 13) (Reg.operands [.gpr 13] [])) #v[5226]
    (.letOp (n := 5279) (.out 0x123922 (rolR32Effect 0x123922 4 11 21) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[5277]
    (.letOp (n := 5280) (.exec 0x123922 (fun s => s.RIP = 0x123922) (rolR32Effect 0x123922 4 11 21) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5277]
    (.letOp (n := 5281) (.out 0x123926 (xorR32R32Effect 0x123926 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[5279, 5275]
    (.letOp (n := 5282) (.exec 0x123926 (fun s => s.RIP = 0x123926) (xorR32R32Effect 0x123926 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[5279, 5275]
    (.letOp (n := 5283) (.out 0x123929 (movR32R32Effect 0x123929 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[5226]
    (.letOp (n := 5284) (.exec 0x123929 (fun s => s.RIP = 0x123929) (movR32R32Effect 0x123929 3 0 13) (Reg.operands [.gpr 13] [])) #v[5226]
    (.letOp (n := 5285) (.out 0x12392c (rolR32Effect 0x12392c 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5283]
    (.letOp (n := 5286) (.exec 0x12392c (fun s => s.RIP = 0x12392c) (rolR32Effect 0x12392c 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5283]
    (.letOp (n := 5287) (.out 0x12392f (xorR32R32Effect 0x12392f 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[5285, 5281]
    (.letOp (n := 5288) (.exec 0x12392f (fun s => s.RIP = 0x12392f) (xorR32R32Effect 0x12392f 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[5285, 5281]
    (b_l121930_134))))))))))))))))))))))))))))))))))))))

def bytes_l121930_133 : List UInt8 :=
  [0x89, 0xCF, 0x89, 0xCE, 0x89, 0xCA, 0xC1, 0xE9, 0x03, 0x31, 0xC1, 0x44, 0x01, 0x54, 0x24, 0x48,
    0x44, 0x01, 0xD1, 0x48, 0x89, 0x4C, 0x24, 0x28, 0x41, 0xC1, 0xEA, 0x0A, 0x45, 0x31, 0xDA, 0x8B,
    0x6C, 0x24, 0x0C, 0x44, 0x01, 0xD5, 0x44, 0x89, 0xE8, 0xC1, 0xC0, 0x1A, 0x45, 0x89, 0xEB, 0x41,
    0xC1, 0xC3, 0x15, 0x41, 0x31, 0xC3, 0x44, 0x89, 0xE8, 0xC1, 0xC0, 0x07, 0x44, 0x31, 0xD8] ++ bytes_l121930_134

theorem code_l121930_133 : ∀ x ∈ codeRange 0x1238f3 bytes_l121930_133, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x238f3 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_134

def b_l121930_132 : Block Op Label signature Reg.count 5212 :=
  .letOp (n := 5212) (.out 0x1238bb (movR32R32Effect 0x1238bb 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[5025]
    (.letOp (n := 5213) (.exec 0x1238bb (fun s => s.RIP = 0x1238bb) (movR32R32Effect 0x1238bb 3 7 14) (Reg.operands [.gpr 14] [])) #v[5025]
    (.letOp (n := 5214) (.out 0x1238be (andR32R32Effect 0x1238be 3 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[5212, 4911]
    (.letOp (n := 5215) (.exec 0x1238be (fun s => s.RIP = 0x1238be) (andR32R32Effect 0x1238be 3 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[5212, 4911]
    (.letOp (n := 5216) (.out 0x1238c1 (movR32R32Effect 0x1238c1 3 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 14] []) (.reg (.gpr 3))) #v[5025]
    (.letOp (n := 5217) (.exec 0x1238c1 (fun s => s.RIP = 0x1238c1) (movR32R32Effect 0x1238c1 3 3 14) (Reg.operands [.gpr 14] [])) #v[5025]
    (.letOp (n := 5218) (.out 0x1238c4 (xorR32R32Effect 0x1238c4 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[5216, 4911]
    (.letOp (n := 5219) (.exec 0x1238c4 (fun s => s.RIP = 0x1238c4) (xorR32R32Effect 0x1238c4 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[5216, 4911]
    (.letOp (n := 5220) (.out 0x1238c7 (andR32R32Effect 0x1238c7 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[5218, 5122]
    (.letOp (n := 5221) (.exec 0x1238c7 (fun s => s.RIP = 0x1238c7) (andR32R32Effect 0x1238c7 3 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[5218, 5122]
    (.letOp (n := 5222) (.out 0x1238ca (xorR32R32Effect 0x1238ca 2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[5220, 5214]
    (.letOp (n := 5223) (.exec 0x1238ca (fun s => s.RIP = 0x1238ca) (xorR32R32Effect 0x1238ca 2 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[5220, 5214]
    (.letOp (n := 5224) (.out 0x1238cc (addR32R32Effect 0x1238cc 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[5222, 5210]
    (.letOp (n := 5225) (.exec 0x1238cc (fun s => s.RIP = 0x1238cc) (addR32R32Effect 0x1238cc 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[5222, 5210]
    (.letOp (n := 5226) (.out 0x1238ce (addR32R32Effect 0x1238ce 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[4796, 5198]
    (.letOp (n := 5227) (.exec 0x1238ce (fun s => s.RIP = 0x1238ce) (addR32R32Effect 0x1238ce 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[4796, 5198]
    (.letOp (n := 5228) (.out 0x1238d1 (movR32R32Effect 0x1238d1 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[5063]
    (.letOp (n := 5229) (.exec 0x1238d1 (fun s => s.RIP = 0x1238d1) (movR32R32Effect 0x1238d1 3 6 10) (Reg.operands [.gpr 10] [])) #v[5063]
    (.letOp (n := 5230) (.out 0x1238d4 (rolR32Effect 0x1238d4 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5228]
    (.letOp (n := 5231) (.exec 0x1238d4 (fun s => s.RIP = 0x1238d4) (rolR32Effect 0x1238d4 3 6 15) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5228]
    (.letOp (n := 5232) (.out 0x1238d7 (addR32R32Effect 0x1238d7 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[5224, 5198]
    (.letOp (n := 5233) (.exec 0x1238d7 (fun s => s.RIP = 0x1238d7) (addR32R32Effect 0x1238d7 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[5224, 5198]
    (.letOp (n := 5234) (.out 0x1238d9 (movR32R32Effect 0x1238d9 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[5063]
    (.letOp (n := 5235) (.exec 0x1238d9 (fun s => s.RIP = 0x1238d9) (movR32R32Effect 0x1238d9 3 11 10) (Reg.operands [.gpr 10] [])) #v[5063]
    (.letOp (n := 5236) (.out 0x1238dc (rolR32Effect 0x1238dc 4 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[5234]
    (.letOp (n := 5237) (.exec 0x1238dc (fun s => s.RIP = 0x1238dc) (rolR32Effect 0x1238dc 4 11 13) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5234]
    (.letOp (n := 5238) (.out 0x1238e0 (xorR32R32Effect 0x1238e0 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[5236, 5230]
    (.letOp (n := 5239) (.exec 0x1238e0 (fun s => s.RIP = 0x1238e0) (xorR32R32Effect 0x1238e0 3 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[5236, 5230]
    (.letOp (n := 5240) (.out 0x1238e3 (movR32R32Effect 0x1238e3 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[5162]
    (.letOp (n := 5241) (.exec 0x1238e3 (fun s => s.RIP = 0x1238e3) (movR32R32Effect 0x1238e3 2 2 1) (Reg.operands [.gpr 1] [])) #v[5162]
    (.letOp (n := 5242) (.out 0x1238e5 (rolR32Effect 0x1238e5 3 2 25) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5240]
    (.letOp (n := 5243) (.exec 0x1238e5 (fun s => s.RIP = 0x1238e5) (rolR32Effect 0x1238e5 3 2 25) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5240]
    (.letOp (n := 5244) (.out 0x1238e8 (movR32R32Effect 0x1238e8 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[5162]
    (.letOp (n := 5245) (.exec 0x1238e8 (fun s => s.RIP = 0x1238e8) (movR32R32Effect 0x1238e8 2 0 1) (Reg.operands [.gpr 1] [])) #v[5162]
    (.letOp (n := 5246) (.out 0x1238ea (rolR32Effect 0x1238ea 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5244]
    (.letOp (n := 5247) (.exec 0x1238ea (fun s => s.RIP = 0x1238ea) (rolR32Effect 0x1238ea 3 0 14) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5244]
    (.letOp (n := 5248) (.out 0x1238ed (xorR32R32Effect 0x1238ed 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[5246, 5242]
    (.letOp (n := 5249) (.exec 0x1238ed (fun s => s.RIP = 0x1238ed) (xorR32R32Effect 0x1238ed 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[5246, 5242]
    (.letOp (n := 5250) (.exec 0x1238ef (StorePre 0x1238ef 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1238ef + BitVec.ofNat 64 4)) 4) (addMREffect 0x1238ef 4 32 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[5162, 4]
    (b_l121930_133)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_132 : List UInt8 :=
  [0x44, 0x89, 0xF7, 0x44, 0x21, 0xE7, 0x44, 0x89, 0xF3, 0x44, 0x31, 0xE3, 0x44, 0x21, 0xC3, 0x31,
    0xFB, 0x01, 0xF3, 0x41, 0x01, 0xC5, 0x44, 0x89, 0xD6, 0xC1, 0xC6, 0x0F, 0x01, 0xC3, 0x45, 0x89,
    0xD3, 0x41, 0xC1, 0xC3, 0x0D, 0x41, 0x31, 0xF3, 0x89, 0xCA, 0xC1, 0xC2, 0x19, 0x89, 0xC8, 0xC1,
    0xC0, 0x0E, 0x31, 0xD0, 0x01, 0x4C, 0x24, 0x70] ++ bytes_l121930_133

theorem code_l121930_132 : ∀ x ∈ codeRange 0x1238bb bytes_l121930_132, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x238bb 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_133

def b_l121930_131 : Block Op Label signature Reg.count 5172 :=
  .letOp (n := 5172) (.out 0x123885 (xorR32R32Effect 0x123885 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[5170, 5166]
    (.letOp (n := 5173) (.exec 0x123885 (fun s => s.RIP = 0x123885) (xorR32R32Effect 0x123885 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[5170, 5166]
    (.letOp (n := 5174) (.out 0x123887 (movR32R32Effect 0x123887 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[5120]
    (.letOp (n := 5175) (.exec 0x123887 (fun s => s.RIP = 0x123887) (movR32R32Effect 0x123887 3 0 9) (Reg.operands [.gpr 9] [])) #v[5120]
    (.letOp (n := 5176) (.out 0x12388a (rolR32Effect 0x12388a 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5174]
    (.letOp (n := 5177) (.exec 0x12388a (fun s => s.RIP = 0x12388a) (rolR32Effect 0x12388a 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5174]
    (.letOp (n := 5178) (.out 0x12388d (xorR32R32Effect 0x12388d 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[5176, 5172]
    (.letOp (n := 5179) (.exec 0x12388d (fun s => s.RIP = 0x12388d) (xorR32R32Effect 0x12388d 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[5176, 5172]
    (.letOp (n := 5180) (.out 0x12388f (movR32R32Effect 0x12388f 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[5049]
    (.letOp (n := 5181) (.exec 0x12388f (fun s => s.RIP = 0x12388f) (movR32R32Effect 0x12388f 2 6 2) (Reg.operands [.gpr 2] [])) #v[5049]
    (.letOp (n := 5182) (.out 0x123891 (xorR32R32Effect 0x123891 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[5180, 4905]
    (.letOp (n := 5183) (.exec 0x123891 (fun s => s.RIP = 0x123891) (xorR32R32Effect 0x123891 3 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[5180, 4905]
    (.letOp (n := 5184) (.out 0x123894 (andR32R32Effect 0x123894 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[5182, 5120]
    (.letOp (n := 5185) (.exec 0x123894 (fun s => s.RIP = 0x123894) (andR32R32Effect 0x123894 3 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[5182, 5120]
    (.letOp (n := 5186) (.out 0x123897 (xorR32R32Effect 0x123897 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[5184, 4905]
    (.letOp (n := 5187) (.exec 0x123897 (fun s => s.RIP = 0x123897) (xorR32R32Effect 0x123897 3 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[5184, 4905]
    (.letOp (n := 5188) (.out 0x12389a (addR32R32Effect 0x12389a 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[4788, 5162]
    (.letOp (n := 5189) (.exec 0x12389a (fun s => s.RIP = 0x12389a) (addR32R32Effect 0x12389a 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[4788, 5162]
    (.letOp (n := 5190) (.out 0x12389c (addR32R32Effect 0x12389c 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[5188, 5186]
    (.letOp (n := 5191) (.exec 0x12389c (fun s => s.RIP = 0x12389c) (addR32R32Effect 0x12389c 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[5188, 5186]
    (.letOp (n := 5192) (.out 0x12389e (movR32R32Effect 0x12389e 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[5122]
    (.letOp (n := 5193) (.exec 0x12389e (fun s => s.RIP = 0x12389e) (movR32R32Effect 0x12389e 3 6 8) (Reg.operands [.gpr 8] [])) #v[5122]
    (.letOp (n := 5194) (.out 0x1238a1 (rolR32Effect 0x1238a1 3 6 30) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5192]
    (.letOp (n := 5195) (.exec 0x1238a1 (fun s => s.RIP = 0x1238a1) (rolR32Effect 0x1238a1 3 6 30) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5192]
    (.letOp (n := 5196) (.out 0x1238a4 (addR32R32Effect 0x1238a4 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[5178, 5190]
    (.letOp (n := 5197) (.exec 0x1238a4 (fun s => s.RIP = 0x1238a4) (addR32R32Effect 0x1238a4 2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[5178, 5190]
    (.letOp (n := 5198) (.out 0x1238a6 (addEaxImm32Effect 0x1238a6 0x19a4c116) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[5196]
    (.letOp (n := 5199) (.exec 0x1238a6 (fun s => s.RIP = 0x1238a6) (addEaxImm32Effect 0x1238a6 0x19a4c116) (Reg.operands [.gpr 0] [])) #v[5196]
    (.letOp (n := 5200) (.out 0x1238ab (movR32R32Effect 0x1238ab 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[5122]
    (.letOp (n := 5201) (.exec 0x1238ab (fun s => s.RIP = 0x1238ab) (movR32R32Effect 0x1238ab 3 7 8) (Reg.operands [.gpr 8] [])) #v[5122]
    (.letOp (n := 5202) (.out 0x1238ae (rolR32Effect 0x1238ae 3 7 19) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[5200]
    (.letOp (n := 5203) (.exec 0x1238ae (fun s => s.RIP = 0x1238ae) (rolR32Effect 0x1238ae 3 7 19) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5200]
    (.letOp (n := 5204) (.out 0x1238b1 (xorR32R32Effect 0x1238b1 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[5202, 5194]
    (.letOp (n := 5205) (.exec 0x1238b1 (fun s => s.RIP = 0x1238b1) (xorR32R32Effect 0x1238b1 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[5202, 5194]
    (.letOp (n := 5206) (.out 0x1238b3 (movR32R32Effect 0x1238b3 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[5122]
    (.letOp (n := 5207) (.exec 0x1238b3 (fun s => s.RIP = 0x1238b3) (movR32R32Effect 0x1238b3 3 6 8) (Reg.operands [.gpr 8] [])) #v[5122]
    (.letOp (n := 5208) (.out 0x1238b6 (rolR32Effect 0x1238b6 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5206]
    (.letOp (n := 5209) (.exec 0x1238b6 (fun s => s.RIP = 0x1238b6) (rolR32Effect 0x1238b6 3 6 10) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5206]
    (.letOp (n := 5210) (.out 0x1238b9 (xorR32R32Effect 0x1238b9 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[5208, 5204]
    (.letOp (n := 5211) (.exec 0x1238b9 (fun s => s.RIP = 0x1238b9) (xorR32R32Effect 0x1238b9 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[5208, 5204]
    (b_l121930_132))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_131 : List UInt8 :=
  [0x31, 0xC6, 0x44, 0x89, 0xC8, 0xC1, 0xC0, 0x07, 0x31, 0xF0, 0x89, 0xD6, 0x44, 0x31, 0xFE, 0x44,
    0x21, 0xCE, 0x44, 0x31, 0xFE, 0x01, 0xCB, 0x01, 0xF3, 0x44, 0x89, 0xC6, 0xC1, 0xC6, 0x1E, 0x01,
    0xD8, 0x05, 0x16, 0xC1, 0xA4, 0x19, 0x44, 0x89, 0xC7, 0xC1, 0xC7, 0x13, 0x31, 0xF7, 0x44, 0x89,
    0xC6, 0xC1, 0xC6, 0x0A, 0x31, 0xFE] ++ bytes_l121930_132

theorem code_l121930_131 : ∀ x ∈ codeRange 0x123885 bytes_l121930_131, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23885 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_132

def b_l121930_130 : Block Op Label signature Reg.count 5134 :=
  .letOp (n := 5134) (.out 0x12384a (movR32R32Effect 0x12384a 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[5063]
    (.letOp (n := 5135) (.exec 0x12384a (fun s => s.RIP = 0x12384a) (movR32R32Effect 0x12384a 3 0 10) (Reg.operands [.gpr 10] [])) #v[5063]
    (.letOp (n := 5136) (.out 0x12384d (rolR32Effect 0x12384d 3 0 25) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5134]
    (.letOp (n := 5137) (.exec 0x12384d (fun s => s.RIP = 0x12384d) (rolR32Effect 0x12384d 3 0 25) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5134]
    (.letOp (n := 5138) (.out 0x123850 (movR32R32Effect 0x123850 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 10] []) (.reg (.gpr 7))) #v[5063]
    (.letOp (n := 5139) (.exec 0x123850 (fun s => s.RIP = 0x123850) (movR32R32Effect 0x123850 3 7 10) (Reg.operands [.gpr 10] [])) #v[5063]
    (.letOp (n := 5140) (.out 0x123853 (rolR32Effect 0x123853 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[5138]
    (.letOp (n := 5141) (.exec 0x123853 (fun s => s.RIP = 0x123853) (rolR32Effect 0x123853 3 7 14) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5138]
    (.letOp (n := 5142) (.out 0x123856 (xorR32R32Effect 0x123856 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[5140, 5136]
    (.letOp (n := 5143) (.exec 0x123856 (fun s => s.RIP = 0x123856) (xorR32R32Effect 0x123856 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[5140, 5136]
    (.letOp (n := 5144) (.out 0x123858 (movR32R32Effect 0x123858 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[5063]
    (.letOp (n := 5145) (.exec 0x123858 (fun s => s.RIP = 0x123858) (movR32R32Effect 0x123858 3 0 10) (Reg.operands [.gpr 10] [])) #v[5063]
    (.letOp (n := 5146) (.out 0x12385b (shrR32Effect 0x12385b 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5144]
    (.letOp (n := 5147) (.exec 0x12385b (fun s => s.RIP = 0x12385b) (shrR32Effect 0x12385b 3 0 3) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5144]
    (.letOp (n := 5148) (.out 0x12385e (xorR32R32Effect 0x12385e 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[5146, 5142]
    (.letOp (n := 5149) (.exec 0x12385e (fun s => s.RIP = 0x12385e) (xorR32R32Effect 0x12385e 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[5146, 5142]
    (.letOp (n := 5150) (.exec 0x123860 (StorePre 0x123860 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x123860 + BitVec.ofNat 64 4)) 4) (addMREffect 0x123860 4 32 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[4949, 4]
    (.letOp (n := 5151) (.out 0x123864 (addR32R32Effect 0x123864 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[5148, 4949]
    (.letOp (n := 5152) (.exec 0x123864 (fun s => s.RIP = 0x123864) (addR32R32Effect 0x123864 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[5148, 4949]
    (.letOp (n := 5153) (.exec 0x123866 (StorePre 0x123866 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x123866 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x123866 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[5151, 4]
    (.letOp (n := 5154) (.out 0x12386b (movR32R32Effect 0x12386b 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[4949]
    (.letOp (n := 5155) (.exec 0x12386b (fun s => s.RIP = 0x12386b) (movR32R32Effect 0x12386b 2 0 1) (Reg.operands [.gpr 1] [])) #v[4949]
    (.letOp (n := 5156) (.out 0x12386d (shrR32Effect 0x12386d 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5154]
    (.letOp (n := 5157) (.exec 0x12386d (fun s => s.RIP = 0x12386d) (shrR32Effect 0x12386d 3 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5154]
    (.letOp (n := 5158) (.out 0x123870 (xorR32R32Effect 0x123870 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[5156, 5132]
    (.letOp (n := 5159) (.exec 0x123870 (fun s => s.RIP = 0x123870) (xorR32R32Effect 0x123870 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[5156, 5132]
    (.letOp (n := 5160) (.out 0x123872 (movR64M64Effect 0x123872 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 5161) (.exec 0x123872 (LoadPre 0x123872 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x123872 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x123872 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5162) (.out 0x123877 (addR32R32Effect 0x123877 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[5160, 5158]
    (.letOp (n := 5163) (.exec 0x123877 (fun s => s.RIP = 0x123877) (addR32R32Effect 0x123877 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[5160, 5158]
    (.letOp (n := 5164) (.out 0x123879 (movR32R32Effect 0x123879 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[5120]
    (.letOp (n := 5165) (.exec 0x123879 (fun s => s.RIP = 0x123879) (movR32R32Effect 0x123879 3 0 9) (Reg.operands [.gpr 9] [])) #v[5120]
    (.letOp (n := 5166) (.out 0x12387c (rolR32Effect 0x12387c 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5164]
    (.letOp (n := 5167) (.exec 0x12387c (fun s => s.RIP = 0x12387c) (rolR32Effect 0x12387c 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5164]
    (.letOp (n := 5168) (.out 0x12387f (movR32R32Effect 0x12387f 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[5120]
    (.letOp (n := 5169) (.exec 0x12387f (fun s => s.RIP = 0x12387f) (movR32R32Effect 0x12387f 3 6 9) (Reg.operands [.gpr 9] [])) #v[5120]
    (.letOp (n := 5170) (.out 0x123882 (rolR32Effect 0x123882 3 6 21) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5168]
    (.letOp (n := 5171) (.exec 0x123882 (fun s => s.RIP = 0x123882) (rolR32Effect 0x123882 3 6 21) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5168]
    (b_l121930_131))))))))))))))))))))))))))))))))))))))

def bytes_l121930_130 : List UInt8 :=
  [0x44, 0x89, 0xD0, 0xC1, 0xC0, 0x19, 0x44, 0x89, 0xD7, 0xC1, 0xC7, 0x0E, 0x31, 0xC7, 0x44, 0x89,
    0xD0, 0xC1, 0xE8, 0x03, 0x31, 0xF8, 0x01, 0x4C, 0x24, 0x14, 0x01, 0xC8, 0x48, 0x89, 0x44, 0x24,
    0x40, 0x89, 0xC8, 0xC1, 0xE8, 0x0A, 0x31, 0xF0, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x01, 0xC1, 0x44,
    0x89, 0xC8, 0xC1, 0xC0, 0x1A, 0x44, 0x89, 0xCE, 0xC1, 0xC6, 0x15] ++ bytes_l121930_131

theorem code_l121930_130 : ∀ x ∈ codeRange 0x12384a bytes_l121930_130, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2384a 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_131

def b_l121930_129 : Block Op Label signature Reg.count 5094 :=
  .letOp (n := 5094) (.out 0x123813 (movR32R32Effect 0x123813 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[5025]
    (.letOp (n := 5095) (.exec 0x123813 (fun s => s.RIP = 0x123813) (movR32R32Effect 0x123813 3 7 14) (Reg.operands [.gpr 14] [])) #v[5025]
    (.letOp (n := 5096) (.out 0x123816 (rolR32Effect 0x123816 3 7 19) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[5094]
    (.letOp (n := 5097) (.exec 0x123816 (fun s => s.RIP = 0x123816) (rolR32Effect 0x123816 3 7 19) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5094]
    (.letOp (n := 5098) (.out 0x123819 (xorR32R32Effect 0x123819 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[5096, 5092]
    (.letOp (n := 5099) (.exec 0x123819 (fun s => s.RIP = 0x123819) (xorR32R32Effect 0x123819 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[5096, 5092]
    (.letOp (n := 5100) (.out 0x12381b (movR32R32Effect 0x12381b 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[5025]
    (.letOp (n := 5101) (.exec 0x12381b (fun s => s.RIP = 0x12381b) (movR32R32Effect 0x12381b 3 6 14) (Reg.operands [.gpr 14] [])) #v[5025]
    (.letOp (n := 5102) (.out 0x12381e (rolR32Effect 0x12381e 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5100]
    (.letOp (n := 5103) (.exec 0x12381e (fun s => s.RIP = 0x12381e) (rolR32Effect 0x12381e 3 6 10) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5100]
    (.letOp (n := 5104) (.out 0x123821 (xorR32R32Effect 0x123821 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[5102, 5098]
    (.letOp (n := 5105) (.exec 0x123821 (fun s => s.RIP = 0x123821) (xorR32R32Effect 0x123821 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[5102, 5098]
    (.letOp (n := 5106) (.out 0x123823 (movR32R32Effect 0x123823 3 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[4911]
    (.letOp (n := 5107) (.exec 0x123823 (fun s => s.RIP = 0x123823) (movR32R32Effect 0x123823 3 7 12) (Reg.operands [.gpr 12] [])) #v[4911]
    (.letOp (n := 5108) (.out 0x123826 (andR32R32Effect 0x123826 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[5106, 4796]
    (.letOp (n := 5109) (.exec 0x123826 (fun s => s.RIP = 0x123826) (andR32R32Effect 0x123826 3 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[5106, 4796]
    (.letOp (n := 5110) (.out 0x123829 (movR32R32Effect 0x123829 3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[4911]
    (.letOp (n := 5111) (.exec 0x123829 (fun s => s.RIP = 0x123829) (movR32R32Effect 0x123829 3 8 12) (Reg.operands [.gpr 12] [])) #v[4911]
    (.letOp (n := 5112) (.out 0x12382c (xorR32R32Effect 0x12382c 3 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[5110, 4796]
    (.letOp (n := 5113) (.exec 0x12382c (fun s => s.RIP = 0x12382c) (xorR32R32Effect 0x12382c 3 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[5110, 4796]
    (.letOp (n := 5114) (.out 0x12382f (andR32R32Effect 0x12382f 3 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[5112, 5025]
    (.letOp (n := 5115) (.exec 0x12382f (fun s => s.RIP = 0x12382f) (andR32R32Effect 0x12382f 3 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[5112, 5025]
    (.letOp (n := 5116) (.out 0x123832 (xorR32R32Effect 0x123832 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[5114, 5108]
    (.letOp (n := 5117) (.exec 0x123832 (fun s => s.RIP = 0x123832) (xorR32R32Effect 0x123832 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[5114, 5108]
    (.letOp (n := 5118) (.out 0x123835 (addR32R32Effect 0x123835 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[5116, 5104]
    (.letOp (n := 5119) (.exec 0x123835 (fun s => s.RIP = 0x123835) (addR32R32Effect 0x123835 3 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[5116, 5104]
    (.letOp (n := 5120) (.out 0x123838 (addR32R32Effect 0x123838 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[4684, 5088]
    (.letOp (n := 5121) (.exec 0x123838 (fun s => s.RIP = 0x123838) (addR32R32Effect 0x123838 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[4684, 5088]
    (.letOp (n := 5122) (.out 0x12383b (addR32R32Effect 0x12383b 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[5118, 5088]
    (.letOp (n := 5123) (.exec 0x12383b (fun s => s.RIP = 0x12383b) (addR32R32Effect 0x12383b 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[5118, 5088]
    (.letOp (n := 5124) (.out 0x12383e (movR32R32Effect 0x12383e 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[4949]
    (.letOp (n := 5125) (.exec 0x12383e (fun s => s.RIP = 0x12383e) (movR32R32Effect 0x12383e 2 0 1) (Reg.operands [.gpr 1] [])) #v[4949]
    (.letOp (n := 5126) (.out 0x123840 (rolR32Effect 0x123840 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5124]
    (.letOp (n := 5127) (.exec 0x123840 (fun s => s.RIP = 0x123840) (rolR32Effect 0x123840 3 0 15) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5124]
    (.letOp (n := 5128) (.out 0x123843 (movR32R32Effect 0x123843 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[4949]
    (.letOp (n := 5129) (.exec 0x123843 (fun s => s.RIP = 0x123843) (movR32R32Effect 0x123843 2 6 1) (Reg.operands [.gpr 1] [])) #v[4949]
    (.letOp (n := 5130) (.out 0x123845 (rolR32Effect 0x123845 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5128]
    (.letOp (n := 5131) (.exec 0x123845 (fun s => s.RIP = 0x123845) (rolR32Effect 0x123845 3 6 13) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5128]
    (.letOp (n := 5132) (.out 0x123848 (xorR32R32Effect 0x123848 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[5130, 5126]
    (.letOp (n := 5133) (.exec 0x123848 (fun s => s.RIP = 0x123848) (xorR32R32Effect 0x123848 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[5130, 5126]
    (b_l121930_130))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_129 : List UInt8 :=
  [0x44, 0x89, 0xF7, 0xC1, 0xC7, 0x13, 0x31, 0xF7, 0x44, 0x89, 0xF6, 0xC1, 0xC6, 0x0A, 0x31, 0xFE,
    0x44, 0x89, 0xE7, 0x44, 0x21, 0xEF, 0x45, 0x89, 0xE0, 0x45, 0x31, 0xE8, 0x45, 0x21, 0xF0, 0x41,
    0x31, 0xF8, 0x41, 0x01, 0xF0, 0x41, 0x01, 0xC1, 0x41, 0x01, 0xC0, 0x89, 0xC8, 0xC1, 0xC0, 0x0F,
    0x89, 0xCE, 0xC1, 0xC6, 0x0D, 0x31, 0xC6] ++ bytes_l121930_130

theorem code_l121930_129 : ∀ x ∈ codeRange 0x123813 bytes_l121930_129, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23813 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_130

def b_l121930_128 : Block Op Label signature Reg.count 5055 :=
  .letOp (n := 5055) (.out 0x1237d9 (xorR32R32Effect 0x1237d9 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[5047, 5031]
    (.letOp (n := 5056) (.exec 0x1237d9 (fun s => s.RIP = 0x1237d9) (xorR32R32Effect 0x1237d9 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[5047, 5031]
    (.letOp (n := 5057) (.out 0x1237db (movR32R32Effect 0x1237db 2 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5019]
    (.letOp (n := 5058) (.exec 0x1237db (fun s => s.RIP = 0x1237db) (movR32R32Effect 0x1237db 2 6 5) (Reg.operands [.gpr 5] [])) #v[5019]
    (.letOp (n := 5059) (.out 0x1237dd (rolR32Effect 0x1237dd 3 6 21) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5057]
    (.letOp (n := 5060) (.exec 0x1237dd (fun s => s.RIP = 0x1237dd) (rolR32Effect 0x1237dd 3 6 21) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5057]
    (.letOp (n := 5061) (.out 0x1237e0 (movR32M32Effect 0x1237e0 10 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 5062) (.exec 0x1237e0 (LoadPre 0x1237e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1237e0 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1237e0 10 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5063) (.out 0x1237e5 (addR32R32Effect 0x1237e5 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[5061, 5055]
    (.letOp (n := 5064) (.exec 0x1237e5 (fun s => s.RIP = 0x1237e5) (addR32R32Effect 0x1237e5 3 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[5061, 5055]
    (.letOp (n := 5065) (.out 0x1237e8 (movR32R32Effect 0x1237e8 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5019]
    (.letOp (n := 5066) (.exec 0x1237e8 (fun s => s.RIP = 0x1237e8) (movR32R32Effect 0x1237e8 2 0 5) (Reg.operands [.gpr 5] [])) #v[5019]
    (.letOp (n := 5067) (.out 0x1237ea (rolR32Effect 0x1237ea 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5065]
    (.letOp (n := 5068) (.exec 0x1237ea (fun s => s.RIP = 0x1237ea) (rolR32Effect 0x1237ea 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5065]
    (.letOp (n := 5069) (.out 0x1237ed (xorR32R32Effect 0x1237ed 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[5059, 5053]
    (.letOp (n := 5070) (.exec 0x1237ed (fun s => s.RIP = 0x1237ed) (xorR32R32Effect 0x1237ed 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[5059, 5053]
    (.letOp (n := 5071) (.out 0x1237ef (xorR32R32Effect 0x1237ef 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[5067, 5069]
    (.letOp (n := 5072) (.exec 0x1237ef (fun s => s.RIP = 0x1237ef) (xorR32R32Effect 0x1237ef 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[5067, 5069]
    (.letOp (n := 5073) (.out 0x1237f1 (movR32R32Effect 0x1237f1 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[4905]
    (.letOp (n := 5074) (.exec 0x1237f1 (fun s => s.RIP = 0x1237f1) (movR32R32Effect 0x1237f1 3 6 15) (Reg.operands [.gpr 15] [])) #v[4905]
    (.letOp (n := 5075) (.out 0x1237f4 (xorR32R32Effect 0x1237f4 2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[5073, 4788]
    (.letOp (n := 5076) (.exec 0x1237f4 (fun s => s.RIP = 0x1237f4) (xorR32R32Effect 0x1237f4 2 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[5073, 4788]
    (.letOp (n := 5077) (.out 0x1237f6 (andR32R32Effect 0x1237f6 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[5075, 5049]
    (.letOp (n := 5078) (.exec 0x1237f6 (fun s => s.RIP = 0x1237f6) (andR32R32Effect 0x1237f6 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[5075, 5049]
    (.letOp (n := 5079) (.exec 0x1237f8 (StorePre 0x1237f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1237f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1237f8 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5019, 4]
    (.letOp (n := 5080) (.out 0x1237fd (xorR32R32Effect 0x1237fd 2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[5077, 4788]
    (.letOp (n := 5081) (.exec 0x1237fd (fun s => s.RIP = 0x1237fd) (xorR32R32Effect 0x1237fd 2 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[5077, 4788]
    (.letOp (n := 5082) (.out 0x1237ff (addR32R32Effect 0x1237ff 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[4682, 5063]
    (.letOp (n := 5083) (.exec 0x1237ff (fun s => s.RIP = 0x1237ff) (addR32R32Effect 0x1237ff 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[4682, 5063]
    (.letOp (n := 5084) (.out 0x123802 (addR32R32Effect 0x123802 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[5082, 5080]
    (.letOp (n := 5085) (.exec 0x123802 (fun s => s.RIP = 0x123802) (addR32R32Effect 0x123802 3 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[5082, 5080]
    (.letOp (n := 5086) (.out 0x123805 (addR32R32Effect 0x123805 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[5071, 5084]
    (.letOp (n := 5087) (.exec 0x123805 (fun s => s.RIP = 0x123805) (addR32R32Effect 0x123805 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[5071, 5084]
    (.letOp (n := 5088) (.out 0x123808 (addEaxImm32Effect 0x123808 0x106aa070) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[5086]
    (.letOp (n := 5089) (.exec 0x123808 (fun s => s.RIP = 0x123808) (addEaxImm32Effect 0x123808 0x106aa070) (Reg.operands [.gpr 0] [])) #v[5086]
    (.letOp (n := 5090) (.out 0x12380d (movR32R32Effect 0x12380d 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[5025]
    (.letOp (n := 5091) (.exec 0x12380d (fun s => s.RIP = 0x12380d) (movR32R32Effect 0x12380d 3 6 14) (Reg.operands [.gpr 14] [])) #v[5025]
    (.letOp (n := 5092) (.out 0x123810 (rolR32Effect 0x123810 3 6 30) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5090]
    (.letOp (n := 5093) (.exec 0x123810 (fun s => s.RIP = 0x123810) (rolR32Effect 0x123810 3 6 30) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5090]
    (b_l121930_129)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_128 : List UInt8 :=
  [0x31, 0xF0, 0x89, 0xEE, 0xC1, 0xC6, 0x15, 0x44, 0x8B, 0x54, 0x24, 0x40, 0x41, 0x01, 0xC2, 0x89,
    0xE8, 0xC1, 0xC0, 0x07, 0x31, 0xFE, 0x31, 0xF0, 0x44, 0x89, 0xFE, 0x31, 0xDE, 0x21, 0xD6, 0x48,
    0x89, 0x6C, 0x24, 0x38, 0x31, 0xDE, 0x45, 0x01, 0xD3, 0x41, 0x01, 0xF3, 0x44, 0x01, 0xD8, 0x05,
    0x70, 0xA0, 0x6A, 0x10, 0x44, 0x89, 0xF6, 0xC1, 0xC6, 0x1E] ++ bytes_l121930_129

theorem code_l121930_128 : ∀ x ∈ codeRange 0x1237d9 bytes_l121930_128, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x237d9 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_129

def b_l121930_127 : Block Op Label signature Reg.count 5017 :=
  .letOp (n := 5017) (.out 0x12379d (movR64M64Effect 0x12379d 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 5018) (.exec 0x12379d (LoadPre 0x12379d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12379d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12379d 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 5019) (.out 0x1237a2 (addR32R32Effect 0x1237a2 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[5017, 4977]
    (.letOp (n := 5020) (.exec 0x1237a2 (fun s => s.RIP = 0x1237a2) (addR32R32Effect 0x1237a2 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[5017, 4977]
    (.letOp (n := 5021) (.out 0x1237a4 (movR32R32Effect 0x1237a4 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[4949]
    (.letOp (n := 5022) (.exec 0x1237a4 (fun s => s.RIP = 0x1237a4) (movR32R32Effect 0x1237a4 3 8 1) (Reg.operands [.gpr 1] [])) #v[4949]
    (.letOp (n := 5023) (.out 0x1237a7 (rolR32Effect 0x1237a7 4 8 25) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[5021]
    (.letOp (n := 5024) (.exec 0x1237a7 (fun s => s.RIP = 0x1237a7) (rolR32Effect 0x1237a7 4 8 25) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5021]
    (.letOp (n := 5025) (.out 0x1237ab (addR32R32Effect 0x1237ab 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[5011, 4977]
    (.letOp (n := 5026) (.exec 0x1237ab (fun s => s.RIP = 0x1237ab) (addR32R32Effect 0x1237ab 3 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[5011, 4977]
    (.letOp (n := 5027) (.out 0x1237ae (movR32R32Effect 0x1237ae 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[4949]
    (.letOp (n := 5028) (.exec 0x1237ae (fun s => s.RIP = 0x1237ae) (movR32R32Effect 0x1237ae 2 0 1) (Reg.operands [.gpr 1] [])) #v[4949]
    (.letOp (n := 5029) (.out 0x1237b0 (rolR32Effect 0x1237b0 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5027]
    (.letOp (n := 5030) (.exec 0x1237b0 (fun s => s.RIP = 0x1237b0) (rolR32Effect 0x1237b0 3 0 14) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5027]
    (.letOp (n := 5031) (.out 0x1237b3 (xorR32R32Effect 0x1237b3 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[5015, 5009]
    (.letOp (n := 5032) (.exec 0x1237b3 (fun s => s.RIP = 0x1237b3) (xorR32R32Effect 0x1237b3 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[5015, 5009]
    (.letOp (n := 5033) (.out 0x1237b5 (xorR32R32Effect 0x1237b5 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[5029, 5023]
    (.letOp (n := 5034) (.exec 0x1237b5 (fun s => s.RIP = 0x1237b5) (xorR32R32Effect 0x1237b5 3 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[5029, 5023]
    (.letOp (n := 5035) (.out 0x1237b8 (movR32R32Effect 0x1237b8 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[4949]
    (.letOp (n := 5036) (.exec 0x1237b8 (fun s => s.RIP = 0x1237b8) (movR32R32Effect 0x1237b8 2 2 1) (Reg.operands [.gpr 1] [])) #v[4949]
    (.letOp (n := 5037) (.out 0x1237ba (shrR32Effect 0x1237ba 3 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[5035]
    (.letOp (n := 5038) (.exec 0x1237ba (fun s => s.RIP = 0x1237ba) (shrR32Effect 0x1237ba 3 2 3) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5035]
    (.letOp (n := 5039) (.out 0x1237bd (xorR32R32Effect 0x1237bd 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[5037, 5033]
    (.letOp (n := 5040) (.exec 0x1237bd (fun s => s.RIP = 0x1237bd) (xorR32R32Effect 0x1237bd 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[5037, 5033]
    (.letOp (n := 5041) (.exec 0x1237bf (StorePre 0x1237bf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1237bf + BitVec.ofNat 64 5)) 4) (addMREffect 0x1237bf 5 32 10 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[4913, 4]
    (.letOp (n := 5042) (.out 0x1237c4 (addR32R32Effect 0x1237c4 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[5039, 4913]
    (.letOp (n := 5043) (.exec 0x1237c4 (fun s => s.RIP = 0x1237c4) (addR32R32Effect 0x1237c4 3 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[5039, 4913]
    (.letOp (n := 5044) (.exec 0x1237c7 (StorePre 0x1237c7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1237c7 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1237c7 2 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[5042, 4]
    (.letOp (n := 5045) (.out 0x1237cb (movR32R32Effect 0x1237cb 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[4913]
    (.letOp (n := 5046) (.exec 0x1237cb (fun s => s.RIP = 0x1237cb) (movR32R32Effect 0x1237cb 3 0 10) (Reg.operands [.gpr 10] [])) #v[4913]
    (.letOp (n := 5047) (.out 0x1237ce (shrR32Effect 0x1237ce 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[5045]
    (.letOp (n := 5048) (.exec 0x1237ce (fun s => s.RIP = 0x1237ce) (shrR32Effect 0x1237ce 3 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5045]
    (.letOp (n := 5049) (.out 0x1237d1 (movR64R64Effect 0x1237d1 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5019]
    (.letOp (n := 5050) (.exec 0x1237d1 (fun s => s.RIP = 0x1237d1) (movR64R64Effect 0x1237d1 2 5) (Reg.operands [.gpr 5] [])) #v[5019]
    (.letOp (n := 5051) (.out 0x1237d4 (movR32R32Effect 0x1237d4 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5019]
    (.letOp (n := 5052) (.exec 0x1237d4 (fun s => s.RIP = 0x1237d4) (movR32R32Effect 0x1237d4 2 7 5) (Reg.operands [.gpr 5] [])) #v[5019]
    (.letOp (n := 5053) (.out 0x1237d6 (rolR32Effect 0x1237d6 3 7 26) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[5051]
    (.letOp (n := 5054) (.exec 0x1237d6 (fun s => s.RIP = 0x1237d6) (rolR32Effect 0x1237d6 3 7 26) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5051]
    (b_l121930_128))))))))))))))))))))))))))))))))))))))

def bytes_l121930_127 : List UInt8 :=
  [0x48, 0x8B, 0x6C, 0x24, 0x38, 0x01, 0xC5, 0x41, 0x89, 0xC8, 0x41, 0xC1, 0xC0, 0x19, 0x41, 0x01,
    0xC6, 0x89, 0xC8, 0xC1, 0xC0, 0x0E, 0x31, 0xFE, 0x44, 0x31, 0xC0, 0x89, 0xCA, 0xC1, 0xEA, 0x03,
    0x31, 0xC2, 0x44, 0x01, 0x54, 0x24, 0x78, 0x44, 0x01, 0xD2, 0x89, 0x54, 0x24, 0x04, 0x44, 0x89,
    0xD0, 0xC1, 0xE8, 0x0A, 0x48, 0x89, 0xEA, 0x89, 0xEF, 0xC1, 0xC7, 0x1A] ++ bytes_l121930_128

theorem code_l121930_127 : ∀ x ∈ codeRange 0x12379d bytes_l121930_127, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2379d 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_128

def b_l121930_126 : Block Op Label signature Reg.count 4977 :=
  .letOp (n := 4977) (.out 0x123761 (addEaxImm32Effect 0x123761 0xf40e3585) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[4975]
    (.letOp (n := 4978) (.exec 0x123761 (fun s => s.RIP = 0x123761) (addEaxImm32Effect 0x123761 0xf40e3585) (Reg.operands [.gpr 0] [])) #v[4975]
    (.letOp (n := 4979) (.out 0x123766 (movR32R32Effect 0x123766 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[4911]
    (.letOp (n := 4980) (.exec 0x123766 (fun s => s.RIP = 0x123766) (movR32R32Effect 0x123766 3 2 12) (Reg.operands [.gpr 12] [])) #v[4911]
    (.letOp (n := 4981) (.out 0x123769 (rolR32Effect 0x123769 3 2 30) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[4979]
    (.letOp (n := 4982) (.exec 0x123769 (fun s => s.RIP = 0x123769) (rolR32Effect 0x123769 3 2 30) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4979]
    (.letOp (n := 4983) (.out 0x12376c (movR32R32Effect 0x12376c 3 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[4911]
    (.letOp (n := 4984) (.exec 0x12376c (fun s => s.RIP = 0x12376c) (movR32R32Effect 0x12376c 3 6 12) (Reg.operands [.gpr 12] [])) #v[4911]
    (.letOp (n := 4985) (.out 0x12376f (rolR32Effect 0x12376f 3 6 19) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[4983]
    (.letOp (n := 4986) (.exec 0x12376f (fun s => s.RIP = 0x12376f) (rolR32Effect 0x12376f 3 6 19) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4983]
    (.letOp (n := 4987) (.out 0x123772 (xorR32R32Effect 0x123772 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[4985, 4981]
    (.letOp (n := 4988) (.exec 0x123772 (fun s => s.RIP = 0x123772) (xorR32R32Effect 0x123772 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[4985, 4981]
    (.letOp (n := 4989) (.out 0x123774 (movR32R32Effect 0x123774 3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[4911]
    (.letOp (n := 4990) (.exec 0x123774 (fun s => s.RIP = 0x123774) (movR32R32Effect 0x123774 3 8 12) (Reg.operands [.gpr 12] [])) #v[4911]
    (.letOp (n := 4991) (.out 0x123777 (rolR32Effect 0x123777 4 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4989]
    (.letOp (n := 4992) (.exec 0x123777 (fun s => s.RIP = 0x123777) (rolR32Effect 0x123777 4 8 10) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4989]
    (.letOp (n := 4993) (.out 0x12377b (xorR32R32Effect 0x12377b 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[4991, 4987]
    (.letOp (n := 4994) (.exec 0x12377b (fun s => s.RIP = 0x12377b) (xorR32R32Effect 0x12377b 3 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[4991, 4987]
    (.letOp (n := 4995) (.out 0x12377e (movR32R32Effect 0x12377e 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[4796]
    (.letOp (n := 4996) (.exec 0x12377e (fun s => s.RIP = 0x12377e) (movR32R32Effect 0x12377e 3 6 13) (Reg.operands [.gpr 13] [])) #v[4796]
    (.letOp (n := 4997) (.out 0x123781 (andR32R32Effect 0x123781 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[4995, 4684]
    (.letOp (n := 4998) (.exec 0x123781 (fun s => s.RIP = 0x123781) (andR32R32Effect 0x123781 3 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[4995, 4684]
    (.letOp (n := 4999) (.out 0x123784 (movR32R32Effect 0x123784 3 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 13] []) (.reg (.gpr 14))) #v[4796]
    (.letOp (n := 5000) (.exec 0x123784 (fun s => s.RIP = 0x123784) (movR32R32Effect 0x123784 3 14 13) (Reg.operands [.gpr 13] [])) #v[4796]
    (.letOp (n := 5001) (.out 0x123787 (xorR32R32Effect 0x123787 3 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[4999, 4684]
    (.letOp (n := 5002) (.exec 0x123787 (fun s => s.RIP = 0x123787) (xorR32R32Effect 0x123787 3 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[4999, 4684]
    (.letOp (n := 5003) (.out 0x12378a (andR32R32Effect 0x12378a 3 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[5001, 4911]
    (.letOp (n := 5004) (.exec 0x12378a (fun s => s.RIP = 0x12378a) (andR32R32Effect 0x12378a 3 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[5001, 4911]
    (.letOp (n := 5005) (.out 0x12378d (xorR32R32Effect 0x12378d 3 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[5003, 4997]
    (.letOp (n := 5006) (.exec 0x12378d (fun s => s.RIP = 0x12378d) (xorR32R32Effect 0x12378d 3 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[5003, 4997]
    (.letOp (n := 5007) (.out 0x123790 (movR32R32Effect 0x123790 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[4858]
    (.letOp (n := 5008) (.exec 0x123790 (fun s => s.RIP = 0x123790) (movR32R32Effect 0x123790 2 7 5) (Reg.operands [.gpr 5] [])) #v[4858]
    (.letOp (n := 5009) (.out 0x123792 (rolR32Effect 0x123792 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[5007]
    (.letOp (n := 5010) (.exec 0x123792 (fun s => s.RIP = 0x123792) (rolR32Effect 0x123792 3 7 15) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5007]
    (.letOp (n := 5011) (.out 0x123795 (addR32R32Effect 0x123795 3 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[5005, 4993]
    (.letOp (n := 5012) (.exec 0x123795 (fun s => s.RIP = 0x123795) (addR32R32Effect 0x123795 3 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[5005, 4993]
    (.letOp (n := 5013) (.out 0x123798 (movR32R32Effect 0x123798 2 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[4858]
    (.letOp (n := 5014) (.exec 0x123798 (fun s => s.RIP = 0x123798) (movR32R32Effect 0x123798 2 6 5) (Reg.operands [.gpr 5] [])) #v[4858]
    (.letOp (n := 5015) (.out 0x12379a (rolR32Effect 0x12379a 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[5013]
    (.letOp (n := 5016) (.exec 0x12379a (fun s => s.RIP = 0x12379a) (rolR32Effect 0x12379a 3 6 13) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5013]
    (b_l121930_127))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_126 : List UInt8 :=
  [0x05, 0x85, 0x35, 0x0E, 0xF4, 0x44, 0x89, 0xE2, 0xC1, 0xC2, 0x1E, 0x44, 0x89, 0xE6, 0xC1, 0xC6,
    0x13, 0x31, 0xD6, 0x45, 0x89, 0xE0, 0x41, 0xC1, 0xC0, 0x0A, 0x41, 0x31, 0xF0, 0x44, 0x89, 0xEE,
    0x44, 0x21, 0xCE, 0x45, 0x89, 0xEE, 0x45, 0x31, 0xCE, 0x45, 0x21, 0xE6, 0x41, 0x31, 0xF6, 0x89,
    0xEF, 0xC1, 0xC7, 0x0F, 0x45, 0x01, 0xC6, 0x89, 0xEE, 0xC1, 0xC6, 0x0D] ++ bytes_l121930_127

theorem code_l121930_126 : ∀ x ∈ codeRange 0x123761 bytes_l121930_126, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23761 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_127

def b_l121930_125 : Block Op Label signature Reg.count 4937 :=
  .letOp (n := 4937) (.out 0x12372c (movR32R32Effect 0x12372c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[4899]
    (.letOp (n := 4938) (.exec 0x12372c (fun s => s.RIP = 0x12372c) (movR32R32Effect 0x12372c 2 0 1) (Reg.operands [.gpr 1] [])) #v[4899]
    (.letOp (n := 4939) (.out 0x12372e (shrR32Effect 0x12372e 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4937]
    (.letOp (n := 4940) (.exec 0x12372e (fun s => s.RIP = 0x12372e) (shrR32Effect 0x12372e 3 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4937]
    (.letOp (n := 4941) (.out 0x123731 (xorR32R32Effect 0x123731 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[4939, 4919]
    (.letOp (n := 4942) (.exec 0x123731 (fun s => s.RIP = 0x123731) (xorR32R32Effect 0x123731 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[4939, 4919]
    (.letOp (n := 4943) (.out 0x123733 (movR32R32Effect 0x123733 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[4905]
    (.letOp (n := 4944) (.exec 0x123733 (fun s => s.RIP = 0x123733) (movR32R32Effect 0x123733 3 6 15) (Reg.operands [.gpr 15] [])) #v[4905]
    (.letOp (n := 4945) (.out 0x123736 (rolR32Effect 0x123736 3 6 26) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[4943]
    (.letOp (n := 4946) (.exec 0x123736 (fun s => s.RIP = 0x123736) (rolR32Effect 0x123736 3 6 26) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4943]
    (.letOp (n := 4947) (.out 0x123739 (movR32M32LowEffect 0x123739 1 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 4948) (.exec 0x123739 (LoadPre 0x123739 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x123739 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x123739 1 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 4949) (.out 0x12373d (addR32R32Effect 0x12373d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[4947, 4941]
    (.letOp (n := 4950) (.exec 0x12373d (fun s => s.RIP = 0x12373d) (addR32R32Effect 0x12373d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[4947, 4941]
    (.letOp (n := 4951) (.out 0x12373f (movR32R32Effect 0x12373f 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[4905]
    (.letOp (n := 4952) (.exec 0x12373f (fun s => s.RIP = 0x12373f) (movR32R32Effect 0x12373f 3 0 15) (Reg.operands [.gpr 15] [])) #v[4905]
    (.letOp (n := 4953) (.out 0x123742 (rolR32Effect 0x123742 3 0 21) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4951]
    (.letOp (n := 4954) (.exec 0x123742 (fun s => s.RIP = 0x123742) (rolR32Effect 0x123742 3 0 21) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4951]
    (.letOp (n := 4955) (.out 0x123745 (xorR32R32Effect 0x123745 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[4953, 4945]
    (.letOp (n := 4956) (.exec 0x123745 (fun s => s.RIP = 0x123745) (xorR32R32Effect 0x123745 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[4953, 4945]
    (.letOp (n := 4957) (.out 0x123747 (movR32R32Effect 0x123747 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[4905]
    (.letOp (n := 4958) (.exec 0x123747 (fun s => s.RIP = 0x123747) (movR32R32Effect 0x123747 3 6 15) (Reg.operands [.gpr 15] [])) #v[4905]
    (.letOp (n := 4959) (.out 0x12374a (rolR32Effect 0x12374a 3 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[4957]
    (.letOp (n := 4960) (.exec 0x12374a (fun s => s.RIP = 0x12374a) (rolR32Effect 0x12374a 3 6 7) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4957]
    (.letOp (n := 4961) (.out 0x12374d (xorR32R32Effect 0x12374d 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[4959, 4955]
    (.letOp (n := 4962) (.exec 0x12374d (fun s => s.RIP = 0x12374d) (xorR32R32Effect 0x12374d 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[4959, 4955]
    (.letOp (n := 4963) (.out 0x12374f (movR32R32Effect 0x12374f 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[4788]
    (.letOp (n := 4964) (.exec 0x12374f (fun s => s.RIP = 0x12374f) (movR32R32Effect 0x12374f 2 0 3) (Reg.operands [.gpr 3] [])) #v[4788]
    (.letOp (n := 4965) (.out 0x123751 (xorR32R32Effect 0x123751 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[4963, 4682]
    (.letOp (n := 4966) (.exec 0x123751 (fun s => s.RIP = 0x123751) (xorR32R32Effect 0x123751 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[4963, 4682]
    (.letOp (n := 4967) (.out 0x123754 (andR32R32Effect 0x123754 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[4965, 4905]
    (.letOp (n := 4968) (.exec 0x123754 (fun s => s.RIP = 0x123754) (andR32R32Effect 0x123754 3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[4965, 4905]
    (.letOp (n := 4969) (.out 0x123757 (xorR32R32Effect 0x123757 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[4967, 4682]
    (.letOp (n := 4970) (.exec 0x123757 (fun s => s.RIP = 0x123757) (xorR32R32Effect 0x123757 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[4967, 4682]
    (.letOp (n := 4971) (.out 0x12375a (addR32R32Effect 0x12375a 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[4580, 4949]
    (.letOp (n := 4972) (.exec 0x12375a (fun s => s.RIP = 0x12375a) (addR32R32Effect 0x12375a 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[4580, 4949]
    (.letOp (n := 4973) (.out 0x12375c (addR32R32Effect 0x12375c 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[4971, 4969]
    (.letOp (n := 4974) (.exec 0x12375c (fun s => s.RIP = 0x12375c) (addR32R32Effect 0x12375c 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[4971, 4969]
    (.letOp (n := 4975) (.out 0x12375e (leaR32Effect 0x12375e 3 0 (.sib 6 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 2] []) (.reg (.gpr 0))) #v[4961, 4973]
    (.letOp (n := 4976) (.exec 0x12375e (fun s => s.RIP = 0x12375e) (leaR32Effect 0x12375e 3 0 (.sib 6 (some 2) 0 .none)) (Reg.operands [.gpr 6, .gpr 2] [])) #v[4961, 4973]
    (b_l121930_126))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_125 : List UInt8 :=
  [0x89, 0xC8, 0xC1, 0xE8, 0x0A, 0x31, 0xF0, 0x44, 0x89, 0xFE, 0xC1, 0xC6, 0x1A, 0x8B, 0x4C, 0x24,
    0x04, 0x01, 0xC1, 0x44, 0x89, 0xF8, 0xC1, 0xC0, 0x15, 0x31, 0xF0, 0x44, 0x89, 0xFE, 0xC1, 0xC6,
    0x07, 0x31, 0xC6, 0x89, 0xD8, 0x44, 0x31, 0xD8, 0x44, 0x21, 0xF8, 0x44, 0x31, 0xD8, 0x01, 0xCA,
    0x01, 0xC2, 0x8D, 0x04, 0x16] ++ bytes_l121930_126

theorem code_l121930_125 : ∀ x ∈ codeRange 0x12372c bytes_l121930_125, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2372c 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_126

def b_l121930_124 : Block Op Label signature Reg.count 4899 :=
  .letOp (n := 4899) (.out 0x1236f6 (movR32R32Effect 0x1236f6 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[4724]
    (.letOp (n := 4900) (.exec 0x1236f6 (fun s => s.RIP = 0x1236f6) (movR32R32Effect 0x1236f6 3 1 10) (Reg.operands [.gpr 10] [])) #v[4724]
    (.letOp (n := 4901) (.out 0x1236f9 (movR32R32Effect 0x1236f9 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[4724]
    (.letOp (n := 4902) (.exec 0x1236f9 (fun s => s.RIP = 0x1236f9) (movR32R32Effect 0x1236f9 3 0 10) (Reg.operands [.gpr 10] [])) #v[4724]
    (.letOp (n := 4903) (.out 0x1236fc (rolR32Effect 0x1236fc 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4901]
    (.letOp (n := 4904) (.exec 0x1236fc (fun s => s.RIP = 0x1236fc) (rolR32Effect 0x1236fc 3 0 15) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4901]
    (.letOp (n := 4905) (.out 0x1236ff (addR32R32Effect 0x1236ff 3 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[4472, 4872]
    (.letOp (n := 4906) (.exec 0x1236ff (fun s => s.RIP = 0x1236ff) (addR32R32Effect 0x1236ff 3 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[4472, 4872]
    (.letOp (n := 4907) (.out 0x123702 (movR32R32Effect 0x123702 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[4724]
    (.letOp (n := 4908) (.exec 0x123702 (fun s => s.RIP = 0x123702) (movR32R32Effect 0x123702 3 6 10) (Reg.operands [.gpr 10] [])) #v[4724]
    (.letOp (n := 4909) (.out 0x123705 (rolR32Effect 0x123705 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[4907]
    (.letOp (n := 4910) (.exec 0x123705 (fun s => s.RIP = 0x123705) (rolR32Effect 0x123705 3 6 13) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4907]
    (.letOp (n := 4911) (.out 0x123708 (addR32R32Effect 0x123708 3 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 8] []) (.reg (.gpr 12))) #v[4897, 4872]
    (.letOp (n := 4912) (.exec 0x123708 (fun s => s.RIP = 0x123708) (addR32R32Effect 0x123708 3 12 8) (Reg.operands [.gpr 12, .gpr 8] [])) #v[4897, 4872]
    (.letOp (n := 4913) (.out 0x12370b (movR32R32Effect 0x12370b 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 5] []) (.reg (.gpr 10))) #v[4858]
    (.letOp (n := 4914) (.exec 0x12370b (fun s => s.RIP = 0x12370b) (movR32R32Effect 0x12370b 3 10 5) (Reg.operands [.gpr 5] [])) #v[4858]
    (.letOp (n := 4915) (.out 0x12370e (movR32R32Effect 0x12370e 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[4858]
    (.letOp (n := 4916) (.exec 0x12370e (fun s => s.RIP = 0x12370e) (movR32R32Effect 0x12370e 2 7 5) (Reg.operands [.gpr 5] [])) #v[4858]
    (.letOp (n := 4917) (.out 0x123710 (rolR32Effect 0x123710 3 7 25) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[4915]
    (.letOp (n := 4918) (.exec 0x123710 (fun s => s.RIP = 0x123710) (rolR32Effect 0x123710 3 7 25) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4915]
    (.letOp (n := 4919) (.out 0x123713 (xorR32R32Effect 0x123713 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[4909, 4903]
    (.letOp (n := 4920) (.exec 0x123713 (fun s => s.RIP = 0x123713) (xorR32R32Effect 0x123713 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[4909, 4903]
    (.letOp (n := 4921) (.out 0x123715 (movR32R32Effect 0x123715 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[4858]
    (.letOp (n := 4922) (.exec 0x123715 (fun s => s.RIP = 0x123715) (movR32R32Effect 0x123715 2 0 5) (Reg.operands [.gpr 5] [])) #v[4858]
    (.letOp (n := 4923) (.out 0x123717 (rolR32Effect 0x123717 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4921]
    (.letOp (n := 4924) (.exec 0x123717 (fun s => s.RIP = 0x123717) (rolR32Effect 0x123717 3 0 14) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4921]
    (.letOp (n := 4925) (.out 0x12371a (xorR32R32Effect 0x12371a 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[4923, 4917]
    (.letOp (n := 4926) (.exec 0x12371a (fun s => s.RIP = 0x12371a) (xorR32R32Effect 0x12371a 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[4923, 4917]
    (.letOp (n := 4927) (.out 0x12371c (movR32R32Effect 0x12371c 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[4858]
    (.letOp (n := 4928) (.exec 0x12371c (fun s => s.RIP = 0x12371c) (movR32R32Effect 0x12371c 2 7 5) (Reg.operands [.gpr 5] [])) #v[4858]
    (.letOp (n := 4929) (.out 0x12371e (shrR32Effect 0x12371e 3 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[4927]
    (.letOp (n := 4930) (.exec 0x12371e (fun s => s.RIP = 0x12371e) (shrR32Effect 0x12371e 3 7 3) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4927]
    (.letOp (n := 4931) (.out 0x123721 (xorR32R32Effect 0x123721 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[4929, 4925]
    (.letOp (n := 4932) (.exec 0x123721 (fun s => s.RIP = 0x123721) (xorR32R32Effect 0x123721 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[4929, 4925]
    (.letOp (n := 4933) (.exec 0x123723 (StorePre 0x123723 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x123723 + BitVec.ofNat 64 4)) 4) (addMREffect 0x123723 4 32 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[4899, 4]
    (.letOp (n := 4934) (.out 0x123727 (addR32R32Effect 0x123727 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[4931, 4899]
    (.letOp (n := 4935) (.exec 0x123727 (fun s => s.RIP = 0x123727) (addR32R32Effect 0x123727 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[4931, 4899]
    (.letOp (n := 4936) (.exec 0x123729 (StorePre 0x123729 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x123729 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x123729 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 7, .gpr 4] [])) #v[4934, 4]
    (b_l121930_125))))))))))))))))))))))))))))))))))))))

def bytes_l121930_124 : List UInt8 :=
  [0x44, 0x89, 0xD1, 0x44, 0x89, 0xD0, 0xC1, 0xC0, 0x0F, 0x45, 0x01, 0xC7, 0x44, 0x89, 0xD6, 0xC1,
    0xC6, 0x0D, 0x45, 0x01, 0xC4, 0x41, 0x89, 0xEA, 0x89, 0xEF, 0xC1, 0xC7, 0x19, 0x31, 0xC6, 0x89,
    0xE8, 0xC1, 0xC0, 0x0E, 0x31, 0xF8, 0x89, 0xEF, 0xC1, 0xEF, 0x03, 0x31, 0xC7, 0x01, 0x4C, 0x24,
    0x50, 0x01, 0xCF, 0x89, 0x3C, 0x24] ++ bytes_l121930_125

theorem code_l121930_124 : ∀ x ∈ codeRange 0x1236f6 bytes_l121930_124, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x236f6 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_125

def b_l121930_123 : Block Op Label signature Reg.count 4860 :=
  .letOp (n := 4860) (.out 0x1236b7 (movR32R32Effect 0x1236b7 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[4796]
    (.letOp (n := 4861) (.exec 0x1236b7 (fun s => s.RIP = 0x1236b7) (movR32R32Effect 0x1236b7 3 7 13) (Reg.operands [.gpr 13] [])) #v[4796]
    (.letOp (n := 4862) (.out 0x1236ba (rolR32Effect 0x1236ba 3 7 30) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[4860]
    (.letOp (n := 4863) (.exec 0x1236ba (fun s => s.RIP = 0x1236ba) (rolR32Effect 0x1236ba 3 7 30) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4860]
    (.letOp (n := 4864) (.out 0x1236bd (addR32R32Effect 0x1236bd 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[4856, 4854]
    (.letOp (n := 4865) (.exec 0x1236bd (fun s => s.RIP = 0x1236bd) (addR32R32Effect 0x1236bd 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[4856, 4854]
    (.letOp (n := 4866) (.out 0x1236bf (movR32R32Effect 0x1236bf 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[4796]
    (.letOp (n := 4867) (.exec 0x1236bf (fun s => s.RIP = 0x1236bf) (movR32R32Effect 0x1236bf 3 1 13) (Reg.operands [.gpr 13] [])) #v[4796]
    (.letOp (n := 4868) (.out 0x1236c2 (rolR32Effect 0x1236c2 3 1 19) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4866]
    (.letOp (n := 4869) (.exec 0x1236c2 (fun s => s.RIP = 0x1236c2) (rolR32Effect 0x1236c2 3 1 19) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4866]
    (.letOp (n := 4870) (.out 0x1236c5 (leaR32Effect 0x1236c5 4 8 (.sib 0 (some 6) 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0, .gpr 6] []) (.reg (.gpr 8))) #v[4846, 4864]
    (.letOp (n := 4871) (.exec 0x1236c5 (fun s => s.RIP = 0x1236c5) (leaR32Effect 0x1236c5 4 8 (.sib 0 (some 6) 0 .none)) (Reg.operands [.gpr 0, .gpr 6] [])) #v[4846, 4864]
    (.letOp (n := 4872) (.out 0x1236c9 (addR32Imm32Effect 0x1236c9 7 8 0xd6990624) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[4870]
    (.letOp (n := 4873) (.exec 0x1236c9 (fun s => s.RIP = 0x1236c9) (addR32Imm32Effect 0x1236c9 7 8 0xd6990624) (Reg.operands [.gpr 8] [])) #v[4870]
    (.letOp (n := 4874) (.out 0x1236d0 (movR32R32Effect 0x1236d0 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[4796]
    (.letOp (n := 4875) (.exec 0x1236d0 (fun s => s.RIP = 0x1236d0) (movR32R32Effect 0x1236d0 3 0 13) (Reg.operands [.gpr 13] [])) #v[4796]
    (.letOp (n := 4876) (.out 0x1236d3 (rolR32Effect 0x1236d3 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4874]
    (.letOp (n := 4877) (.exec 0x1236d3 (fun s => s.RIP = 0x1236d3) (rolR32Effect 0x1236d3 3 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4874]
    (.letOp (n := 4878) (.out 0x1236d6 (xorR32R32Effect 0x1236d6 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[4868, 4862]
    (.letOp (n := 4879) (.exec 0x1236d6 (fun s => s.RIP = 0x1236d6) (xorR32R32Effect 0x1236d6 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[4868, 4862]
    (.letOp (n := 4880) (.out 0x1236d8 (xorR32R32Effect 0x1236d8 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[4876, 4878]
    (.letOp (n := 4881) (.exec 0x1236d8 (fun s => s.RIP = 0x1236d8) (xorR32R32Effect 0x1236d8 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[4876, 4878]
    (.letOp (n := 4882) (.out 0x1236da (movR32R32Effect 0x1236da 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[4684]
    (.letOp (n := 4883) (.exec 0x1236da (fun s => s.RIP = 0x1236da) (movR32R32Effect 0x1236da 3 6 9) (Reg.operands [.gpr 9] [])) #v[4684]
    (.letOp (n := 4884) (.out 0x1236dd (movR64R64Effect 0x1236dd 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[4586]
    (.letOp (n := 4885) (.exec 0x1236dd (fun s => s.RIP = 0x1236dd) (movR64R64Effect 0x1236dd 1 12) (Reg.operands [.gpr 12] [])) #v[4586]
    (.letOp (n := 4886) (.exec 0x1236e0 (StorePre 0x1236e0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1236e0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1236e0 12 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[4586, 4]
    (.letOp (n := 4887) (.out 0x1236e5 (andR32R32Effect 0x1236e5 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[4882, 4884]
    (.letOp (n := 4888) (.exec 0x1236e5 (fun s => s.RIP = 0x1236e5) (andR32R32Effect 0x1236e5 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[4882, 4884]
    (.letOp (n := 4889) (.out 0x1236e7 (movR32R32Effect 0x1236e7 3 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[4684]
    (.letOp (n := 4890) (.exec 0x1236e7 (fun s => s.RIP = 0x1236e7) (movR32R32Effect 0x1236e7 3 12 9) (Reg.operands [.gpr 9] [])) #v[4684]
    (.letOp (n := 4891) (.out 0x1236ea (xorR32R32Effect 0x1236ea 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[4889, 4884]
    (.letOp (n := 4892) (.exec 0x1236ea (fun s => s.RIP = 0x1236ea) (xorR32R32Effect 0x1236ea 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[4889, 4884]
    (.letOp (n := 4893) (.out 0x1236ed (andR32R32Effect 0x1236ed 3 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[4891, 4796]
    (.letOp (n := 4894) (.exec 0x1236ed (fun s => s.RIP = 0x1236ed) (andR32R32Effect 0x1236ed 3 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[4891, 4796]
    (.letOp (n := 4895) (.out 0x1236f0 (xorR32R32Effect 0x1236f0 3 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[4893, 4887]
    (.letOp (n := 4896) (.exec 0x1236f0 (fun s => s.RIP = 0x1236f0) (xorR32R32Effect 0x1236f0 3 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[4893, 4887]
    (.letOp (n := 4897) (.out 0x1236f3 (addR32R32Effect 0x1236f3 3 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[4895, 4880]
    (.letOp (n := 4898) (.exec 0x1236f3 (fun s => s.RIP = 0x1236f3) (addR32R32Effect 0x1236f3 3 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[4895, 4880]
    (b_l121930_124)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_123 : List UInt8 :=
  [0x44, 0x89, 0xEF, 0xC1, 0xC7, 0x1E, 0x01, 0xCE, 0x44, 0x89, 0xE9, 0xC1, 0xC1, 0x13, 0x44, 0x8D,
    0x04, 0x30, 0x41, 0x81, 0xC0, 0x24, 0x06, 0x99, 0xD6, 0x44, 0x89, 0xE8, 0xC1, 0xC0, 0x0A, 0x31,
    0xF9, 0x31, 0xC8, 0x44, 0x89, 0xCE, 0x4C, 0x89, 0xE1, 0x4C, 0x89, 0x64, 0x24, 0x38, 0x21, 0xCE,
    0x45, 0x89, 0xCC, 0x41, 0x31, 0xCC, 0x45, 0x21, 0xEC, 0x41, 0x31, 0xF4, 0x41, 0x01, 0xC4] ++ bytes_l121930_124

theorem code_l121930_123 : ∀ x ∈ codeRange 0x1236b7 bytes_l121930_123, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x236b7 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_124

def b_l121930_122 : Block Op Label signature Reg.count 4821 :=
  .letOp (n := 4821) (.out 0x123685 (addR32R32Effect 0x123685 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[4818, 4626]
    (.letOp (n := 4822) (.exec 0x123685 (fun s => s.RIP = 0x123685) (addR32R32Effect 0x123685 3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[4818, 4626]
    (.letOp (n := 4823) (.exec 0x123688 (StorePre 0x123688 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x123688 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x123688 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[4821, 4]
    (.letOp (n := 4824) (.out 0x12368c (shrR32Effect 0x12368c 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[4790]
    (.letOp (n := 4825) (.exec 0x12368c (fun s => s.RIP = 0x12368c) (shrR32Effect 0x12368c 3 5 10) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4790]
    (.letOp (n := 4826) (.out 0x12368f (xorR32R32Effect 0x12368f 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[4824, 4802]
    (.letOp (n := 4827) (.exec 0x12368f (fun s => s.RIP = 0x12368f) (xorR32R32Effect 0x12368f 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[4824, 4802]
    (.letOp (n := 4828) (.out 0x123691 (movR32M32LowEffect 0x123691 7 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 4829) (.exec 0x123691 (LoadPre 0x123691 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x123691 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x123691 7 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 4830) (.out 0x123695 (addR32R32Effect 0x123695 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[4828, 4826]
    (.letOp (n := 4831) (.exec 0x123695 (fun s => s.RIP = 0x123695) (addR32R32Effect 0x123695 2 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[4828, 4826]
    (.letOp (n := 4832) (.out 0x123697 (movR32R32Effect 0x123697 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[4788]
    (.letOp (n := 4833) (.exec 0x123697 (fun s => s.RIP = 0x123697) (movR32R32Effect 0x123697 2 0 3) (Reg.operands [.gpr 3] [])) #v[4788]
    (.letOp (n := 4834) (.out 0x123699 (rolR32Effect 0x123699 3 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4832]
    (.letOp (n := 4835) (.exec 0x123699 (fun s => s.RIP = 0x123699) (rolR32Effect 0x123699 3 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4832]
    (.letOp (n := 4836) (.out 0x12369c (movR32R32Effect 0x12369c 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[4788]
    (.letOp (n := 4837) (.exec 0x12369c (fun s => s.RIP = 0x12369c) (movR32R32Effect 0x12369c 2 1 3) (Reg.operands [.gpr 3] [])) #v[4788]
    (.letOp (n := 4838) (.out 0x12369e (rolR32Effect 0x12369e 3 1 21) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4836]
    (.letOp (n := 4839) (.exec 0x12369e (fun s => s.RIP = 0x12369e) (rolR32Effect 0x12369e 3 1 21) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4836]
    (.letOp (n := 4840) (.out 0x1236a1 (xorR32R32Effect 0x1236a1 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[4838, 4834]
    (.letOp (n := 4841) (.exec 0x1236a1 (fun s => s.RIP = 0x1236a1) (xorR32R32Effect 0x1236a1 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[4838, 4834]
    (.letOp (n := 4842) (.out 0x1236a3 (movR32R32Effect 0x1236a3 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[4788]
    (.letOp (n := 4843) (.exec 0x1236a3 (fun s => s.RIP = 0x1236a3) (movR32R32Effect 0x1236a3 2 0 3) (Reg.operands [.gpr 3] [])) #v[4788]
    (.letOp (n := 4844) (.out 0x1236a5 (rolR32Effect 0x1236a5 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4842]
    (.letOp (n := 4845) (.exec 0x1236a5 (fun s => s.RIP = 0x1236a5) (rolR32Effect 0x1236a5 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4842]
    (.letOp (n := 4846) (.out 0x1236a8 (xorR32R32Effect 0x1236a8 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[4844, 4840]
    (.letOp (n := 4847) (.exec 0x1236a8 (fun s => s.RIP = 0x1236a8) (xorR32R32Effect 0x1236a8 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[4844, 4840]
    (.letOp (n := 4848) (.out 0x1236aa (movR32R32Effect 0x1236aa 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11] []) (.reg (.gpr 1))) #v[4682]
    (.letOp (n := 4849) (.exec 0x1236aa (fun s => s.RIP = 0x1236aa) (movR32R32Effect 0x1236aa 3 1 11) (Reg.operands [.gpr 11] [])) #v[4682]
    (.letOp (n := 4850) (.out 0x1236ad (xorR32R32Effect 0x1236ad 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[4848, 4580]
    (.letOp (n := 4851) (.exec 0x1236ad (fun s => s.RIP = 0x1236ad) (xorR32R32Effect 0x1236ad 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[4848, 4580]
    (.letOp (n := 4852) (.out 0x1236af (andR32R32Effect 0x1236af 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[4850, 4788]
    (.letOp (n := 4853) (.exec 0x1236af (fun s => s.RIP = 0x1236af) (andR32R32Effect 0x1236af 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[4850, 4788]
    (.letOp (n := 4854) (.out 0x1236b1 (xorR32R32Effect 0x1236b1 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[4852, 4580]
    (.letOp (n := 4855) (.exec 0x1236b1 (fun s => s.RIP = 0x1236b1) (xorR32R32Effect 0x1236b1 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[4852, 4580]
    (.letOp (n := 4856) (.out 0x1236b3 (addR32R32Effect 0x1236b3 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[4466, 4830]
    (.letOp (n := 4857) (.exec 0x1236b3 (fun s => s.RIP = 0x1236b3) (addR32R32Effect 0x1236b3 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[4466, 4830]
    (.letOp (n := 4858) (.out 0x1236b5 (movR32R32Effect 0x1236b5 2 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 7] []) (.reg (.gpr 5))) #v[4830]
    (.letOp (n := 4859) (.exec 0x1236b5 (fun s => s.RIP = 0x1236b5) (movR32R32Effect 0x1236b5 2 5 7) (Reg.operands [.gpr 7] [])) #v[4830]
    (b_l121930_123)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_122 : List UInt8 :=
  [0x44, 0x01, 0xF1, 0x89, 0x4C, 0x24, 0x10, 0xC1, 0xED, 0x0A, 0x31, 0xC5, 0x8B, 0x7C, 0x24, 0x24,
    0x01, 0xEF, 0x89, 0xD8, 0xC1, 0xC0, 0x1A, 0x89, 0xD9, 0xC1, 0xC1, 0x15, 0x31, 0xC1, 0x89, 0xD8,
    0xC1, 0xC0, 0x07, 0x31, 0xC8, 0x44, 0x89, 0xD9, 0x31, 0xD1, 0x21, 0xD9, 0x31, 0xD1, 0x01, 0xFE,
    0x89, 0xFD] ++ bytes_l121930_123

theorem code_l121930_122 : ∀ x ∈ codeRange 0x123685 bytes_l121930_122, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23685 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_123

def b_l121930_121 : Block Op Label signature Reg.count 4782 :=
  .letOp (n := 4782) (.out 0x12364b (andR32R32Effect 0x12364b 3 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[4780, 4684]
    (.letOp (n := 4783) (.exec 0x12364b (fun s => s.RIP = 0x12364b) (andR32R32Effect 0x12364b 3 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[4780, 4684]
    (.letOp (n := 4784) (.out 0x12364e (xorR32R32Effect 0x12364e 3 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[4782, 4776]
    (.letOp (n := 4785) (.exec 0x12364e (fun s => s.RIP = 0x12364e) (xorR32R32Effect 0x12364e 3 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[4782, 4776]
    (.letOp (n := 4786) (.out 0x123651 (addR32R32Effect 0x123651 3 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 7] []) (.reg (.gpr 13))) #v[4784, 4772]
    (.letOp (n := 4787) (.exec 0x123651 (fun s => s.RIP = 0x123651) (addR32R32Effect 0x123651 3 13 7) (Reg.operands [.gpr 13, .gpr 7] [])) #v[4784, 4772]
    (.letOp (n := 4788) (.out 0x123654 (addR32R32Effect 0x123654 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[4362, 4760]
    (.letOp (n := 4789) (.exec 0x123654 (fun s => s.RIP = 0x123654) (addR32R32Effect 0x123654 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[4362, 4760]
    (.letOp (n := 4790) (.out 0x123656 (movR32R32Effect 0x123656 3 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 14] []) (.reg (.gpr 5))) #v[4626]
    (.letOp (n := 4791) (.exec 0x123656 (fun s => s.RIP = 0x123656) (movR32R32Effect 0x123656 3 5 14) (Reg.operands [.gpr 14] [])) #v[4626]
    (.letOp (n := 4792) (.out 0x123659 (movR32R32Effect 0x123659 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[4626]
    (.letOp (n := 4793) (.exec 0x123659 (fun s => s.RIP = 0x123659) (movR32R32Effect 0x123659 3 1 14) (Reg.operands [.gpr 14] [])) #v[4626]
    (.letOp (n := 4794) (.out 0x12365c (rolR32Effect 0x12365c 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4792]
    (.letOp (n := 4795) (.exec 0x12365c (fun s => s.RIP = 0x12365c) (rolR32Effect 0x12365c 3 1 15) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4792]
    (.letOp (n := 4796) (.out 0x12365f (addR32R32Effect 0x12365f 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[4786, 4760]
    (.letOp (n := 4797) (.exec 0x12365f (fun s => s.RIP = 0x12365f) (addR32R32Effect 0x12365f 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[4786, 4760]
    (.letOp (n := 4798) (.out 0x123662 (movR32R32Effect 0x123662 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[4626]
    (.letOp (n := 4799) (.exec 0x123662 (fun s => s.RIP = 0x123662) (movR32R32Effect 0x123662 3 0 14) (Reg.operands [.gpr 14] [])) #v[4626]
    (.letOp (n := 4800) (.out 0x123665 (rolR32Effect 0x123665 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[4798]
    (.letOp (n := 4801) (.exec 0x123665 (fun s => s.RIP = 0x123665) (rolR32Effect 0x123665 3 0 13) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4798]
    (.letOp (n := 4802) (.out 0x123668 (xorR32R32Effect 0x123668 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[4800, 4794]
    (.letOp (n := 4803) (.exec 0x123668 (fun s => s.RIP = 0x123668) (xorR32R32Effect 0x123668 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[4800, 4794]
    (.letOp (n := 4804) (.out 0x12366a (movR32R32Effect 0x12366a 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[4724]
    (.letOp (n := 4805) (.exec 0x12366a (fun s => s.RIP = 0x12366a) (movR32R32Effect 0x12366a 3 1 10) (Reg.operands [.gpr 10] [])) #v[4724]
    (.letOp (n := 4806) (.out 0x12366d (rolR32Effect 0x12366d 3 1 25) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4804]
    (.letOp (n := 4807) (.exec 0x12366d (fun s => s.RIP = 0x12366d) (rolR32Effect 0x12366d 3 1 25) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4804]
    (.letOp (n := 4808) (.out 0x123670 (movR32R32Effect 0x123670 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 10] []) (.reg (.gpr 7))) #v[4724]
    (.letOp (n := 4809) (.exec 0x123670 (fun s => s.RIP = 0x123670) (movR32R32Effect 0x123670 3 7 10) (Reg.operands [.gpr 10] [])) #v[4724]
    (.letOp (n := 4810) (.out 0x123673 (rolR32Effect 0x123673 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[4808]
    (.letOp (n := 4811) (.exec 0x123673 (fun s => s.RIP = 0x123673) (rolR32Effect 0x123673 3 7 14) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4808]
    (.letOp (n := 4812) (.out 0x123676 (xorR32R32Effect 0x123676 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[4810, 4806]
    (.letOp (n := 4813) (.exec 0x123676 (fun s => s.RIP = 0x123676) (xorR32R32Effect 0x123676 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[4810, 4806]
    (.letOp (n := 4814) (.out 0x123678 (movR32R32Effect 0x123678 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[4724]
    (.letOp (n := 4815) (.exec 0x123678 (fun s => s.RIP = 0x123678) (movR32R32Effect 0x123678 3 1 10) (Reg.operands [.gpr 10] [])) #v[4724]
    (.letOp (n := 4816) (.out 0x12367b (shrR32Effect 0x12367b 3 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4814]
    (.letOp (n := 4817) (.exec 0x12367b (fun s => s.RIP = 0x12367b) (shrR32Effect 0x12367b 3 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4814]
    (.letOp (n := 4818) (.out 0x12367e (xorR32R32Effect 0x12367e 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[4816, 4812]
    (.letOp (n := 4819) (.exec 0x12367e (fun s => s.RIP = 0x12367e) (xorR32R32Effect 0x12367e 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[4816, 4812]
    (.letOp (n := 4820) (.exec 0x123680 (StorePre 0x123680 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x123680 + BitVec.ofNat 64 5)) 4) (addMREffect 0x123680 5 32 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[4626, 4]
    (b_l121930_122)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_121 : List UInt8 :=
  [0x45, 0x21, 0xCD, 0x41, 0x31, 0xCD, 0x41, 0x01, 0xFD, 0x01, 0xC3, 0x44, 0x89, 0xF5, 0x44, 0x89,
    0xF1, 0xC1, 0xC1, 0x0F, 0x41, 0x01, 0xC5, 0x44, 0x89, 0xF0, 0xC1, 0xC0, 0x0D, 0x31, 0xC8, 0x44,
    0x89, 0xD1, 0xC1, 0xC1, 0x19, 0x44, 0x89, 0xD7, 0xC1, 0xC7, 0x0E, 0x31, 0xCF, 0x44, 0x89, 0xD1,
    0xC1, 0xE9, 0x03, 0x31, 0xF9, 0x44, 0x01, 0x74, 0x24, 0x08] ++ bytes_l121930_122

theorem code_l121930_121 : ∀ x ∈ codeRange 0x12364b bytes_l121930_121, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2364b 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_122

def b_l121930_120 : Block Op Label signature Reg.count 4742 :=
  .letOp (n := 4742) (.out 0x123614 (movR32R32Effect 0x123614 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[4580]
    (.letOp (n := 4743) (.exec 0x123614 (fun s => s.RIP = 0x123614) (movR32R32Effect 0x123614 2 7 2) (Reg.operands [.gpr 2] [])) #v[4580]
    (.letOp (n := 4744) (.out 0x123616 (xorR32R32Effect 0x123616 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[4742, 4466]
    (.letOp (n := 4745) (.exec 0x123616 (fun s => s.RIP = 0x123616) (xorR32R32Effect 0x123616 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[4742, 4466]
    (.letOp (n := 4746) (.out 0x123618 (andR32R32Effect 0x123618 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[4744, 4682]
    (.letOp (n := 4747) (.exec 0x123618 (fun s => s.RIP = 0x123618) (andR32R32Effect 0x123618 3 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[4744, 4682]
    (.letOp (n := 4748) (.out 0x12361b (xorR32R32Effect 0x12361b 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[4746, 4466]
    (.letOp (n := 4749) (.exec 0x12361b (fun s => s.RIP = 0x12361b) (xorR32R32Effect 0x12361b 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[4746, 4466]
    (.letOp (n := 4750) (.out 0x12361d (addR32R32Effect 0x12361d 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[4356, 4724]
    (.letOp (n := 4751) (.exec 0x12361d (fun s => s.RIP = 0x12361d) (addR32R32Effect 0x12361d 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[4356, 4724]
    (.letOp (n := 4752) (.out 0x123620 (addR32R32Effect 0x123620 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[4750, 4748]
    (.letOp (n := 4753) (.exec 0x123620 (fun s => s.RIP = 0x123620) (addR32R32Effect 0x123620 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[4750, 4748]
    (.letOp (n := 4754) (.out 0x123622 (movR32R32Effect 0x123622 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[4684]
    (.letOp (n := 4755) (.exec 0x123622 (fun s => s.RIP = 0x123622) (movR32R32Effect 0x123622 3 7 9) (Reg.operands [.gpr 9] [])) #v[4684]
    (.letOp (n := 4756) (.out 0x123625 (rolR32Effect 0x123625 3 7 30) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[4754]
    (.letOp (n := 4757) (.exec 0x123625 (fun s => s.RIP = 0x123625) (rolR32Effect 0x123625 3 7 30) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4754]
    (.letOp (n := 4758) (.out 0x123628 (addR32R32Effect 0x123628 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[4752, 4740]
    (.letOp (n := 4759) (.exec 0x123628 (fun s => s.RIP = 0x123628) (addR32R32Effect 0x123628 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[4752, 4740]
    (.letOp (n := 4760) (.out 0x12362a (addEaxImm32Effect 0x12362a 0xd192e819) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[4758]
    (.letOp (n := 4761) (.exec 0x12362a (fun s => s.RIP = 0x12362a) (addEaxImm32Effect 0x12362a 0xd192e819) (Reg.operands [.gpr 0] [])) #v[4758]
    (.letOp (n := 4762) (.out 0x12362f (movR32R32Effect 0x12362f 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[4684]
    (.letOp (n := 4763) (.exec 0x12362f (fun s => s.RIP = 0x12362f) (movR32R32Effect 0x12362f 3 1 9) (Reg.operands [.gpr 9] [])) #v[4684]
    (.letOp (n := 4764) (.out 0x123632 (rolR32Effect 0x123632 3 1 19) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4762]
    (.letOp (n := 4765) (.exec 0x123632 (fun s => s.RIP = 0x123632) (rolR32Effect 0x123632 3 1 19) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4762]
    (.letOp (n := 4766) (.out 0x123635 (xorR32R32Effect 0x123635 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[4764, 4756]
    (.letOp (n := 4767) (.exec 0x123635 (fun s => s.RIP = 0x123635) (xorR32R32Effect 0x123635 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[4764, 4756]
    (.letOp (n := 4768) (.out 0x123637 (movR32R32Effect 0x123637 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[4684]
    (.letOp (n := 4769) (.exec 0x123637 (fun s => s.RIP = 0x123637) (movR32R32Effect 0x123637 3 7 9) (Reg.operands [.gpr 9] [])) #v[4684]
    (.letOp (n := 4770) (.out 0x12363a (rolR32Effect 0x12363a 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[4768]
    (.letOp (n := 4771) (.exec 0x12363a (fun s => s.RIP = 0x12363a) (rolR32Effect 0x12363a 3 7 10) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4768]
    (.letOp (n := 4772) (.out 0x12363d (xorR32R32Effect 0x12363d 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[4770, 4766]
    (.letOp (n := 4773) (.exec 0x12363d (fun s => s.RIP = 0x12363d) (xorR32R32Effect 0x12363d 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[4770, 4766]
    (.letOp (n := 4774) (.out 0x12363f (movR32R32Effect 0x12363f 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[4586]
    (.letOp (n := 4775) (.exec 0x12363f (fun s => s.RIP = 0x12363f) (movR32R32Effect 0x12363f 3 1 12) (Reg.operands [.gpr 12] [])) #v[4586]
    (.letOp (n := 4776) (.out 0x123642 (andR32R32Effect 0x123642 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[4774, 4472]
    (.letOp (n := 4777) (.exec 0x123642 (fun s => s.RIP = 0x123642) (andR32R32Effect 0x123642 3 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[4774, 4472]
    (.letOp (n := 4778) (.out 0x123645 (movR32R32Effect 0x123645 3 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 12] []) (.reg (.gpr 13))) #v[4586]
    (.letOp (n := 4779) (.exec 0x123645 (fun s => s.RIP = 0x123645) (movR32R32Effect 0x123645 3 13 12) (Reg.operands [.gpr 12] [])) #v[4586]
    (.letOp (n := 4780) (.out 0x123648 (xorR32R32Effect 0x123648 3 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[4778, 4472]
    (.letOp (n := 4781) (.exec 0x123648 (fun s => s.RIP = 0x123648) (xorR32R32Effect 0x123648 3 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[4778, 4472]
    (b_l121930_121))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_120 : List UInt8 :=
  [0x89, 0xD7, 0x31, 0xF7, 0x44, 0x21, 0xDF, 0x31, 0xF7, 0x44, 0x01, 0xD0, 0x01, 0xF8, 0x44, 0x89,
    0xCF, 0xC1, 0xC7, 0x1E, 0x01, 0xC8, 0x05, 0x19, 0xE8, 0x92, 0xD1, 0x44, 0x89, 0xC9, 0xC1, 0xC1,
    0x13, 0x31, 0xF9, 0x44, 0x89, 0xCF, 0xC1, 0xC7, 0x0A, 0x31, 0xCF, 0x44, 0x89, 0xE1, 0x44, 0x21,
    0xF9, 0x45, 0x89, 0xE5, 0x45, 0x31, 0xFD] ++ bytes_l121930_121

theorem code_l121930_120 : ∀ x ∈ codeRange 0x123614 bytes_l121930_120, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23614 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_121

def b_l121930_119 : Block Op Label signature Reg.count 4704 :=
  .letOp (n := 4704) (.out 0x1235db (xorR32R32Effect 0x1235db 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[4702, 4698]
    (.letOp (n := 4705) (.exec 0x1235db (fun s => s.RIP = 0x1235db) (xorR32R32Effect 0x1235db 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[4702, 4698]
    (.letOp (n := 4706) (.out 0x1235de (movR32R32Effect 0x1235de 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[4626]
    (.letOp (n := 4707) (.exec 0x1235de (fun s => s.RIP = 0x1235de) (movR32R32Effect 0x1235de 3 1 14) (Reg.operands [.gpr 14] [])) #v[4626]
    (.letOp (n := 4708) (.out 0x1235e1 (shrR32Effect 0x1235e1 3 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4706]
    (.letOp (n := 4709) (.exec 0x1235e1 (fun s => s.RIP = 0x1235e1) (shrR32Effect 0x1235e1 3 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4706]
    (.letOp (n := 4710) (.out 0x1235e4 (xorR32R32Effect 0x1235e4 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[4708, 4704]
    (.letOp (n := 4711) (.exec 0x1235e4 (fun s => s.RIP = 0x1235e4) (xorR32R32Effect 0x1235e4 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[4708, 4704]
    (.letOp (n := 4712) (.exec 0x1235e7 (StorePre 0x1235e7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1235e7 + BitVec.ofNat 64 4)) 4) (addMREffect 0x1235e7 4 32 5 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[4510, 4]
    (.letOp (n := 4713) (.out 0x1235eb (addR32R32Effect 0x1235eb 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[4710, 4510]
    (.letOp (n := 4714) (.exec 0x1235eb (fun s => s.RIP = 0x1235eb) (addR32R32Effect 0x1235eb 2 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[4710, 4510]
    (.letOp (n := 4715) (.exec 0x1235ed (StorePre 0x1235ed 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1235ed + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1235ed 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[4713, 4]
    (.letOp (n := 4716) (.out 0x1235f1 (movR32R32Effect 0x1235f1 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[4510]
    (.letOp (n := 4717) (.exec 0x1235f1 (fun s => s.RIP = 0x1235f1) (movR32R32Effect 0x1235f1 2 1 5) (Reg.operands [.gpr 5] [])) #v[4510]
    (.letOp (n := 4718) (.out 0x1235f3 (shrR32Effect 0x1235f3 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4716]
    (.letOp (n := 4719) (.exec 0x1235f3 (fun s => s.RIP = 0x1235f3) (shrR32Effect 0x1235f3 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4716]
    (.letOp (n := 4720) (.out 0x1235f6 (xorR32R32Effect 0x1235f6 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[4718, 4694]
    (.letOp (n := 4721) (.exec 0x1235f6 (fun s => s.RIP = 0x1235f6) (xorR32R32Effect 0x1235f6 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[4718, 4694]
    (.letOp (n := 4722) (.out 0x1235f8 (movR32R32Effect 0x1235f8 3 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 13] []) (.reg (.gpr 10))) #v[4169]
    (.letOp (n := 4723) (.exec 0x1235f8 (fun s => s.RIP = 0x1235f8) (movR32R32Effect 0x1235f8 3 10 13) (Reg.operands [.gpr 13] [])) #v[4169]
    (.letOp (n := 4724) (.out 0x1235fb (addR32R32Effect 0x1235fb 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[4722, 4720]
    (.letOp (n := 4725) (.exec 0x1235fb (fun s => s.RIP = 0x1235fb) (addR32R32Effect 0x1235fb 3 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[4722, 4720]
    (.letOp (n := 4726) (.out 0x1235fe (movR32R32Effect 0x1235fe 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11] []) (.reg (.gpr 1))) #v[4682]
    (.letOp (n := 4727) (.exec 0x1235fe (fun s => s.RIP = 0x1235fe) (movR32R32Effect 0x1235fe 3 1 11) (Reg.operands [.gpr 11] [])) #v[4682]
    (.letOp (n := 4728) (.out 0x123601 (rolR32Effect 0x123601 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4726]
    (.letOp (n := 4729) (.exec 0x123601 (fun s => s.RIP = 0x123601) (rolR32Effect 0x123601 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4726]
    (.letOp (n := 4730) (.out 0x123604 (movR32R32Effect 0x123604 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 11] []) (.reg (.gpr 7))) #v[4682]
    (.letOp (n := 4731) (.exec 0x123604 (fun s => s.RIP = 0x123604) (movR32R32Effect 0x123604 3 7 11) (Reg.operands [.gpr 11] [])) #v[4682]
    (.letOp (n := 4732) (.out 0x123607 (rolR32Effect 0x123607 3 7 21) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[4730]
    (.letOp (n := 4733) (.exec 0x123607 (fun s => s.RIP = 0x123607) (rolR32Effect 0x123607 3 7 21) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4730]
    (.letOp (n := 4734) (.out 0x12360a (xorR32R32Effect 0x12360a 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[4732, 4728]
    (.letOp (n := 4735) (.exec 0x12360a (fun s => s.RIP = 0x12360a) (xorR32R32Effect 0x12360a 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[4732, 4728]
    (.letOp (n := 4736) (.out 0x12360c (movR32R32Effect 0x12360c 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11] []) (.reg (.gpr 1))) #v[4682]
    (.letOp (n := 4737) (.exec 0x12360c (fun s => s.RIP = 0x12360c) (movR32R32Effect 0x12360c 3 1 11) (Reg.operands [.gpr 11] [])) #v[4682]
    (.letOp (n := 4738) (.out 0x12360f (rolR32Effect 0x12360f 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4736]
    (.letOp (n := 4739) (.exec 0x12360f (fun s => s.RIP = 0x12360f) (rolR32Effect 0x12360f 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4736]
    (.letOp (n := 4740) (.out 0x123612 (xorR32R32Effect 0x123612 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[4738, 4734]
    (.letOp (n := 4741) (.exec 0x123612 (fun s => s.RIP = 0x123612) (xorR32R32Effect 0x123612 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[4738, 4734]
    (b_l121930_120))))))))))))))))))))))))))))))))))))))

def bytes_l121930_119 : List UInt8 :=
  [0x41, 0x31, 0xC8, 0x44, 0x89, 0xF1, 0xC1, 0xE9, 0x03, 0x44, 0x31, 0xC1, 0x01, 0x6C, 0x24, 0x0C,
    0x01, 0xE9, 0x89, 0x4C, 0x24, 0x58, 0x89, 0xE9, 0xC1, 0xE9, 0x0A, 0x31, 0xF9, 0x45, 0x89, 0xEA,
    0x41, 0x01, 0xCA, 0x44, 0x89, 0xD9, 0xC1, 0xC1, 0x1A, 0x44, 0x89, 0xDF, 0xC1, 0xC7, 0x15, 0x31,
    0xCF, 0x44, 0x89, 0xD9, 0xC1, 0xC1, 0x07, 0x31, 0xF9] ++ bytes_l121930_120

theorem code_l121930_119 : ∀ x ∈ codeRange 0x1235db bytes_l121930_119, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x235db 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_120

def b_l121930_118 : Block Op Label signature Reg.count 4664 :=
  .letOp (n := 4664) (.out 0x1235a1 (rolR32Effect 0x1235a1 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[4662]
    (.letOp (n := 4665) (.exec 0x1235a1 (fun s => s.RIP = 0x1235a1) (rolR32Effect 0x1235a1 3 7 10) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4662]
    (.letOp (n := 4666) (.out 0x1235a4 (xorR32R32Effect 0x1235a4 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[4664, 4660]
    (.letOp (n := 4667) (.exec 0x1235a4 (fun s => s.RIP = 0x1235a4) (xorR32R32Effect 0x1235a4 3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[4664, 4660]
    (.letOp (n := 4668) (.out 0x1235a7 (movR32R32Effect 0x1235a7 3 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[4472]
    (.letOp (n := 4669) (.exec 0x1235a7 (fun s => s.RIP = 0x1235a7) (movR32R32Effect 0x1235a7 3 8 15) (Reg.operands [.gpr 15] [])) #v[4472]
    (.letOp (n := 4670) (.out 0x1235aa (andR32R32Effect 0x1235aa 3 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[4668, 4362]
    (.letOp (n := 4671) (.exec 0x1235aa (fun s => s.RIP = 0x1235aa) (andR32R32Effect 0x1235aa 3 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[4668, 4362]
    (.letOp (n := 4672) (.out 0x1235ad (movR32R32Effect 0x1235ad 3 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 15] []) (.reg (.gpr 9))) #v[4472]
    (.letOp (n := 4673) (.exec 0x1235ad (fun s => s.RIP = 0x1235ad) (movR32R32Effect 0x1235ad 3 9 15) (Reg.operands [.gpr 15] [])) #v[4472]
    (.letOp (n := 4674) (.out 0x1235b0 (xorR32R32Effect 0x1235b0 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[4672, 4362]
    (.letOp (n := 4675) (.exec 0x1235b0 (fun s => s.RIP = 0x1235b0) (xorR32R32Effect 0x1235b0 3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[4672, 4362]
    (.letOp (n := 4676) (.out 0x1235b3 (andR32R32Effect 0x1235b3 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[4674, 4586]
    (.letOp (n := 4677) (.exec 0x1235b3 (fun s => s.RIP = 0x1235b3) (andR32R32Effect 0x1235b3 3 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[4674, 4586]
    (.letOp (n := 4678) (.out 0x1235b6 (xorR32R32Effect 0x1235b6 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[4676, 4670]
    (.letOp (n := 4679) (.exec 0x1235b6 (fun s => s.RIP = 0x1235b6) (xorR32R32Effect 0x1235b6 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[4676, 4670]
    (.letOp (n := 4680) (.out 0x1235b9 (addR32R32Effect 0x1235b9 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[4678, 4666]
    (.letOp (n := 4681) (.exec 0x1235b9 (fun s => s.RIP = 0x1235b9) (addR32R32Effect 0x1235b9 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[4678, 4666]
    (.letOp (n := 4682) (.out 0x1235bc (addR32R32Effect 0x1235bc 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[4248, 4650]
    (.letOp (n := 4683) (.exec 0x1235bc (fun s => s.RIP = 0x1235bc) (addR32R32Effect 0x1235bc 3 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[4248, 4650]
    (.letOp (n := 4684) (.out 0x1235bf (addR32R32Effect 0x1235bf 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[4680, 4650]
    (.letOp (n := 4685) (.exec 0x1235bf (fun s => s.RIP = 0x1235bf) (addR32R32Effect 0x1235bf 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[4680, 4650]
    (.letOp (n := 4686) (.out 0x1235c2 (movR32R32Effect 0x1235c2 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[4510]
    (.letOp (n := 4687) (.exec 0x1235c2 (fun s => s.RIP = 0x1235c2) (movR32R32Effect 0x1235c2 2 1 5) (Reg.operands [.gpr 5] [])) #v[4510]
    (.letOp (n := 4688) (.out 0x1235c4 (rolR32Effect 0x1235c4 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4686]
    (.letOp (n := 4689) (.exec 0x1235c4 (fun s => s.RIP = 0x1235c4) (rolR32Effect 0x1235c4 3 1 15) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4686]
    (.letOp (n := 4690) (.out 0x1235c7 (movR32R32Effect 0x1235c7 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[4510]
    (.letOp (n := 4691) (.exec 0x1235c7 (fun s => s.RIP = 0x1235c7) (movR32R32Effect 0x1235c7 2 7 5) (Reg.operands [.gpr 5] [])) #v[4510]
    (.letOp (n := 4692) (.out 0x1235c9 (rolR32Effect 0x1235c9 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[4690]
    (.letOp (n := 4693) (.exec 0x1235c9 (fun s => s.RIP = 0x1235c9) (rolR32Effect 0x1235c9 3 7 13) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4690]
    (.letOp (n := 4694) (.out 0x1235cc (xorR32R32Effect 0x1235cc 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[4692, 4688]
    (.letOp (n := 4695) (.exec 0x1235cc (fun s => s.RIP = 0x1235cc) (xorR32R32Effect 0x1235cc 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[4692, 4688]
    (.letOp (n := 4696) (.out 0x1235ce (movR32R32Effect 0x1235ce 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[4626]
    (.letOp (n := 4697) (.exec 0x1235ce (fun s => s.RIP = 0x1235ce) (movR32R32Effect 0x1235ce 3 1 14) (Reg.operands [.gpr 14] [])) #v[4626]
    (.letOp (n := 4698) (.out 0x1235d1 (rolR32Effect 0x1235d1 3 1 25) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4696]
    (.letOp (n := 4699) (.exec 0x1235d1 (fun s => s.RIP = 0x1235d1) (rolR32Effect 0x1235d1 3 1 25) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4696]
    (.letOp (n := 4700) (.out 0x1235d4 (movR32R32Effect 0x1235d4 3 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[4626]
    (.letOp (n := 4701) (.exec 0x1235d4 (fun s => s.RIP = 0x1235d4) (movR32R32Effect 0x1235d4 3 8 14) (Reg.operands [.gpr 14] [])) #v[4626]
    (.letOp (n := 4702) (.out 0x1235d7 (rolR32Effect 0x1235d7 4 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4700]
    (.letOp (n := 4703) (.exec 0x1235d7 (fun s => s.RIP = 0x1235d7) (rolR32Effect 0x1235d7 4 8 14) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4700]
    (b_l121930_119))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_118 : List UInt8 :=
  [0xC1, 0xC7, 0x0A, 0x44, 0x31, 0xC7, 0x45, 0x89, 0xF8, 0x41, 0x21, 0xD8, 0x45, 0x89, 0xF9, 0x41,
    0x31, 0xD9, 0x45, 0x21, 0xE1, 0x45, 0x31, 0xC1, 0x41, 0x01, 0xF9, 0x41, 0x01, 0xCB, 0x41, 0x01,
    0xC9, 0x89, 0xE9, 0xC1, 0xC1, 0x0F, 0x89, 0xEF, 0xC1, 0xC7, 0x0D, 0x31, 0xCF, 0x44, 0x89, 0xF1,
    0xC1, 0xC1, 0x19, 0x45, 0x89, 0xF0, 0x41, 0xC1, 0xC0, 0x0E] ++ bytes_l121930_119

theorem code_l121930_118 : ∀ x ∈ codeRange 0x1235a1 bytes_l121930_118, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x235a1 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_119

def b_l121930_117 : Block Op Label signature Reg.count 4624 :=
  .letOp (n := 4624) (.out 0x123561 (movR32M32Effect 0x123561 14 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 4625) (.exec 0x123561 (LoadPre 0x123561 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x123561 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x123561 14 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 4626) (.out 0x123566 (addR32R32Effect 0x123566 3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[4624, 4618]
    (.letOp (n := 4627) (.exec 0x123566 (fun s => s.RIP = 0x123566) (addR32R32Effect 0x123566 3 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[4624, 4618]
    (.letOp (n := 4628) (.out 0x123569 (movR32R32Effect 0x123569 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[4580]
    (.letOp (n := 4629) (.exec 0x123569 (fun s => s.RIP = 0x123569) (movR32R32Effect 0x123569 2 1 2) (Reg.operands [.gpr 2] [])) #v[4580]
    (.letOp (n := 4630) (.out 0x12356b (rolR32Effect 0x12356b 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4628]
    (.letOp (n := 4631) (.exec 0x12356b (fun s => s.RIP = 0x12356b) (rolR32Effect 0x12356b 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4628]
    (.letOp (n := 4632) (.out 0x12356e (xorR32R32Effect 0x12356e 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[4622, 4616]
    (.letOp (n := 4633) (.exec 0x12356e (fun s => s.RIP = 0x12356e) (xorR32R32Effect 0x12356e 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[4622, 4616]
    (.letOp (n := 4634) (.out 0x123571 (xorR32R32Effect 0x123571 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[4630, 4632]
    (.letOp (n := 4635) (.exec 0x123571 (fun s => s.RIP = 0x123571) (xorR32R32Effect 0x123571 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[4630, 4632]
    (.letOp (n := 4636) (.out 0x123574 (movR32R32Effect 0x123574 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[4466]
    (.letOp (n := 4637) (.exec 0x123574 (fun s => s.RIP = 0x123574) (movR32R32Effect 0x123574 3 8 6) (Reg.operands [.gpr 6] [])) #v[4466]
    (.letOp (n := 4638) (.out 0x123577 (xorR32R32Effect 0x123577 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[4636, 4356]
    (.letOp (n := 4639) (.exec 0x123577 (fun s => s.RIP = 0x123577) (xorR32R32Effect 0x123577 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[4636, 4356]
    (.letOp (n := 4640) (.out 0x12357a (andR32R32Effect 0x12357a 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[4638, 4580]
    (.letOp (n := 4641) (.exec 0x12357a (fun s => s.RIP = 0x12357a) (andR32R32Effect 0x12357a 3 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[4638, 4580]
    (.letOp (n := 4642) (.out 0x12357d (xorR32R32Effect 0x12357d 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[4640, 4356]
    (.letOp (n := 4643) (.exec 0x12357d (fun s => s.RIP = 0x12357d) (xorR32R32Effect 0x12357d 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[4640, 4356]
    (.letOp (n := 4644) (.out 0x123580 (addR32R32Effect 0x123580 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[4246, 4626]
    (.letOp (n := 4645) (.exec 0x123580 (fun s => s.RIP = 0x123580) (addR32R32Effect 0x123580 3 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[4246, 4626]
    (.letOp (n := 4646) (.out 0x123583 (addR32R32Effect 0x123583 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[4644, 4642]
    (.letOp (n := 4647) (.exec 0x123583 (fun s => s.RIP = 0x123583) (addR32R32Effect 0x123583 3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[4644, 4642]
    (.letOp (n := 4648) (.out 0x123586 (addR32R32Effect 0x123586 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[4634, 4646]
    (.letOp (n := 4649) (.exec 0x123586 (fun s => s.RIP = 0x123586) (addR32R32Effect 0x123586 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[4634, 4646]
    (.letOp (n := 4650) (.out 0x123588 (addR32Imm32Effect 0x123588 6 1 0xc76c51a3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[4648]
    (.letOp (n := 4651) (.exec 0x123588 (fun s => s.RIP = 0x123588) (addR32Imm32Effect 0x123588 6 1 0xc76c51a3) (Reg.operands [.gpr 1] [])) #v[4648]
    (.letOp (n := 4652) (.out 0x12358e (movR32R32Effect 0x12358e 3 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[4586]
    (.letOp (n := 4653) (.exec 0x12358e (fun s => s.RIP = 0x12358e) (movR32R32Effect 0x12358e 3 7 12) (Reg.operands [.gpr 12] [])) #v[4586]
    (.letOp (n := 4654) (.out 0x123591 (rolR32Effect 0x123591 3 7 30) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[4652]
    (.letOp (n := 4655) (.exec 0x123591 (fun s => s.RIP = 0x123591) (rolR32Effect 0x123591 3 7 30) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4652]
    (.letOp (n := 4656) (.out 0x123594 (movR32R32Effect 0x123594 3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[4586]
    (.letOp (n := 4657) (.exec 0x123594 (fun s => s.RIP = 0x123594) (movR32R32Effect 0x123594 3 8 12) (Reg.operands [.gpr 12] [])) #v[4586]
    (.letOp (n := 4658) (.out 0x123597 (rolR32Effect 0x123597 4 8 19) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4656]
    (.letOp (n := 4659) (.exec 0x123597 (fun s => s.RIP = 0x123597) (rolR32Effect 0x123597 4 8 19) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4656]
    (.letOp (n := 4660) (.out 0x12359b (xorR32R32Effect 0x12359b 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[4658, 4654]
    (.letOp (n := 4661) (.exec 0x12359b (fun s => s.RIP = 0x12359b) (xorR32R32Effect 0x12359b 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[4658, 4654]
    (.letOp (n := 4662) (.out 0x12359e (movR32R32Effect 0x12359e 3 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[4586]
    (.letOp (n := 4663) (.exec 0x12359e (fun s => s.RIP = 0x12359e) (movR32R32Effect 0x12359e 3 7 12) (Reg.operands [.gpr 12] [])) #v[4586]
    (b_l121930_118))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_117 : List UInt8 :=
  [0x44, 0x8B, 0x74, 0x24, 0x58, 0x41, 0x01, 0xCE, 0x89, 0xD1, 0xC1, 0xC1, 0x07, 0x45, 0x31, 0xC8,
    0x44, 0x31, 0xC1, 0x41, 0x89, 0xF0, 0x41, 0x31, 0xC0, 0x41, 0x21, 0xD0, 0x41, 0x31, 0xC0, 0x44,
    0x01, 0xF7, 0x44, 0x01, 0xC7, 0x01, 0xF9, 0x81, 0xC1, 0xA3, 0x51, 0x6C, 0xC7, 0x44, 0x89, 0xE7,
    0xC1, 0xC7, 0x1E, 0x45, 0x89, 0xE0, 0x41, 0xC1, 0xC0, 0x13, 0x41, 0x31, 0xF8, 0x44, 0x89, 0xE7] ++ bytes_l121930_118

theorem code_l121930_117 : ∀ x ∈ codeRange 0x123561 bytes_l121930_117, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23561 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_118

def b_l121930_116 : Block Op Label signature Reg.count 4586 :=
  .letOp (n := 4586) (.out 0x12351a (addR32R32Effect 0x12351a 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[4574, 4538]
    (.letOp (n := 4587) (.exec 0x12351a (fun s => s.RIP = 0x12351a) (addR32R32Effect 0x12351a 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[4574, 4538]
    (.letOp (n := 4588) (.out 0x12351d (movR32R32Effect 0x12351d 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[4510]
    (.letOp (n := 4589) (.exec 0x12351d (fun s => s.RIP = 0x12351d) (movR32R32Effect 0x12351d 2 1 5) (Reg.operands [.gpr 5] [])) #v[4510]
    (.letOp (n := 4590) (.out 0x12351f (rolR32Effect 0x12351f 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4588]
    (.letOp (n := 4591) (.exec 0x12351f (fun s => s.RIP = 0x12351f) (rolR32Effect 0x12351f 3 1 14) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4588]
    (.letOp (n := 4592) (.out 0x123522 (xorR32R32Effect 0x123522 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[4578, 4570]
    (.letOp (n := 4593) (.exec 0x123522 (fun s => s.RIP = 0x123522) (xorR32R32Effect 0x123522 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[4578, 4570]
    (.letOp (n := 4594) (.out 0x123525 (xorR32R32Effect 0x123525 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[4590, 4584]
    (.letOp (n := 4595) (.exec 0x123525 (fun s => s.RIP = 0x123525) (xorR32R32Effect 0x123525 3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[4590, 4584]
    (.letOp (n := 4596) (.out 0x123528 (movR32R32Effect 0x123528 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[4510]
    (.letOp (n := 4597) (.exec 0x123528 (fun s => s.RIP = 0x123528) (movR32R32Effect 0x123528 3 9 5) (Reg.operands [.gpr 5] [])) #v[4510]
    (.letOp (n := 4598) (.out 0x12352b (shrR32Effect 0x12352b 4 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4596]
    (.letOp (n := 4599) (.exec 0x12352b (fun s => s.RIP = 0x12352b) (shrR32Effect 0x12352b 4 9 3) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4596]
    (.letOp (n := 4600) (.out 0x12352f (xorR32R32Effect 0x12352f 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[4598, 4594]
    (.letOp (n := 4601) (.exec 0x12352f (fun s => s.RIP = 0x12352f) (xorR32R32Effect 0x12352f 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[4598, 4594]
    (.letOp (n := 4602) (.out 0x123532 (movR64M64Effect 0x123532 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 4603) (.exec 0x123532 (LoadPre 0x123532 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x123532 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x123532 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 4604) (.out 0x123537 (addR32R32Effect 0x123537 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[4602, 4474]
    (.letOp (n := 4605) (.exec 0x123537 (fun s => s.RIP = 0x123537) (addR32R32Effect 0x123537 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[4602, 4474]
    (.letOp (n := 4606) (.exec 0x12353a (StorePre 0x12353a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12353a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12353a 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[4604, 4]
    (.letOp (n := 4607) (.out 0x12353f (addR32R32Effect 0x12353f 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[4600, 4474]
    (.letOp (n := 4608) (.exec 0x12353f (fun s => s.RIP = 0x12353f) (addR32R32Effect 0x12353f 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[4600, 4474]
    (.letOp (n := 4609) (.exec 0x123542 (StorePre 0x123542 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x123542 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x123542 9 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[4607, 4]
    (.letOp (n := 4610) (.out 0x12354a (movR32R32Effect 0x12354a 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[4474]
    (.letOp (n := 4611) (.exec 0x12354a (fun s => s.RIP = 0x12354a) (movR32R32Effect 0x12354a 3 1 10) (Reg.operands [.gpr 10] [])) #v[4474]
    (.letOp (n := 4612) (.out 0x12354d (shrR32Effect 0x12354d 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4610]
    (.letOp (n := 4613) (.exec 0x12354d (fun s => s.RIP = 0x12354d) (shrR32Effect 0x12354d 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4610]
    (.letOp (n := 4614) (.out 0x123550 (movR32R32Effect 0x123550 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[4580]
    (.letOp (n := 4615) (.exec 0x123550 (fun s => s.RIP = 0x123550) (movR32R32Effect 0x123550 3 9 2) (Reg.operands [.gpr 2] [])) #v[4580]
    (.letOp (n := 4616) (.out 0x123553 (rolR32Effect 0x123553 4 9 26) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4614]
    (.letOp (n := 4617) (.exec 0x123553 (fun s => s.RIP = 0x123553) (rolR32Effect 0x123553 4 9 26) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4614]
    (.letOp (n := 4618) (.out 0x123557 (xorR32R32Effect 0x123557 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[4612, 4592]
    (.letOp (n := 4619) (.exec 0x123557 (fun s => s.RIP = 0x123557) (xorR32R32Effect 0x123557 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[4612, 4592]
    (.letOp (n := 4620) (.out 0x12355a (movR32R32Effect 0x12355a 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[4580]
    (.letOp (n := 4621) (.exec 0x12355a (fun s => s.RIP = 0x12355a) (movR32R32Effect 0x12355a 3 8 2) (Reg.operands [.gpr 2] [])) #v[4580]
    (.letOp (n := 4622) (.out 0x12355d (rolR32Effect 0x12355d 4 8 21) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4620]
    (.letOp (n := 4623) (.exec 0x12355d (fun s => s.RIP = 0x12355d) (rolR32Effect 0x12355d 4 8 21) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4620]
    (b_l121930_117))))))))))))))))))))))))))))))))))))))

def bytes_l121930_116 : List UInt8 :=
  [0x41, 0x01, 0xCC, 0x89, 0xE9, 0xC1, 0xC1, 0x0E, 0x45, 0x31, 0xC8, 0x44, 0x31, 0xF1, 0x41, 0x89,
    0xE9, 0x41, 0xC1, 0xE9, 0x03, 0x41, 0x31, 0xC9, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x44, 0x01, 0xD1,
    0x48, 0x89, 0x4C, 0x24, 0x28, 0x45, 0x01, 0xD1, 0x44, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x44, 0x89, 0xD1, 0xC1, 0xE9, 0x0A, 0x41, 0x89, 0xD1, 0x41, 0xC1, 0xC1, 0x1A, 0x44, 0x31, 0xC1,
    0x41, 0x89, 0xD0, 0x41, 0xC1, 0xC0, 0x15] ++ bytes_l121930_117

theorem code_l121930_116 : ∀ x ∈ codeRange 0x12351a bytes_l121930_116, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2351a 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_117

def b_l121930_115 : Block Op Label signature Reg.count 4546 :=
  .letOp (n := 4546) (.out 0x1234da (rolR32Effect 0x1234da 4 9 19) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4544]
    (.letOp (n := 4547) (.exec 0x1234da (fun s => s.RIP = 0x1234da) (rolR32Effect 0x1234da 4 9 19) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4544]
    (.letOp (n := 4548) (.out 0x1234de (xorR32R32Effect 0x1234de 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[4546, 4542]
    (.letOp (n := 4549) (.exec 0x1234de (fun s => s.RIP = 0x1234de) (xorR32R32Effect 0x1234de 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[4546, 4542]
    (.letOp (n := 4550) (.out 0x1234e1 (movR32R32Effect 0x1234e1 3 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[4472]
    (.letOp (n := 4551) (.exec 0x1234e1 (fun s => s.RIP = 0x1234e1) (movR32R32Effect 0x1234e1 3 8 15) (Reg.operands [.gpr 15] [])) #v[4472]
    (.letOp (n := 4552) (.out 0x1234e4 (rolR32Effect 0x1234e4 4 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4550]
    (.letOp (n := 4553) (.exec 0x1234e4 (fun s => s.RIP = 0x1234e4) (rolR32Effect 0x1234e4 4 8 10) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4550]
    (.letOp (n := 4554) (.out 0x1234e8 (xorR32R32Effect 0x1234e8 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[4552, 4548]
    (.letOp (n := 4555) (.exec 0x1234e8 (fun s => s.RIP = 0x1234e8) (xorR32R32Effect 0x1234e8 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[4552, 4548]
    (.letOp (n := 4556) (.out 0x1234eb (movR32R32Effect 0x1234eb 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[4362]
    (.letOp (n := 4557) (.exec 0x1234eb (fun s => s.RIP = 0x1234eb) (movR32R32Effect 0x1234eb 3 9 3) (Reg.operands [.gpr 3] [])) #v[4362]
    (.letOp (n := 4558) (.out 0x1234ee (andR32R32Effect 0x1234ee 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[4556, 4248]
    (.letOp (n := 4559) (.exec 0x1234ee (fun s => s.RIP = 0x1234ee) (andR32R32Effect 0x1234ee 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[4556, 4248]
    (.letOp (n := 4560) (.out 0x1234f1 (movR32R32Effect 0x1234f1 3 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 3] []) (.reg (.gpr 14))) #v[4362]
    (.letOp (n := 4561) (.exec 0x1234f1 (fun s => s.RIP = 0x1234f1) (movR32R32Effect 0x1234f1 3 14 3) (Reg.operands [.gpr 3] [])) #v[4362]
    (.letOp (n := 4562) (.out 0x1234f4 (xorR32R32Effect 0x1234f4 3 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[4560, 4248]
    (.letOp (n := 4563) (.exec 0x1234f4 (fun s => s.RIP = 0x1234f4) (xorR32R32Effect 0x1234f4 3 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[4560, 4248]
    (.letOp (n := 4564) (.out 0x1234f7 (andR32R32Effect 0x1234f7 3 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[4562, 4472]
    (.letOp (n := 4565) (.exec 0x1234f7 (fun s => s.RIP = 0x1234f7) (andR32R32Effect 0x1234f7 3 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[4562, 4472]
    (.letOp (n := 4566) (.out 0x1234fa (xorR32R32Effect 0x1234fa 3 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[4564, 4558]
    (.letOp (n := 4567) (.exec 0x1234fa (fun s => s.RIP = 0x1234fa) (xorR32R32Effect 0x1234fa 3 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[4564, 4558]
    (.letOp (n := 4568) (.out 0x1234fd (movR32R32Effect 0x1234fd 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[4474]
    (.letOp (n := 4569) (.exec 0x1234fd (fun s => s.RIP = 0x1234fd) (movR32R32Effect 0x1234fd 3 9 10) (Reg.operands [.gpr 10] [])) #v[4474]
    (.letOp (n := 4570) (.out 0x123500 (rolR32Effect 0x123500 4 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4568]
    (.letOp (n := 4571) (.exec 0x123500 (fun s => s.RIP = 0x123500) (rolR32Effect 0x123500 4 9 15) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4568]
    (.letOp (n := 4572) (.out 0x123504 (addR32R32Effect 0x123504 3 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[4566, 4554]
    (.letOp (n := 4573) (.exec 0x123504 (fun s => s.RIP = 0x123504) (addR32R32Effect 0x123504 3 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[4566, 4554]
    (.letOp (n := 4574) (.out 0x123507 (movR64R64Effect 0x123507 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[4572]
    (.letOp (n := 4575) (.exec 0x123507 (fun s => s.RIP = 0x123507) (movR64R64Effect 0x123507 12 14) (Reg.operands [.gpr 14] [])) #v[4572]
    (.letOp (n := 4576) (.out 0x12350a (movR32R32Effect 0x12350a 3 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[4474]
    (.letOp (n := 4577) (.exec 0x12350a (fun s => s.RIP = 0x12350a) (movR32R32Effect 0x12350a 3 8 10) (Reg.operands [.gpr 10] [])) #v[4474]
    (.letOp (n := 4578) (.out 0x12350d (rolR32Effect 0x12350d 4 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4576]
    (.letOp (n := 4579) (.exec 0x12350d (fun s => s.RIP = 0x12350d) (rolR32Effect 0x12350d 4 8 13) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4576]
    (.letOp (n := 4580) (.out 0x123511 (addR32R32Effect 0x123511 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[4151, 4538]
    (.letOp (n := 4581) (.exec 0x123511 (fun s => s.RIP = 0x123511) (addR32R32Effect 0x123511 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[4151, 4538]
    (.letOp (n := 4582) (.out 0x123513 (movR32R32Effect 0x123513 3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 5] []) (.reg (.gpr 14))) #v[4510]
    (.letOp (n := 4583) (.exec 0x123513 (fun s => s.RIP = 0x123513) (movR32R32Effect 0x123513 3 14 5) (Reg.operands [.gpr 5] [])) #v[4510]
    (.letOp (n := 4584) (.out 0x123516 (rolR32Effect 0x123516 4 14 25) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[4582]
    (.letOp (n := 4585) (.exec 0x123516 (fun s => s.RIP = 0x123516) (rolR32Effect 0x123516 4 14 25) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4582]
    (b_l121930_116))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_115 : List UInt8 :=
  [0x41, 0xC1, 0xC1, 0x13, 0x45, 0x31, 0xC1, 0x45, 0x89, 0xF8, 0x41, 0xC1, 0xC0, 0x0A, 0x45, 0x31,
    0xC8, 0x41, 0x89, 0xD9, 0x45, 0x21, 0xD9, 0x41, 0x89, 0xDE, 0x45, 0x31, 0xDE, 0x45, 0x21, 0xFE,
    0x45, 0x31, 0xCE, 0x45, 0x89, 0xD1, 0x41, 0xC1, 0xC1, 0x0F, 0x45, 0x01, 0xC6, 0x4D, 0x89, 0xF4,
    0x45, 0x89, 0xD0, 0x41, 0xC1, 0xC0, 0x0D, 0x01, 0xCA, 0x41, 0x89, 0xEE, 0x41, 0xC1, 0xC6, 0x19] ++ bytes_l121930_116

theorem code_l121930_115 : ∀ x ∈ codeRange 0x1234da bytes_l121930_115, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x234da 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_116

def b_l121930_114 : Block Op Label signature Reg.count 4506 :=
  .letOp (n := 4506) (.out 0x123496 (rolR32Effect 0x123496 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4504]
    (.letOp (n := 4507) (.exec 0x123496 (fun s => s.RIP = 0x123496) (rolR32Effect 0x123496 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4504]
    (.letOp (n := 4508) (.out 0x123499 (movR32M32LowEffect 0x123499 5 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 4509) (.exec 0x123499 (LoadPre 0x123499 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x123499 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x123499 5 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 4510) (.out 0x1234a0 (addR32R32Effect 0x1234a0 3 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[4508, 4502]
    (.letOp (n := 4511) (.exec 0x1234a0 (fun s => s.RIP = 0x1234a0) (addR32R32Effect 0x1234a0 3 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[4508, 4502]
    (.letOp (n := 4512) (.out 0x1234a3 (movR32R32Effect 0x1234a3 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[4466]
    (.letOp (n := 4513) (.exec 0x1234a3 (fun s => s.RIP = 0x1234a3) (movR32R32Effect 0x1234a3 3 8 6) (Reg.operands [.gpr 6] [])) #v[4466]
    (.letOp (n := 4514) (.out 0x1234a6 (rolR32Effect 0x1234a6 4 8 21) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4512]
    (.letOp (n := 4515) (.exec 0x1234a6 (fun s => s.RIP = 0x1234a6) (rolR32Effect 0x1234a6 4 8 21) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4512]
    (.letOp (n := 4516) (.out 0x1234aa (xorR32R32Effect 0x1234aa 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[4514, 4506]
    (.letOp (n := 4517) (.exec 0x1234aa (fun s => s.RIP = 0x1234aa) (xorR32R32Effect 0x1234aa 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[4514, 4506]
    (.letOp (n := 4518) (.out 0x1234ad (movR32R32Effect 0x1234ad 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[4466]
    (.letOp (n := 4519) (.exec 0x1234ad (fun s => s.RIP = 0x1234ad) (movR32R32Effect 0x1234ad 2 1 6) (Reg.operands [.gpr 6] [])) #v[4466]
    (.letOp (n := 4520) (.out 0x1234af (rolR32Effect 0x1234af 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4518]
    (.letOp (n := 4521) (.exec 0x1234af (fun s => s.RIP = 0x1234af) (rolR32Effect 0x1234af 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4518]
    (.letOp (n := 4522) (.out 0x1234b2 (xorR32R32Effect 0x1234b2 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[4520, 4516]
    (.letOp (n := 4523) (.exec 0x1234b2 (fun s => s.RIP = 0x1234b2) (xorR32R32Effect 0x1234b2 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[4520, 4516]
    (.letOp (n := 4524) (.out 0x1234b5 (movR32R32Effect 0x1234b5 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[4356]
    (.letOp (n := 4525) (.exec 0x1234b5 (fun s => s.RIP = 0x1234b5) (movR32R32Effect 0x1234b5 3 8 0) (Reg.operands [.gpr 0] [])) #v[4356]
    (.letOp (n := 4526) (.out 0x1234b8 (xorR32R32Effect 0x1234b8 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[4524, 4246]
    (.letOp (n := 4527) (.exec 0x1234b8 (fun s => s.RIP = 0x1234b8) (xorR32R32Effect 0x1234b8 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[4524, 4246]
    (.letOp (n := 4528) (.out 0x1234bb (andR32R32Effect 0x1234bb 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[4526, 4466]
    (.letOp (n := 4529) (.exec 0x1234bb (fun s => s.RIP = 0x1234bb) (andR32R32Effect 0x1234bb 3 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[4526, 4466]
    (.letOp (n := 4530) (.out 0x1234be (xorR32R32Effect 0x1234be 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[4528, 4246]
    (.letOp (n := 4531) (.exec 0x1234be (fun s => s.RIP = 0x1234be) (xorR32R32Effect 0x1234be 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[4528, 4246]
    (.letOp (n := 4532) (.out 0x1234c1 (addR32R32Effect 0x1234c1 3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[4145, 4510]
    (.letOp (n := 4533) (.exec 0x1234c1 (fun s => s.RIP = 0x1234c1) (addR32R32Effect 0x1234c1 3 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[4145, 4510]
    (.letOp (n := 4534) (.out 0x1234c4 (addR32R32Effect 0x1234c4 3 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[4532, 4530]
    (.letOp (n := 4535) (.exec 0x1234c4 (fun s => s.RIP = 0x1234c4) (addR32R32Effect 0x1234c4 3 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[4532, 4530]
    (.letOp (n := 4536) (.out 0x1234c7 (addR32R32Effect 0x1234c7 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[4522, 4534]
    (.letOp (n := 4537) (.exec 0x1234c7 (fun s => s.RIP = 0x1234c7) (addR32R32Effect 0x1234c7 3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[4522, 4534]
    (.letOp (n := 4538) (.out 0x1234ca (addR32Imm32Effect 0x1234ca 6 1 0xc24b8b70) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[4536]
    (.letOp (n := 4539) (.exec 0x1234ca (fun s => s.RIP = 0x1234ca) (addR32Imm32Effect 0x1234ca 6 1 0xc24b8b70) (Reg.operands [.gpr 1] [])) #v[4536]
    (.letOp (n := 4540) (.out 0x1234d0 (movR32R32Effect 0x1234d0 3 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[4472]
    (.letOp (n := 4541) (.exec 0x1234d0 (fun s => s.RIP = 0x1234d0) (movR32R32Effect 0x1234d0 3 8 15) (Reg.operands [.gpr 15] [])) #v[4472]
    (.letOp (n := 4542) (.out 0x1234d3 (rolR32Effect 0x1234d3 4 8 30) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4540]
    (.letOp (n := 4543) (.exec 0x1234d3 (fun s => s.RIP = 0x1234d3) (rolR32Effect 0x1234d3 4 8 30) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4540]
    (.letOp (n := 4544) (.out 0x1234d7 (movR32R32Effect 0x1234d7 3 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 15] []) (.reg (.gpr 9))) #v[4472]
    (.letOp (n := 4545) (.exec 0x1234d7 (fun s => s.RIP = 0x1234d7) (movR32R32Effect 0x1234d7 3 9 15) (Reg.operands [.gpr 15] [])) #v[4472]
    (b_l121930_115))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_114 : List UInt8 :=
  [0xC1, 0xC1, 0x1A, 0x8B, 0xAC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x44, 0x01, 0xC5, 0x41, 0x89, 0xF0,
    0x41, 0xC1, 0xC0, 0x15, 0x41, 0x31, 0xC8, 0x89, 0xF1, 0xC1, 0xC1, 0x07, 0x44, 0x31, 0xC1, 0x41,
    0x89, 0xC0, 0x41, 0x31, 0xF8, 0x41, 0x21, 0xF0, 0x41, 0x31, 0xF8, 0x41, 0x01, 0xEE, 0x45, 0x01,
    0xC6, 0x44, 0x01, 0xF1, 0x81, 0xC1, 0x70, 0x8B, 0x4B, 0xC2, 0x45, 0x89, 0xF8, 0x41, 0xC1, 0xC0,
    0x1E, 0x45, 0x89, 0xF9] ++ bytes_l121930_115

theorem code_l121930_114 : ∀ x ∈ codeRange 0x123496 bytes_l121930_114, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23496 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_115

def b_l121930_113 : Block Op Label signature Reg.count 4468 :=
  .letOp (n := 4468) (.out 0x123453 (movR32R32Effect 0x123453 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[4292]
    (.letOp (n := 4469) (.exec 0x123453 (fun s => s.RIP = 0x123453) (movR32R32Effect 0x123453 3 1 12) (Reg.operands [.gpr 12] [])) #v[4292]
    (.letOp (n := 4470) (.out 0x123456 (rolR32Effect 0x123456 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4468]
    (.letOp (n := 4471) (.exec 0x123456 (fun s => s.RIP = 0x123456) (rolR32Effect 0x123456 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4468]
    (.letOp (n := 4472) (.out 0x123459 (addR32R32Effect 0x123459 3 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[4460, 4438]
    (.letOp (n := 4473) (.exec 0x123459 (fun s => s.RIP = 0x123459) (addR32R32Effect 0x123459 3 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[4460, 4438]
    (.letOp (n := 4474) (.out 0x12345c (movR32R32Effect 0x12345c 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 5] []) (.reg (.gpr 10))) #v[4398]
    (.letOp (n := 4475) (.exec 0x12345c (fun s => s.RIP = 0x12345c) (movR32R32Effect 0x12345c 3 10 5) (Reg.operands [.gpr 5] [])) #v[4398]
    (.letOp (n := 4476) (.out 0x12345f (movR32R32Effect 0x12345f 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[4398]
    (.letOp (n := 4477) (.exec 0x12345f (fun s => s.RIP = 0x12345f) (movR32R32Effect 0x12345f 3 9 5) (Reg.operands [.gpr 5] [])) #v[4398]
    (.letOp (n := 4478) (.out 0x123462 (rolR32Effect 0x123462 4 9 25) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4476]
    (.letOp (n := 4479) (.exec 0x123462 (fun s => s.RIP = 0x123462) (rolR32Effect 0x123462 4 9 25) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4476]
    (.letOp (n := 4480) (.out 0x123466 (xorR32R32Effect 0x123466 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[4470, 4464]
    (.letOp (n := 4481) (.exec 0x123466 (fun s => s.RIP = 0x123466) (xorR32R32Effect 0x123466 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[4470, 4464]
    (.letOp (n := 4482) (.out 0x123469 (movR32R32Effect 0x123469 3 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[4398]
    (.letOp (n := 4483) (.exec 0x123469 (fun s => s.RIP = 0x123469) (movR32R32Effect 0x123469 3 8 5) (Reg.operands [.gpr 5] [])) #v[4398]
    (.letOp (n := 4484) (.out 0x12346c (rolR32Effect 0x12346c 4 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4482]
    (.letOp (n := 4485) (.exec 0x12346c (fun s => s.RIP = 0x12346c) (rolR32Effect 0x12346c 4 8 14) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4482]
    (.letOp (n := 4486) (.out 0x123470 (xorR32R32Effect 0x123470 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[4484, 4478]
    (.letOp (n := 4487) (.exec 0x123470 (fun s => s.RIP = 0x123470) (xorR32R32Effect 0x123470 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[4484, 4478]
    (.letOp (n := 4488) (.out 0x123473 (movR32R32Effect 0x123473 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[4398]
    (.letOp (n := 4489) (.exec 0x123473 (fun s => s.RIP = 0x123473) (movR32R32Effect 0x123473 3 9 5) (Reg.operands [.gpr 5] [])) #v[4398]
    (.letOp (n := 4490) (.out 0x123476 (shrR32Effect 0x123476 4 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4488]
    (.letOp (n := 4491) (.exec 0x123476 (fun s => s.RIP = 0x123476) (shrR32Effect 0x123476 4 9 3) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4488]
    (.letOp (n := 4492) (.out 0x12347a (xorR32R32Effect 0x12347a 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[4490, 4486]
    (.letOp (n := 4493) (.exec 0x12347a (fun s => s.RIP = 0x12347a) (xorR32R32Effect 0x12347a 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[4490, 4486]
    (.letOp (n := 4494) (.exec 0x12347d (StorePre 0x12347d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x12347d + BitVec.ofNat 64 5)) 4) (addMREffect 0x12347d 5 32 12 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[4292, 4]
    (.letOp (n := 4495) (.out 0x123482 (addR32R32Effect 0x123482 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[4492, 4292]
    (.letOp (n := 4496) (.exec 0x123482 (fun s => s.RIP = 0x123482) (addR32R32Effect 0x123482 3 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[4492, 4292]
    (.letOp (n := 4497) (.exec 0x123485 (StorePre 0x123485 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x123485 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x123485 9 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[4495, 4]
    (.letOp (n := 4498) (.out 0x12348a (movR32R32Effect 0x12348a 3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[4292]
    (.letOp (n := 4499) (.exec 0x12348a (fun s => s.RIP = 0x12348a) (movR32R32Effect 0x12348a 3 8 12) (Reg.operands [.gpr 12] [])) #v[4292]
    (.letOp (n := 4500) (.out 0x12348d (shrR32Effect 0x12348d 4 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4498]
    (.letOp (n := 4501) (.exec 0x12348d (fun s => s.RIP = 0x12348d) (shrR32Effect 0x12348d 4 8 10) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4498]
    (.letOp (n := 4502) (.out 0x123491 (xorR32R32Effect 0x123491 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[4500, 4480]
    (.letOp (n := 4503) (.exec 0x123491 (fun s => s.RIP = 0x123491) (xorR32R32Effect 0x123491 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[4500, 4480]
    (.letOp (n := 4504) (.out 0x123494 (movR32R32Effect 0x123494 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[4466]
    (.letOp (n := 4505) (.exec 0x123494 (fun s => s.RIP = 0x123494) (movR32R32Effect 0x123494 2 1 6) (Reg.operands [.gpr 6] [])) #v[4466]
    (b_l121930_114))))))))))))))))))))))))))))))))))))))

def bytes_l121930_113 : List UInt8 :=
  [0x44, 0x89, 0xE1, 0xC1, 0xC1, 0x0D, 0x45, 0x01, 0xD7, 0x41, 0x89, 0xEA, 0x41, 0x89, 0xE9, 0x41,
    0xC1, 0xC1, 0x19, 0x44, 0x31, 0xC1, 0x41, 0x89, 0xE8, 0x41, 0xC1, 0xC0, 0x0E, 0x45, 0x31, 0xC8,
    0x41, 0x89, 0xE9, 0x41, 0xC1, 0xE9, 0x03, 0x45, 0x31, 0xC1, 0x44, 0x01, 0x64, 0x24, 0x40, 0x45,
    0x01, 0xE1, 0x44, 0x89, 0x4C, 0x24, 0x68, 0x45, 0x89, 0xE0, 0x41, 0xC1, 0xE8, 0x0A, 0x41, 0x31,
    0xC8, 0x89, 0xF1] ++ bytes_l121930_114

theorem code_l121930_113 : ∀ x ∈ codeRange 0x123453 bytes_l121930_113, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23453 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_114

def b_l121930_112 : Block Op Label signature Reg.count 4428 :=
  .letOp (n := 4428) (.out 0x123411 (rolR32Effect 0x123411 4 9 30) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4426]
    (.letOp (n := 4429) (.exec 0x123411 (fun s => s.RIP = 0x123411) (rolR32Effect 0x123411 4 9 30) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4426]
    (.letOp (n := 4430) (.out 0x123415 (addR32R32Effect 0x123415 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[4424, 4422]
    (.letOp (n := 4431) (.exec 0x123415 (fun s => s.RIP = 0x123415) (addR32R32Effect 0x123415 3 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[4424, 4422]
    (.letOp (n := 4432) (.out 0x123418 (movR32R32Effect 0x123418 3 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[4362]
    (.letOp (n := 4433) (.exec 0x123418 (fun s => s.RIP = 0x123418) (movR32R32Effect 0x123418 3 8 3) (Reg.operands [.gpr 3] [])) #v[4362]
    (.letOp (n := 4434) (.out 0x12341b (rolR32Effect 0x12341b 4 8 19) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4432]
    (.letOp (n := 4435) (.exec 0x12341b (fun s => s.RIP = 0x12341b) (rolR32Effect 0x12341b 4 8 19) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4432]
    (.letOp (n := 4436) (.out 0x12341f (addR32R32Effect 0x12341f 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[4430, 4414]
    (.letOp (n := 4437) (.exec 0x12341f (fun s => s.RIP = 0x12341f) (addR32R32Effect 0x12341f 3 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[4430, 4414]
    (.letOp (n := 4438) (.out 0x123422 (addR32Imm32Effect 0x123422 7 10 0xa81a664b) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[4436]
    (.letOp (n := 4439) (.exec 0x123422 (fun s => s.RIP = 0x123422) (addR32Imm32Effect 0x123422 7 10 0xa81a664b) (Reg.operands [.gpr 10] [])) #v[4436]
    (.letOp (n := 4440) (.out 0x123429 (movR32R32Effect 0x123429 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[4362]
    (.letOp (n := 4441) (.exec 0x123429 (fun s => s.RIP = 0x123429) (movR32R32Effect 0x123429 2 1 3) (Reg.operands [.gpr 3] [])) #v[4362]
    (.letOp (n := 4442) (.out 0x12342b (rolR32Effect 0x12342b 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4440]
    (.letOp (n := 4443) (.exec 0x12342b (fun s => s.RIP = 0x12342b) (rolR32Effect 0x12342b 3 1 10) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4440]
    (.letOp (n := 4444) (.out 0x12342e (xorR32R32Effect 0x12342e 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[4434, 4428]
    (.letOp (n := 4445) (.exec 0x12342e (fun s => s.RIP = 0x12342e) (xorR32R32Effect 0x12342e 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[4434, 4428]
    (.letOp (n := 4446) (.out 0x123431 (xorR32R32Effect 0x123431 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[4442, 4444]
    (.letOp (n := 4447) (.exec 0x123431 (fun s => s.RIP = 0x123431) (xorR32R32Effect 0x123431 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[4442, 4444]
    (.letOp (n := 4448) (.out 0x123434 (movR32R32Effect 0x123434 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[4248]
    (.letOp (n := 4449) (.exec 0x123434 (fun s => s.RIP = 0x123434) (movR32R32Effect 0x123434 3 8 11) (Reg.operands [.gpr 11] [])) #v[4248]
    (.letOp (n := 4450) (.out 0x123437 (andR32R32Effect 0x123437 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[4448, 4151]
    (.letOp (n := 4451) (.exec 0x123437 (fun s => s.RIP = 0x123437) (andR32R32Effect 0x123437 3 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[4448, 4151]
    (.letOp (n := 4452) (.out 0x12343a (movR32R32Effect 0x12343a 3 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 11] []) (.reg (.gpr 15))) #v[4248]
    (.letOp (n := 4453) (.exec 0x12343a (fun s => s.RIP = 0x12343a) (movR32R32Effect 0x12343a 3 15 11) (Reg.operands [.gpr 11] [])) #v[4248]
    (.letOp (n := 4454) (.out 0x12343d (xorR32R32Effect 0x12343d 3 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[4452, 4151]
    (.letOp (n := 4455) (.exec 0x12343d (fun s => s.RIP = 0x12343d) (xorR32R32Effect 0x12343d 3 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[4452, 4151]
    (.letOp (n := 4456) (.out 0x123440 (andR32R32Effect 0x123440 3 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[4454, 4362]
    (.letOp (n := 4457) (.exec 0x123440 (fun s => s.RIP = 0x123440) (andR32R32Effect 0x123440 3 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[4454, 4362]
    (.letOp (n := 4458) (.out 0x123443 (xorR32R32Effect 0x123443 3 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[4456, 4450]
    (.letOp (n := 4459) (.exec 0x123443 (fun s => s.RIP = 0x123443) (xorR32R32Effect 0x123443 3 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[4456, 4450]
    (.letOp (n := 4460) (.out 0x123446 (addR32R32Effect 0x123446 3 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[4458, 4446]
    (.letOp (n := 4461) (.exec 0x123446 (fun s => s.RIP = 0x123446) (addR32R32Effect 0x123446 3 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[4458, 4446]
    (.letOp (n := 4462) (.out 0x123449 (movR32R32Effect 0x123449 3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[4292]
    (.letOp (n := 4463) (.exec 0x123449 (fun s => s.RIP = 0x123449) (movR32R32Effect 0x123449 3 8 12) (Reg.operands [.gpr 12] [])) #v[4292]
    (.letOp (n := 4464) (.out 0x12344c (rolR32Effect 0x12344c 4 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4462]
    (.letOp (n := 4465) (.exec 0x12344c (fun s => s.RIP = 0x12344c) (rolR32Effect 0x12344c 4 8 15) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4462]
    (.letOp (n := 4466) (.out 0x123450 (addR32R32Effect 0x123450 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[4041, 4438]
    (.letOp (n := 4467) (.exec 0x123450 (fun s => s.RIP = 0x123450) (addR32R32Effect 0x123450 3 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[4041, 4438]
    (b_l121930_113))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_112 : List UInt8 :=
  [0x41, 0xC1, 0xC1, 0x1E, 0x45, 0x01, 0xC2, 0x41, 0x89, 0xD8, 0x41, 0xC1, 0xC0, 0x13, 0x41, 0x01,
    0xCA, 0x41, 0x81, 0xC2, 0x4B, 0x66, 0x1A, 0xA8, 0x89, 0xD9, 0xC1, 0xC1, 0x0A, 0x45, 0x31, 0xC8,
    0x44, 0x31, 0xC1, 0x45, 0x89, 0xD8, 0x41, 0x21, 0xD0, 0x45, 0x89, 0xDF, 0x41, 0x31, 0xD7, 0x41,
    0x21, 0xDF, 0x45, 0x31, 0xC7, 0x41, 0x01, 0xCF, 0x45, 0x89, 0xE0, 0x41, 0xC1, 0xC0, 0x0F, 0x44,
    0x01, 0xD6] ++ bytes_l121930_113

theorem code_l121930_112 : ∀ x ∈ codeRange 0x123411 bytes_l121930_112, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23411 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_113

def b_l121930_111 : Block Op Label signature Reg.count 4389 :=
  .letOp (n := 4389) (.exec 0x1233d3 (StorePre 0x1233d3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1233d3 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1233d3 8 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[4387, 4]
    (.letOp (n := 4390) (.out 0x1233d8 (movR32R32Effect 0x1233d8 3 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[4262]
    (.letOp (n := 4391) (.exec 0x1233d8 (fun s => s.RIP = 0x1233d8) (movR32R32Effect 0x1233d8 3 8 5) (Reg.operands [.gpr 5] [])) #v[4262]
    (.letOp (n := 4392) (.out 0x1233db (shrR32Effect 0x1233db 4 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4390]
    (.letOp (n := 4393) (.exec 0x1233db (fun s => s.RIP = 0x1233db) (shrR32Effect 0x1233db 4 8 10) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4390]
    (.letOp (n := 4394) (.out 0x1233df (xorR32R32Effect 0x1233df 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[4392, 4368]
    (.letOp (n := 4395) (.exec 0x1233df (fun s => s.RIP = 0x1233df) (xorR32R32Effect 0x1233df 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[4392, 4368]
    (.letOp (n := 4396) (.out 0x1233e2 (movR32M32LowEffect 0x1233e2 5 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 4397) (.exec 0x1233e2 (LoadPre 0x1233e2 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1233e2 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1233e2 5 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 4398) (.out 0x1233e5 (addR32R32Effect 0x1233e5 3 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[4396, 4394]
    (.letOp (n := 4399) (.exec 0x1233e5 (fun s => s.RIP = 0x1233e5) (addR32R32Effect 0x1233e5 3 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[4396, 4394]
    (.letOp (n := 4400) (.out 0x1233e8 (movR32R32Effect 0x1233e8 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[4356]
    (.letOp (n := 4401) (.exec 0x1233e8 (fun s => s.RIP = 0x1233e8) (movR32R32Effect 0x1233e8 2 1 0) (Reg.operands [.gpr 0] [])) #v[4356]
    (.letOp (n := 4402) (.out 0x1233ea (rolR32Effect 0x1233ea 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4400]
    (.letOp (n := 4403) (.exec 0x1233ea (fun s => s.RIP = 0x1233ea) (rolR32Effect 0x1233ea 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4400]
    (.letOp (n := 4404) (.out 0x1233ed (movR32R32Effect 0x1233ed 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[4356]
    (.letOp (n := 4405) (.exec 0x1233ed (fun s => s.RIP = 0x1233ed) (movR32R32Effect 0x1233ed 3 8 0) (Reg.operands [.gpr 0] [])) #v[4356]
    (.letOp (n := 4406) (.out 0x1233f0 (rolR32Effect 0x1233f0 4 8 21) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4404]
    (.letOp (n := 4407) (.exec 0x1233f0 (fun s => s.RIP = 0x1233f0) (rolR32Effect 0x1233f0 4 8 21) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4404]
    (.letOp (n := 4408) (.out 0x1233f4 (xorR32R32Effect 0x1233f4 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[4406, 4402]
    (.letOp (n := 4409) (.exec 0x1233f4 (fun s => s.RIP = 0x1233f4) (xorR32R32Effect 0x1233f4 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[4406, 4402]
    (.letOp (n := 4410) (.out 0x1233f7 (movR32R32Effect 0x1233f7 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[4356]
    (.letOp (n := 4411) (.exec 0x1233f7 (fun s => s.RIP = 0x1233f7) (movR32R32Effect 0x1233f7 2 1 0) (Reg.operands [.gpr 0] [])) #v[4356]
    (.letOp (n := 4412) (.out 0x1233f9 (rolR32Effect 0x1233f9 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4410]
    (.letOp (n := 4413) (.exec 0x1233f9 (fun s => s.RIP = 0x1233f9) (rolR32Effect 0x1233f9 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4410]
    (.letOp (n := 4414) (.out 0x1233fc (xorR32R32Effect 0x1233fc 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[4412, 4408]
    (.letOp (n := 4415) (.exec 0x1233fc (fun s => s.RIP = 0x1233fc) (xorR32R32Effect 0x1233fc 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[4412, 4408]
    (.letOp (n := 4416) (.out 0x1233ff (movR32R32Effect 0x1233ff 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[4246]
    (.letOp (n := 4417) (.exec 0x1233ff (fun s => s.RIP = 0x1233ff) (movR32R32Effect 0x1233ff 3 8 7) (Reg.operands [.gpr 7] [])) #v[4246]
    (.letOp (n := 4418) (.out 0x123402 (xorR32R32Effect 0x123402 3 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[4416, 4145]
    (.letOp (n := 4419) (.exec 0x123402 (fun s => s.RIP = 0x123402) (xorR32R32Effect 0x123402 3 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[4416, 4145]
    (.letOp (n := 4420) (.out 0x123405 (andR32R32Effect 0x123405 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[4418, 4356]
    (.letOp (n := 4421) (.exec 0x123405 (fun s => s.RIP = 0x123405) (andR32R32Effect 0x123405 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[4418, 4356]
    (.letOp (n := 4422) (.out 0x123408 (xorR32R32Effect 0x123408 3 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[4420, 4145]
    (.letOp (n := 4423) (.exec 0x123408 (fun s => s.RIP = 0x123408) (xorR32R32Effect 0x123408 3 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[4420, 4145]
    (.letOp (n := 4424) (.out 0x12340b (addR32R32Effect 0x12340b 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[4035, 4398]
    (.letOp (n := 4425) (.exec 0x12340b (fun s => s.RIP = 0x12340b) (addR32R32Effect 0x12340b 3 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[4035, 4398]
    (.letOp (n := 4426) (.out 0x12340e (movR32R32Effect 0x12340e 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[4362]
    (.letOp (n := 4427) (.exec 0x12340e (fun s => s.RIP = 0x12340e) (movR32R32Effect 0x12340e 3 9 3) (Reg.operands [.gpr 3] [])) #v[4362]
    (b_l121930_112)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_111 : List UInt8 :=
  [0x44, 0x89, 0x44, 0x24, 0x70, 0x41, 0x89, 0xE8, 0x41, 0xC1, 0xE8, 0x0A, 0x41, 0x31, 0xC8, 0x8B,
    0x2C, 0x24, 0x44, 0x01, 0xC5, 0x89, 0xC1, 0xC1, 0xC1, 0x1A, 0x41, 0x89, 0xC0, 0x41, 0xC1, 0xC0,
    0x15, 0x41, 0x31, 0xC8, 0x89, 0xC1, 0xC1, 0xC1, 0x07, 0x44, 0x31, 0xC1, 0x41, 0x89, 0xF8, 0x45,
    0x31, 0xF0, 0x41, 0x21, 0xC0, 0x45, 0x31, 0xF0, 0x41, 0x01, 0xEA, 0x41, 0x89, 0xD9] ++ bytes_l121930_112

theorem code_l121930_111 : ∀ x ∈ codeRange 0x1233d3 bytes_l121930_111, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x233d3 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_112

def b_l121930_110 : Block Op Label signature Reg.count 4350 :=
  .letOp (n := 4350) (.out 0x123395 (andR32R32Effect 0x123395 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[4348, 4248]
    (.letOp (n := 4351) (.exec 0x123395 (fun s => s.RIP = 0x123395) (andR32R32Effect 0x123395 3 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[4348, 4248]
    (.letOp (n := 4352) (.out 0x123398 (xorR32R32Effect 0x123398 3 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[4350, 4344]
    (.letOp (n := 4353) (.exec 0x123398 (fun s => s.RIP = 0x123398) (xorR32R32Effect 0x123398 3 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[4350, 4344]
    (.letOp (n := 4354) (.out 0x12339b (addR32R32Effect 0x12339b 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[4352, 4340]
    (.letOp (n := 4355) (.exec 0x12339b (fun s => s.RIP = 0x12339b) (addR32R32Effect 0x12339b 3 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[4352, 4340]
    (.letOp (n := 4356) (.out 0x12339e (addR32R32Effect 0x12339e 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[3931, 4328]
    (.letOp (n := 4357) (.exec 0x12339e (fun s => s.RIP = 0x12339e) (addR32R32Effect 0x12339e 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[3931, 4328]
    (.letOp (n := 4358) (.out 0x1233a0 (movR32R32Effect 0x1233a0 3 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[4262]
    (.letOp (n := 4359) (.exec 0x1233a0 (fun s => s.RIP = 0x1233a0) (movR32R32Effect 0x1233a0 3 8 5) (Reg.operands [.gpr 5] [])) #v[4262]
    (.letOp (n := 4360) (.out 0x1233a3 (rolR32Effect 0x1233a3 4 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4358]
    (.letOp (n := 4361) (.exec 0x1233a3 (fun s => s.RIP = 0x1233a3) (rolR32Effect 0x1233a3 4 8 15) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4358]
    (.letOp (n := 4362) (.out 0x1233a7 (addR32R32Effect 0x1233a7 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[4354, 4328]
    (.letOp (n := 4363) (.exec 0x1233a7 (fun s => s.RIP = 0x1233a7) (addR32R32Effect 0x1233a7 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[4354, 4328]
    (.letOp (n := 4364) (.out 0x1233a9 (movR32R32Effect 0x1233a9 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[4262]
    (.letOp (n := 4365) (.exec 0x1233a9 (fun s => s.RIP = 0x1233a9) (movR32R32Effect 0x1233a9 2 1 5) (Reg.operands [.gpr 5] [])) #v[4262]
    (.letOp (n := 4366) (.out 0x1233ab (rolR32Effect 0x1233ab 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[4364]
    (.letOp (n := 4367) (.exec 0x1233ab (fun s => s.RIP = 0x1233ab) (rolR32Effect 0x1233ab 3 1 13) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4364]
    (.letOp (n := 4368) (.out 0x1233ae (xorR32R32Effect 0x1233ae 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[4366, 4360]
    (.letOp (n := 4369) (.exec 0x1233ae (fun s => s.RIP = 0x1233ae) (xorR32R32Effect 0x1233ae 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[4366, 4360]
    (.letOp (n := 4370) (.out 0x1233b1 (movR32R32Effect 0x1233b1 3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[4292]
    (.letOp (n := 4371) (.exec 0x1233b1 (fun s => s.RIP = 0x1233b1) (movR32R32Effect 0x1233b1 3 8 12) (Reg.operands [.gpr 12] [])) #v[4292]
    (.letOp (n := 4372) (.out 0x1233b4 (rolR32Effect 0x1233b4 4 8 25) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4370]
    (.letOp (n := 4373) (.exec 0x1233b4 (fun s => s.RIP = 0x1233b4) (rolR32Effect 0x1233b4 4 8 25) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4370]
    (.letOp (n := 4374) (.out 0x1233b8 (movR32R32Effect 0x1233b8 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 12] []) (.reg (.gpr 9))) #v[4292]
    (.letOp (n := 4375) (.exec 0x1233b8 (fun s => s.RIP = 0x1233b8) (movR32R32Effect 0x1233b8 3 9 12) (Reg.operands [.gpr 12] [])) #v[4292]
    (.letOp (n := 4376) (.out 0x1233bb (rolR32Effect 0x1233bb 4 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4374]
    (.letOp (n := 4377) (.exec 0x1233bb (fun s => s.RIP = 0x1233bb) (rolR32Effect 0x1233bb 4 9 14) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4374]
    (.letOp (n := 4378) (.out 0x1233bf (xorR32R32Effect 0x1233bf 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[4376, 4372]
    (.letOp (n := 4379) (.exec 0x1233bf (fun s => s.RIP = 0x1233bf) (xorR32R32Effect 0x1233bf 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[4376, 4372]
    (.letOp (n := 4380) (.out 0x1233c2 (movR32R32Effect 0x1233c2 3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[4292]
    (.letOp (n := 4381) (.exec 0x1233c2 (fun s => s.RIP = 0x1233c2) (movR32R32Effect 0x1233c2 3 8 12) (Reg.operands [.gpr 12] [])) #v[4292]
    (.letOp (n := 4382) (.out 0x1233c5 (shrR32Effect 0x1233c5 4 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4380]
    (.letOp (n := 4383) (.exec 0x1233c5 (fun s => s.RIP = 0x1233c5) (shrR32Effect 0x1233c5 4 8 3) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4380]
    (.letOp (n := 4384) (.out 0x1233c9 (xorR32R32Effect 0x1233c9 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[4382, 4378]
    (.letOp (n := 4385) (.exec 0x1233c9 (fun s => s.RIP = 0x1233c9) (xorR32R32Effect 0x1233c9 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[4382, 4378]
    (.letOp (n := 4386) (.exec 0x1233cc (StorePre 0x1233cc 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1233cc + BitVec.ofNat 64 4)) 4) (addMREffect 0x1233cc 4 32 5 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[4262, 4]
    (.letOp (n := 4387) (.out 0x1233d0 (addR32R32Effect 0x1233d0 3 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[4384, 4262]
    (.letOp (n := 4388) (.exec 0x1233d0 (fun s => s.RIP = 0x1233d0) (addR32R32Effect 0x1233d0 3 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[4384, 4262]
    (b_l121930_111)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_110 : List UInt8 :=
  [0x44, 0x21, 0xDB, 0x44, 0x31, 0xC3, 0x44, 0x01, 0xCB, 0x01, 0xC8, 0x41, 0x89, 0xE8, 0x41, 0xC1,
    0xC0, 0x0F, 0x01, 0xCB, 0x89, 0xE9, 0xC1, 0xC1, 0x0D, 0x44, 0x31, 0xC1, 0x45, 0x89, 0xE0, 0x41,
    0xC1, 0xC0, 0x19, 0x45, 0x89, 0xE1, 0x41, 0xC1, 0xC1, 0x0E, 0x45, 0x31, 0xC1, 0x45, 0x89, 0xE0,
    0x41, 0xC1, 0xE8, 0x03, 0x45, 0x31, 0xC8, 0x01, 0x6C, 0x24, 0x04, 0x41, 0x01, 0xE8] ++ bytes_l121930_111

theorem code_l121930_110 : ∀ x ∈ codeRange 0x123395 bytes_l121930_110, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23395 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_111

def b_l121930_109 : Block Op Label signature Reg.count 4310 :=
  .letOp (n := 4310) (.out 0x123355 (movR32R32Effect 0x123355 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[4145]
    (.letOp (n := 4311) (.exec 0x123355 (fun s => s.RIP = 0x123355) (movR32R32Effect 0x123355 3 9 14) (Reg.operands [.gpr 14] [])) #v[4145]
    (.letOp (n := 4312) (.out 0x123358 (xorR32R32Effect 0x123358 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[4310, 4035]
    (.letOp (n := 4313) (.exec 0x123358 (fun s => s.RIP = 0x123358) (xorR32R32Effect 0x123358 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[4310, 4035]
    (.letOp (n := 4314) (.out 0x12335b (andR32R32Effect 0x12335b 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[4312, 4246]
    (.letOp (n := 4315) (.exec 0x12335b (fun s => s.RIP = 0x12335b) (andR32R32Effect 0x12335b 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[4312, 4246]
    (.letOp (n := 4316) (.out 0x12335e (xorR32R32Effect 0x12335e 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[4314, 4035]
    (.letOp (n := 4317) (.exec 0x12335e (fun s => s.RIP = 0x12335e) (xorR32R32Effect 0x12335e 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[4314, 4035]
    (.letOp (n := 4318) (.out 0x123361 (addR32R32Effect 0x123361 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[3925, 4292]
    (.letOp (n := 4319) (.exec 0x123361 (fun s => s.RIP = 0x123361) (addR32R32Effect 0x123361 3 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[3925, 4292]
    (.letOp (n := 4320) (.out 0x123364 (addR32R32Effect 0x123364 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[4318, 4316]
    (.letOp (n := 4321) (.exec 0x123364 (fun s => s.RIP = 0x123364) (addR32R32Effect 0x123364 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[4318, 4316]
    (.letOp (n := 4322) (.out 0x123367 (movR32R32Effect 0x123367 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 11] []) (.reg (.gpr 9))) #v[4248]
    (.letOp (n := 4323) (.exec 0x123367 (fun s => s.RIP = 0x123367) (movR32R32Effect 0x123367 3 9 11) (Reg.operands [.gpr 11] [])) #v[4248]
    (.letOp (n := 4324) (.out 0x12336a (rolR32Effect 0x12336a 4 9 30) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4322]
    (.letOp (n := 4325) (.exec 0x12336a (fun s => s.RIP = 0x12336a) (rolR32Effect 0x12336a 4 9 30) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4322]
    (.letOp (n := 4326) (.out 0x12336e (addR32R32Effect 0x12336e 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[4320, 4308]
    (.letOp (n := 4327) (.exec 0x12336e (fun s => s.RIP = 0x12336e) (addR32R32Effect 0x12336e 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[4320, 4308]
    (.letOp (n := 4328) (.out 0x123371 (addR32Imm32Effect 0x123371 6 1 0xa2bfe8a1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[4326]
    (.letOp (n := 4329) (.exec 0x123371 (fun s => s.RIP = 0x123371) (addR32Imm32Effect 0x123371 6 1 0xa2bfe8a1) (Reg.operands [.gpr 1] [])) #v[4326]
    (.letOp (n := 4330) (.out 0x123377 (movR32R32Effect 0x123377 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[4248]
    (.letOp (n := 4331) (.exec 0x123377 (fun s => s.RIP = 0x123377) (movR32R32Effect 0x123377 3 8 11) (Reg.operands [.gpr 11] [])) #v[4248]
    (.letOp (n := 4332) (.out 0x12337a (rolR32Effect 0x12337a 4 8 19) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4330]
    (.letOp (n := 4333) (.exec 0x12337a (fun s => s.RIP = 0x12337a) (rolR32Effect 0x12337a 4 8 19) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4330]
    (.letOp (n := 4334) (.out 0x12337e (xorR32R32Effect 0x12337e 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[4332, 4324]
    (.letOp (n := 4335) (.exec 0x12337e (fun s => s.RIP = 0x12337e) (xorR32R32Effect 0x12337e 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[4332, 4324]
    (.letOp (n := 4336) (.out 0x123381 (movR32R32Effect 0x123381 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 11] []) (.reg (.gpr 9))) #v[4248]
    (.letOp (n := 4337) (.exec 0x123381 (fun s => s.RIP = 0x123381) (movR32R32Effect 0x123381 3 9 11) (Reg.operands [.gpr 11] [])) #v[4248]
    (.letOp (n := 4338) (.out 0x123384 (rolR32Effect 0x123384 4 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4336]
    (.letOp (n := 4339) (.exec 0x123384 (fun s => s.RIP = 0x123384) (rolR32Effect 0x123384 4 9 10) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4336]
    (.letOp (n := 4340) (.out 0x123388 (xorR32R32Effect 0x123388 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[4338, 4334]
    (.letOp (n := 4341) (.exec 0x123388 (fun s => s.RIP = 0x123388) (xorR32R32Effect 0x123388 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[4338, 4334]
    (.letOp (n := 4342) (.out 0x12338b (movR32R32Effect 0x12338b 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[4151]
    (.letOp (n := 4343) (.exec 0x12338b (fun s => s.RIP = 0x12338b) (movR32R32Effect 0x12338b 3 8 2) (Reg.operands [.gpr 2] [])) #v[4151]
    (.letOp (n := 4344) (.out 0x12338e (andR32R32Effect 0x12338e 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[4342, 4041]
    (.letOp (n := 4345) (.exec 0x12338e (fun s => s.RIP = 0x12338e) (andR32R32Effect 0x12338e 3 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[4342, 4041]
    (.letOp (n := 4346) (.out 0x123391 (movR32R32Effect 0x123391 2 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[4151]
    (.letOp (n := 4347) (.exec 0x123391 (fun s => s.RIP = 0x123391) (movR32R32Effect 0x123391 2 3 2) (Reg.operands [.gpr 2] [])) #v[4151]
    (.letOp (n := 4348) (.out 0x123393 (xorR32R32Effect 0x123393 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[4346, 4041]
    (.letOp (n := 4349) (.exec 0x123393 (fun s => s.RIP = 0x123393) (xorR32R32Effect 0x123393 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[4346, 4041]
    (b_l121930_110))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_109 : List UInt8 :=
  [0x45, 0x89, 0xF1, 0x45, 0x31, 0xD1, 0x41, 0x21, 0xF9, 0x45, 0x31, 0xD1, 0x44, 0x01, 0xE1, 0x44,
    0x01, 0xC9, 0x45, 0x89, 0xD9, 0x41, 0xC1, 0xC1, 0x1E, 0x44, 0x01, 0xC1, 0x81, 0xC1, 0xA1, 0xE8,
    0xBF, 0xA2, 0x45, 0x89, 0xD8, 0x41, 0xC1, 0xC0, 0x13, 0x45, 0x31, 0xC8, 0x45, 0x89, 0xD9, 0x41,
    0xC1, 0xC1, 0x0A, 0x45, 0x31, 0xC1, 0x41, 0x89, 0xD0, 0x41, 0x21, 0xF0, 0x89, 0xD3, 0x31, 0xF3] ++ bytes_l121930_110

theorem code_l121930_109 : ∀ x ∈ codeRange 0x123355 bytes_l121930_109, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23355 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_110

def b_l121930_108 : Block Op Label signature Reg.count 4272 :=
  .letOp (n := 4272) (.out 0x12330e (xorR32R32Effect 0x12330e 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[4270, 4266]
    (.letOp (n := 4273) (.exec 0x12330e (fun s => s.RIP = 0x12330e) (xorR32R32Effect 0x12330e 3 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[4270, 4266]
    (.letOp (n := 4274) (.out 0x123311 (movR32R32Effect 0x123311 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 12] []) (.reg (.gpr 9))) #v[4190]
    (.letOp (n := 4275) (.exec 0x123311 (fun s => s.RIP = 0x123311) (movR32R32Effect 0x123311 3 9 12) (Reg.operands [.gpr 12] [])) #v[4190]
    (.letOp (n := 4276) (.out 0x123314 (shrR32Effect 0x123314 4 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4274]
    (.letOp (n := 4277) (.exec 0x123314 (fun s => s.RIP = 0x123314) (shrR32Effect 0x123314 4 9 3) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4274]
    (.letOp (n := 4278) (.out 0x123318 (xorR32R32Effect 0x123318 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[4276, 4272]
    (.letOp (n := 4279) (.exec 0x123318 (fun s => s.RIP = 0x123318) (xorR32R32Effect 0x123318 3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[4276, 4272]
    (.letOp (n := 4280) (.exec 0x12331b (StorePre 0x12331b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x12331b + BitVec.ofNat 64 5)) 4) (addMREffect 0x12331b 5 32 15 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[4256, 4]
    (.letOp (n := 4281) (.out 0x123320 (addR32R32Effect 0x123320 3 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[4278, 4256]
    (.letOp (n := 4282) (.exec 0x123320 (fun s => s.RIP = 0x123320) (addR32R32Effect 0x123320 3 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[4278, 4256]
    (.letOp (n := 4283) (.exec 0x123323 (StorePre 0x123323 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x123323 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x123323 9 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[4281, 4]
    (.letOp (n := 4284) (.out 0x123328 (movR32R32Effect 0x123328 3 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 15] []) (.reg (.gpr 9))) #v[4256]
    (.letOp (n := 4285) (.exec 0x123328 (fun s => s.RIP = 0x123328) (movR32R32Effect 0x123328 3 9 15) (Reg.operands [.gpr 15] [])) #v[4256]
    (.letOp (n := 4286) (.out 0x12332b (shrR32Effect 0x12332b 4 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4284]
    (.letOp (n := 4287) (.exec 0x12332b (fun s => s.RIP = 0x12332b) (shrR32Effect 0x12332b 4 9 10) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4284]
    (.letOp (n := 4288) (.out 0x12332f (xorR32R32Effect 0x12332f 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[4286, 4260]
    (.letOp (n := 4289) (.exec 0x12332f (fun s => s.RIP = 0x12332f) (xorR32R32Effect 0x12332f 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[4286, 4260]
    (.letOp (n := 4290) (.out 0x123332 (movR32M32Effect 0x123332 12 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 4291) (.exec 0x123332 (LoadPre 0x123332 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x123332 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x123332 12 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 4292) (.out 0x123337 (addR32R32Effect 0x123337 3 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 9] []) (.reg (.gpr 12))) #v[4290, 4288]
    (.letOp (n := 4293) (.exec 0x123337 (fun s => s.RIP = 0x123337) (addR32R32Effect 0x123337 3 12 9) (Reg.operands [.gpr 12, .gpr 9] [])) #v[4290, 4288]
    (.letOp (n := 4294) (.out 0x12333a (movR32R32Effect 0x12333a 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[4246]
    (.letOp (n := 4295) (.exec 0x12333a (fun s => s.RIP = 0x12333a) (movR32R32Effect 0x12333a 3 8 7) (Reg.operands [.gpr 7] [])) #v[4246]
    (.letOp (n := 4296) (.out 0x12333d (rolR32Effect 0x12333d 4 8 26) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4294]
    (.letOp (n := 4297) (.exec 0x12333d (fun s => s.RIP = 0x12333d) (rolR32Effect 0x12333d 4 8 26) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4294]
    (.letOp (n := 4298) (.out 0x123341 (movR32R32Effect 0x123341 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[4246]
    (.letOp (n := 4299) (.exec 0x123341 (fun s => s.RIP = 0x123341) (movR32R32Effect 0x123341 3 9 7) (Reg.operands [.gpr 7] [])) #v[4246]
    (.letOp (n := 4300) (.out 0x123344 (rolR32Effect 0x123344 4 9 21) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4298]
    (.letOp (n := 4301) (.exec 0x123344 (fun s => s.RIP = 0x123344) (rolR32Effect 0x123344 4 9 21) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4298]
    (.letOp (n := 4302) (.out 0x123348 (xorR32R32Effect 0x123348 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[4300, 4296]
    (.letOp (n := 4303) (.exec 0x123348 (fun s => s.RIP = 0x123348) (xorR32R32Effect 0x123348 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[4300, 4296]
    (.letOp (n := 4304) (.out 0x12334b (movR32R32Effect 0x12334b 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[4246]
    (.letOp (n := 4305) (.exec 0x12334b (fun s => s.RIP = 0x12334b) (movR32R32Effect 0x12334b 3 8 7) (Reg.operands [.gpr 7] [])) #v[4246]
    (.letOp (n := 4306) (.out 0x12334e (rolR32Effect 0x12334e 4 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4304]
    (.letOp (n := 4307) (.exec 0x12334e (fun s => s.RIP = 0x12334e) (rolR32Effect 0x12334e 4 8 7) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4304]
    (.letOp (n := 4308) (.out 0x123352 (xorR32R32Effect 0x123352 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[4306, 4302]
    (.letOp (n := 4309) (.exec 0x123352 (fun s => s.RIP = 0x123352) (xorR32R32Effect 0x123352 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[4306, 4302]
    (b_l121930_109))))))))))))))))))))))))))))))))))))))

def bytes_l121930_108 : List UInt8 :=
  [0x44, 0x31, 0xCB, 0x45, 0x89, 0xE1, 0x41, 0xC1, 0xE9, 0x03, 0x41, 0x31, 0xD9, 0x44, 0x01, 0x7C,
    0x24, 0x24, 0x45, 0x01, 0xF9, 0x44, 0x89, 0x4C, 0x24, 0x48, 0x45, 0x89, 0xF9, 0x41, 0xC1, 0xE9,
    0x0A, 0x45, 0x31, 0xC1, 0x44, 0x8B, 0x64, 0x24, 0x70, 0x45, 0x01, 0xCC, 0x41, 0x89, 0xF8, 0x41,
    0xC1, 0xC0, 0x1A, 0x41, 0x89, 0xF9, 0x41, 0xC1, 0xC1, 0x15, 0x45, 0x31, 0xC1, 0x41, 0x89, 0xF8,
    0x41, 0xC1, 0xC0, 0x07, 0x45, 0x31, 0xC8] ++ bytes_l121930_109

theorem code_l121930_108 : ∀ x ∈ codeRange 0x12330e bytes_l121930_108, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2330e 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_109

def b_l121930_107 : Block Op Label signature Reg.count 4232 :=
  .letOp (n := 4232) (.out 0x1232d1 (movR32R32Effect 0x1232d1 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[4041]
    (.letOp (n := 4233) (.exec 0x1232d1 (fun s => s.RIP = 0x1232d1) (movR32R32Effect 0x1232d1 2 3 6) (Reg.operands [.gpr 6] [])) #v[4041]
    (.letOp (n := 4234) (.out 0x1232d3 (andR32R32Effect 0x1232d3 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[4232, 3931]
    (.letOp (n := 4235) (.exec 0x1232d3 (fun s => s.RIP = 0x1232d3) (andR32R32Effect 0x1232d3 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[4232, 3931]
    (.letOp (n := 4236) (.out 0x1232d5 (movR32R32Effect 0x1232d5 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[4041]
    (.letOp (n := 4237) (.exec 0x1232d5 (fun s => s.RIP = 0x1232d5) (movR32R32Effect 0x1232d5 3 11 6) (Reg.operands [.gpr 6] [])) #v[4041]
    (.letOp (n := 4238) (.out 0x1232d8 (xorR32R32Effect 0x1232d8 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[4236, 3931]
    (.letOp (n := 4239) (.exec 0x1232d8 (fun s => s.RIP = 0x1232d8) (xorR32R32Effect 0x1232d8 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[4236, 3931]
    (.letOp (n := 4240) (.out 0x1232db (andR32R32Effect 0x1232db 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[4238, 4151]
    (.letOp (n := 4241) (.exec 0x1232db (fun s => s.RIP = 0x1232db) (andR32R32Effect 0x1232db 3 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[4238, 4151]
    (.letOp (n := 4242) (.out 0x1232de (xorR32R32Effect 0x1232de 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[4240, 4234]
    (.letOp (n := 4243) (.exec 0x1232de (fun s => s.RIP = 0x1232de) (xorR32R32Effect 0x1232de 3 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[4240, 4234]
    (.letOp (n := 4244) (.out 0x1232e1 (addR32R32Effect 0x1232e1 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[4242, 4230]
    (.letOp (n := 4245) (.exec 0x1232e1 (fun s => s.RIP = 0x1232e1) (addR32R32Effect 0x1232e1 3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[4242, 4230]
    (.letOp (n := 4246) (.out 0x1232e4 (addR32R32Effect 0x1232e4 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[3821, 4214]
    (.letOp (n := 4247) (.exec 0x1232e4 (fun s => s.RIP = 0x1232e4) (addR32R32Effect 0x1232e4 3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[3821, 4214]
    (.letOp (n := 4248) (.out 0x1232e7 (addR32R32Effect 0x1232e7 3 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[4244, 4214]
    (.letOp (n := 4249) (.exec 0x1232e7 (fun s => s.RIP = 0x1232e7) (addR32R32Effect 0x1232e7 3 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[4244, 4214]
    (.letOp (n := 4250) (.out 0x1232ea (movR32R32Effect 0x1232ea 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[4077]
    (.letOp (n := 4251) (.exec 0x1232ea (fun s => s.RIP = 0x1232ea) (movR32R32Effect 0x1232ea 3 9 5) (Reg.operands [.gpr 5] [])) #v[4077]
    (.letOp (n := 4252) (.out 0x1232ed (rolR32Effect 0x1232ed 4 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4250]
    (.letOp (n := 4253) (.exec 0x1232ed (fun s => s.RIP = 0x1232ed) (rolR32Effect 0x1232ed 4 9 15) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4250]
    (.letOp (n := 4254) (.out 0x1232f1 (movR32R32Effect 0x1232f1 3 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[4077]
    (.letOp (n := 4255) (.exec 0x1232f1 (fun s => s.RIP = 0x1232f1) (movR32R32Effect 0x1232f1 3 8 5) (Reg.operands [.gpr 5] [])) #v[4077]
    (.letOp (n := 4256) (.out 0x1232f4 (movR32R32Effect 0x1232f4 3 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 5] []) (.reg (.gpr 15))) #v[4077]
    (.letOp (n := 4257) (.exec 0x1232f4 (fun s => s.RIP = 0x1232f4) (movR32R32Effect 0x1232f4 3 15 5) (Reg.operands [.gpr 5] [])) #v[4077]
    (.letOp (n := 4258) (.out 0x1232f7 (rolR32Effect 0x1232f7 4 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[4254]
    (.letOp (n := 4259) (.exec 0x1232f7 (fun s => s.RIP = 0x1232f7) (rolR32Effect 0x1232f7 4 8 13) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4254]
    (.letOp (n := 4260) (.out 0x1232fb (xorR32R32Effect 0x1232fb 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[4258, 4252]
    (.letOp (n := 4261) (.exec 0x1232fb (fun s => s.RIP = 0x1232fb) (xorR32R32Effect 0x1232fb 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[4258, 4252]
    (.letOp (n := 4262) (.out 0x1232fe (movR32R32Effect 0x1232fe 3 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 12] []) (.reg (.gpr 5))) #v[4190]
    (.letOp (n := 4263) (.exec 0x1232fe (fun s => s.RIP = 0x1232fe) (movR32R32Effect 0x1232fe 3 5 12) (Reg.operands [.gpr 12] [])) #v[4190]
    (.letOp (n := 4264) (.out 0x123301 (movR32R32Effect 0x123301 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 12] []) (.reg (.gpr 9))) #v[4190]
    (.letOp (n := 4265) (.exec 0x123301 (fun s => s.RIP = 0x123301) (movR32R32Effect 0x123301 3 9 12) (Reg.operands [.gpr 12] [])) #v[4190]
    (.letOp (n := 4266) (.out 0x123304 (rolR32Effect 0x123304 4 9 25) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4264]
    (.letOp (n := 4267) (.exec 0x123304 (fun s => s.RIP = 0x123304) (rolR32Effect 0x123304 4 9 25) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4264]
    (.letOp (n := 4268) (.out 0x123308 (movR32R32Effect 0x123308 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[4190]
    (.letOp (n := 4269) (.exec 0x123308 (fun s => s.RIP = 0x123308) (movR32R32Effect 0x123308 3 3 12) (Reg.operands [.gpr 12] [])) #v[4190]
    (.letOp (n := 4270) (.out 0x12330b (rolR32Effect 0x12330b 3 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[4268]
    (.letOp (n := 4271) (.exec 0x12330b (fun s => s.RIP = 0x12330b) (rolR32Effect 0x12330b 3 3 14) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4268]
    (b_l121930_108))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_107 : List UInt8 :=
  [0x89, 0xF3, 0x21, 0xC3, 0x41, 0x89, 0xF3, 0x41, 0x31, 0xC3, 0x41, 0x21, 0xD3, 0x41, 0x31, 0xDB,
    0x45, 0x01, 0xCB, 0x44, 0x01, 0xC7, 0x45, 0x01, 0xC3, 0x41, 0x89, 0xE9, 0x41, 0xC1, 0xC1, 0x0F,
    0x41, 0x89, 0xE8, 0x41, 0x89, 0xEF, 0x41, 0xC1, 0xC0, 0x0D, 0x45, 0x31, 0xC8, 0x44, 0x89, 0xE5,
    0x45, 0x89, 0xE1, 0x41, 0xC1, 0xC1, 0x19, 0x44, 0x89, 0xE3, 0xC1, 0xC3, 0x0E] ++ bytes_l121930_108

theorem code_l121930_107 : ∀ x ∈ codeRange 0x1232d1 bytes_l121930_107, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x232d1 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_108

def b_l121930_106 : Block Op Label signature Reg.count 4192 :=
  .letOp (n := 4192) (.out 0x12328d (movR32R32Effect 0x12328d 3 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 14] []) (.reg (.gpr 11))) #v[4145]
    (.letOp (n := 4193) (.exec 0x12328d (fun s => s.RIP = 0x12328d) (movR32R32Effect 0x12328d 3 11 14) (Reg.operands [.gpr 14] [])) #v[4145]
    (.letOp (n := 4194) (.out 0x123290 (rolR32Effect 0x123290 4 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[4192]
    (.letOp (n := 4195) (.exec 0x123290 (fun s => s.RIP = 0x123290) (rolR32Effect 0x123290 4 11 7) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4192]
    (.letOp (n := 4196) (.out 0x123294 (xorR32R32Effect 0x123294 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[4186, 4180]
    (.letOp (n := 4197) (.exec 0x123294 (fun s => s.RIP = 0x123294) (xorR32R32Effect 0x123294 3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[4186, 4180]
    (.letOp (n := 4198) (.out 0x123297 (xorR32R32Effect 0x123297 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[4194, 4196]
    (.letOp (n := 4199) (.exec 0x123297 (fun s => s.RIP = 0x123297) (xorR32R32Effect 0x123297 3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[4194, 4196]
    (.letOp (n := 4200) (.out 0x12329a (movR32R32Effect 0x12329a 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[4035]
    (.letOp (n := 4201) (.exec 0x12329a (fun s => s.RIP = 0x12329a) (movR32R32Effect 0x12329a 3 9 10) (Reg.operands [.gpr 10] [])) #v[4035]
    (.letOp (n := 4202) (.out 0x12329d (xorR32R32Effect 0x12329d 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[4200, 3925]
    (.letOp (n := 4203) (.exec 0x12329d (fun s => s.RIP = 0x12329d) (xorR32R32Effect 0x12329d 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[4200, 3925]
    (.letOp (n := 4204) (.out 0x1232a0 (andR32R32Effect 0x1232a0 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[4202, 4145]
    (.letOp (n := 4205) (.exec 0x1232a0 (fun s => s.RIP = 0x1232a0) (andR32R32Effect 0x1232a0 3 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[4202, 4145]
    (.letOp (n := 4206) (.out 0x1232a3 (xorR32R32Effect 0x1232a3 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[4204, 3925]
    (.letOp (n := 4207) (.exec 0x1232a3 (fun s => s.RIP = 0x1232a3) (xorR32R32Effect 0x1232a3 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[4204, 3925]
    (.letOp (n := 4208) (.out 0x1232a6 (addR32R32Effect 0x1232a6 3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[3819, 4190]
    (.letOp (n := 4209) (.exec 0x1232a6 (fun s => s.RIP = 0x1232a6) (addR32R32Effect 0x1232a6 3 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[3819, 4190]
    (.letOp (n := 4210) (.out 0x1232a9 (addR32R32Effect 0x1232a9 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[4208, 4206]
    (.letOp (n := 4211) (.exec 0x1232a9 (fun s => s.RIP = 0x1232a9) (addR32R32Effect 0x1232a9 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[4208, 4206]
    (.letOp (n := 4212) (.out 0x1232ac (addR32R32Effect 0x1232ac 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[4210, 4198]
    (.letOp (n := 4213) (.exec 0x1232ac (fun s => s.RIP = 0x1232ac) (addR32R32Effect 0x1232ac 3 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[4210, 4198]
    (.letOp (n := 4214) (.out 0x1232af (addR32Imm32Effect 0x1232af 7 8 0x92722c85) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[4212]
    (.letOp (n := 4215) (.exec 0x1232af (fun s => s.RIP = 0x1232af) (addR32Imm32Effect 0x1232af 7 8 0x92722c85) (Reg.operands [.gpr 8] [])) #v[4212]
    (.letOp (n := 4216) (.out 0x1232b6 (movR32R32Effect 0x1232b6 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[4151]
    (.letOp (n := 4217) (.exec 0x1232b6 (fun s => s.RIP = 0x1232b6) (movR32R32Effect 0x1232b6 3 9 2) (Reg.operands [.gpr 2] [])) #v[4151]
    (.letOp (n := 4218) (.out 0x1232b9 (rolR32Effect 0x1232b9 4 9 30) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4216]
    (.letOp (n := 4219) (.exec 0x1232b9 (fun s => s.RIP = 0x1232b9) (rolR32Effect 0x1232b9 4 9 30) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4216]
    (.letOp (n := 4220) (.out 0x1232bd (movR32R32Effect 0x1232bd 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[4151]
    (.letOp (n := 4221) (.exec 0x1232bd (fun s => s.RIP = 0x1232bd) (movR32R32Effect 0x1232bd 3 11 2) (Reg.operands [.gpr 2] [])) #v[4151]
    (.letOp (n := 4222) (.out 0x1232c0 (rolR32Effect 0x1232c0 4 11 19) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[4220]
    (.letOp (n := 4223) (.exec 0x1232c0 (fun s => s.RIP = 0x1232c0) (rolR32Effect 0x1232c0 4 11 19) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4220]
    (.letOp (n := 4224) (.out 0x1232c4 (xorR32R32Effect 0x1232c4 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[4222, 4218]
    (.letOp (n := 4225) (.exec 0x1232c4 (fun s => s.RIP = 0x1232c4) (xorR32R32Effect 0x1232c4 3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[4222, 4218]
    (.letOp (n := 4226) (.out 0x1232c7 (movR32R32Effect 0x1232c7 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[4151]
    (.letOp (n := 4227) (.exec 0x1232c7 (fun s => s.RIP = 0x1232c7) (movR32R32Effect 0x1232c7 3 9 2) (Reg.operands [.gpr 2] [])) #v[4151]
    (.letOp (n := 4228) (.out 0x1232ca (rolR32Effect 0x1232ca 4 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4226]
    (.letOp (n := 4229) (.exec 0x1232ca (fun s => s.RIP = 0x1232ca) (rolR32Effect 0x1232ca 4 9 10) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4226]
    (.letOp (n := 4230) (.out 0x1232ce (xorR32R32Effect 0x1232ce 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[4228, 4224]
    (.letOp (n := 4231) (.exec 0x1232ce (fun s => s.RIP = 0x1232ce) (xorR32R32Effect 0x1232ce 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[4228, 4224]
    (b_l121930_107))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_106 : List UInt8 :=
  [0x45, 0x89, 0xF3, 0x41, 0xC1, 0xC3, 0x07, 0x41, 0x31, 0xD9, 0x45, 0x31, 0xCB, 0x45, 0x89, 0xD1,
    0x41, 0x31, 0xC9, 0x45, 0x21, 0xF1, 0x41, 0x31, 0xC9, 0x45, 0x01, 0xE0, 0x45, 0x01, 0xC8, 0x45,
    0x01, 0xD8, 0x41, 0x81, 0xC0, 0x85, 0x2C, 0x72, 0x92, 0x41, 0x89, 0xD1, 0x41, 0xC1, 0xC1, 0x1E,
    0x41, 0x89, 0xD3, 0x41, 0xC1, 0xC3, 0x13, 0x45, 0x31, 0xCB, 0x41, 0x89, 0xD1, 0x41, 0xC1, 0xC1,
    0x0A, 0x45, 0x31, 0xD9] ++ bytes_l121930_107

theorem code_l121930_106 : ∀ x ∈ codeRange 0x12328d bytes_l121930_106, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2328d 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_107

def b_l121930_105 : Block Op Label signature Reg.count 4153 :=
  .letOp (n := 4153) (.out 0x12324a (movR32R32Effect 0x12324a 3 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 5] []) (.reg (.gpr 11))) #v[4077]
    (.letOp (n := 4154) (.exec 0x12324a (fun s => s.RIP = 0x12324a) (movR32R32Effect 0x12324a 3 11 5) (Reg.operands [.gpr 5] [])) #v[4077]
    (.letOp (n := 4155) (.out 0x12324d (rolR32Effect 0x12324d 4 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[4153]
    (.letOp (n := 4156) (.exec 0x12324d (fun s => s.RIP = 0x12324d) (rolR32Effect 0x12324d 4 11 14) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4153]
    (.letOp (n := 4157) (.out 0x123251 (xorR32R32Effect 0x123251 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[4143, 4137]
    (.letOp (n := 4158) (.exec 0x123251 (fun s => s.RIP = 0x123251) (xorR32R32Effect 0x123251 3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[4143, 4137]
    (.letOp (n := 4159) (.out 0x123254 (xorR32R32Effect 0x123254 3 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[4155, 4149]
    (.letOp (n := 4160) (.exec 0x123254 (fun s => s.RIP = 0x123254) (xorR32R32Effect 0x123254 3 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[4155, 4149]
    (.letOp (n := 4161) (.out 0x123257 (movR32R32Effect 0x123257 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 5] []) (.reg (.gpr 3))) #v[4077]
    (.letOp (n := 4162) (.exec 0x123257 (fun s => s.RIP = 0x123257) (movR32R32Effect 0x123257 2 3 5) (Reg.operands [.gpr 5] [])) #v[4077]
    (.letOp (n := 4163) (.out 0x123259 (shrR32Effect 0x123259 3 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[4161]
    (.letOp (n := 4164) (.exec 0x123259 (fun s => s.RIP = 0x123259) (shrR32Effect 0x123259 3 3 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4161]
    (.letOp (n := 4165) (.out 0x12325c (xorR32R32Effect 0x12325c 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[4163, 4159]
    (.letOp (n := 4166) (.exec 0x12325c (fun s => s.RIP = 0x12325c) (xorR32R32Effect 0x12325c 3 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[4163, 4159]
    (.letOp (n := 4167) (.out 0x12325f (movR32M32Effect 0x12325f 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 4168) (.exec 0x12325f (LoadPre 0x12325f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12325f + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12325f 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 4169) (.out 0x123264 (addR32R32Effect 0x123264 3 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[4167, 3967]
    (.letOp (n := 4170) (.exec 0x123264 (fun s => s.RIP = 0x123264) (addR32R32Effect 0x123264 3 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[4167, 3967]
    (.letOp (n := 4171) (.out 0x123267 (addR32R32Effect 0x123267 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[4165, 3967]
    (.letOp (n := 4172) (.exec 0x123267 (fun s => s.RIP = 0x123267) (addR32R32Effect 0x123267 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[4165, 3967]
    (.letOp (n := 4173) (.exec 0x12326a (StorePre 0x12326a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x12326a + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x12326a 3 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[4171, 4]
    (.letOp (n := 4174) (.out 0x12326e (movR32R32Effect 0x12326e 3 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 12] []) (.reg (.gpr 11))) #v[3967]
    (.letOp (n := 4175) (.exec 0x12326e (fun s => s.RIP = 0x12326e) (movR32R32Effect 0x12326e 3 11 12) (Reg.operands [.gpr 12] [])) #v[3967]
    (.letOp (n := 4176) (.out 0x123271 (shrR32Effect 0x123271 4 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[4174]
    (.letOp (n := 4177) (.exec 0x123271 (fun s => s.RIP = 0x123271) (shrR32Effect 0x123271 4 11 10) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4174]
    (.letOp (n := 4178) (.out 0x123275 (movR32R32Effect 0x123275 3 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 14] []) (.reg (.gpr 3))) #v[4145]
    (.letOp (n := 4179) (.exec 0x123275 (fun s => s.RIP = 0x123275) (movR32R32Effect 0x123275 3 3 14) (Reg.operands [.gpr 14] [])) #v[4145]
    (.letOp (n := 4180) (.out 0x123278 (rolR32Effect 0x123278 3 3 26) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[4178]
    (.letOp (n := 4181) (.exec 0x123278 (fun s => s.RIP = 0x123278) (rolR32Effect 0x123278 3 3 26) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4178]
    (.letOp (n := 4182) (.out 0x12327b (xorR32R32Effect 0x12327b 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[4176, 4157]
    (.letOp (n := 4183) (.exec 0x12327b (fun s => s.RIP = 0x12327b) (xorR32R32Effect 0x12327b 3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[4176, 4157]
    (.letOp (n := 4184) (.out 0x12327e (movR32R32Effect 0x12327e 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[4145]
    (.letOp (n := 4185) (.exec 0x12327e (fun s => s.RIP = 0x12327e) (movR32R32Effect 0x12327e 3 9 14) (Reg.operands [.gpr 14] [])) #v[4145]
    (.letOp (n := 4186) (.out 0x123281 (rolR32Effect 0x123281 4 9 21) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4184]
    (.letOp (n := 4187) (.exec 0x123281 (fun s => s.RIP = 0x123281) (rolR32Effect 0x123281 4 9 21) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4184]
    (.letOp (n := 4188) (.out 0x123285 (movR32M32Effect 0x123285 12 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 4189) (.exec 0x123285 (LoadPre 0x123285 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x123285 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x123285 12 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 4190) (.out 0x12328a (addR32R32Effect 0x12328a 3 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[4188, 4182]
    (.letOp (n := 4191) (.exec 0x12328a (fun s => s.RIP = 0x12328a) (addR32R32Effect 0x12328a 3 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[4188, 4182]
    (b_l121930_106)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_105 : List UInt8 :=
  [0x41, 0x89, 0xEB, 0x41, 0xC1, 0xC3, 0x0E, 0x41, 0x31, 0xD9, 0x45, 0x31, 0xFB, 0x89, 0xEB, 0xC1,
    0xEB, 0x03, 0x44, 0x31, 0xDB, 0x44, 0x8B, 0x6C, 0x24, 0x10, 0x45, 0x01, 0xE5, 0x44, 0x01, 0xE3,
    0x89, 0x5C, 0x24, 0x14, 0x45, 0x89, 0xE3, 0x41, 0xC1, 0xEB, 0x0A, 0x44, 0x89, 0xF3, 0xC1, 0xC3,
    0x1A, 0x45, 0x31, 0xCB, 0x45, 0x89, 0xF1, 0x41, 0xC1, 0xC1, 0x15, 0x44, 0x8B, 0x64, 0x24, 0x48,
    0x45, 0x01, 0xDC] ++ bytes_l121930_106

theorem code_l121930_105 : ∀ x ∈ codeRange 0x12324a bytes_l121930_105, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2324a 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_106

def b_l121930_104 : Block Op Label signature Reg.count 4113 :=
  .letOp (n := 4113) (.out 0x12320d (rolR32Effect 0x12320d 4 9 19) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4111]
    (.letOp (n := 4114) (.exec 0x12320d (fun s => s.RIP = 0x12320d) (rolR32Effect 0x12320d 4 9 19) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4111]
    (.letOp (n := 4115) (.out 0x123211 (xorR32R32Effect 0x123211 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[4113, 4109]
    (.letOp (n := 4116) (.exec 0x123211 (fun s => s.RIP = 0x123211) (xorR32R32Effect 0x123211 3 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[4113, 4109]
    (.letOp (n := 4117) (.out 0x123214 (movR32R32Effect 0x123214 3 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[4041]
    (.letOp (n := 4118) (.exec 0x123214 (fun s => s.RIP = 0x123214) (movR32R32Effect 0x123214 3 15 6) (Reg.operands [.gpr 6] [])) #v[4041]
    (.letOp (n := 4119) (.out 0x123217 (rolR32Effect 0x123217 4 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[4117]
    (.letOp (n := 4120) (.exec 0x123217 (fun s => s.RIP = 0x123217) (rolR32Effect 0x123217 4 15 10) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4117]
    (.letOp (n := 4121) (.out 0x12321b (xorR32R32Effect 0x12321b 3 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9] []) (.reg (.gpr 15))) #v[4119, 4115]
    (.letOp (n := 4122) (.exec 0x12321b (fun s => s.RIP = 0x12321b) (xorR32R32Effect 0x12321b 3 15 9) (Reg.operands [.gpr 15, .gpr 9] [])) #v[4119, 4115]
    (.letOp (n := 4123) (.out 0x12321e (movR32R32Effect 0x12321e 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[3931]
    (.letOp (n := 4124) (.exec 0x12321e (fun s => s.RIP = 0x12321e) (movR32R32Effect 0x12321e 3 9 0) (Reg.operands [.gpr 0] [])) #v[3931]
    (.letOp (n := 4125) (.out 0x123221 (andR32R32Effect 0x123221 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[4123, 3821]
    (.letOp (n := 4126) (.exec 0x123221 (fun s => s.RIP = 0x123221) (andR32R32Effect 0x123221 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[4123, 3821]
    (.letOp (n := 4127) (.out 0x123224 (movR32R32Effect 0x123224 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[3931]
    (.letOp (n := 4128) (.exec 0x123224 (fun s => s.RIP = 0x123224) (movR32R32Effect 0x123224 2 2 0) (Reg.operands [.gpr 0] [])) #v[3931]
    (.letOp (n := 4129) (.out 0x123226 (xorR32R32Effect 0x123226 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[4127, 3821]
    (.letOp (n := 4130) (.exec 0x123226 (fun s => s.RIP = 0x123226) (xorR32R32Effect 0x123226 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[4127, 3821]
    (.letOp (n := 4131) (.out 0x123228 (andR32R32Effect 0x123228 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[4129, 4041]
    (.letOp (n := 4132) (.exec 0x123228 (fun s => s.RIP = 0x123228) (andR32R32Effect 0x123228 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[4129, 4041]
    (.letOp (n := 4133) (.out 0x12322a (xorR32R32Effect 0x12322a 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[4131, 4125]
    (.letOp (n := 4134) (.exec 0x12322a (fun s => s.RIP = 0x12322a) (xorR32R32Effect 0x12322a 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[4131, 4125]
    (.letOp (n := 4135) (.out 0x12322d (movR32R32Effect 0x12322d 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[3967]
    (.letOp (n := 4136) (.exec 0x12322d (fun s => s.RIP = 0x12322d) (movR32R32Effect 0x12322d 3 3 12) (Reg.operands [.gpr 12] [])) #v[3967]
    (.letOp (n := 4137) (.out 0x123230 (rolR32Effect 0x123230 3 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[4135]
    (.letOp (n := 4138) (.exec 0x123230 (fun s => s.RIP = 0x123230) (rolR32Effect 0x123230 3 3 15) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4135]
    (.letOp (n := 4139) (.out 0x123233 (addR32R32Effect 0x123233 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[4133, 4121]
    (.letOp (n := 4140) (.exec 0x123233 (fun s => s.RIP = 0x123233) (addR32R32Effect 0x123233 3 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[4133, 4121]
    (.letOp (n := 4141) (.out 0x123236 (movR32R32Effect 0x123236 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 12] []) (.reg (.gpr 9))) #v[3967]
    (.letOp (n := 4142) (.exec 0x123236 (fun s => s.RIP = 0x123236) (movR32R32Effect 0x123236 3 9 12) (Reg.operands [.gpr 12] [])) #v[3967]
    (.letOp (n := 4143) (.out 0x123239 (rolR32Effect 0x123239 4 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4141]
    (.letOp (n := 4144) (.exec 0x123239 (fun s => s.RIP = 0x123239) (rolR32Effect 0x123239 4 9 13) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4141]
    (.letOp (n := 4145) (.out 0x12323d (addR32R32Effect 0x12323d 3 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[3727, 4105]
    (.letOp (n := 4146) (.exec 0x12323d (fun s => s.RIP = 0x12323d) (addR32R32Effect 0x12323d 3 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[3727, 4105]
    (.letOp (n := 4147) (.out 0x123240 (movR32R32Effect 0x123240 3 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 5] []) (.reg (.gpr 15))) #v[4077]
    (.letOp (n := 4148) (.exec 0x123240 (fun s => s.RIP = 0x123240) (movR32R32Effect 0x123240 3 15 5) (Reg.operands [.gpr 5] [])) #v[4077]
    (.letOp (n := 4149) (.out 0x123243 (rolR32Effect 0x123243 4 15 25) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[4147]
    (.letOp (n := 4150) (.exec 0x123243 (fun s => s.RIP = 0x123243) (rolR32Effect 0x123243 4 15 25) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4147]
    (.letOp (n := 4151) (.out 0x123247 (addR32R32Effect 0x123247 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[4139, 4105]
    (.letOp (n := 4152) (.exec 0x123247 (fun s => s.RIP = 0x123247) (addR32R32Effect 0x123247 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[4139, 4105]
    (b_l121930_105))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_104 : List UInt8 :=
  [0x41, 0xC1, 0xC1, 0x13, 0x41, 0x31, 0xD1, 0x41, 0x89, 0xF7, 0x41, 0xC1, 0xC7, 0x0A, 0x45, 0x31,
    0xCF, 0x41, 0x89, 0xC1, 0x41, 0x21, 0xF9, 0x89, 0xC2, 0x31, 0xFA, 0x21, 0xF2, 0x44, 0x31, 0xCA,
    0x44, 0x89, 0xE3, 0xC1, 0xC3, 0x0F, 0x44, 0x01, 0xFA, 0x45, 0x89, 0xE1, 0x41, 0xC1, 0xC1, 0x0D,
    0x45, 0x01, 0xDE, 0x41, 0x89, 0xEF, 0x41, 0xC1, 0xC7, 0x19, 0x44, 0x01, 0xDA] ++ bytes_l121930_105

theorem code_l121930_104 : ∀ x ∈ codeRange 0x12320d bytes_l121930_104, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2320d 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_105

def b_l121930_103 : Block Op Label signature Reg.count 4073 :=
  .letOp (n := 4073) (.out 0x1231cb (rolR32Effect 0x1231cb 3 2 26) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[4071]
    (.letOp (n := 4074) (.exec 0x1231cb (fun s => s.RIP = 0x1231cb) (rolR32Effect 0x1231cb 3 2 26) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4071]
    (.letOp (n := 4075) (.out 0x1231ce (movR32M32LowEffect 0x1231ce 5 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 4076) (.exec 0x1231ce (LoadPre 0x1231ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1231ce + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1231ce 5 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 4077) (.out 0x1231d2 (addR32R32Effect 0x1231d2 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[4075, 4069]
    (.letOp (n := 4078) (.exec 0x1231d2 (fun s => s.RIP = 0x1231d2) (addR32R32Effect 0x1231d2 3 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[4075, 4069]
    (.letOp (n := 4079) (.out 0x1231d5 (movR32R32Effect 0x1231d5 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[4035]
    (.letOp (n := 4080) (.exec 0x1231d5 (fun s => s.RIP = 0x1231d5) (movR32R32Effect 0x1231d5 3 9 10) (Reg.operands [.gpr 10] [])) #v[4035]
    (.letOp (n := 4081) (.out 0x1231d8 (rolR32Effect 0x1231d8 4 9 21) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4079]
    (.letOp (n := 4082) (.exec 0x1231d8 (fun s => s.RIP = 0x1231d8) (rolR32Effect 0x1231d8 4 9 21) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4079]
    (.letOp (n := 4083) (.out 0x1231dc (xorR32R32Effect 0x1231dc 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[4081, 4073]
    (.letOp (n := 4084) (.exec 0x1231dc (fun s => s.RIP = 0x1231dc) (xorR32R32Effect 0x1231dc 3 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[4081, 4073]
    (.letOp (n := 4085) (.out 0x1231df (movR32R32Effect 0x1231df 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[4035]
    (.letOp (n := 4086) (.exec 0x1231df (fun s => s.RIP = 0x1231df) (movR32R32Effect 0x1231df 3 2 10) (Reg.operands [.gpr 10] [])) #v[4035]
    (.letOp (n := 4087) (.out 0x1231e2 (rolR32Effect 0x1231e2 3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[4085]
    (.letOp (n := 4088) (.exec 0x1231e2 (fun s => s.RIP = 0x1231e2) (rolR32Effect 0x1231e2 3 2 7) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4085]
    (.letOp (n := 4089) (.out 0x1231e5 (xorR32R32Effect 0x1231e5 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[4087, 4083]
    (.letOp (n := 4090) (.exec 0x1231e5 (fun s => s.RIP = 0x1231e5) (xorR32R32Effect 0x1231e5 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[4087, 4083]
    (.letOp (n := 4091) (.out 0x1231e8 (movR32R32Effect 0x1231e8 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[3925]
    (.letOp (n := 4092) (.exec 0x1231e8 (fun s => s.RIP = 0x1231e8) (movR32R32Effect 0x1231e8 3 9 1) (Reg.operands [.gpr 1] [])) #v[3925]
    (.letOp (n := 4093) (.out 0x1231eb (xorR32R32Effect 0x1231eb 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[4091, 3819]
    (.letOp (n := 4094) (.exec 0x1231eb (fun s => s.RIP = 0x1231eb) (xorR32R32Effect 0x1231eb 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[4091, 3819]
    (.letOp (n := 4095) (.out 0x1231ee (andR32R32Effect 0x1231ee 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[4093, 4035]
    (.letOp (n := 4096) (.exec 0x1231ee (fun s => s.RIP = 0x1231ee) (andR32R32Effect 0x1231ee 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[4093, 4035]
    (.letOp (n := 4097) (.out 0x1231f1 (xorR32R32Effect 0x1231f1 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[4095, 3819]
    (.letOp (n := 4098) (.exec 0x1231f1 (fun s => s.RIP = 0x1231f1) (xorR32R32Effect 0x1231f1 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[4095, 3819]
    (.letOp (n := 4099) (.out 0x1231f4 (addR32R32Effect 0x1231f4 3 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[3721, 4077]
    (.letOp (n := 4100) (.exec 0x1231f4 (fun s => s.RIP = 0x1231f4) (addR32R32Effect 0x1231f4 3 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[3721, 4077]
    (.letOp (n := 4101) (.out 0x1231f7 (addR32R32Effect 0x1231f7 3 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[4099, 4097]
    (.letOp (n := 4102) (.exec 0x1231f7 (fun s => s.RIP = 0x1231f7) (addR32R32Effect 0x1231f7 3 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[4099, 4097]
    (.letOp (n := 4103) (.out 0x1231fa (leaR32Effect 0x1231fa 4 11 (.sib 2 (some 13) 0 .none)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2, .gpr 13] []) (.reg (.gpr 11))) #v[4089, 4101]
    (.letOp (n := 4104) (.exec 0x1231fa (fun s => s.RIP = 0x1231fa) (leaR32Effect 0x1231fa 4 11 (.sib 2 (some 13) 0 .none)) (Reg.operands [.gpr 2, .gpr 13] [])) #v[4089, 4101]
    (.letOp (n := 4105) (.out 0x1231fe (addR32Imm32Effect 0x1231fe 7 11 0x81c2c92e) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[4103]
    (.letOp (n := 4106) (.exec 0x1231fe (fun s => s.RIP = 0x1231fe) (addR32Imm32Effect 0x1231fe 7 11 0x81c2c92e) (Reg.operands [.gpr 11] [])) #v[4103]
    (.letOp (n := 4107) (.out 0x123205 (movR32R32Effect 0x123205 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[4041]
    (.letOp (n := 4108) (.exec 0x123205 (fun s => s.RIP = 0x123205) (movR32R32Effect 0x123205 2 2 6) (Reg.operands [.gpr 6] [])) #v[4041]
    (.letOp (n := 4109) (.out 0x123207 (rolR32Effect 0x123207 3 2 30) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[4107]
    (.letOp (n := 4110) (.exec 0x123207 (fun s => s.RIP = 0x123207) (rolR32Effect 0x123207 3 2 30) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4107]
    (.letOp (n := 4111) (.out 0x12320a (movR32R32Effect 0x12320a 3 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[4041]
    (.letOp (n := 4112) (.exec 0x12320a (fun s => s.RIP = 0x12320a) (movR32R32Effect 0x12320a 3 9 6) (Reg.operands [.gpr 6] [])) #v[4041]
    (b_l121930_104))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_103 : List UInt8 :=
  [0xC1, 0xC2, 0x1A, 0x8B, 0x6C, 0x24, 0x14, 0x44, 0x01, 0xCD, 0x45, 0x89, 0xD1, 0x41, 0xC1, 0xC1,
    0x15, 0x41, 0x31, 0xD1, 0x44, 0x89, 0xD2, 0xC1, 0xC2, 0x07, 0x44, 0x31, 0xCA, 0x41, 0x89, 0xC9,
    0x45, 0x31, 0xC1, 0x45, 0x21, 0xD1, 0x45, 0x31, 0xC1, 0x41, 0x01, 0xED, 0x45, 0x01, 0xCD, 0x46,
    0x8D, 0x1C, 0x2A, 0x41, 0x81, 0xC3, 0x2E, 0xC9, 0xC2, 0x81, 0x89, 0xF2, 0xC1, 0xC2, 0x1E, 0x41,
    0x89, 0xF1] ++ bytes_l121930_104

theorem code_l121930_103 : ∀ x ∈ codeRange 0x1231cb bytes_l121930_103, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x231cb 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_104

def b_l121930_102 : Block Op Label signature Reg.count 4035 :=
  .letOp (n := 4035) (.out 0x123189 (addR32R32Effect 0x123189 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[3617, 4007]
    (.letOp (n := 4036) (.exec 0x123189 (fun s => s.RIP = 0x123189) (addR32R32Effect 0x123189 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[3617, 4007]
    (.letOp (n := 4037) (.out 0x12318c (movR32R32Effect 0x12318c 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3861]
    (.letOp (n := 4038) (.exec 0x12318c (fun s => s.RIP = 0x12318c) (movR32R32Effect 0x12318c 2 2 3) (Reg.operands [.gpr 3] [])) #v[3861]
    (.letOp (n := 4039) (.out 0x12318e (rolR32Effect 0x12318e 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[4037]
    (.letOp (n := 4040) (.exec 0x12318e (fun s => s.RIP = 0x12318e) (rolR32Effect 0x12318e 3 2 13) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4037]
    (.letOp (n := 4041) (.out 0x123191 (addR32R32Effect 0x123191 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[4029, 4007]
    (.letOp (n := 4042) (.exec 0x123191 (fun s => s.RIP = 0x123191) (addR32R32Effect 0x123191 3 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[4029, 4007]
    (.letOp (n := 4043) (.out 0x123194 (movR32R32Effect 0x123194 3 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 12] []) (.reg (.gpr 11))) #v[3967]
    (.letOp (n := 4044) (.exec 0x123194 (fun s => s.RIP = 0x123194) (movR32R32Effect 0x123194 3 11 12) (Reg.operands [.gpr 12] [])) #v[3967]
    (.letOp (n := 4045) (.out 0x123197 (rolR32Effect 0x123197 4 11 25) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[4043]
    (.letOp (n := 4046) (.exec 0x123197 (fun s => s.RIP = 0x123197) (rolR32Effect 0x123197 4 11 25) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4043]
    (.letOp (n := 4047) (.out 0x12319b (xorR32R32Effect 0x12319b 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[4039, 4033]
    (.letOp (n := 4048) (.exec 0x12319b (fun s => s.RIP = 0x12319b) (xorR32R32Effect 0x12319b 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[4039, 4033]
    (.letOp (n := 4049) (.out 0x12319e (movR32R32Effect 0x12319e 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 12] []) (.reg (.gpr 9))) #v[3967]
    (.letOp (n := 4050) (.exec 0x12319e (fun s => s.RIP = 0x12319e) (movR32R32Effect 0x12319e 3 9 12) (Reg.operands [.gpr 12] [])) #v[3967]
    (.letOp (n := 4051) (.out 0x1231a1 (rolR32Effect 0x1231a1 4 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4049]
    (.letOp (n := 4052) (.exec 0x1231a1 (fun s => s.RIP = 0x1231a1) (rolR32Effect 0x1231a1 4 9 14) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4049]
    (.letOp (n := 4053) (.out 0x1231a5 (xorR32R32Effect 0x1231a5 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[4051, 4045]
    (.letOp (n := 4054) (.exec 0x1231a5 (fun s => s.RIP = 0x1231a5) (xorR32R32Effect 0x1231a5 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[4051, 4045]
    (.letOp (n := 4055) (.out 0x1231a8 (movR32R32Effect 0x1231a8 3 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 12] []) (.reg (.gpr 11))) #v[3967]
    (.letOp (n := 4056) (.exec 0x1231a8 (fun s => s.RIP = 0x1231a8) (movR32R32Effect 0x1231a8 3 11 12) (Reg.operands [.gpr 12] [])) #v[3967]
    (.letOp (n := 4057) (.out 0x1231ab (shrR32Effect 0x1231ab 4 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[4055]
    (.letOp (n := 4058) (.exec 0x1231ab (fun s => s.RIP = 0x1231ab) (shrR32Effect 0x1231ab 4 11 3) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4055]
    (.letOp (n := 4059) (.out 0x1231af (xorR32R32Effect 0x1231af 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[4057, 4053]
    (.letOp (n := 4060) (.exec 0x1231af (fun s => s.RIP = 0x1231af) (xorR32R32Effect 0x1231af 3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[4057, 4053]
    (.letOp (n := 4061) (.exec 0x1231b2 (StorePre 0x1231b2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1231b2 + BitVec.ofNat 64 4)) 4) (addMREffect 0x1231b2 4 32 3 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3861, 4]
    (.letOp (n := 4062) (.out 0x1231b6 (addR32R32Effect 0x1231b6 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[4059, 3861]
    (.letOp (n := 4063) (.exec 0x1231b6 (fun s => s.RIP = 0x1231b6) (addR32R32Effect 0x1231b6 3 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[4059, 3861]
    (.letOp (n := 4064) (.exec 0x1231b9 (StorePre 0x1231b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1231b9 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1231b9 11 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[4062, 4]
    (.letOp (n := 4065) (.out 0x1231be (movR32R32Effect 0x1231be 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[3861]
    (.letOp (n := 4066) (.exec 0x1231be (fun s => s.RIP = 0x1231be) (movR32R32Effect 0x1231be 3 9 3) (Reg.operands [.gpr 3] [])) #v[3861]
    (.letOp (n := 4067) (.out 0x1231c1 (shrR32Effect 0x1231c1 4 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4065]
    (.letOp (n := 4068) (.exec 0x1231c1 (fun s => s.RIP = 0x1231c1) (shrR32Effect 0x1231c1 4 9 10) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4065]
    (.letOp (n := 4069) (.out 0x1231c5 (xorR32R32Effect 0x1231c5 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[4067, 4047]
    (.letOp (n := 4070) (.exec 0x1231c5 (fun s => s.RIP = 0x1231c5) (xorR32R32Effect 0x1231c5 3 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[4067, 4047]
    (.letOp (n := 4071) (.out 0x1231c8 (movR32R32Effect 0x1231c8 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[4035]
    (.letOp (n := 4072) (.exec 0x1231c8 (fun s => s.RIP = 0x1231c8) (movR32R32Effect 0x1231c8 3 2 10) (Reg.operands [.gpr 10] [])) #v[4035]
    (b_l121930_103))))))))))))))))))))))))))))))))))))))

def bytes_l121930_102 : List UInt8 :=
  [0x45, 0x01, 0xDA, 0x89, 0xDA, 0xC1, 0xC2, 0x0D, 0x44, 0x01, 0xDE, 0x45, 0x89, 0xE3, 0x41, 0xC1,
    0xC3, 0x19, 0x44, 0x31, 0xCA, 0x45, 0x89, 0xE1, 0x41, 0xC1, 0xC1, 0x0E, 0x45, 0x31, 0xD9, 0x45,
    0x89, 0xE3, 0x41, 0xC1, 0xEB, 0x03, 0x45, 0x31, 0xCB, 0x01, 0x5C, 0x24, 0x58, 0x41, 0x01, 0xDB,
    0x44, 0x89, 0x5C, 0x24, 0x78, 0x41, 0x89, 0xD9, 0x41, 0xC1, 0xE9, 0x0A, 0x41, 0x31, 0xD1, 0x44,
    0x89, 0xD2] ++ bytes_l121930_103

theorem code_l121930_102 : ∀ x ∈ codeRange 0x123189 bytes_l121930_102, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23189 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_103

def b_l121930_101 : Block Op Label signature Reg.count 3995 :=
  .letOp (n := 3995) (.out 0x12314d (movR32R32Effect 0x12314d 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[3931]
    (.letOp (n := 3996) (.exec 0x12314d (fun s => s.RIP = 0x12314d) (movR32R32Effect 0x12314d 3 9 0) (Reg.operands [.gpr 0] [])) #v[3931]
    (.letOp (n := 3997) (.out 0x123150 (rolR32Effect 0x123150 4 9 30) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[3995]
    (.letOp (n := 3998) (.exec 0x123150 (fun s => s.RIP = 0x123150) (rolR32Effect 0x123150 4 9 30) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3995]
    (.letOp (n := 3999) (.out 0x123154 (addR32R32Effect 0x123154 3 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[3993, 3991]
    (.letOp (n := 4000) (.exec 0x123154 (fun s => s.RIP = 0x123154) (addR32R32Effect 0x123154 3 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[3993, 3991]
    (.letOp (n := 4001) (.out 0x123157 (movR32R32Effect 0x123157 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[3931]
    (.letOp (n := 4002) (.exec 0x123157 (fun s => s.RIP = 0x123157) (movR32R32Effect 0x123157 2 6 0) (Reg.operands [.gpr 0] [])) #v[3931]
    (.letOp (n := 4003) (.out 0x123159 (rolR32Effect 0x123159 3 6 19) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[4001]
    (.letOp (n := 4004) (.exec 0x123159 (fun s => s.RIP = 0x123159) (rolR32Effect 0x123159 3 6 19) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4001]
    (.letOp (n := 4005) (.out 0x12315c (addR32R32Effect 0x12315c 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[3999, 3983]
    (.letOp (n := 4006) (.exec 0x12315c (fun s => s.RIP = 0x12315c) (addR32R32Effect 0x12315c 3 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[3999, 3983]
    (.letOp (n := 4007) (.out 0x12315f (addR32Imm32Effect 0x12315f 7 11 0x766a0abb) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[4005]
    (.letOp (n := 4008) (.exec 0x12315f (fun s => s.RIP = 0x12315f) (addR32Imm32Effect 0x12315f 7 11 0x766a0abb) (Reg.operands [.gpr 11] [])) #v[4005]
    (.letOp (n := 4009) (.out 0x123166 (movR32R32Effect 0x123166 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[3931]
    (.letOp (n := 4010) (.exec 0x123166 (fun s => s.RIP = 0x123166) (movR32R32Effect 0x123166 2 2 0) (Reg.operands [.gpr 0] [])) #v[3931]
    (.letOp (n := 4011) (.out 0x123168 (rolR32Effect 0x123168 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[4009]
    (.letOp (n := 4012) (.exec 0x123168 (fun s => s.RIP = 0x123168) (rolR32Effect 0x123168 3 2 10) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4009]
    (.letOp (n := 4013) (.out 0x12316b (xorR32R32Effect 0x12316b 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[4003, 3997]
    (.letOp (n := 4014) (.exec 0x12316b (fun s => s.RIP = 0x12316b) (xorR32R32Effect 0x12316b 3 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[4003, 3997]
    (.letOp (n := 4015) (.out 0x12316e (xorR32R32Effect 0x12316e 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[4011, 4013]
    (.letOp (n := 4016) (.exec 0x12316e (fun s => s.RIP = 0x12316e) (xorR32R32Effect 0x12316e 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[4011, 4013]
    (.letOp (n := 4017) (.out 0x123170 (movR32R32Effect 0x123170 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[3821]
    (.letOp (n := 4018) (.exec 0x123170 (fun s => s.RIP = 0x123170) (movR32R32Effect 0x123170 3 9 7) (Reg.operands [.gpr 7] [])) #v[3821]
    (.letOp (n := 4019) (.out 0x123173 (andR32R32Effect 0x123173 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[4017, 3727]
    (.letOp (n := 4020) (.exec 0x123173 (fun s => s.RIP = 0x123173) (andR32R32Effect 0x123173 3 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[4017, 3727]
    (.letOp (n := 4021) (.out 0x123176 (movR32R32Effect 0x123176 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[3821]
    (.letOp (n := 4022) (.exec 0x123176 (fun s => s.RIP = 0x123176) (movR32R32Effect 0x123176 2 6 7) (Reg.operands [.gpr 7] [])) #v[3821]
    (.letOp (n := 4023) (.out 0x123178 (xorR32R32Effect 0x123178 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[4021, 3727]
    (.letOp (n := 4024) (.exec 0x123178 (fun s => s.RIP = 0x123178) (xorR32R32Effect 0x123178 3 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[4021, 3727]
    (.letOp (n := 4025) (.out 0x12317b (andR32R32Effect 0x12317b 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[4023, 3931]
    (.letOp (n := 4026) (.exec 0x12317b (fun s => s.RIP = 0x12317b) (andR32R32Effect 0x12317b 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[4023, 3931]
    (.letOp (n := 4027) (.out 0x12317d (xorR32R32Effect 0x12317d 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[4025, 4019]
    (.letOp (n := 4028) (.exec 0x12317d (fun s => s.RIP = 0x12317d) (xorR32R32Effect 0x12317d 3 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[4025, 4019]
    (.letOp (n := 4029) (.out 0x123180 (addR32R32Effect 0x123180 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[4027, 4015]
    (.letOp (n := 4030) (.exec 0x123180 (fun s => s.RIP = 0x123180) (addR32R32Effect 0x123180 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[4027, 4015]
    (.letOp (n := 4031) (.out 0x123182 (movR32R32Effect 0x123182 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[3861]
    (.letOp (n := 4032) (.exec 0x123182 (fun s => s.RIP = 0x123182) (movR32R32Effect 0x123182 3 9 3) (Reg.operands [.gpr 3] [])) #v[3861]
    (.letOp (n := 4033) (.out 0x123185 (rolR32Effect 0x123185 4 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[4031]
    (.letOp (n := 4034) (.exec 0x123185 (fun s => s.RIP = 0x123185) (rolR32Effect 0x123185 4 9 15) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[4031]
    (b_l121930_102))))))))))))))))))))))))))))))))))))))))

def bytes_l121930_101 : List UInt8 :=
  [0x41, 0x89, 0xC1, 0x41, 0xC1, 0xC1, 0x1E, 0x41, 0x01, 0xF3, 0x89, 0xC6, 0xC1, 0xC6, 0x13, 0x41,
    0x01, 0xD3, 0x41, 0x81, 0xC3, 0xBB, 0x0A, 0x6A, 0x76, 0x89, 0xC2, 0xC1, 0xC2, 0x0A, 0x44, 0x31,
    0xCE, 0x31, 0xF2, 0x41, 0x89, 0xF9, 0x45, 0x21, 0xF1, 0x89, 0xFE, 0x44, 0x31, 0xF6, 0x21, 0xC6,
    0x44, 0x31, 0xCE, 0x01, 0xD6, 0x41, 0x89, 0xD9, 0x41, 0xC1, 0xC1, 0x0F] ++ bytes_l121930_102

theorem code_l121930_101 : ∀ x ∈ codeRange 0x12314d bytes_l121930_101, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2314d 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_102

def b_l121930_100 : Block Op Label signature Reg.count 3956 :=
  .letOp (n := 3956) (.out 0x123117 (addR32R32Effect 0x123117 2 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[3953, 3763]
    (.letOp (n := 3957) (.exec 0x123117 (fun s => s.RIP = 0x123117) (addR32R32Effect 0x123117 2 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[3953, 3763]
    (.letOp (n := 3958) (.exec 0x123119 (StorePre 0x123119 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x123119 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x123119 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[3956, 4]
    (.letOp (n := 3959) (.out 0x12311d (movR32R32Effect 0x12311d 2 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[3763]
    (.letOp (n := 3960) (.exec 0x12311d (fun s => s.RIP = 0x12311d) (movR32R32Effect 0x12311d 2 6 5) (Reg.operands [.gpr 5] [])) #v[3763]
    (.letOp (n := 3961) (.out 0x12311f (shrR32Effect 0x12311f 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3959]
    (.letOp (n := 3962) (.exec 0x12311f (fun s => s.RIP = 0x12311f) (shrR32Effect 0x12311f 3 6 10) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3959]
    (.letOp (n := 3963) (.out 0x123122 (xorR32R32Effect 0x123122 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[3961, 3937]
    (.letOp (n := 3964) (.exec 0x123122 (fun s => s.RIP = 0x123122) (xorR32R32Effect 0x123122 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[3961, 3937]
    (.letOp (n := 3965) (.out 0x123124 (movR32M32Effect 0x123124 12 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 3966) (.exec 0x123124 (LoadPre 0x123124 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x123124 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x123124 12 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 3967) (.out 0x123129 (addR32R32Effect 0x123129 3 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[3965, 3963]
    (.letOp (n := 3968) (.exec 0x123129 (fun s => s.RIP = 0x123129) (addR32R32Effect 0x123129 3 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[3965, 3963]
    (.letOp (n := 3969) (.out 0x12312c (movR32R32Effect 0x12312c 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[3925]
    (.letOp (n := 3970) (.exec 0x12312c (fun s => s.RIP = 0x12312c) (movR32R32Effect 0x12312c 2 2 1) (Reg.operands [.gpr 1] [])) #v[3925]
    (.letOp (n := 3971) (.out 0x12312e (rolR32Effect 0x12312e 3 2 26) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3969]
    (.letOp (n := 3972) (.exec 0x12312e (fun s => s.RIP = 0x12312e) (rolR32Effect 0x12312e 3 2 26) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3969]
    (.letOp (n := 3973) (.out 0x123131 (movR32R32Effect 0x123131 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[3925]
    (.letOp (n := 3974) (.exec 0x123131 (fun s => s.RIP = 0x123131) (movR32R32Effect 0x123131 2 6 1) (Reg.operands [.gpr 1] [])) #v[3925]
    (.letOp (n := 3975) (.out 0x123133 (rolR32Effect 0x123133 3 6 21) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3973]
    (.letOp (n := 3976) (.exec 0x123133 (fun s => s.RIP = 0x123133) (rolR32Effect 0x123133 3 6 21) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3973]
    (.letOp (n := 3977) (.out 0x123136 (xorR32R32Effect 0x123136 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[3975, 3971]
    (.letOp (n := 3978) (.exec 0x123136 (fun s => s.RIP = 0x123136) (xorR32R32Effect 0x123136 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[3975, 3971]
    (.letOp (n := 3979) (.out 0x123138 (movR32R32Effect 0x123138 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[3925]
    (.letOp (n := 3980) (.exec 0x123138 (fun s => s.RIP = 0x123138) (movR32R32Effect 0x123138 2 2 1) (Reg.operands [.gpr 1] [])) #v[3925]
    (.letOp (n := 3981) (.out 0x12313a (rolR32Effect 0x12313a 3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3979]
    (.letOp (n := 3982) (.exec 0x12313a (fun s => s.RIP = 0x12313a) (rolR32Effect 0x12313a 3 2 7) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3979]
    (.letOp (n := 3983) (.out 0x12313d (xorR32R32Effect 0x12313d 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[3981, 3977]
    (.letOp (n := 3984) (.exec 0x12313d (fun s => s.RIP = 0x12313d) (xorR32R32Effect 0x12313d 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[3981, 3977]
    (.letOp (n := 3985) (.out 0x12313f (movR32R32Effect 0x12313f 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[3819]
    (.letOp (n := 3986) (.exec 0x12313f (fun s => s.RIP = 0x12313f) (movR32R32Effect 0x12313f 3 6 8) (Reg.operands [.gpr 8] [])) #v[3819]
    (.letOp (n := 3987) (.out 0x123142 (xorR32R32Effect 0x123142 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[3985, 3721]
    (.letOp (n := 3988) (.exec 0x123142 (fun s => s.RIP = 0x123142) (xorR32R32Effect 0x123142 3 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[3985, 3721]
    (.letOp (n := 3989) (.out 0x123145 (andR32R32Effect 0x123145 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[3987, 3925]
    (.letOp (n := 3990) (.exec 0x123145 (fun s => s.RIP = 0x123145) (andR32R32Effect 0x123145 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[3987, 3925]
    (.letOp (n := 3991) (.out 0x123147 (xorR32R32Effect 0x123147 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[3989, 3721]
    (.letOp (n := 3992) (.exec 0x123147 (fun s => s.RIP = 0x123147) (xorR32R32Effect 0x123147 3 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[3989, 3721]
    (.letOp (n := 3993) (.out 0x12314a (addR32R32Effect 0x12314a 3 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 12] []) (.reg (.gpr 11))) #v[3611, 3967]
    (.letOp (n := 3994) (.exec 0x12314a (fun s => s.RIP = 0x12314a) (addR32R32Effect 0x12314a 3 11 12) (Reg.operands [.gpr 11, .gpr 12] [])) #v[3611, 3967]
    (b_l121930_101)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_100 : List UInt8 :=
  [0x01, 0xEE, 0x89, 0x74, 0x24, 0x50, 0x89, 0xEE, 0xC1, 0xEE, 0x0A, 0x31, 0xD6, 0x44, 0x8B, 0x64,
    0x24, 0x68, 0x41, 0x01, 0xF4, 0x89, 0xCA, 0xC1, 0xC2, 0x1A, 0x89, 0xCE, 0xC1, 0xC6, 0x15, 0x31,
    0xD6, 0x89, 0xCA, 0xC1, 0xC2, 0x07, 0x31, 0xF2, 0x44, 0x89, 0xC6, 0x44, 0x31, 0xEE, 0x21, 0xCE,
    0x44, 0x31, 0xEE, 0x45, 0x01, 0xE3] ++ bytes_l121930_101

theorem code_l121930_100 : ∀ x ∈ codeRange 0x123117 bytes_l121930_100, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x23117 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_101

def b_l121930_99 : Block Op Label signature Reg.count 3917 :=
  .letOp (n := 3917) (.out 0x1230dc (xorR32R32Effect 0x1230dc 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[3915, 3617]
    (.letOp (n := 3918) (.exec 0x1230dc (fun s => s.RIP = 0x1230dc) (xorR32R32Effect 0x1230dc 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[3915, 3617]
    (.letOp (n := 3919) (.out 0x1230df (andR32R32Effect 0x1230df 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[3917, 3821]
    (.letOp (n := 3920) (.exec 0x1230df (fun s => s.RIP = 0x1230df) (andR32R32Effect 0x1230df 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[3917, 3821]
    (.letOp (n := 3921) (.out 0x1230e1 (xorR32R32Effect 0x1230e1 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[3919, 3913]
    (.letOp (n := 3922) (.exec 0x1230e1 (fun s => s.RIP = 0x1230e1) (xorR32R32Effect 0x1230e1 3 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[3919, 3913]
    (.letOp (n := 3923) (.out 0x1230e4 (addR32R32Effect 0x1230e4 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[3921, 3909]
    (.letOp (n := 3924) (.exec 0x1230e4 (fun s => s.RIP = 0x1230e4) (addR32R32Effect 0x1230e4 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[3921, 3909]
    (.letOp (n := 3925) (.out 0x1230e6 (addR32R32Effect 0x1230e6 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[3507, 3897]
    (.letOp (n := 3926) (.exec 0x1230e6 (fun s => s.RIP = 0x1230e6) (addR32R32Effect 0x1230e6 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[3507, 3897]
    (.letOp (n := 3927) (.out 0x1230e8 (movR32R32Effect 0x1230e8 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[3763]
    (.letOp (n := 3928) (.exec 0x1230e8 (fun s => s.RIP = 0x1230e8) (movR32R32Effect 0x1230e8 3 9 5) (Reg.operands [.gpr 5] [])) #v[3763]
    (.letOp (n := 3929) (.out 0x1230eb (rolR32Effect 0x1230eb 4 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[3927]
    (.letOp (n := 3930) (.exec 0x1230eb (fun s => s.RIP = 0x1230eb) (rolR32Effect 0x1230eb 4 9 15) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3927]
    (.letOp (n := 3931) (.out 0x1230ef (addR32R32Effect 0x1230ef 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[3923, 3897]
    (.letOp (n := 3932) (.exec 0x1230ef (fun s => s.RIP = 0x1230ef) (addR32R32Effect 0x1230ef 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[3923, 3897]
    (.letOp (n := 3933) (.out 0x1230f1 (movR32R32Effect 0x1230f1 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[3763]
    (.letOp (n := 3934) (.exec 0x1230f1 (fun s => s.RIP = 0x1230f1) (movR32R32Effect 0x1230f1 2 2 5) (Reg.operands [.gpr 5] [])) #v[3763]
    (.letOp (n := 3935) (.out 0x1230f3 (rolR32Effect 0x1230f3 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[3933]
    (.letOp (n := 3936) (.exec 0x1230f3 (fun s => s.RIP = 0x1230f3) (rolR32Effect 0x1230f3 3 2 13) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3933]
    (.letOp (n := 3937) (.out 0x1230f6 (xorR32R32Effect 0x1230f6 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[3935, 3929]
    (.letOp (n := 3938) (.exec 0x1230f6 (fun s => s.RIP = 0x1230f6) (xorR32R32Effect 0x1230f6 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[3935, 3929]
    (.letOp (n := 3939) (.out 0x1230f9 (movR32R32Effect 0x1230f9 2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3861]
    (.letOp (n := 3940) (.exec 0x1230f9 (fun s => s.RIP = 0x1230f9) (movR32R32Effect 0x1230f9 2 6 3) (Reg.operands [.gpr 3] [])) #v[3861]
    (.letOp (n := 3941) (.out 0x1230fb (rolR32Effect 0x1230fb 3 6 25) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3939]
    (.letOp (n := 3942) (.exec 0x1230fb (fun s => s.RIP = 0x1230fb) (rolR32Effect 0x1230fb 3 6 25) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3939]
    (.letOp (n := 3943) (.out 0x1230fe (movR32R32Effect 0x1230fe 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[3861]
    (.letOp (n := 3944) (.exec 0x1230fe (fun s => s.RIP = 0x1230fe) (movR32R32Effect 0x1230fe 3 9 3) (Reg.operands [.gpr 3] [])) #v[3861]
    (.letOp (n := 3945) (.out 0x123101 (rolR32Effect 0x123101 4 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[3943]
    (.letOp (n := 3946) (.exec 0x123101 (fun s => s.RIP = 0x123101) (rolR32Effect 0x123101 4 9 14) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3943]
    (.letOp (n := 3947) (.out 0x123105 (xorR32R32Effect 0x123105 3 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[3945, 3941]
    (.letOp (n := 3948) (.exec 0x123105 (fun s => s.RIP = 0x123105) (xorR32R32Effect 0x123105 3 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[3945, 3941]
    (.letOp (n := 3949) (.out 0x123108 (movR32R32Effect 0x123108 2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3861]
    (.letOp (n := 3950) (.exec 0x123108 (fun s => s.RIP = 0x123108) (movR32R32Effect 0x123108 2 6 3) (Reg.operands [.gpr 3] [])) #v[3861]
    (.letOp (n := 3951) (.out 0x12310a (shrR32Effect 0x12310a 3 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[3949]
    (.letOp (n := 3952) (.exec 0x12310a (fun s => s.RIP = 0x12310a) (shrR32Effect 0x12310a 3 6 3) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3949]
    (.letOp (n := 3953) (.out 0x12310d (xorR32R32Effect 0x12310d 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[3951, 3947]
    (.letOp (n := 3954) (.exec 0x12310d (fun s => s.RIP = 0x12310d) (xorR32R32Effect 0x12310d 3 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[3951, 3947]
    (.letOp (n := 3955) (.exec 0x123110 (StorePre 0x123110 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x123110 + BitVec.ofNat 64 7)) 4) (addMREffect 0x123110 7 32 5 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[3763, 4]
    (b_l121930_100)))))))))))))))))))))))))))))))))))))))

def bytes_l121930_99 : List UInt8 :=
  [0x44, 0x31, 0xD0, 0x21, 0xF8, 0x44, 0x31, 0xC8, 0x01, 0xD0, 0x01, 0xF1, 0x41, 0x89, 0xE9, 0x41,
    0xC1, 0xC1, 0x0F, 0x01, 0xF0, 0x89, 0xEA, 0xC1, 0xC2, 0x0D, 0x44, 0x31, 0xCA, 0x89, 0xDE, 0xC1,
    0xC6, 0x19, 0x41, 0x89, 0xD9, 0x41, 0xC1, 0xC1, 0x0E, 0x41, 0x31, 0xF1, 0x89, 0xDE, 0xC1, 0xEE,
    0x03, 0x44, 0x31, 0xCE, 0x01, 0xAC, 0x24, 0x80, 0x00, 0x00, 0x00] ++ bytes_l121930_100

theorem code_l121930_99 : ∀ x ∈ codeRange 0x1230dc bytes_l121930_99, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x230dc 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l121930_100

@[cfg_block] def b_l1240c4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1240c4 (movR64M64Effect 0x1240c4 7 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1240c4 (LoadPre 0x1240c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1240c4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1240c4 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1240cc (StorePre 0x1240cc 4 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x1240cc + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1240cc 14 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 14, .gpr 7] [])) #v[14, 53]
    (.letOp (n := 56) (.exec 0x1240d0 (StorePre 0x1240d0 3 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1240d0 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1240d0 0 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[0, 53]
    (.letOp (n := 57) (.exec 0x1240d3 (StorePre 0x1240d3 4 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x1240d3 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1240d3 9 (.base 7 (.d8 0xc))) (Reg.operands [.gpr 9, .gpr 7] [])) #v[9, 53]
    (.letOp (n := 58) (.exec 0x1240d7 (StorePre 0x1240d7 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x1240d7 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1240d7 8 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[8, 53]
    (.letOp (n := 59) (.exec 0x1240db (StorePre 0x1240db 4 (fun s => AddrMode.addr (.base 7 (.d8 0x14)) s (0x1240db + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1240db 10 (.base 7 (.d8 0x14))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[10, 53]
    (.letOp (n := 60) (.exec 0x1240df (StorePre 0x1240df 3 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1240df + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1240df 2 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[2, 53]
    (.letOp (n := 61) (.exec 0x1240e2 (StorePre 0x1240e2 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1c)) s (0x1240e2 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1240e2 1 (.base 7 (.d8 0x1c))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1, 53]
    (.letOp (n := 62) (.exec 0x1240e5 (StorePre 0x1240e5 2 (fun s => AddrMode.addr (.base 7 .none) s (0x1240e5 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1240e5 3 (.base 7 .none)) (Reg.operands [.gpr 3, .gpr 7] [])) #v[3, 53]
    (.letOp (n := 63) (.out 0x1240e7 (addR64Imm32Effect 0x1240e7 4 0x120) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x1240e7 (fun s => s.RIP = 0x1240e7) (addR64Imm32Effect 0x1240e7 4 0x120) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1240ee (popR64Effect 0x1240ee 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[63]
    (.letOp (n := 66) (.out 0x1240ee (popR64Effect 0x1240ee 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x1240ee (PopPre 0x1240ee) (popR64Effect 0x1240ee 1 3) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x1240ef (popR64Effect 0x1240ef 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[66]
    (.letOp (n := 69) (.out 0x1240ef (popR64Effect 0x1240ef 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x1240ef (PopPre 0x1240ef) (popR64Effect 0x1240ef 2 12) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 71) (.out 0x1240f1 (popR64Effect 0x1240f1 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[69]
    (.letOp (n := 72) (.out 0x1240f1 (popR64Effect 0x1240f1 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 73) (.exec 0x1240f1 (PopPre 0x1240f1) (popR64Effect 0x1240f1 2 13) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 74) (.out 0x1240f3 (popR64Effect 0x1240f3 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[72]
    (.letOp (n := 75) (.out 0x1240f3 (popR64Effect 0x1240f3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[72]
    (.letOp (n := 76) (.exec 0x1240f3 (PopPre 0x1240f3) (popR64Effect 0x1240f3 2 14) (Reg.operands [.gpr 4] [])) #v[72]
    (.letOp (n := 77) (.out 0x1240f5 (popR64Effect 0x1240f5 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[75]
    (.letOp (n := 78) (.out 0x1240f5 (popR64Effect 0x1240f5 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[75]
    (.letOp (n := 79) (.exec 0x1240f5 (PopPre 0x1240f5) (popR64Effect 0x1240f5 2 15) (Reg.operands [.gpr 4] [])) #v[75]
    (.letOp (n := 80) (.out 0x1240f7 (popR64Effect 0x1240f7 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[78]
    (.letOp (n := 81) (.out 0x1240f7 (popR64Effect 0x1240f7 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[78]
    (.letOp (n := 82) (.exec 0x1240f7 (PopPre 0x1240f7) (popR64Effect 0x1240f7 1 5) (Reg.operands [.gpr 4] [])) #v[78]
    (.terminate (.br ⟨.l1240f8, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 65), (4, 81), (5, 80), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 68), (13, 71), (14, 74), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩)))))))))))))))))))))))))))))))

def bytes_l1240c4 : List UInt8 :=
  [0x48, 0x8B, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x44, 0x89, 0x77, 0x04, 0x89, 0x47, 0x08, 0x44,
    0x89, 0x4F, 0x0C, 0x44, 0x89, 0x47, 0x10, 0x44, 0x89, 0x57, 0x14, 0x89, 0x57, 0x18, 0x89, 0x4F,
    0x1C, 0x89, 0x1F, 0x48, 0x81, 0xC4, 0x20, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D]

theorem code_l1240c4 : ∀ x ∈ codeRange 0x1240c4 bytes_l1240c4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x240c4 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1240f8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1240f8 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 54) (.out 0x1240f8 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x1240f8 (RetPre 0x1240f8) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56) (some ⟨53, by decide⟩)))))

def bytes_l1240f8 : List UInt8 :=
  [0xC3]

theorem code_l1240f8 : ∀ x ∈ codeRange 0x1240f8 bytes_l1240f8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x240f8 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124100 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124100 (pushR64Effect 0x124100 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 14]
    (.letOp (n := 54) (.exec 0x124100 (PushPre 0x124100 2) (pushR64Effect 0x124100 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 55) (.out 0x124102 (pushR64Effect 0x124102 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x124102 (PushPre 0x124102 1) (pushR64Effect 0x124102 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x124103 (pushR64Effect 0x124103 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[55, 0]
    (.letOp (n := 58) (.exec 0x124103 (PushPre 0x124103 1) (pushR64Effect 0x124103 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[55, 0]
    (.letOp (n := 59) (.out 0x124104 (movR64M64Effect 0x124104 1 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 60) (.exec 0x124104 (LoadPre 0x124104 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x124104 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124104 1 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 61) (.out 0x124108 (leaR64Effect 0x124108 0 (.base 1 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 62) (.exec 0x124108 (fun s => s.RIP = 0x124108) (leaR64Effect 0x124108 0 (.base 1 (.d8 0x1))) (Reg.operands [.gpr 1] [])) #v[59]
    (.letOp (n := 63) (.out 0x12410c (cmpR64R64Effect 0x12410c 1 6) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 6] []) (.flag .ZF)) #v[59, 6]
    (.letOp (n := 64) (.exec 0x12410c (fun s => s.RIP = 0x12410c) (cmpR64R64Effect 0x12410c 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[59, 6]
    (.letOp (n := 65) (.pure (condOp 4)) #v[63]
    (.terminate (.condBr (Fin.last 65) ⟨.l12411a, RegMap.args [(0, 61), (1, 59), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ ⟨.l124111, RegMap.args [(0, 61), (1, 59), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l124100 : List UInt8 :=
  [0x41, 0x56, 0x53, 0x50, 0x48, 0x8B, 0x4F, 0x10, 0x48, 0x8D, 0x41, 0x01, 0x48, 0x39, 0xF1, 0x74,
    0x09]

theorem code_l124100 : ∀ x ∈ codeRange 0x124100 bytes_l124100, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24100 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124111 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124111 (cmpR64R64Effect 0x124111 0 6) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 6] []) (.flag .ZF)) #v[0, 6]
    (.letOp (n := 54) (.exec 0x124111 (fun s => s.RIP = 0x124111) (cmpR64R64Effect 0x124111 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[0, 6]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1241bf, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l12411a, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l124111 : List UInt8 :=
  [0x48, 0x39, 0xF0, 0x0F, 0x85, 0xA5, 0x00, 0x00, 0x00]

theorem code_l124111 : ∀ x ∈ codeRange 0x124111 bytes_l124111, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24111 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12411a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12411a (cmpR64R64Effect 0x12411a 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[6, 1]
    (.letOp (n := 54) (.out 0x12411a (cmpR64R64Effect 0x12411a 6 1) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 1] []) (.flag .ZF)) #v[6, 1]
    (.letOp (n := 55) (.exec 0x12411a (fun s => s.RIP = 0x12411a) (cmpR64R64Effect 0x12411a 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[6, 1]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l12417c, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l12411f, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l12411a : List UInt8 :=
  [0x48, 0x39, 0xCE, 0x76, 0x5D]

theorem code_l12411a : ∀ x ∈ codeRange 0x12411a bytes_l12411a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2411a 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12411f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12411f (StorePre 0x12411f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x12411f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12411f 0 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[0, 7]
    (.letOp (n := 54) (.out 0x124123 (movR64M64Effect 0x124123 1 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 55) (.exec 0x124123 (LoadPre 0x124123 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x124123 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124123 1 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 56) (.out 0x124127 (movR64M64Effect 0x124127 0 (.base 7 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 57) (.exec 0x124127 (LoadPre 0x124127 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x124127 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124127 0 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 58) (.exec 0x12412b (StorePre 0x12412b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x12412b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12412b 0 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[56, 7]
    (.letOp (n := 59) (.out 0x12412f (testR64R64Effect 0x12412f 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[54, 54]
    (.letOp (n := 60) (.exec 0x12412f (fun s => s.RIP = 0x12412f) (testR64R64Effect 0x12412f 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[54, 54]
    (.letOp (n := 61) (.pure (condOp 4)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l12418c, RegMap.args [(0, 56), (1, 54), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l124134, RegMap.args [(0, 56), (1, 54), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l12411f : List UInt8 :=
  [0x48, 0x89, 0x47, 0x10, 0x48, 0x8B, 0x4F, 0x08, 0x48, 0x8B, 0x47, 0x20, 0x48, 0x89, 0x47, 0x18,
    0x48, 0x85, 0xC9, 0x74, 0x58]

theorem code_l12411f : ∀ x ∈ codeRange 0x12411f bytes_l12411f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2411f 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124134 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124134 (cmpR64Imm8Effect 0x124134 1 0x7) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[1]
    (.letOp (n := 54) (.out 0x124134 (cmpR64Imm8Effect 0x124134 1 0x7) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[1]
    (.letOp (n := 55) (.exec 0x124134 (fun s => s.RIP = 0x124134) (cmpR64Imm8Effect 0x124134 1 0x7) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 56) (.pure (condOp 7)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l12419e, RegMap.args [(0, 0), (1, 1), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l12413a, RegMap.args [(0, 0), (1, 1), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l124134 : List UInt8 :=
  [0x48, 0x83, 0xF9, 0x07, 0x77, 0x64]

theorem code_l124134 : ∀ x ∈ codeRange 0x124134 bytes_l124134, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24134 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12413a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12413a (StorePre 0x12413a 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12413a + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x12413a (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x124142 (movR64M64Effect 0x124142 6 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 55) (.exec 0x124142 (LoadPre 0x124142 (fun s => AddrMode.addr (.base 7 .none) s (0x124142 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x124142 6 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 56) (.out 0x124145 (movR64R64Effect 0x124145 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 57) (.exec 0x124145 (fun s => s.RIP = 0x124145) (movR64R64Effect 0x124145 2 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x124148 (movR64R64Effect 0x124148 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 59) (.exec 0x124148 (fun s => s.RIP = 0x124148) (movR64R64Effect 0x124148 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 60) (.out 0x12414b (movR64R64Effect 0x12414b 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[56]
    (.letOp (n := 61) (.exec 0x12414b (fun s => s.RIP = 0x12414b) (movR64R64Effect 0x12414b 7 2) (Reg.operands [.gpr 2] [])) #v[56]
    (.letOp (n := 62) (.out 0x12414e (movR64R64Effect 0x12414e 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 63) (.exec 0x12414e (fun s => s.RIP = 0x12414e) (movR64R64Effect 0x12414e 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 64) (.out 0x124151 (movR64R64Effect 0x124151 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[0]
    (.letOp (n := 65) (.exec 0x124151 (fun s => s.RIP = 0x124151) (movR64R64Effect 0x124151 3 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 66) (.out 0x124154 (callEffect (callMemPtr 0x124154 (.rip 0xdfc76)) (0x124154 + BitVec.ofNat 64 (callMemLen (.rip 0xdfc76)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 67) (.exec 0x124154 (GoesTo (CallMemPre 0x124154 (.rip 0xdfc76)) (callEffect (callMemPtr 0x124154 (.rip 0xdfc76)) (0x124154 + BitVec.ofNat 64 (callMemLen (.rip 0xdfc76)))) 0x12a820) (callEffect (callMemPtr 0x124154 (.rip 0xdfc76)) (0x124154 + BitVec.ofNat 64 (callMemLen (.rip 0xdfc76)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.const ⟨64, 0x12415a⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 0), (1, 1), (2, 62), (3, 64), (4, 66), (5, 5), (6, 54), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l12415a, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l12413a : List UInt8 :=
  [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x37, 0x48, 0x89, 0xE2, 0x49, 0x89,
    0xFE, 0x48, 0x89, 0xD7, 0x48, 0x89, 0xCA, 0x48, 0x89, 0xC3, 0xFF, 0x15, 0x76, 0xFC, 0x0D, 0x00]

theorem code_l12413a : ∀ x ∈ codeRange 0x12413a bytes_l12413a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2413a 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12415a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12415a (movR64R64Effect 0x12415a 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x12415a (fun s => s.RIP = 0x12415a) (movR64R64Effect 0x12415a 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x12415d (movR64M64Effect 0x12415d 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x12415d (LoadPre 0x12415d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12415d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12415d 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x124161 (StorePre 0x124161 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x124161 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124161 2 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 58) (.exec 0x124165 (StorePre 0x124165 7 (fun s => AddrMode.addr (.base 14 .none) s (0x124165 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x124165 (.base 14 .none) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.exec 0x12416c (StorePre 0x12416c 8 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12416c + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x12416c (.base 14 (.d8 0x8)) 0x0) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 60) (.out 0x124174 (addR64Imm8Effect 0x124174 4 0x8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x124174 (fun s => s.RIP = 0x124174) (addR64Imm8Effect 0x124174 4 0x8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x124178 (popR64Effect 0x124178 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[60]
    (.letOp (n := 63) (.out 0x124178 (popR64Effect 0x124178 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x124178 (PopPre 0x124178) (popR64Effect 0x124178 1 3) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x124179 (popR64Effect 0x124179 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[63]
    (.letOp (n := 66) (.out 0x124179 (popR64Effect 0x124179 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x124179 (PopPre 0x124179) (popR64Effect 0x124179 2 14) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x12417b (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[66]
    (.letOp (n := 69) (.out 0x12417b (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x12417b (RetPre 0x12417b) (retEffect) (Reg.operands [.gpr 4] [])) #v[66]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 55), (3, 62), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71) (some ⟨68, by decide⟩))))))))))))))))))))

def bytes_l12415a : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x8B, 0x14, 0x24, 0x49, 0x89, 0x56, 0x20, 0x49, 0xC7, 0x06, 0x01, 0x00,
    0x00, 0x00, 0x49, 0xC7, 0x46, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0x83, 0xC4, 0x08, 0x5B, 0x41,
    0x5E, 0xC3]

theorem code_l12415a : ∀ x ∈ codeRange 0x12415a bytes_l12415a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2415a 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12417c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12417c (movR64M64Effect 0x12417c 0 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x12417c (LoadPre 0x12417c (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x12417c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12417c 0 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x124180 (movR64M64Effect 0x124180 2 (.base 7 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 56) (.exec 0x124180 (LoadPre 0x124180 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x124180 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124180 2 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x124184 (addR64Imm8Effect 0x124184 4 0x8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x124184 (fun s => s.RIP = 0x124184) (addR64Imm8Effect 0x124184 4 0x8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x124188 (popR64Effect 0x124188 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[57]
    (.letOp (n := 60) (.out 0x124188 (popR64Effect 0x124188 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 61) (.exec 0x124188 (PopPre 0x124188) (popR64Effect 0x124188 1 3) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 62) (.out 0x124189 (popR64Effect 0x124189 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[60]
    (.letOp (n := 63) (.out 0x124189 (popR64Effect 0x124189 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x124189 (PopPre 0x124189) (popR64Effect 0x124189 2 14) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x12418b (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[63]
    (.letOp (n := 66) (.out 0x12418b (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x12418b (RetPre 0x12418b) (retEffect) (Reg.operands [.gpr 4] [])) #v[63]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 55), (3, 59), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68) (some ⟨65, by decide⟩)))))))))))))))))

def bytes_l12417c : List UInt8 :=
  [0x48, 0x8B, 0x47, 0x18, 0x48, 0x8B, 0x57, 0x20, 0x48, 0x83, 0xC4, 0x08, 0x5B, 0x41, 0x5E, 0xC3]

theorem code_l12417c : ∀ x ∈ codeRange 0x12417c bytes_l12417c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2417c 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12418c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12418c (StorePre 0x12418c 8 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x12418c + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x12418c (.base 7 (.d8 0x20)) 0x0) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 54) (.out 0x124194 (xorR32R32Effect 0x124194 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 55) (.exec 0x124194 (fun s => s.RIP = 0x124194) (xorR32R32Effect 0x124194 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 56) (.out 0x124196 (addR64Imm8Effect 0x124196 4 0x8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x124196 (fun s => s.RIP = 0x124196) (addR64Imm8Effect 0x124196 4 0x8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x12419a (popR64Effect 0x12419a 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[56]
    (.letOp (n := 59) (.out 0x12419a (popR64Effect 0x12419a 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x12419a (PopPre 0x12419a) (popR64Effect 0x12419a 1 3) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x12419b (popR64Effect 0x12419b 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[59]
    (.letOp (n := 62) (.out 0x12419b (popR64Effect 0x12419b 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x12419b (PopPre 0x12419b) (popR64Effect 0x12419b 2 14) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x12419d (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[62]
    (.letOp (n := 65) (.out 0x12419d (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x12419d (RetPre 0x12419d) (retEffect) (Reg.operands [.gpr 4] [])) #v[62]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 54), (3, 58), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67) (some ⟨64, by decide⟩))))))))))))))))

def bytes_l12418c : List UInt8 :=
  [0x48, 0xC7, 0x47, 0x20, 0x00, 0x00, 0x00, 0x00, 0x31, 0xD2, 0x48, 0x83, 0xC4, 0x08, 0x5B, 0x41,
    0x5E, 0xC3]

theorem code_l12418c : ∀ x ∈ codeRange 0x12418c bytes_l12418c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2418c 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12419e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12419e (movR64M64Effect 0x12419e 6 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 54) (.exec 0x12419e (LoadPre 0x12419e (fun s => AddrMode.addr (.base 7 .none) s (0x12419e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12419e 6 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1241a1 (addR64Imm8Effect 0x1241a1 1 0xf8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x1241a1 (fun s => s.RIP = 0x1241a1) (addR64Imm8Effect 0x1241a1 1 0xf8) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x1241a5 (movR64M64Effect 0x1241a5 2 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 58) (.exec 0x1241a5 (LoadPre 0x1241a5 (fun s => AddrMode.addr (.base 6 .none) s (0x1241a5 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1241a5 2 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 59) (.out 0x1241a8 (addR64Imm8Effect 0x1241a8 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 60) (.exec 0x1241a8 (fun s => s.RIP = 0x1241a8) (addR64Imm8Effect 0x1241a8 6 0x8) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 61) (.exec 0x1241ac (StorePre 0x1241ac 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x1241ac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1241ac 2 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[57, 7]
    (.letOp (n := 62) (.exec 0x1241b0 (StorePre 0x1241b0 3 (fun s => AddrMode.addr (.base 7 .none) s (0x1241b0 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1241b0 6 (.base 7 .none)) (Reg.operands [.gpr 6, .gpr 7] [])) #v[59, 7]
    (.letOp (n := 63) (.exec 0x1241b3 (StorePre 0x1241b3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1241b3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1241b3 1 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[55, 7]
    (.letOp (n := 64) (.out 0x1241b7 (addR64Imm8Effect 0x1241b7 4 0x8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x1241b7 (fun s => s.RIP = 0x1241b7) (addR64Imm8Effect 0x1241b7 4 0x8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x1241bb (popR64Effect 0x1241bb 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[64]
    (.letOp (n := 67) (.out 0x1241bb (popR64Effect 0x1241bb 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x1241bb (PopPre 0x1241bb) (popR64Effect 0x1241bb 1 3) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x1241bc (popR64Effect 0x1241bc 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[67]
    (.letOp (n := 70) (.out 0x1241bc (popR64Effect 0x1241bc 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x1241bc (PopPre 0x1241bc) (popR64Effect 0x1241bc 2 14) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x1241be (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[70]
    (.letOp (n := 73) (.out 0x1241be (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x1241be (RetPre 0x1241be) (retEffect) (Reg.operands [.gpr 4] [])) #v[70]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 55), (2, 57), (3, 66), (4, 73), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75) (some ⟨72, by decide⟩))))))))))))))))))))))))

def bytes_l12419e : List UInt8 :=
  [0x48, 0x8B, 0x37, 0x48, 0x83, 0xC1, 0xF8, 0x48, 0x8B, 0x16, 0x48, 0x83, 0xC6, 0x08, 0x48, 0x89,
    0x57, 0x20, 0x48, 0x89, 0x37, 0x48, 0x89, 0x4F, 0x08, 0x48, 0x83, 0xC4, 0x08, 0x5B, 0x41, 0x5E,
    0xC3]

theorem code_l12419e : ∀ x ∈ codeRange 0x12419e bytes_l12419e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2419e 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1241bf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1241bf (movR32Imm32Effect 0x1241bf 5 6 0x41) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x1241bf (fun s => s.RIP = 0x1241bf) (movR32Imm32Effect 0x1241bf 5 6 0x41) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1241c4 (movR64Imm32Effect 0x1241c4 7 0x203400) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x1241c4 (fun s => s.RIP = 0x1241c4) (movR64Imm32Effect 0x1241c4 7 0x203400) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1241cb (movR64Imm32Effect 0x1241cb 2 0x203448) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1241cb (fun s => s.RIP = 0x1241cb) (movR64Imm32Effect 0x1241cb 2 0x203448) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1241d2 (callEffect (fun _ => 0x129750) 0x1241d7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1241d2 (PushPre 0x1241d2 5) (callEffect (fun _ => 0x129750) 0x1241d7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1241d7⟩) #v[]
    (.terminate (.call ⟨.l129750, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)] 62⟩ { target := .l1241d7, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1241bf : List UInt8 :=
  [0xBE, 0x41, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x00, 0x34, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0x48,
    0x34, 0x20, 0x00, 0xE8, 0x79, 0x55, 0x00, 0x00]

theorem code_l1241bf : ∀ x ∈ codeRange 0x1241bf bytes_l1241bf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x241bf 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1241d7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1241d7 (fun s => s.RIP = 0x1241d7) (fun _ => nopEffect 0x1241d7 9) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1241e0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l1241d7 : List UInt8 :=
  [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l1241d7 : ∀ x ∈ codeRange 0x1241d7 bytes_l1241d7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x241d7 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1241e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1241e0 (pushR64Effect 0x1241e0 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 14]
    (.letOp (n := 54) (.exec 0x1241e0 (PushPre 0x1241e0 2) (pushR64Effect 0x1241e0 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 55) (.out 0x1241e2 (pushR64Effect 0x1241e2 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x1241e2 (PushPre 0x1241e2 1) (pushR64Effect 0x1241e2 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x1241e3 (pushR64Effect 0x1241e3 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[55, 0]
    (.letOp (n := 58) (.exec 0x1241e3 (PushPre 0x1241e3 1) (pushR64Effect 0x1241e3 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[55, 0]
    (.letOp (n := 59) (.out 0x1241e4 (movR64R64Effect 0x1241e4 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 60) (.exec 0x1241e4 (fun s => s.RIP = 0x1241e4) (movR64R64Effect 0x1241e4 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 61) (.out 0x1241e7 (testR64R64Effect 0x1241e7 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 62) (.exec 0x1241e7 (fun s => s.RIP = 0x1241e7) (testR64R64Effect 0x1241e7 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 63) (.pure (condOp 4)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l12420e, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l1241ec, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l1241e0 : List UInt8 :=
  [0x41, 0x56, 0x53, 0x50, 0x48, 0x89, 0xFB, 0x48, 0x85, 0xD2, 0x74, 0x22]

theorem code_l1241e0 : ∀ x ∈ codeRange 0x1241e0 bytes_l1241e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x241e0 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1241ec : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1241ec (cmpR64Imm8Effect 0x1241ec 2 0x7) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 54) (.out 0x1241ec (cmpR64Imm8Effect 0x1241ec 2 0x7) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 55) (.exec 0x1241ec (fun s => s.RIP = 0x1241ec) (cmpR64Imm8Effect 0x1241ec 2 0x7) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.pure (condOp 7)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l124237, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l1241f2, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1241ec : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x07, 0x77, 0x45]

theorem code_l1241ec : ∀ x ∈ codeRange 0x1241ec bytes_l1241ec, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x241ec 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1241f2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1241f2 (StorePre 0x1241f2 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1241f2 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1241f2 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x1241fa (movR64R64Effect 0x1241fa 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x1241fa (fun s => s.RIP = 0x1241fa) (movR64R64Effect 0x1241fa 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1241fd (callEffect (callMemPtr 0x1241fd (.rip 0xdfbcd)) (0x1241fd + BitVec.ofNat 64 (callMemLen (.rip 0xdfbcd)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x1241fd (GoesTo (CallMemPre 0x1241fd (.rip 0xdfbcd)) (callEffect (callMemPtr 0x1241fd (.rip 0xdfbcd)) (0x1241fd + BitVec.ofNat 64 (callMemLen (.rip 0xdfbcd)))) 0x12a820) (callEffect (callMemPtr 0x1241fd (.rip 0xdfbcd)) (0x1241fd + BitVec.ofNat 64 (callMemLen (.rip 0xdfbcd)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.const ⟨64, 0x124203⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ { target := .l124203, kept := #v[], arity := rfl, guard := some (Fin.last 58) })))))))

def bytes_l1241f2 : List UInt8 :=
  [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE7, 0xFF, 0x15, 0xCD, 0xFB, 0x0D,
    0x00]

theorem code_l1241f2 : ∀ x ∈ codeRange 0x1241f2 bytes_l1241f2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x241f2 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124203 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124203 (movR64M64Effect 0x124203 14 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x124203 (LoadPre 0x124203 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124203 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124203 14 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124207 (movR32Imm32Effect 0x124207 5 6 0x1) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x124207 (fun s => s.RIP = 0x124207) (movR32Imm32Effect 0x124207 5 6 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l124211, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l124203 : List UInt8 :=
  [0x4C, 0x8B, 0x34, 0x24, 0xBE, 0x01, 0x00, 0x00, 0x00, 0xEB, 0x03]

theorem code_l124203 : ∀ x ∈ codeRange 0x124203 bytes_l124203, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24203 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12420e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12420e (xorR32R32Effect 0x12420e 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 54) (.exec 0x12420e (fun s => s.RIP = 0x12420e) (xorR32R32Effect 0x12420e 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.terminate (.br ⟨.l124211, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l12420e : List UInt8 :=
  [0x45, 0x31, 0xF6]

theorem code_l12420e : ∀ x ∈ codeRange 0x12420e bytes_l12420e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2420e 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124211 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124211 (xorR32R32Effect 0x124211 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 54) (.exec 0x124211 (fun s => s.RIP = 0x124211) (xorR32R32Effect 0x124211 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.terminate (.br ⟨.l124213, RegMap.args [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l124211 : List UInt8 :=
  [0x31, 0xC9]

theorem code_l124211 : ∀ x ∈ codeRange 0x124211 bytes_l124211, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24211 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124213 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124213 (xorR32R32Effect 0x124213 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x124213 (fun s => s.RIP = 0x124213) (xorR32R32Effect 0x124213 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.terminate (.br ⟨.l124215, RegMap.args [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l124213 : List UInt8 :=
  [0x31, 0xD2]

theorem code_l124213 : ∀ x ∈ codeRange 0x124213 bytes_l124213, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24213 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124215 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124215 (StorePre 0x124215 3 (fun s => AddrMode.addr (.base 3 .none) s (0x124215 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x124215 6 (.base 3 .none)) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 54) (.exec 0x124218 (StorePre 0x124218 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x124218 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124218 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 55) (.exec 0x12421c (StorePre 0x12421c 8 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x12421c + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x12421c (.base 3 (.d8 0x10)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.exec 0x124224 (StorePre 0x124224 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x124224 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124224 14 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[14, 3]
    (.letOp (n := 57) (.exec 0x124228 (StorePre 0x124228 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x124228 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124228 1 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 58) (.out 0x12422c (movR64R64Effect 0x12422c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 59) (.exec 0x12422c (fun s => s.RIP = 0x12422c) (movR64R64Effect 0x12422c 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 60) (.out 0x12422f (addR64Imm8Effect 0x12422f 4 0x8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x12422f (fun s => s.RIP = 0x12422f) (addR64Imm8Effect 0x12422f 4 0x8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x124233 (popR64Effect 0x124233 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[60]
    (.letOp (n := 63) (.out 0x124233 (popR64Effect 0x124233 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x124233 (PopPre 0x124233) (popR64Effect 0x124233 1 3) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x124234 (popR64Effect 0x124234 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[63]
    (.letOp (n := 66) (.out 0x124234 (popR64Effect 0x124234 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x124234 (PopPre 0x124234) (popR64Effect 0x124234 2 14) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x124236 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[66]
    (.letOp (n := 69) (.out 0x124236 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x124236 (RetPre 0x124236) (retEffect) (Reg.operands [.gpr 4] [])) #v[66]
    (.terminate (.ret (RegMap.args [(0, 58), (1, 1), (2, 2), (3, 62), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71) (some ⟨68, by decide⟩))))))))))))))))))))

def bytes_l124215 : List UInt8 :=
  [0x48, 0x89, 0x33, 0x48, 0x89, 0x53, 0x08, 0x48, 0xC7, 0x43, 0x10, 0x00, 0x00, 0x00, 0x00, 0x4C,
    0x89, 0x73, 0x18, 0x48, 0x89, 0x4B, 0x20, 0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x08, 0x5B, 0x41,
    0x5E, 0xC3]

theorem code_l124215 : ∀ x ∈ codeRange 0x124215 bytes_l124215, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24215 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124237 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124237 (leaR64Effect 0x124237 0 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x124237 (fun s => s.RIP = 0x124237) (leaR64Effect 0x124237 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x12423b (movR64R64Effect 0x12423b 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 56) (.exec 0x12423b (fun s => s.RIP = 0x12423b) (movR64R64Effect 0x12423b 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 57) (.out 0x12423e (movR64M64Effect 0x12423e 14 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 58) (.exec 0x12423e (LoadPre 0x12423e (fun s => AddrMode.addr (.base 6 .none) s (0x12423e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12423e 14 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x124241 (addR64Imm8Effect 0x124241 1 0xf8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 60) (.out 0x124241 (addR64Imm8Effect 0x124241 1 0xf8) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[55]
    (.letOp (n := 61) (.exec 0x124241 (fun s => s.RIP = 0x124241) (addR64Imm8Effect 0x124241 1 0xf8) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 62) (.pure (condOp 4)) #v[60]
    (.terminate (.condBr (Fin.last 62) ⟨.l12426f, RegMap.args [(0, 53), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ ⟨.l124247, RegMap.args [(0, 53), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l124237 : List UInt8 :=
  [0x48, 0x8D, 0x46, 0x08, 0x48, 0x89, 0xD1, 0x4C, 0x8B, 0x36, 0x48, 0x83, 0xC1, 0xF8, 0x74, 0x28]

theorem code_l124237 : ∀ x ∈ codeRange 0x124237 bytes_l124237, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24237 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124247 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124247 (cmpR64Imm8Effect 0x124247 2 0xf) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 54) (.out 0x124247 (cmpR64Imm8Effect 0x124247 2 0xf) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 55) (.exec 0x124247 (fun s => s.RIP = 0x124247) (cmpR64Imm8Effect 0x124247 2 0xf) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.pure (condOp 7)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l124278, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l12424d, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l124247 : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x0F, 0x77, 0x2B]

theorem code_l124247 : ∀ x ∈ codeRange 0x124247 bytes_l124247, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24247 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12424d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12424d (StorePre 0x12424d 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12424d + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x12424d (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x124255 (movR64R64Effect 0x124255 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x124255 (fun s => s.RIP = 0x124255) (movR64R64Effect 0x124255 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x124258 (movR64R64Effect 0x124258 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[0]
    (.letOp (n := 57) (.exec 0x124258 (fun s => s.RIP = 0x124258) (movR64R64Effect 0x124258 6 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 58) (.out 0x12425b (movR64R64Effect 0x12425b 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 59) (.exec 0x12425b (fun s => s.RIP = 0x12425b) (movR64R64Effect 0x12425b 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 60) (.out 0x12425e (callEffect (callMemPtr 0x12425e (.rip 0xdfb6c)) (0x12425e + BitVec.ofNat 64 (callMemLen (.rip 0xdfb6c)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x12425e (GoesTo (CallMemPre 0x12425e (.rip 0xdfb6c)) (callEffect (callMemPtr 0x12425e (.rip 0xdfb6c)) (0x12425e + BitVec.ofNat 64 (callMemLen (.rip 0xdfb6c)))) 0x12a820) (callEffect (callMemPtr 0x12425e (.rip 0xdfb6c)) (0x12425e + BitVec.ofNat 64 (callMemLen (.rip 0xdfb6c)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x124264⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 0), (1, 1), (2, 58), (3, 3), (4, 60), (5, 5), (6, 56), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ { target := .l124264, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l12424d : List UInt8 :=
  [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE7, 0x48, 0x89, 0xC6, 0x48, 0x89,
    0xCA, 0xFF, 0x15, 0x6C, 0xFB, 0x0D, 0x00]

theorem code_l12424d : ∀ x ∈ codeRange 0x12424d bytes_l12424d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2424d 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124264 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124264 (movR64M64Effect 0x124264 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x124264 (LoadPre 0x124264 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124264 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124264 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124268 (movR32Imm32Effect 0x124268 5 6 0x1) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x124268 (fun s => s.RIP = 0x124268) (movR32Imm32Effect 0x124268 5 6 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l124213, RegMap.args [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l124264 : List UInt8 :=
  [0x48, 0x8B, 0x0C, 0x24, 0xBE, 0x01, 0x00, 0x00, 0x00, 0xEB, 0xA4]

theorem code_l124264 : ∀ x ∈ codeRange 0x124264 bytes_l124264, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24264 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12426f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12426f (xorR32R32Effect 0x12426f 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 54) (.exec 0x12426f (fun s => s.RIP = 0x12426f) (xorR32R32Effect 0x12426f 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.out 0x124271 (xorR32R32Effect 0x124271 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 56) (.exec 0x124271 (fun s => s.RIP = 0x124271) (xorR32R32Effect 0x124271 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 57) (.out 0x124273 (movR64R64Effect 0x124273 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[0]
    (.letOp (n := 58) (.exec 0x124273 (fun s => s.RIP = 0x124273) (movR64R64Effect 0x124273 6 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l124215, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l12426f : List UInt8 :=
  [0x31, 0xC9, 0x31, 0xD2, 0x48, 0x89, 0xC6, 0xEB, 0x9D]

theorem code_l12426f : ∀ x ∈ codeRange 0x12426f bytes_l12426f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2426f 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124278 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124278 (addR64Imm8Effect 0x124278 2 0xf0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 54) (.exec 0x124278 (fun s => s.RIP = 0x124278) (addR64Imm8Effect 0x124278 2 0xf0) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x12427c (movR64M64Effect 0x12427c 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 56) (.exec 0x12427c (LoadPre 0x12427c (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x12427c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12427c 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x124280 (addR64Imm8Effect 0x124280 6 0x10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 58) (.exec 0x124280 (fun s => s.RIP = 0x124280) (addR64Imm8Effect 0x124280 6 0x10) (Reg.operands [.gpr 6] [])) #v[6]
    (.terminate (.br ⟨.l124215, RegMap.args [(1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l124278 : List UInt8 :=
  [0x48, 0x83, 0xC2, 0xF0, 0x48, 0x8B, 0x4E, 0x08, 0x48, 0x83, 0xC6, 0x10, 0xEB, 0x8F]

theorem code_l124278 : ∀ x ∈ codeRange 0x124278 bytes_l124278, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24278 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124290 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124290 (pushR64Effect 0x124290 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x124290 (PushPre 0x124290 1) (pushR64Effect 0x124290 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x124291 (pushR64Effect 0x124291 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x124291 (PushPre 0x124291 2) (pushR64Effect 0x124291 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x124293 (pushR64Effect 0x124293 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[55, 3]
    (.letOp (n := 58) (.exec 0x124293 (PushPre 0x124293 1) (pushR64Effect 0x124293 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 59) (.out 0x124294 (subR64Imm8Effect 0x124294 4 0x60) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x124294 (fun s => s.RIP = 0x124294) (subR64Imm8Effect 0x124294 4 0x60) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x124298 (movR64R64Effect 0x124298 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 62) (.exec 0x124298 (fun s => s.RIP = 0x124298) (movR64R64Effect 0x124298 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.out 0x12429b (movR32M32LowEffect 0x12429b 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 64) (.exec 0x12429b (LoadPre 0x12429b (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x12429b + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12429b 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x12429e (cmpR32M32Effect 0x12429e 3 0 (.base 6 (.d8 0x1c))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[63, 6]
    (.letOp (n := 66) (.out 0x12429e (cmpR32M32Effect 0x12429e 3 0 (.base 6 (.d8 0x1c))) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 6] []) (.flag .ZF)) #v[63, 6]
    (.letOp (n := 67) (.exec 0x12429e (LoadPre 0x12429e (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x12429e + BitVec.ofNat 64 3)) 4) (cmpR32M32Effect 0x12429e 3 0 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[63, 6]
    (.letOp (n := 68) (.pure (condOp 6)) #v[65, 66]
    (.terminate (.condBr (Fin.last 68) ⟨.l124322, RegMap.args [(0, 63), (1, 1), (2, 2), (3, 61), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 65), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ ⟨.l1242a3, RegMap.args [(0, 63), (1, 1), (2, 2), (3, 61), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 65), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l124290 : List UInt8 :=
  [0x55, 0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x60, 0x48, 0x89, 0xFB, 0x8B, 0x46, 0x18, 0x3B, 0x46,
    0x1C, 0x76, 0x7F]

theorem code_l124290 : ∀ x ∈ codeRange 0x124290 bytes_l124290, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24290 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1242a3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1242a3 (movR32R32Effect 0x1242a3 2 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 54) (.exec 0x1242a3 (fun s => s.RIP = 0x1242a3) (movR32R32Effect 0x1242a3 2 5 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x1242a5 (movR32R32Effect 0x1242a5 3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[1]
    (.letOp (n := 56) (.exec 0x1242a5 (fun s => s.RIP = 0x1242a5) (movR32R32Effect 0x1242a5 3 14 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x1242a8 (movR64M64Effect 0x1242a8 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 58) (.exec 0x1242a8 (LoadPre 0x1242a8 (fun s => AddrMode.addr (.base 6 .none) s (0x1242a8 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1242a8 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x1242ab (movR64M64Effect 0x1242ab 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 60) (.exec 0x1242ab (LoadPre 0x1242ab (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1242ab + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1242ab 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x1242af (movzxR32M8Effect 0x1242af 4 2 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 62) (.exec 0x1242af (LoadPre 0x1242af (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1242af + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1242af 4 2 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x1242b3 (movR64M64Effect 0x1242b3 7 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 64) (.exec 0x1242b3 (LoadPre 0x1242b3 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1242b3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1242b3 7 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.exec 0x1242b7 (StorePre 0x1242b7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1242b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242b7 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x1242bc (movR64M64Effect 0x1242bc 6 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 67) (.exec 0x1242bc (LoadPre 0x1242bc (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1242bc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1242bc 6 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 68) (.exec 0x1242c0 (StorePre 0x1242c0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1242c0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242c0 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.exec 0x1242c5 (StorePre 0x1242c5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1242c5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242c5 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 70) (.exec 0x1242ca (StorePre 0x1242ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1242ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242ca 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 71) (.exec 0x1242cf (StorePre 0x1242cf 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1242cf + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1242cf 4 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 72) (.out 0x1242d3 (movR64R64Effect 0x1242d3 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 73) (.exec 0x1242d3 (fun s => s.RIP = 0x1242d3) (movR64R64Effect 0x1242d3 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x1242d6 (leaR64Effect 0x1242d6 6 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 75) (.exec 0x1242d6 (fun s => s.RIP = 0x1242d6) (leaR64Effect 0x1242d6 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x1242db (callEffect (fun _ => 0x124430) 0x1242e0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 77) (.exec 0x1242db (PushPre 0x1242db 5) (callEffect (fun _ => 0x124430) 0x1242e0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.const ⟨64, 0x1242e0⟩) #v[]
    (.terminate (.call ⟨.l124430, RegMap.args [(0, 57), (1, 59), (2, 61), (3, 3), (4, 76), (5, 53), (6, 74), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩ { target := .l1242e0, kept := #v[], arity := rfl, guard := some (Fin.last 78) })))))))))))))))))))))))))))

def bytes_l1242a3 : List UInt8 :=
  [0x89, 0xD5, 0x41, 0x89, 0xCE, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x0F, 0xB6, 0x56, 0x20,
    0x48, 0x8B, 0x7E, 0x18, 0x48, 0x89, 0x7C, 0x24, 0x50, 0x48, 0x8B, 0x76, 0x10, 0x48, 0x89, 0x74,
    0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x89, 0x4C, 0x24, 0x40, 0x88, 0x54, 0x24, 0x58,
    0x48, 0x89, 0xE7, 0x48, 0x8D, 0x74, 0x24, 0x38, 0xE8, 0x50, 0x01, 0x00, 0x00]

theorem code_l1242a3 : ∀ x ∈ codeRange 0x1242a3 bytes_l1242a3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x242a3 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1242e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1242e0 (movR32M32LowEffect 0x1242e0 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1242e0 (LoadPre 0x1242e0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1242e0 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1242e0 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1242e3 (movR64M64Effect 0x1242e3 0 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1242e3 (LoadPre 0x1242e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1242e3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1242e3 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1242e8 (cmpR32Imm8Effect 0x1242e8 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x1242e8 (fun s => s.RIP = 0x1242e8) (cmpR32Imm8Effect 0x1242e8 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l12432b, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1242ed, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1242e0 : List UInt8 :=
  [0x8B, 0x0C, 0x24, 0x48, 0x8B, 0x44, 0x24, 0x04, 0x83, 0xF9, 0x02, 0x75, 0x3E]

theorem code_l1242e0 : ∀ x ∈ codeRange 0x1242e0 bytes_l1242e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x242e0 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1242ed : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1242ed (leaR32Effect 0x1242ed 3 2 (.base 0 (.d8 0xea))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[0]
    (.letOp (n := 54) (.exec 0x1242ed (fun s => s.RIP = 0x1242ed) (leaR32Effect 0x1242ed 3 2 (.base 0 (.d8 0xea))) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1242f0 (movR32R32Effect 0x1242f0 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x1242f0 (fun s => s.RIP = 0x1242f0) (movR32R32Effect 0x1242f0 2 6 2) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.out 0x1242f2 (shlR8Effect 0x1242f2 4 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 58) (.exec 0x1242f2 (fun s => s.RIP = 0x1242f2) (shlR8Effect 0x1242f2 4 6 6) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x1242f6 (addR8Imm8Effect 0x1242f6 4 6 0x40) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[57]
    (.letOp (n := 60) (.exec 0x1242f6 (fun s => s.RIP = 0x1242f6) (addR8Imm8Effect 0x1242f6 4 6 0x40) (Reg.operands [.gpr 6] [])) #v[57]
    (.letOp (n := 61) (.out 0x1242fa (xorR32R32Effect 0x1242fa 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 62) (.exec 0x1242fa (fun s => s.RIP = 0x1242fa) (xorR32R32Effect 0x1242fa 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 63) (.out 0x1242fc (cmpR8Imm8Effect 0x1242fc 3 2 0x3) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[53]
    (.letOp (n := 64) (.exec 0x1242fc (fun s => s.RIP = 0x1242fc) (cmpR8Imm8Effect 0x1242fc 3 2 0x3) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 65) (.out 0x1242ff (movzxR32R8Effect 0x1242ff 4 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 66) (.exec 0x1242ff (fun s => s.RIP = 0x1242ff) (movzxR32R8Effect 0x1242ff 4 2 6) (Reg.operands [.gpr 6] [])) #v[59]
    (.letOp (n := 67) (.out 0x124303 (atFlags (condHolds 3) (cmovR32R32Effect 0x124303 3 2 1)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[65, 61, 63]
    (.letOp (n := 68) (.exec 0x124303 (fun s => s.RIP = 0x124303) (atFlags (condHolds 3) (cmovR32R32Effect 0x124303 3 2 1)) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[65, 61, 63]
    (.letOp (n := 69) (.out 0x124306 (cmpR8R8Effect 0x124306 3 2 5) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 5] []) (.flag .ZF)) #v[67, 5]
    (.letOp (n := 70) (.exec 0x124306 (fun s => s.RIP = 0x124306) (cmpR8R8Effect 0x124306 3 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[67, 5]
    (.letOp (n := 71) (.pure (condOp 5)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l124411, RegMap.args [(0, 0), (1, 61), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l12430f, RegMap.args [(0, 0), (1, 61), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l1242ed : List UInt8 :=
  [0x8D, 0x50, 0xEA, 0x89, 0xD6, 0x40, 0xC0, 0xE6, 0x06, 0x40, 0x80, 0xC6, 0x40, 0x31, 0xC9, 0x80,
    0xFA, 0x03, 0x40, 0x0F, 0xB6, 0xD6, 0x0F, 0x43, 0xD1, 0x40, 0x38, 0xEA, 0x0F, 0x85, 0x02, 0x01,
    0x00, 0x00]

theorem code_l1242ed : ∀ x ∈ codeRange 0x1242ed bytes_l1242ed, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x242ed 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12430f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12430f (fun s => s.RIP = 0x12430f) (movzxR32R8Effect 0x12430f 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (cutBlock 0x124312)

def bytes_l12430f : List UInt8 :=
  [0x0F, 0xB6, 0xC8, 0xFF, 0x24, 0xCD, 0x60, 0x34, 0x20, 0x00]

theorem code_l12430f : ∀ x ∈ codeRange 0x12430f bytes_l12430f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2430f 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124322 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124322 (StorePre 0x124322 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124322 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124322 (.base 3 (.d8 0x4)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l124414, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l124322 : List UInt8 :=
  [0xC6, 0x43, 0x04, 0x00, 0xE9, 0xE9, 0x00, 0x00, 0x00]

theorem code_l124322 : ∀ x ∈ codeRange 0x124322 bytes_l124322, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24322 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12432b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12432b (movR32M32LowEffect 0x12432b 2 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x12432b (LoadPre 0x12432b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x12432b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12432b 2 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x12432f (StorePre 0x12432f 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x12432f + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12432f 2 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x124332 (movR64M64Effect 0x124332 2 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 57) (.exec 0x124332 (LoadPre 0x124332 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x124332 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124332 2 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x124337 (StorePre 0x124337 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x124337 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124337 2 (.base 3 (.d8 0x2c))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x12433b (movR64M64Effect 0x12433b 2 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x12433b (LoadPre 0x12433b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x12433b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12433b 2 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x124340 (StorePre 0x124340 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x124340 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124340 2 (.base 3 (.d8 0x24))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x124344 (movR64M64Effect 0x124344 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x124344 (LoadPre 0x124344 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x124344 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124344 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x124349 (StorePre 0x124349 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x124349 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124349 2 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x12434d (movR64M64Effect 0x12434d 2 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 66) (.exec 0x12434d (LoadPre 0x12434d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x12434d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12434d 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x124352 (movR64M64Effect 0x124352 6 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x124352 (LoadPre 0x124352 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124352 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124352 6 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x124357 (StorePre 0x124357 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x124357 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124357 6 (.base 3 (.d8 0x14))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 70) (.exec 0x12435b (StorePre 0x12435b 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x12435b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12435b 2 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 71) (.exec 0x12435f (StorePre 0x12435f 2 (fun s => AddrMode.addr (.base 3 .none) s (0x12435f + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x12435f 1 (.base 3 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 72) (.exec 0x124361 (StorePre 0x124361 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124361 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124361 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.terminate (.br ⟨.l12441a, RegMap.args [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l12432b : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x34, 0x89, 0x53, 0x34, 0x48, 0x8B, 0x54, 0x24, 0x2C, 0x48, 0x89, 0x53, 0x2C,
    0x48, 0x8B, 0x54, 0x24, 0x24, 0x48, 0x89, 0x53, 0x24, 0x48, 0x8B, 0x54, 0x24, 0x1C, 0x48, 0x89,
    0x53, 0x1C, 0x48, 0x8B, 0x54, 0x24, 0x0C, 0x48, 0x8B, 0x74, 0x24, 0x14, 0x48, 0x89, 0x73, 0x14,
    0x48, 0x89, 0x53, 0x0C, 0x89, 0x0B, 0x48, 0x89, 0x43, 0x04, 0xE9, 0xB0, 0x00, 0x00, 0x00]

theorem code_l12432b : ∀ x ∈ codeRange 0x12432b bytes_l12432b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2432b 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124411 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124411 (StorePre 0x124411 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124411 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x124411 3 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.terminate (.br ⟨.l124414, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l124411 : List UInt8 :=
  [0x88, 0x4B, 0x04]

theorem code_l124411 : ∀ x ∈ codeRange 0x124411 bytes_l124411, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24411 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124414 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124414 (StorePre 0x124414 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124414 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124414 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l12441a, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l124414 : List UInt8 :=
  [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00]

theorem code_l124414 : ∀ x ∈ codeRange 0x124414 bytes_l124414, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24414 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12441a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12441a (movR64R64Effect 0x12441a 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x12441a (fun s => s.RIP = 0x12441a) (movR64R64Effect 0x12441a 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x12441d (addR64Imm8Effect 0x12441d 4 0x60) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x12441d (fun s => s.RIP = 0x12441d) (addR64Imm8Effect 0x12441d 4 0x60) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124421 (popR64Effect 0x124421 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x124421 (popR64Effect 0x124421 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x124421 (PopPre 0x124421) (popR64Effect 0x124421 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x124422 (popR64Effect 0x124422 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.out 0x124422 (popR64Effect 0x124422 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x124422 (PopPre 0x124422) (popR64Effect 0x124422 2 14) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x124424 (popR64Effect 0x124424 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[61]
    (.letOp (n := 64) (.out 0x124424 (popR64Effect 0x124424 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x124424 (PopPre 0x124424) (popR64Effect 0x124424 1 5) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x124425 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[64]
    (.letOp (n := 67) (.out 0x124425 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x124425 (RetPre 0x124425) (retEffect) (Reg.operands [.gpr 4] [])) #v[64]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69) (some ⟨66, by decide⟩))))))))))))))))))

def bytes_l12441a : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x60, 0x5B, 0x41, 0x5E, 0x5D, 0xC3]

theorem code_l12441a : ∀ x ∈ codeRange 0x12441a bytes_l12441a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2441a 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124430 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124430 (pushR64Effect 0x124430 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x124430 (PushPre 0x124430 1) (pushR64Effect 0x124430 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x124431 (pushR64Effect 0x124431 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x124431 (PushPre 0x124431 2) (pushR64Effect 0x124431 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x124433 (pushR64Effect 0x124433 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[55, 3]
    (.letOp (n := 58) (.exec 0x124433 (PushPre 0x124433 1) (pushR64Effect 0x124433 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 59) (.out 0x124434 (subR64Imm8Effect 0x124434 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x124434 (fun s => s.RIP = 0x124434) (subR64Imm8Effect 0x124434 4 0x40) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x124438 (movR64R64Effect 0x124438 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 62) (.exec 0x124438 (fun s => s.RIP = 0x124438) (movR64R64Effect 0x124438 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x12443b (movR64R64Effect 0x12443b 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 64) (.exec 0x12443b (fun s => s.RIP = 0x12443b) (movR64R64Effect 0x12443b 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 65) (.out 0x12443e (leaR64Effect 0x12443e 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 66) (.exec 0x12443e (fun s => s.RIP = 0x12443e) (leaR64Effect 0x12443e 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 67) (.out 0x124443 (movR32Imm32Effect 0x124443 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 68) (.exec 0x124443 (fun s => s.RIP = 0x124443) (movR32Imm32Effect 0x124443 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x124448 (callEffect (fun _ => 0x127b80) 0x12444d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 70) (.exec 0x124448 (PushPre 0x124448 5) (callEffect (fun _ => 0x127b80) 0x12444d) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 71) (.const ⟨64, 0x12444d⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 67), (3, 63), (4, 69), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l12444d, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l124430 : List UInt8 :=
  [0x55, 0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x40, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFB, 0x48, 0x8D,
    0x7C, 0x24, 0x08, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x33, 0x37, 0x00, 0x00]

theorem code_l124430 : ∀ x ∈ codeRange 0x124430 bytes_l124430, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24430 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12444d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12444d (movR32M32LowEffect 0x12444d 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12444d (LoadPre 0x12444d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12444d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12444d 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124451 (cmpR32Imm8Effect 0x124451 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124451 (fun s => s.RIP = 0x124451) (cmpR32Imm8Effect 0x124451 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124488, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124456, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12444d : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x83, 0xF8, 0x02, 0x75, 0x32]

theorem code_l12444d : ∀ x ∈ codeRange 0x12444d bytes_l12444d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2444d 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124456 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124456 (movR64M64Effect 0x124456 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124456 (LoadPre 0x124456 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124456 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124456 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12445b (cmpR64Imm8Effect 0x12445b 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x12445b (fun s => s.RIP = 0x12445b) (cmpR64Imm8Effect 0x12445b 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12465d, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124465, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124456 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0xF8, 0x01, 0x00, 0x00]

theorem code_l124456 : ∀ x ∈ codeRange 0x124456 bytes_l124456, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24456 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124465 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124465 (movR64M64Effect 0x124465 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124465 (LoadPre 0x124465 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124465 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124465 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12446a (movzxR32M8Effect 0x12446a 3 5 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x12446a (LoadPre 0x12446a (fun s => AddrMode.addr (.base 0 .none) s (0x12446a + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x12446a 3 5 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x12446d (movR32R32Effect 0x12446d 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x12446d (fun s => s.RIP = 0x12446d) (movR32R32Effect 0x12446d 2 0 5) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 59) (.out 0x12446f (decR32Effect 0x12446f 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x12446f (fun s => s.RIP = 0x12446f) (decR32Effect 0x12446f 2 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x124471 (cmpR32Imm8Effect 0x124471 3 0 0x30) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x124471 (cmpR32Imm8Effect 0x124471 3 0 0x30) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x124471 (fun s => s.RIP = 0x124471) (cmpR32Imm8Effect 0x124471 3 0 0x30) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 7)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l124518, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l12447a, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l124465 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x0F, 0xB6, 0x28, 0x89, 0xE8, 0xFF, 0xC8, 0x83, 0xF8, 0x30, 0x0F,
    0x87, 0x9E, 0x00, 0x00, 0x00]

theorem code_l124465 : ∀ x ∈ codeRange 0x124465 bytes_l124465, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24465 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12447a : Block Op Label signature Reg.count 53 :=
  cutBlock 0x12447a

def bytes_l12447a : List UInt8 :=
  [0xFF, 0x24, 0xC5, 0x28, 0x35, 0x20, 0x00]

theorem code_l12447a : ∀ x ∈ codeRange 0x12447a bytes_l12447a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2447a 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124488 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124488 (movR32M32LowEffect 0x124488 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x124488 (LoadPre 0x124488 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124488 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124488 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12448c (movR64M64Effect 0x12448c 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x12448c (LoadPre 0x12448c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12448c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12448c 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124491 (movR64M64Effect 0x124491 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x124491 (LoadPre 0x124491 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124491 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124491 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x124496 (movR64M64Effect 0x124496 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x124496 (LoadPre 0x124496 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124496 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124496 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x12449b (StorePre 0x12449b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x12449b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12449b 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x12449f (movR64M64Effect 0x12449f 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x12449f (LoadPre 0x12449f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12449f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12449f 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1244a4 (StorePre 0x1244a4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1244a4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244a4 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x1244a8 (movR64M64Effect 0x1244a8 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x1244a8 (LoadPre 0x1244a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1244a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1244a8 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1244ad (StorePre 0x1244ad 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1244ad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244ad 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x1244b1 (movR64M64Effect 0x1244b1 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x1244b1 (LoadPre 0x1244b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1244b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1244b1 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x1244b6 (StorePre 0x1244b6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1244b6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244b6 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 71) (.exec 0x1244ba (StorePre 0x1244ba 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1244ba + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1244ba 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 72) (.exec 0x1244bc (StorePre 0x1244bc 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1244bc + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1244bc 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 73) (.exec 0x1244bf (StorePre 0x1244bf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1244bf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244bf 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 74) (.exec 0x1244c3 (StorePre 0x1244c3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1244c3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1244c3 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[57, 3]
    (.terminate (.br ⟨.l12456a, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l124488 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x0C, 0x48, 0x8B, 0x54, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x8B,
    0x7C, 0x24, 0x38, 0x48, 0x89, 0x7B, 0x30, 0x48, 0x8B, 0x7C, 0x24, 0x30, 0x48, 0x89, 0x7B, 0x28,
    0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x89, 0x7B, 0x20, 0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x89,
    0x7B, 0x18, 0x89, 0x03, 0x89, 0x4B, 0x04, 0x48, 0x89, 0x53, 0x08, 0x48, 0x89, 0x73, 0x10, 0xE9,
    0x9E, 0x00, 0x00, 0x00]

theorem code_l124488 : ∀ x ∈ codeRange 0x124488 bytes_l124488, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24488 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124518 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124518 (cmpR8Imm8Effect 0x124518 4 5 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 5] []) (.flag .ZF)) #v[5]
    (.letOp (n := 54) (.out 0x124518 (cmpR8Imm8Effect 0x124518 4 5 0x3f) (EffectPart.reads (.flag .SF) [.gpr 5] []) (.flag .SF)) #v[5]
    (.letOp (n := 55) (.out 0x124518 (cmpR8Imm8Effect 0x124518 4 5 0x3f) (EffectPart.reads (.flag .OF) [.gpr 5] []) (.flag .OF)) #v[5]
    (.letOp (n := 56) (.exec 0x124518 (fun s => s.RIP = 0x124518) (cmpR8Imm8Effect 0x124518 4 5 0x3f) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.pure (condOp 14)) #v[53, 54, 55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12458b, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12451e, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124518 : List UInt8 :=
  [0x40, 0x80, 0xFD, 0x3F, 0x7E, 0x6D]

theorem code_l124518 : ∀ x ∈ codeRange 0x124518 bytes_l124518, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24518 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12451e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12451e (movzxR32R8Effect 0x12451e 4 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 54) (.exec 0x12451e (fun s => s.RIP = 0x12451e) (movzxR32R8Effect 0x12451e 4 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x124522 (leaR64Effect 0x124522 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x124522 (fun s => s.RIP = 0x124522) (leaR64Effect 0x124522 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124527 (movR64R64Effect 0x124527 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x124527 (fun s => s.RIP = 0x124527) (movR64R64Effect 0x124527 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x12452a (callEffect (fun _ => 0x124670) 0x12452f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x12452a (PushPre 0x12452a 5) (callEffect (fun _ => 0x124670) 0x12452f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x12452f⟩) #v[]
    (.terminate (.call ⟨.l124670, RegMap.args [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l12452f, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l12451e : List UInt8 :=
  [0x40, 0x0F, 0xB6, 0xF5, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF2, 0xE8, 0x41, 0x01, 0x00,
    0x00]

theorem code_l12451e : ∀ x ∈ codeRange 0x12451e bytes_l12451e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2451e 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12452f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12452f (movR32M32LowEffect 0x12452f 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x12452f (LoadPre 0x12452f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12452f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12452f 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124533 (movzxR32M8Effect 0x124533 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x124533 (LoadPre 0x124533 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124533 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x124533 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124538 (cmpR32Imm8Effect 0x124538 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x124538 (fun s => s.RIP = 0x124538) (cmpR32Imm8Effect 0x124538 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1245e8, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l124541, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l12452f : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x0C, 0x83, 0xF9, 0x02, 0x0F, 0x85, 0xA7, 0x00,
    0x00, 0x00]

theorem code_l12452f : ∀ x ∈ codeRange 0x12452f bytes_l12452f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2452f 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124541 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124541 (movR32M32LowEffect 0x124541 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x124541 (LoadPre 0x124541 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124541 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124541 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124545 (movR8Imm8Effect 0x124545 2 1 0x16) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x124545 (fun s => s.RIP = 0x124545) (movR8Imm8Effect 0x124545 2 1 0x16) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l12454f, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l124541 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x10, 0xB1, 0x16, 0xEB, 0x06]

theorem code_l124541 : ∀ x ∈ codeRange 0x124541 bytes_l124541, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24541 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12454f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12454f (shrR8Effect 0x12454f 4 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x12454f (fun s => s.RIP = 0x12454f) (shrR8Effect 0x12454f 4 5 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 55) (.out 0x124553 (andR8Imm8Effect 0x124553 4 5 0x1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x124553 (fun s => s.RIP = 0x124553) (andR8Imm8Effect 0x124553 4 5 0x1) (Reg.operands [.gpr 5] [])) #v[53]
    (.letOp (n := 57) (.exec 0x124557 (StorePre 0x124557 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124557 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x124557 3 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 58) (.exec 0x12455a (StorePre 0x12455a 3 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x12455a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x12455a 3 0 (.base 3 (.d8 0x5))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 59) (.exec 0x12455d (StorePre 0x12455d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12455d + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12455d 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 60) (.exec 0x124560 (StorePre 0x124560 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x124560 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x124560 4 5 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 61) (.exec 0x124564 (StorePre 0x124564 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124564 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124564 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l12456a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l12454f : List UInt8 :=
  [0x40, 0xC0, 0xED, 0x05, 0x40, 0x80, 0xE5, 0x01, 0x88, 0x4B, 0x04, 0x88, 0x43, 0x05, 0x89, 0x53,
    0x08, 0x40, 0x88, 0x6B, 0x0C, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00]

theorem code_l12454f : ∀ x ∈ codeRange 0x12454f bytes_l12454f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2454f 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12456a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12456a (addR64Imm8Effect 0x12456a 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x12456a (fun s => s.RIP = 0x12456a) (addR64Imm8Effect 0x12456a 4 0x40) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12456e (popR64Effect 0x12456e 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x12456e (popR64Effect 0x12456e 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x12456e (PopPre 0x12456e) (popR64Effect 0x12456e 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x12456f (popR64Effect 0x12456f 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[56]
    (.letOp (n := 59) (.out 0x12456f (popR64Effect 0x12456f 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x12456f (PopPre 0x12456f) (popR64Effect 0x12456f 2 14) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x124571 (popR64Effect 0x124571 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[59]
    (.letOp (n := 62) (.out 0x124571 (popR64Effect 0x124571 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x124571 (PopPre 0x124571) (popR64Effect 0x124571 1 5) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x124572 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[62]
    (.letOp (n := 65) (.out 0x124572 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x124572 (RetPre 0x124572) (retEffect) (Reg.operands [.gpr 4] [])) #v[62]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (5, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67) (some ⟨64, by decide⟩))))))))))))))))

def bytes_l12456a : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x40, 0x5B, 0x41, 0x5E, 0x5D, 0xC3]

theorem code_l12456a : ∀ x ∈ codeRange 0x12456a bytes_l12456a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2456a 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12458b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12458b (cmpR8Imm8Effect 0x12458b 4 5 0xc0) (EffectPart.reads (.flag .CF) [.gpr 5] []) (.flag .CF)) #v[5]
    (.letOp (n := 54) (.out 0x12458b (cmpR8Imm8Effect 0x12458b 4 5 0xc0) (EffectPart.reads (.flag .SF) [.gpr 5] []) (.flag .SF)) #v[5]
    (.letOp (n := 55) (.out 0x12458b (cmpR8Imm8Effect 0x12458b 4 5 0xc0) (EffectPart.reads (.flag .OF) [.gpr 5] []) (.flag .OF)) #v[5]
    (.letOp (n := 56) (.exec 0x12458b (fun s => s.RIP = 0x12458b) (cmpR8Imm8Effect 0x12458b 4 5 0xc0) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.pure (condOp 13)) #v[54, 55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1245b8, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124591, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12458b : List UInt8 :=
  [0x40, 0x80, 0xFD, 0xC0, 0x7D, 0x27]

theorem code_l12458b : ∀ x ∈ codeRange 0x12458b bytes_l12458b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2458b 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124591 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124591 (movzxR32R8Effect 0x124591 4 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 54) (.exec 0x124591 (fun s => s.RIP = 0x124591) (movzxR32R8Effect 0x124591 4 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x124595 (leaR64Effect 0x124595 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x124595 (fun s => s.RIP = 0x124595) (leaR64Effect 0x124595 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12459a (movR64R64Effect 0x12459a 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x12459a (fun s => s.RIP = 0x12459a) (movR64R64Effect 0x12459a 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x12459d (callEffect (fun _ => 0x124670) 0x1245a2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x12459d (PushPre 0x12459d 5) (callEffect (fun _ => 0x124670) 0x1245a2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1245a2⟩) #v[]
    (.terminate (.call ⟨.l124670, RegMap.args [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1245a2, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l124591 : List UInt8 :=
  [0x40, 0x0F, 0xB6, 0xF5, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF2, 0xE8, 0xCE, 0x00, 0x00,
    0x00]

theorem code_l124591 : ∀ x ∈ codeRange 0x124591 bytes_l124591, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24591 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245a2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1245a2 (movR32M32LowEffect 0x1245a2 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1245a2 (LoadPre 0x1245a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1245a2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245a2 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1245a6 (movzxR32M8Effect 0x1245a6 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1245a6 (LoadPre 0x1245a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1245a6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1245a6 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1245ab (cmpR32Imm8Effect 0x1245ab 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x1245ab (fun s => s.RIP = 0x1245ab) (cmpR32Imm8Effect 0x1245ab 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1245e8, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1245b0, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1245a2 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x0C, 0x83, 0xF9, 0x02, 0x75, 0x38]

theorem code_l1245a2 : ∀ x ∈ codeRange 0x1245a2 bytes_l1245a2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x245a2 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1245b0 (movR32M32LowEffect 0x1245b0 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1245b0 (LoadPre 0x1245b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1245b0 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245b0 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1245b4 (movR8Imm8Effect 0x1245b4 2 1 0x17) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x1245b4 (fun s => s.RIP = 0x1245b4) (movR8Imm8Effect 0x1245b4 2 1 0x17) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l12454f, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1245b0 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x10, 0xB1, 0x17, 0xEB, 0x97]

theorem code_l1245b0 : ∀ x ∈ codeRange 0x1245b0 bytes_l1245b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x245b0 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245b8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.pure (condOp 2)) #v[16]
    (.terminate (.condBr (Fin.last 53) ⟨.l12463e, RegMap.args (entryMap (live .l1245b8)) 54⟩ ⟨.l1245be, RegMap.args (entryMap (live .l1245b8)) 54⟩))

def bytes_l1245b8 : List UInt8 :=
  [0x0F, 0x82, 0x80, 0x00, 0x00, 0x00]

theorem code_l1245b8 : ∀ x ∈ codeRange 0x1245b8 bytes_l1245b8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x245b8 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245be : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1245be (movzxR32R8Effect 0x1245be 4 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 54) (.exec 0x1245be (fun s => s.RIP = 0x1245be) (movzxR32R8Effect 0x1245be 4 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x1245c2 (leaR64Effect 0x1245c2 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x1245c2 (fun s => s.RIP = 0x1245c2) (leaR64Effect 0x1245c2 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1245c7 (movR64R64Effect 0x1245c7 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x1245c7 (fun s => s.RIP = 0x1245c7) (movR64R64Effect 0x1245c7 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x1245ca (callEffect (fun _ => 0x124670) 0x1245cf) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1245ca (PushPre 0x1245ca 5) (callEffect (fun _ => 0x124670) 0x1245cf) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1245cf⟩) #v[]
    (.terminate (.call ⟨.l124670, RegMap.args [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1245cf, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1245be : List UInt8 :=
  [0x40, 0x0F, 0xB6, 0xF5, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF2, 0xE8, 0xA1, 0x00, 0x00,
    0x00]

theorem code_l1245be : ∀ x ∈ codeRange 0x1245be bytes_l1245be, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x245be 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245cf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1245cf (movR32M32LowEffect 0x1245cf 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1245cf (LoadPre 0x1245cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1245cf + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245cf 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1245d3 (movzxR32M8Effect 0x1245d3 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1245d3 (LoadPre 0x1245d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1245d3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1245d3 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1245d8 (cmpR32Imm8Effect 0x1245d8 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x1245d8 (fun s => s.RIP = 0x1245d8) (cmpR32Imm8Effect 0x1245d8 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1245e8, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1245dd, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1245cf : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x0C, 0x83, 0xF9, 0x02, 0x75, 0x0B]

theorem code_l1245cf : ∀ x ∈ codeRange 0x1245cf bytes_l1245cf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x245cf 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245dd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1245dd (movR32M32LowEffect 0x1245dd 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1245dd (LoadPre 0x1245dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1245dd + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245dd 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1245e1 (movR8Imm8Effect 0x1245e1 2 1 0x18) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x1245e1 (fun s => s.RIP = 0x1245e1) (movR8Imm8Effect 0x1245e1 2 1 0x18) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l12454f, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1245dd : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x10, 0xB1, 0x18, 0xE9, 0x67, 0xFF, 0xFF, 0xFF]

theorem code_l1245dd : ∀ x ∈ codeRange 0x1245dd bytes_l1245dd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x245dd 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245e8_1 : Block Op Label signature Reg.count 82 :=
  .terminate (.br ⟨.l12456a, RegMap.args [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩)

def bytes_l1245e8_1 : List UInt8 :=
  [0xE9, 0x2C, 0xFF, 0xFF, 0xFF]

theorem code_l1245e8_1 : ∀ x ∈ codeRange 0x124639 bytes_l1245e8_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24639 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1245e8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1245e8 (movzxR32M8Effect 0x1245e8 5 2 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1245e8 (LoadPre 0x1245e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1245e8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1245e8 5 2 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1245ed (StorePre 0x1245ed 3 (fun s => AddrMode.addr (.base 3 (.d8 0x7)) s (0x1245ed + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1245ed 3 2 (.base 3 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x1245f0 (movzxR32M16Effect 0x1245f0 5 2 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 57) (.exec 0x1245f0 (LoadPre 0x1245f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x1245f0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1245f0 5 2 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1245f5 (StorePre 0x1245f5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x1245f5 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1245f5 4 2 (.base 3 (.d8 0x5))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x1245f9 (movR32M32LowEffect 0x1245f9 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x1245f9 (LoadPre 0x1245f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1245f9 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1245f9 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1245fd (movR64M64Effect 0x1245fd 6 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x1245fd (LoadPre 0x1245fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1245fd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1245fd 6 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x124602 (StorePre 0x124602 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x124602 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124602 6 (.base 3 (.d8 0x14))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 64) (.out 0x124606 (movR64M64Effect 0x124606 6 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 65) (.exec 0x124606 (LoadPre 0x124606 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x124606 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124606 6 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x12460b (StorePre 0x12460b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x12460b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12460b 6 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 67) (.out 0x12460f (movR64M64Effect 0x12460f 6 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x12460f (LoadPre 0x12460f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x12460f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12460f 6 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x124614 (StorePre 0x124614 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x124614 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124614 6 (.base 3 (.d8 0x24))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 70) (.out 0x124618 (movR64M64Effect 0x124618 6 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x124618 (LoadPre 0x124618 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x124618 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124618 6 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x12461d (StorePre 0x12461d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x12461d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12461d 6 (.base 3 (.d8 0x2c))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[70, 3]
    (.letOp (n := 73) (.out 0x124621 (movR32M32LowEffect 0x124621 6 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 74) (.exec 0x124621 (LoadPre 0x124621 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x124621 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124621 6 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x124625 (StorePre 0x124625 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x124625 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124625 6 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[73, 3]
    (.letOp (n := 76) (.out 0x124628 (movR64M64Effect 0x124628 6 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 77) (.exec 0x124628 (LoadPre 0x124628 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124628 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124628 6 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x12462d (StorePre 0x12462d 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x12462d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12462d 6 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[76, 3]
    (.letOp (n := 79) (.exec 0x124631 (StorePre 0x124631 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124631 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124631 1 (.base 3 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 80) (.exec 0x124633 (StorePre 0x124633 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124633 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x124633 3 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 81) (.exec 0x124636 (StorePre 0x124636 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x124636 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124636 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[59, 3]
    (b_l1245e8_1)))))))))))))))))))))))))))))

def bytes_l1245e8 : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x24, 0x0F, 0x88, 0x53, 0x07, 0x0F, 0xB7, 0x54, 0x24, 0x0D, 0x66, 0x89, 0x53,
    0x05, 0x8B, 0x54, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x1C, 0x48, 0x89, 0x73, 0x14, 0x48, 0x8B,
    0x74, 0x24, 0x24, 0x48, 0x89, 0x73, 0x1C, 0x48, 0x8B, 0x74, 0x24, 0x2C, 0x48, 0x89, 0x73, 0x24,
    0x48, 0x8B, 0x74, 0x24, 0x34, 0x48, 0x89, 0x73, 0x2C, 0x8B, 0x74, 0x24, 0x3C, 0x89, 0x73, 0x34,
    0x48, 0x8B, 0x74, 0x24, 0x14, 0x48, 0x89, 0x73, 0x0C, 0x89, 0x0B, 0x88, 0x43, 0x04, 0x89, 0x53,
    0x08] ++ bytes_l1245e8_1

theorem code_l1245e8 : ∀ x ∈ codeRange 0x1245e8 bytes_l1245e8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x245e8 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1245e8_1

@[cfg_block] def b_l12463e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12463e (StorePre 0x12463e 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x12463e + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x12463e (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x124643 (movR32M32Effect 0x124643 0 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 55) (.exec 0x124643 (LoadPre 0x124643 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x124643 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x124643 0 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x124647 (StorePre 0x124647 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124647 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124647 6 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x12464d (StorePre 0x12464d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x12464d + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12464d 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 58) (.exec 0x124650 (StorePre 0x124650 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x124650 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124650 (.base 3 (.d8 0x8)) 0x12) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.exec 0x124654 (StorePre 0x124654 4 (fun s => AddrMode.addr (.base 3 (.d8 0x9)) s (0x124654 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x124654 4 5 (.base 3 (.d8 0x9))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[5, 3]
    (.terminate (.br ⟨.l12456a, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l12463e : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x46, 0x1C, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00, 0x89,
    0x43, 0x04, 0xC6, 0x43, 0x08, 0x12, 0x40, 0x88, 0x6B, 0x09, 0xE9, 0x0D, 0xFF, 0xFF, 0xFF]

theorem code_l12463e : ∀ x ∈ codeRange 0x12463e bytes_l12463e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2463e 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12465d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12465d (movR32Imm32Effect 0x12465d 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x12465d (fun s => s.RIP = 0x12465d) (movR32Imm32Effect 0x12465d 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x124662 (movR64Imm32Effect 0x124662 2 0x2036e0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x124662 (fun s => s.RIP = 0x124662) (movR64Imm32Effect 0x124662 2 0x2036e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x124669 (callEffect (fun _ => 0x129c90) 0x12466e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x124669 (PushPre 0x124669 5) (callEffect (fun _ => 0x129c90) 0x12466e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x12466e⟩) #v[]
    (.terminate (.call ⟨.l129c90, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l12466e, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l12465d : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00, 0xE8, 0x22, 0x56, 0x00,
    0x00]

theorem code_l12465d : ∀ x ∈ codeRange 0x12465d bytes_l12465d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2465d 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12466e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12466e (fun s => s.RIP = 0x12466e) (fun _ => nopEffect 0x12466e 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l124670, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l12466e : List UInt8 :=
  [0x66, 0x90]

theorem code_l12466e : ∀ x ∈ codeRange 0x12466e bytes_l12466e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2466e 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124670 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124670 (pushR64Effect 0x124670 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x124670 (PushPre 0x124670 1) (pushR64Effect 0x124670 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x124671 (pushR64Effect 0x124671 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x124671 (PushPre 0x124671 2) (pushR64Effect 0x124671 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x124673 (pushR64Effect 0x124673 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x124673 (PushPre 0x124673 2) (pushR64Effect 0x124673 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x124675 (pushR64Effect 0x124675 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x124675 (PushPre 0x124675 2) (pushR64Effect 0x124675 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x124677 (pushR64Effect 0x124677 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x124677 (PushPre 0x124677 2) (pushR64Effect 0x124677 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x124679 (pushR64Effect 0x124679 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x124679 (PushPre 0x124679 1) (pushR64Effect 0x124679 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x12467a (subR64Imm8Effect 0x12467a 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x12467a (fun s => s.RIP = 0x12467a) (subR64Imm8Effect 0x12467a 4 0x38) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x12467e (movR64R64Effect 0x12467e 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x12467e (fun s => s.RIP = 0x12467e) (movR64R64Effect 0x12467e 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x124681 (movR32R32Effect 0x124681 2 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 70) (.exec 0x124681 (fun s => s.RIP = 0x124681) (movR32R32Effect 0x124681 2 5 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x124683 (andR8Imm8Effect 0x124683 4 5 0x20) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[69]
    (.letOp (n := 72) (.exec 0x124683 (fun s => s.RIP = 0x124683) (andR8Imm8Effect 0x124683 4 5 0x20) (Reg.operands [.gpr 5] [])) #v[69]
    (.letOp (n := 73) (.out 0x124687 (andR8Imm8Effect 0x124687 4 6 0x1f) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 74) (.exec 0x124687 (fun s => s.RIP = 0x124687) (andR8Imm8Effect 0x124687 4 6 0x1f) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 75) (.out 0x12468b (cmpR8Imm8Effect 0x12468b 4 6 0x1f) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[73]
    (.letOp (n := 76) (.exec 0x12468b (fun s => s.RIP = 0x12468b) (cmpR8Imm8Effect 0x12468b 4 6 0x1f) (Reg.operands [.gpr 6] [])) #v[73]
    (.letOp (n := 77) (.pure (condOp 5)) #v[75]
    (.terminate (.condBr (Fin.last 77) ⟨.l1246eb, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ ⟨.l124691, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l124670 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x38, 0x48, 0x89,
    0xFB, 0x89, 0xF5, 0x40, 0x80, 0xE5, 0x20, 0x40, 0x80, 0xE6, 0x1F, 0x40, 0x80, 0xFE, 0x1F, 0x75,
    0x5A]

theorem code_l124670 : ∀ x ∈ codeRange 0x124670 bytes_l124670, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24670 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124691 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124691 (movR64R64Effect 0x124691 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 54) (.exec 0x124691 (fun s => s.RIP = 0x124691) (movR64R64Effect 0x124691 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x124694 (movR64R64Effect 0x124694 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x124694 (fun s => s.RIP = 0x124694) (movR64R64Effect 0x124694 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124697 (movR64R64Effect 0x124697 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 58) (.exec 0x124697 (fun s => s.RIP = 0x124697) (movR64R64Effect 0x124697 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 59) (.out 0x12469a (movR32Imm32Effect 0x12469a 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x12469a (fun s => s.RIP = 0x12469a) (movR32Imm32Effect 0x12469a 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x12469f (callEffect (fun _ => 0x127b80) 0x1246a4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x12469f (PushPre 0x12469f 5) (callEffect (fun _ => 0x127b80) 0x1246a4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x1246a4⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l1246a4, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l124691 : List UInt8 :=
  [0x49, 0x89, 0xD6, 0x48, 0x89, 0xE7, 0x48, 0x89, 0xD6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0xDC,
    0x34, 0x00, 0x00]

theorem code_l124691 : ∀ x ∈ codeRange 0x124691 bytes_l124691, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24691 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246a4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1246a4 (movR32M32LowEffect 0x1246a4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1246a4 (LoadPre 0x1246a4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1246a4 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1246a4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1246a7 (cmpR32Imm8Effect 0x1246a7 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1246a7 (fun s => s.RIP = 0x1246a7) (cmpR32Imm8Effect 0x1246a7 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124855, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1246b0, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1246a4 : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xA5, 0x01, 0x00, 0x00]

theorem code_l1246a4 : ∀ x ∈ codeRange 0x1246a4 bytes_l1246a4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246a4 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1246b0 (movR64M64Effect 0x1246b0 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1246b0 (LoadPre 0x1246b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1246b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1246b0 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1246b5 (cmpR64Imm8Effect 0x1246b5 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1246b5 (fun s => s.RIP = 0x1246b5) (cmpR64Imm8Effect 0x1246b5 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1248a3, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1246bf, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1246b0 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0xE4, 0x01, 0x00, 0x00]

theorem code_l1246b0 : ∀ x ∈ codeRange 0x1246b0 bytes_l1246b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246b0 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246bf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1246bf (movR64M64Effect 0x1246bf 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1246bf (LoadPre 0x1246bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1246bf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1246bf 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1246c4 (movzxR32M8Effect 0x1246c4 4 15 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[53]
    (.letOp (n := 56) (.exec 0x1246c4 (LoadPre 0x1246c4 (fun s => AddrMode.addr (.base 0 .none) s (0x1246c4 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1246c4 4 15 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1246c8 (movR32R32Effect 0x1246c8 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x1246c8 (fun s => s.RIP = 0x1246c8) (movR32R32Effect 0x1246c8 3 0 15) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 59) (.out 0x1246cb (andR32Imm8Effect 0x1246cb 4 15 0x7f) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[55]
    (.letOp (n := 60) (.exec 0x1246cb (fun s => s.RIP = 0x1246cb) (andR32Imm8Effect 0x1246cb 4 15 0x7f) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 61) (.out 0x1246cf (testR8R8Effect 0x1246cf 2 0 0) (EffectPart.reads (.flag .SF) [.gpr 0, .gpr 0] []) (.flag .SF)) #v[57, 57]
    (.letOp (n := 62) (.exec 0x1246cf (fun s => s.RIP = 0x1246cf) (testR8R8Effect 0x1246cf 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[57, 57]
    (.letOp (n := 63) (.pure (condOp 8)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l124705, RegMap.args [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 59), (20, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l1246d3, RegMap.args [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 59), (20, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l1246bf : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x38, 0x44, 0x89, 0xF8, 0x41, 0x83, 0xE7, 0x7F,
    0x84, 0xC0, 0x78, 0x32]

theorem code_l1246bf : ∀ x ∈ codeRange 0x1246bf bytes_l1246bf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246bf 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246d3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1246d3 (cmpR8Imm8Effect 0x1246d3 4 15 0x1f) (EffectPart.reads (.flag .CF) [.gpr 15] []) (.flag .CF)) #v[15]
    (.letOp (n := 54) (.exec 0x1246d3 (fun s => s.RIP = 0x1246d3) (cmpR8Imm8Effect 0x1246d3 4 15 0x1f) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.pure (condOp 2)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1247f9, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1246dd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1246d3 : List UInt8 :=
  [0x41, 0x80, 0xFF, 0x1F, 0x0F, 0x82, 0x1C, 0x01, 0x00, 0x00]

theorem code_l1246d3 : ∀ x ∈ codeRange 0x1246d3 bytes_l1246d3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246d3 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246dd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1246dd (shrR8Effect 0x1246dd 4 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x1246dd (fun s => s.RIP = 0x1246dd) (shrR8Effect 0x1246dd 4 5 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 55) (.exec 0x1246e1 (StorePre 0x1246e1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1246e1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1246e1 4 5 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.exec 0x1246e5 (StorePre 0x1246e5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1246e5 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1246e5 15 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.terminate (.br ⟨.l1246fa, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1246dd : List UInt8 :=
  [0x40, 0xC0, 0xED, 0x05, 0x40, 0x88, 0x6B, 0x04, 0x44, 0x89, 0x7B, 0x08, 0xEB, 0x0F]

theorem code_l1246dd : ∀ x ∈ codeRange 0x1246dd bytes_l1246dd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246dd 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246eb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1246eb (movzxR32R8Effect 0x1246eb 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x1246eb (fun s => s.RIP = 0x1246eb) (movzxR32R8Effect 0x1246eb 4 0 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1246ef (shrR8Effect 0x1246ef 4 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 56) (.exec 0x1246ef (fun s => s.RIP = 0x1246ef) (shrR8Effect 0x1246ef 4 5 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 57) (.exec 0x1246f3 (StorePre 0x1246f3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1246f3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1246f3 4 5 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 58) (.exec 0x1246f7 (StorePre 0x1246f7 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1246f7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1246f7 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.terminate (.br ⟨.l1246fa, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1246eb : List UInt8 :=
  [0x40, 0x0F, 0xB6, 0xC6, 0x40, 0xC0, 0xED, 0x05, 0x40, 0x88, 0x6B, 0x04, 0x89, 0x43, 0x08]

theorem code_l1246eb : ∀ x ∈ codeRange 0x1246eb bytes_l1246eb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246eb 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1246fa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1246fa (StorePre 0x1246fa 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1246fa + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1246fa 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l124894, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l1246fa : List UInt8 :=
  [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0x8F, 0x01, 0x00, 0x00]

theorem code_l1246fa : ∀ x ∈ codeRange 0x1246fa bytes_l1246fa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x246fa 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124705 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124705 (testR8R8Effect 0x124705 3 15 15) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 15] []) (.flag .ZF)) #v[15, 15]
    (.letOp (n := 54) (.exec 0x124705 (fun s => s.RIP = 0x124705) (testR8R8Effect 0x124705 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1247f9, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l12470e, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l124705 : List UInt8 :=
  [0x45, 0x84, 0xFF, 0x0F, 0x84, 0xEB, 0x00, 0x00, 0x00]

theorem code_l124705 : ∀ x ∈ codeRange 0x124705 bytes_l124705, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24705 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12470e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12470e (movR64R64Effect 0x12470e 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x12470e (fun s => s.RIP = 0x12470e) (movR64R64Effect 0x12470e 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124711 (movR64R64Effect 0x124711 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x124711 (fun s => s.RIP = 0x124711) (movR64R64Effect 0x124711 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x124714 (movR32Imm32Effect 0x124714 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x124714 (fun s => s.RIP = 0x124714) (movR32Imm32Effect 0x124714 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x124719 (callEffect (fun _ => 0x127b80) 0x12471e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x124719 (PushPre 0x124719 5) (callEffect (fun _ => 0x127b80) 0x12471e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x12471e⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l12471e, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l12470e : List UInt8 :=
  [0x48, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x62, 0x34, 0x00, 0x00]

theorem code_l12470e : ∀ x ∈ codeRange 0x12470e bytes_l12470e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2470e 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12471e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12471e (movR32M32LowEffect 0x12471e 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12471e (LoadPre 0x12471e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12471e + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12471e 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124721 (cmpR32Imm8Effect 0x124721 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124721 (fun s => s.RIP = 0x124721) (cmpR32Imm8Effect 0x124721 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124855, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12472a, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12471e : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x2B, 0x01, 0x00, 0x00]

theorem code_l12471e : ∀ x ∈ codeRange 0x12471e bytes_l12471e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2471e 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12472a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12472a (movR64M64Effect 0x12472a 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x12472a (LoadPre 0x12472a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12472a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12472a 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12472f (cmpR64Imm8Effect 0x12472f 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x12472f (fun s => s.RIP = 0x12472f) (cmpR64Imm8Effect 0x12472f 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1248a3, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124739, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12472a : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0x6A, 0x01, 0x00, 0x00]

theorem code_l12472a : ∀ x ∈ codeRange 0x12472a bytes_l12472a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2472a 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124739 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124739 (movR32R32Effect 0x124739 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x124739 (fun s => s.RIP = 0x124739) (movR32R32Effect 0x124739 3 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x12473c (shlR32Effect 0x12473c 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x12473c (fun s => s.RIP = 0x12473c) (shlR32Effect 0x12473c 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x12473f (movR64M64Effect 0x12473f 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x12473f (LoadPre 0x12473f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12473f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12473f 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x124744 (movzxR32M8Effect 0x124744 4 12 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[57]
    (.letOp (n := 60) (.exec 0x124744 (LoadPre 0x124744 (fun s => AddrMode.addr (.base 1 .none) s (0x124744 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x124744 4 12 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 61) (.out 0x124748 (movR32R32Effect 0x124748 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x124748 (fun s => s.RIP = 0x124748) (movR32R32Effect 0x124748 3 1 12) (Reg.operands [.gpr 12] [])) #v[59]
    (.letOp (n := 63) (.out 0x12474b (andR32Imm8Effect 0x12474b 4 12 0x7f) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[59]
    (.letOp (n := 64) (.exec 0x12474b (fun s => s.RIP = 0x12474b) (andR32Imm8Effect 0x12474b 4 12 0x7f) (Reg.operands [.gpr 12] [])) #v[59]
    (.letOp (n := 65) (.out 0x12474f (orR32R32Effect 0x12474f 3 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[63, 55]
    (.letOp (n := 66) (.exec 0x12474f (fun s => s.RIP = 0x12474f) (orR32R32Effect 0x12474f 3 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[63, 55]
    (.letOp (n := 67) (.out 0x124752 (testR8R8Effect 0x124752 2 1 1) (EffectPart.reads (.flag .SF) [.gpr 1, .gpr 1] []) (.flag .SF)) #v[61, 61]
    (.letOp (n := 68) (.exec 0x124752 (fun s => s.RIP = 0x124752) (testR8R8Effect 0x124752 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[61, 61]
    (.letOp (n := 69) (.pure (condOp 8)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l12475b, RegMap.args [(0, 55), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l124756, RegMap.args [(0, 55), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l124739 : List UInt8 :=
  [0x44, 0x89, 0xF8, 0xC1, 0xE0, 0x07, 0x48, 0x8B, 0x4C, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x21, 0x44,
    0x89, 0xE1, 0x41, 0x83, 0xE4, 0x7F, 0x41, 0x09, 0xC4, 0x84, 0xC9, 0x78, 0x05]

theorem code_l124739 : ∀ x ∈ codeRange 0x124739 bytes_l124739, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24739 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124756 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124756 (movR32R32Effect 0x124756 3 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[12]
    (.letOp (n := 54) (.exec 0x124756 (fun s => s.RIP = 0x124756) (movR32R32Effect 0x124756 3 15 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.terminate (.br ⟨.l1246dd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l124756 : List UInt8 :=
  [0x45, 0x89, 0xE7, 0xEB, 0x82]

theorem code_l124756 : ∀ x ∈ codeRange 0x124756 bytes_l124756, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24756 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12475b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12475b (movR64R64Effect 0x12475b 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x12475b (fun s => s.RIP = 0x12475b) (movR64R64Effect 0x12475b 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12475e (movR64R64Effect 0x12475e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x12475e (fun s => s.RIP = 0x12475e) (movR64R64Effect 0x12475e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x124761 (movR32Imm32Effect 0x124761 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x124761 (fun s => s.RIP = 0x124761) (movR32Imm32Effect 0x124761 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x124766 (callEffect (fun _ => 0x127b80) 0x12476b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x124766 (PushPre 0x124766 5) (callEffect (fun _ => 0x127b80) 0x12476b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x12476b⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l12476b, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l12475b : List UInt8 :=
  [0x48, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x15, 0x34, 0x00, 0x00]

theorem code_l12475b : ∀ x ∈ codeRange 0x12475b bytes_l12475b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2475b 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12476b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12476b (movR32M32LowEffect 0x12476b 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12476b (LoadPre 0x12476b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12476b + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12476b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12476e (cmpR32Imm8Effect 0x12476e 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x12476e (fun s => s.RIP = 0x12476e) (cmpR32Imm8Effect 0x12476e 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124855, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124777, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12476b : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xDE, 0x00, 0x00, 0x00]

theorem code_l12476b : ∀ x ∈ codeRange 0x12476b bytes_l12476b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2476b 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124777 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124777 (movR64M64Effect 0x124777 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124777 (LoadPre 0x124777 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124777 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124777 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12477c (cmpR64Imm8Effect 0x12477c 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x12477c (fun s => s.RIP = 0x12477c) (cmpR64Imm8Effect 0x12477c 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1248a3, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124786, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124777 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0x1D, 0x01, 0x00, 0x00]

theorem code_l124777 : ∀ x ∈ codeRange 0x124777 bytes_l124777, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24777 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124786 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124786 (shlR32Effect 0x124786 4 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 54) (.exec 0x124786 (fun s => s.RIP = 0x124786) (shlR32Effect 0x124786 4 12 7) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 55) (.out 0x12478a (movR64M64Effect 0x12478a 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x12478a (LoadPre 0x12478a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12478a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12478a 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12478f (movzxR32M8Effect 0x12478f 4 13 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[55]
    (.letOp (n := 58) (.exec 0x12478f (LoadPre 0x12478f (fun s => AddrMode.addr (.base 0 .none) s (0x12478f + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x12478f 4 13 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x124793 (movR32R32Effect 0x124793 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x124793 (fun s => s.RIP = 0x124793) (movR32R32Effect 0x124793 3 0 13) (Reg.operands [.gpr 13] [])) #v[57]
    (.letOp (n := 61) (.out 0x124796 (andR32Imm8Effect 0x124796 4 13 0x7f) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 62) (.exec 0x124796 (fun s => s.RIP = 0x124796) (andR32Imm8Effect 0x124796 4 13 0x7f) (Reg.operands [.gpr 13] [])) #v[57]
    (.letOp (n := 63) (.out 0x12479a (orR32R32Effect 0x12479a 3 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[61, 53]
    (.letOp (n := 64) (.exec 0x12479a (fun s => s.RIP = 0x12479a) (orR32R32Effect 0x12479a 3 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[61, 53]
    (.letOp (n := 65) (.out 0x12479d (testR8R8Effect 0x12479d 2 0 0) (EffectPart.reads (.flag .SF) [.gpr 0, .gpr 0] []) (.flag .SF)) #v[59, 59]
    (.letOp (n := 66) (.exec 0x12479d (fun s => s.RIP = 0x12479d) (testR8R8Effect 0x12479d 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[59, 59]
    (.letOp (n := 67) (.pure (condOp 8)) #v[65]
    (.terminate (.condBr (Fin.last 67) ⟨.l1247a9, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 63), (14, 14), (15, 15), (20, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l1247a1, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 63), (14, 14), (15, 15), (20, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l124786 : List UInt8 :=
  [0x41, 0xC1, 0xE4, 0x07, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x28, 0x44, 0x89, 0xE8,
    0x41, 0x83, 0xE5, 0x7F, 0x45, 0x09, 0xE5, 0x84, 0xC0, 0x78, 0x08]

theorem code_l124786 : ∀ x ∈ codeRange 0x124786 bytes_l124786, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24786 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247a1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1247a1 (movR32R32Effect 0x1247a1 3 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 13] []) (.reg (.gpr 15))) #v[13]
    (.letOp (n := 54) (.exec 0x1247a1 (fun s => s.RIP = 0x1247a1) (movR32R32Effect 0x1247a1 3 15 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.terminate (.br ⟨.l1246dd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1247a1 : List UInt8 :=
  [0x45, 0x89, 0xEF, 0xE9, 0x34, 0xFF, 0xFF, 0xFF]

theorem code_l1247a1 : ∀ x ∈ codeRange 0x1247a1 bytes_l1247a1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247a1 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247a9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1247a9 (movR64R64Effect 0x1247a9 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1247a9 (fun s => s.RIP = 0x1247a9) (movR64R64Effect 0x1247a9 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1247ac (movR64R64Effect 0x1247ac 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x1247ac (fun s => s.RIP = 0x1247ac) (movR64R64Effect 0x1247ac 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x1247af (movR32Imm32Effect 0x1247af 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1247af (fun s => s.RIP = 0x1247af) (movR32Imm32Effect 0x1247af 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1247b4 (callEffect (fun _ => 0x127b80) 0x1247b9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1247b4 (PushPre 0x1247b4 5) (callEffect (fun _ => 0x127b80) 0x1247b9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1247b9⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1247b9, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1247a9 : List UInt8 :=
  [0x48, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0xC7, 0x33, 0x00, 0x00]

theorem code_l1247a9 : ∀ x ∈ codeRange 0x1247a9 bytes_l1247a9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247a9 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247b9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1247b9 (movR32M32LowEffect 0x1247b9 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1247b9 (LoadPre 0x1247b9 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1247b9 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1247b9 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1247bc (cmpR32Imm8Effect 0x1247bc 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1247bc (fun s => s.RIP = 0x1247bc) (cmpR32Imm8Effect 0x1247bc 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124855, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1247c5, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1247b9 : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x90, 0x00, 0x00, 0x00]

theorem code_l1247b9 : ∀ x ∈ codeRange 0x1247b9 bytes_l1247b9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247b9 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247c5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1247c5 (movR64M64Effect 0x1247c5 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1247c5 (LoadPre 0x1247c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1247c5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1247c5 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1247ca (cmpR64Imm8Effect 0x1247ca 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1247ca (fun s => s.RIP = 0x1247ca) (cmpR64Imm8Effect 0x1247ca 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1248a3, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1247d4, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1247c5 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0xCF, 0x00, 0x00, 0x00]

theorem code_l1247c5 : ∀ x ∈ codeRange 0x1247c5 bytes_l1247c5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247c5 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247d4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1247d4 (shlR32Effect 0x1247d4 4 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 54) (.exec 0x1247d4 (fun s => s.RIP = 0x1247d4) (shlR32Effect 0x1247d4 4 13 7) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[13]
    (.letOp (n := 55) (.out 0x1247d8 (movR64M64Effect 0x1247d8 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1247d8 (LoadPre 0x1247d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1247d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1247d8 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1247dd (movzxR32M8Effect 0x1247dd 4 12 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 58) (.exec 0x1247dd (LoadPre 0x1247dd (fun s => AddrMode.addr (.base 0 .none) s (0x1247dd + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1247dd 4 12 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x1247e1 (movR32R32Effect 0x1247e1 3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x1247e1 (fun s => s.RIP = 0x1247e1) (movR32R32Effect 0x1247e1 3 0 12) (Reg.operands [.gpr 12] [])) #v[57]
    (.letOp (n := 61) (.out 0x1247e4 (andR32Imm8Effect 0x1247e4 4 12 0x7f) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[57]
    (.letOp (n := 62) (.exec 0x1247e4 (fun s => s.RIP = 0x1247e4) (andR32Imm8Effect 0x1247e4 4 12 0x7f) (Reg.operands [.gpr 12] [])) #v[57]
    (.letOp (n := 63) (.out 0x1247e8 (orR32R32Effect 0x1247e8 3 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[61, 53]
    (.letOp (n := 64) (.exec 0x1247e8 (fun s => s.RIP = 0x1247e8) (orR32R32Effect 0x1247e8 3 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[61, 53]
    (.letOp (n := 65) (.out 0x1247eb (testR8R8Effect 0x1247eb 2 0 0) (EffectPart.reads (.flag .SF) [.gpr 0, .gpr 0] []) (.flag .SF)) #v[59, 59]
    (.letOp (n := 66) (.exec 0x1247eb (fun s => s.RIP = 0x1247eb) (testR8R8Effect 0x1247eb 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[59, 59]
    (.letOp (n := 67) (.pure (condOp 9)) #v[65]
    (.terminate (.condBr (Fin.last 67) ⟨.l124756, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 63), (13, 53), (14, 14), (15, 15), (20, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l1247f3, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 63), (13, 53), (14, 14), (15, 15), (20, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l1247d4 : List UInt8 :=
  [0x41, 0xC1, 0xE5, 0x07, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x20, 0x44, 0x89, 0xE0,
    0x41, 0x83, 0xE4, 0x7F, 0x45, 0x09, 0xEC, 0x84, 0xC0, 0x0F, 0x89, 0x63, 0xFF, 0xFF, 0xFF]

theorem code_l1247d4 : ∀ x ∈ codeRange 0x1247d4 bytes_l1247d4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247d4 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1247f3 (cmpR8Imm8Effect 0x1247f3 4 15 0xf) (EffectPart.reads (.flag .CF) [.gpr 15] []) (.flag .CF)) #v[15]
    (.letOp (n := 54) (.out 0x1247f3 (cmpR8Imm8Effect 0x1247f3 4 15 0xf) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[15]
    (.letOp (n := 55) (.exec 0x1247f3 (fun s => s.RIP = 0x1247f3) (cmpR8Imm8Effect 0x1247f3 4 15 0xf) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l124814, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l1247f9, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1247f3 : List UInt8 :=
  [0x41, 0x80, 0xFF, 0x0F, 0x76, 0x1B]

theorem code_l1247f3 : ∀ x ∈ codeRange 0x1247f3 bytes_l1247f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247f3 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1247f9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1247f9 (StorePre 0x1247f9 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1247f9 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1247f9 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x1247fe (movR32M32Effect 0x1247fe 0 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 55) (.exec 0x1247fe (LoadPre 0x1247fe (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1247fe + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1247fe 0 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x124802 (StorePre 0x124802 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124802 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124802 6 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x124808 (StorePre 0x124808 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124808 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124808 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 58) (.exec 0x12480b (StorePre 0x12480b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12480b + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x12480b (.base 3 (.d8 0x8)) 0x10) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l124894, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1247f9 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x46, 0x1C, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00, 0x89,
    0x43, 0x04, 0xC6, 0x43, 0x08, 0x10, 0xE9, 0x80, 0x00, 0x00, 0x00]

theorem code_l1247f9 : ∀ x ∈ codeRange 0x1247f9 bytes_l1247f9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247f9 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124814 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124814 (movR64R64Effect 0x124814 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x124814 (fun s => s.RIP = 0x124814) (movR64R64Effect 0x124814 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124817 (movR64R64Effect 0x124817 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x124817 (fun s => s.RIP = 0x124817) (movR64R64Effect 0x124817 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x12481a (movR32Imm32Effect 0x12481a 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x12481a (fun s => s.RIP = 0x12481a) (movR32Imm32Effect 0x12481a 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x12481f (callEffect (fun _ => 0x127b80) 0x124824) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x12481f (PushPre 0x12481f 5) (callEffect (fun _ => 0x127b80) 0x124824) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x124824⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l124824, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l124814 : List UInt8 :=
  [0x48, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x5C, 0x33, 0x00, 0x00]

theorem code_l124814 : ∀ x ∈ codeRange 0x124814 bytes_l124814, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24814 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124824 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124824 (movR32M32LowEffect 0x124824 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124824 (LoadPre 0x124824 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124824 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124824 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124827 (cmpR32Imm8Effect 0x124827 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124827 (fun s => s.RIP = 0x124827) (cmpR32Imm8Effect 0x124827 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124855, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12482c, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124824 : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x75, 0x29]

theorem code_l124824 : ∀ x ∈ codeRange 0x124824 bytes_l124824, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24824 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12482c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12482c (movR64M64Effect 0x12482c 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x12482c (LoadPre 0x12482c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12482c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12482c 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124831 (cmpR64Imm8Effect 0x124831 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124831 (fun s => s.RIP = 0x124831) (cmpR64Imm8Effect 0x124831 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1248a3, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124837, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12482c : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x83, 0xFE, 0x01, 0x75, 0x6C]

theorem code_l12482c : ∀ x ∈ codeRange 0x12482c bytes_l12482c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2482c 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124837 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124837 (movR64M64Effect 0x124837 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124837 (LoadPre 0x124837 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124837 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124837 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12483c (movzxR32M8Effect 0x12483c 4 15 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[53]
    (.letOp (n := 56) (.exec 0x12483c (LoadPre 0x12483c (fun s => AddrMode.addr (.base 0 .none) s (0x12483c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x12483c 4 15 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x124840 (testR8R8Effect 0x124840 3 15 15) (EffectPart.reads (.flag .SF) [.gpr 15, .gpr 15] []) (.flag .SF)) #v[55, 55]
    (.letOp (n := 58) (.exec 0x124840 (fun s => s.RIP = 0x124840) (testR8R8Effect 0x124840 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[55, 55]
    (.letOp (n := 59) (.pure (condOp 8)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1247f9, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 55), (20, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l124845, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 55), (20, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l124837 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x38, 0x45, 0x84, 0xFF, 0x78, 0xB4]

theorem code_l124837 : ∀ x ∈ codeRange 0x124837 bytes_l124837, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24837 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124845 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124845 (shlR32Effect 0x124845 4 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 54) (.exec 0x124845 (fun s => s.RIP = 0x124845) (shlR32Effect 0x124845 4 12 7) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 55) (.out 0x124849 (andR32Imm8Effect 0x124849 4 15 0x7f) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 56) (.exec 0x124849 (fun s => s.RIP = 0x124849) (andR32Imm8Effect 0x124849 4 15 0x7f) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x12484d (orR32R32Effect 0x12484d 3 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x12484d (fun s => s.RIP = 0x12484d) (orR32R32Effect 0x12484d 3 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[55, 53]
    (.terminate (.br ⟨.l1246dd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l124845 : List UInt8 :=
  [0x41, 0xC1, 0xE4, 0x07, 0x41, 0x83, 0xE7, 0x7F, 0x45, 0x09, 0xE7, 0xE9, 0x88, 0xFE, 0xFF, 0xFF]

theorem code_l124845 : ∀ x ∈ codeRange 0x124845 bytes_l124845, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24845 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124855 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124855 (movR32M32LowEffect 0x124855 1 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x124855 (LoadPre 0x124855 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x124855 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124855 1 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124859 (movR64M64Effect 0x124859 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x124859 (LoadPre 0x124859 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124859 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124859 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12485e (movR64M64Effect 0x12485e 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x12485e (LoadPre 0x12485e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12485e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12485e 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x124863 (movR64M64Effect 0x124863 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x124863 (LoadPre 0x124863 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x124863 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124863 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x124868 (StorePre 0x124868 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x124868 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124868 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x12486c (movR64M64Effect 0x12486c 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x12486c (LoadPre 0x12486c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12486c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12486c 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x124871 (StorePre 0x124871 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x124871 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124871 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x124875 (movR64M64Effect 0x124875 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x124875 (LoadPre 0x124875 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x124875 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124875 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x12487a (StorePre 0x12487a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x12487a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12487a 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x12487e (movR64M64Effect 0x12487e 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x12487e (LoadPre 0x12487e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12487e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12487e 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x124883 (StorePre 0x124883 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x124883 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124883 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 71) (.exec 0x124887 (StorePre 0x124887 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124887 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124887 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 72) (.exec 0x124889 (StorePre 0x124889 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124889 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124889 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 73) (.exec 0x12488c (StorePre 0x12488c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12488c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12488c 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 74) (.exec 0x124890 (StorePre 0x124890 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x124890 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124890 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[57, 3]
    (.terminate (.br ⟨.l124894, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l124855 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x04, 0x48, 0x8B, 0x54, 0x24, 0x08, 0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x8B,
    0x7C, 0x24, 0x30, 0x48, 0x89, 0x7B, 0x30, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x89, 0x7B, 0x28,
    0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x89, 0x7B, 0x20, 0x48, 0x8B, 0x7C, 0x24, 0x18, 0x48, 0x89,
    0x7B, 0x18, 0x89, 0x03, 0x89, 0x4B, 0x04, 0x48, 0x89, 0x53, 0x08, 0x48, 0x89, 0x73, 0x10]

theorem code_l124855 : ∀ x ∈ codeRange 0x124855 bytes_l124855, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24855 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124894 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124894 (addR64Imm8Effect 0x124894 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x124894 (fun s => s.RIP = 0x124894) (addR64Imm8Effect 0x124894 4 0x38) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124898 (popR64Effect 0x124898 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x124898 (popR64Effect 0x124898 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x124898 (PopPre 0x124898) (popR64Effect 0x124898 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x124899 (popR64Effect 0x124899 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x124899 (popR64Effect 0x124899 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x124899 (PopPre 0x124899) (popR64Effect 0x124899 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x12489b (popR64Effect 0x12489b 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x12489b (popR64Effect 0x12489b 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x12489b (PopPre 0x12489b) (popR64Effect 0x12489b 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x12489d (popR64Effect 0x12489d 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x12489d (popR64Effect 0x12489d 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x12489d (PopPre 0x12489d) (popR64Effect 0x12489d 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x12489f (popR64Effect 0x12489f 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x12489f (popR64Effect 0x12489f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x12489f (PopPre 0x12489f) (popR64Effect 0x12489f 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x1248a1 (popR64Effect 0x1248a1 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x1248a1 (popR64Effect 0x1248a1 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x1248a1 (PopPre 0x1248a1) (popR64Effect 0x1248a1 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x1248a2 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x1248a2 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x1248a2 (RetPre 0x1248a2) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l124894 : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x38, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l124894 : ∀ x ∈ codeRange 0x124894 bytes_l124894, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24894 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1248a3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1248a3 (movR32Imm32Effect 0x1248a3 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x1248a3 (fun s => s.RIP = 0x1248a3) (movR32Imm32Effect 0x1248a3 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1248a8 (movR64Imm32Effect 0x1248a8 2 0x2036e0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x1248a8 (fun s => s.RIP = 0x1248a8) (movR64Imm32Effect 0x1248a8 2 0x2036e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1248af (callEffect (fun _ => 0x129c90) 0x1248b4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1248af (PushPre 0x1248af 5) (callEffect (fun _ => 0x129c90) 0x1248b4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1248b4⟩) #v[]
    (.terminate (.call ⟨.l129c90, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l1248b4, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1248a3 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00, 0xE8, 0xDC, 0x53, 0x00,
    0x00]

theorem code_l1248a3 : ∀ x ∈ codeRange 0x1248a3 bytes_l1248a3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x248a3 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1248b4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1248b4 (fun s => s.RIP = 0x1248b4) (fun _ => nopEffect 0x1248b4 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x1248be (fun s => s.RIP = 0x1248be) (fun _ => nopEffect 0x1248be 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1248c0, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1248b4 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x66, 0x90]

theorem code_l1248b4 : ∀ x ∈ codeRange 0x1248b4 bytes_l1248b4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x248b4 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1248c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1248c0 (pushR64Effect 0x1248c0 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x1248c0 (PushPre 0x1248c0 2) (pushR64Effect 0x1248c0 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x1248c2 (pushR64Effect 0x1248c2 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x1248c2 (PushPre 0x1248c2 2) (pushR64Effect 0x1248c2 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x1248c4 (pushR64Effect 0x1248c4 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[55, 12]
    (.letOp (n := 58) (.exec 0x1248c4 (PushPre 0x1248c4 2) (pushR64Effect 0x1248c4 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[55, 12]
    (.letOp (n := 59) (.out 0x1248c6 (pushR64Effect 0x1248c6 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[57, 3]
    (.letOp (n := 60) (.exec 0x1248c6 (PushPre 0x1248c6 1) (pushR64Effect 0x1248c6 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 61) (.out 0x1248c7 (subR64Imm32Effect 0x1248c7 4 0x98) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x1248c7 (fun s => s.RIP = 0x1248c7) (subR64Imm32Effect 0x1248c7 4 0x98) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x1248ce (movR64R64Effect 0x1248ce 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 64) (.exec 0x1248ce (fun s => s.RIP = 0x1248ce) (movR64R64Effect 0x1248ce 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 65) (.out 0x1248d1 (movR32M32Effect 0x1248d1 14 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 66) (.exec 0x1248d1 (LoadPre 0x1248d1 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1248d1 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1248d1 14 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 67) (.exec 0x1248d5 (StorePre 0x1248d5 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x1248d5 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1248d5 (.sib 4 none 0 (.d32 0x8f)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 68) (.exec 0x1248e1 (StorePre 0x1248e1 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1248e1 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1248e1 (.sib 4 none 0 (.d32 0x88)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 69) (.exec 0x1248ed (StorePre 0x1248ed 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1248ed + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1248ed (.sib 4 none 0 (.d32 0x80)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 70) (.exec 0x1248f9 (StorePre 0x1248f9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1248f9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1248f9 (.sib 4 none 0 (.d8 0x78)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 71) (.exec 0x124902 (StorePre 0x124902 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x124902 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124902 (.sib 4 none 0 (.d8 0x70)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 72) (.out 0x12490b (cmpR64Imm8Effect 0x12490b 14 0x28) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[65]
    (.letOp (n := 73) (.exec 0x12490b (fun s => s.RIP = 0x12490b) (cmpR64Imm8Effect 0x12490b 14 0x28) (Reg.operands [.gpr 14] [])) #v[65]
    (.letOp (n := 74) (.pure (condOp 3)) #v[72]
    (.terminate (.condBr (Fin.last 74) ⟨.l124996, RegMap.args [(2, 2), (3, 63), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (16, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ ⟨.l124915, RegMap.args [(2, 2), (3, 63), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (16, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l1248c0 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89,
    0xFB, 0x44, 0x8B, 0x72, 0x08, 0x48, 0xC7, 0x84, 0x24, 0x8F, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84,
    0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x70, 0x00, 0x00, 0x00, 0x00, 0x49, 0x83, 0xFE, 0x28, 0x0F,
    0x83, 0x81, 0x00, 0x00, 0x00]

theorem code_l1248c0 : ∀ x ∈ codeRange 0x1248c0 bytes_l1248c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x248c0 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124915 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124915 (leaR64Effect 0x124915 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x124915 (fun s => s.RIP = 0x124915) (leaR64Effect 0x124915 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12491a (movR64R64Effect 0x12491a 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 56) (.exec 0x12491a (fun s => s.RIP = 0x12491a) (movR64R64Effect 0x12491a 12 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x12491d (movR32R32Effect 0x12491d 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x12491d (fun s => s.RIP = 0x12491d) (movR32R32Effect 0x12491d 3 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x124920 (callEffect (fun _ => 0x127b80) 0x124925) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x124920 (PushPre 0x124920 5) (callEffect (fun _ => 0x127b80) 0x124925) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x124925⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l124925, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l124915 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x49, 0x89, 0xF4, 0x44, 0x89, 0xF2, 0xE8, 0x5B, 0x32, 0x00, 0x00]

theorem code_l124915 : ∀ x ∈ codeRange 0x124915 bytes_l124915, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24915 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124925 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124925 (movR32M32LowEffect 0x124925 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x124925 (LoadPre 0x124925 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124925 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124925 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124929 (cmpR32Imm8Effect 0x124929 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124929 (fun s => s.RIP = 0x124929) (cmpR32Imm8Effect 0x124929 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1249bc, RegMap.args [(1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124932, RegMap.args [(1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124925 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x83, 0xF9, 0x02, 0x0F, 0x85, 0x8A, 0x00, 0x00, 0x00]

theorem code_l124925 : ∀ x ∈ codeRange 0x124925 bytes_l124925, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24925 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124932 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124932 (movR64M64Effect 0x124932 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124932 (LoadPre 0x124932 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124932 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124932 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124937 (cmpR64R64Effect 0x124937 6 14) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 14] []) (.flag .ZF)) #v[53, 14]
    (.letOp (n := 56) (.exec 0x124937 (fun s => s.RIP = 0x124937) (cmpR64R64Effect 0x124937 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124acf, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124940, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124932 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x18, 0x4C, 0x39, 0xF6, 0x0F, 0x85, 0x8F, 0x01, 0x00, 0x00]

theorem code_l124932 : ∀ x ∈ codeRange 0x124932 bytes_l124932, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24932 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124940 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124940 (movR64M64Effect 0x124940 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124940 (LoadPre 0x124940 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124940 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124940 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124945 (leaR64Effect 0x124945 15 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x124945 (fun s => s.RIP = 0x124945) (leaR64Effect 0x124945 15 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12494a (movR64R64Effect 0x12494a 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x12494a (fun s => s.RIP = 0x12494a) (movR64R64Effect 0x12494a 7 15) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 59) (.out 0x12494d (movR64R64Effect 0x12494d 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 60) (.exec 0x12494d (fun s => s.RIP = 0x12494d) (movR64R64Effect 0x12494d 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x124950 (callEffect (callMemPtr 0x124950 (.rip 0xdf47a)) (0x124950 + BitVec.ofNat 64 (callMemLen (.rip 0xdf47a)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x124950 (GoesTo (CallMemPre 0x124950 (.rip 0xdf47a)) (callEffect (callMemPtr 0x124950 (.rip 0xdf47a)) (0x124950 + BitVec.ofNat 64 (callMemLen (.rip 0xdf47a)))) 0x12a820) (callEffect (callMemPtr 0x124950 (.rip 0xdf47a)) (0x124950 + BitVec.ofNat 64 (callMemLen (.rip 0xdf47a)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x124956⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 5), (6, 53), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l124956, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l124940 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x4C, 0x8D, 0x7C, 0x24, 0x70, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xF2,
    0xFF, 0x15, 0x7A, 0xF4, 0x0D, 0x00]

theorem code_l124940 : ∀ x ∈ codeRange 0x124940 bytes_l124940, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24940 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124956 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124956 (leaR64Effect 0x124956 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x124956 (fun s => s.RIP = 0x124956) (leaR64Effect 0x124956 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12495b (movR64R64Effect 0x12495b 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 56) (.exec 0x12495b (fun s => s.RIP = 0x12495b) (movR64R64Effect 0x12495b 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x12495e (movR64R64Effect 0x12495e 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x12495e (fun s => s.RIP = 0x12495e) (movR64R64Effect 0x12495e 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x124961 (callEffect (fun _ => 0x127fc0) 0x124966) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x124961 (PushPre 0x124961 5) (callEffect (fun _ => 0x127fc0) 0x124966) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x124966⟩) #v[]
    (.terminate (.call ⟨.l127fc0, RegMap.args [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l124966, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l124956 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x60, 0x4C, 0x89, 0xFE, 0x4C, 0x89, 0xF2, 0xE8, 0x5A, 0x36, 0x00, 0x00]

theorem code_l124956 : ∀ x ∈ codeRange 0x124956 bytes_l124956, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24956 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124966 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124966 (movR64M64Effect 0x124966 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124966 (LoadPre 0x124966 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x124966 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124966 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12496b (testR64R64Effect 0x12496b 6 6) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 6] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 56) (.exec 0x12496b (fun s => s.RIP = 0x12496b) (testR64R64Effect 0x12496b 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[53, 53]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12497f, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124970, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124966 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x60, 0x48, 0x85, 0xF6, 0x74, 0x0F]

theorem code_l124966 : ∀ x ∈ codeRange 0x124966 bytes_l124966, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24966 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124970 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124970 (movR64M64Effect 0x124970 14 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x124970 (LoadPre 0x124970 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x124970 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124970 14 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124975 (cmpR64Imm8Effect 0x124975 14 0x28) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[53]
    (.letOp (n := 56) (.exec 0x124975 (fun s => s.RIP = 0x124975) (cmpR64Imm8Effect 0x124975 14 0x28) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 2)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124a35, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12497f, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124970 : List UInt8 :=
  [0x4C, 0x8B, 0x74, 0x24, 0x68, 0x49, 0x83, 0xFE, 0x28, 0x0F, 0x82, 0xB6, 0x00, 0x00, 0x00]

theorem code_l124970 : ∀ x ∈ codeRange 0x124970 bytes_l124970, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24970 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12497f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12497f (StorePre 0x12497f 6 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x20)) s (0x12497f + BitVec.ofNat 64 6)) 1) (movM8Imm8RexEffect 0x12497f (.sib 12 none 0 (.d8 0x20)) 0x1) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 54) (.out 0x124985 (movR32M32Effect 0x124985 0 (.sib 12 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 55) (.exec 0x124985 (LoadPre 0x124985 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x1c)) s (0x124985 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x124985 0 (.sib 12 none 0 (.d8 0x1c))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 56) (.out 0x12498a (movR32Imm32Effect 0x12498a 5 2 0x8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 57) (.exec 0x12498a (fun s => s.RIP = 0x12498a) (movR32Imm32Effect 0x12498a 5 2 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x12498f (movR32Imm32Effect 0x12498f 5 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 59) (.exec 0x12498f (fun s => s.RIP = 0x12498f) (movR32Imm32Effect 0x12498f 5 1 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1249f2, RegMap.args [(0, 54), (1, 58), (2, 56), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l12497f : List UInt8 :=
  [0x41, 0xC6, 0x44, 0x24, 0x20, 0x01, 0x41, 0x8B, 0x44, 0x24, 0x1C, 0xBA, 0x08, 0x00, 0x00, 0x00,
    0xB9, 0x01, 0x00, 0x00, 0x00, 0xEB, 0x5C]

theorem code_l12497f : ∀ x ∈ codeRange 0x12497f bytes_l12497f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2497f 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124996 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124996 (StorePre 0x124996 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124996 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124996 (.sib 4 none 0 (.d8 0xc)) 0x5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x12499f (StorePre 0x12499f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12499f + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x12499f (.sib 4 none 0 (.d8 0x8)) 0x5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1249a4 (StorePre 0x1249a4 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1249a4 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1249a4 (.base 6 (.d8 0x20)) 0x1) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.out 0x1249a8 (movR32M32LowEffect 0x1249a8 0 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 57) (.exec 0x1249a8 (LoadPre 0x1249a8 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x1249a8 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1249a8 0 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 58) (.out 0x1249ab (movR64M64Effect 0x1249ab 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x1249ab (LoadPre 0x1249ab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1249ab + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249ab 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x1249b0 (movR64M64Effect 0x1249b0 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 61) (.exec 0x1249b0 (LoadPre 0x1249b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1249b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249b0 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x1249b5 (movR32Imm32Effect 0x1249b5 5 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 63) (.exec 0x1249b5 (fun s => s.RIP = 0x1249b5) (movR32Imm32Effect 0x1249b5 5 1 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1249f2, RegMap.args [(0, 56), (1, 62), (2, 58), (3, 3), (4, 4), (5, 5), (6, 60), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l124996 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x0C, 0x05, 0x00, 0x00, 0x00, 0xC6, 0x44, 0x24, 0x08, 0x05, 0xC6, 0x46,
    0x20, 0x01, 0x8B, 0x46, 0x1C, 0x48, 0x8B, 0x54, 0x24, 0x08, 0x48, 0x8B, 0x74, 0x24, 0x10, 0xB9,
    0x01, 0x00, 0x00, 0x00, 0xEB, 0x36]

theorem code_l124996 : ∀ x ∈ codeRange 0x124996 bytes_l124996, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24996 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1249bc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1249bc (movR32M32LowEffect 0x1249bc 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1249bc (LoadPre 0x1249bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1249bc + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1249bc 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1249c0 (movR64M64Effect 0x1249c0 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x1249c0 (LoadPre 0x1249c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1249c0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249c0 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1249c5 (movR64M64Effect 0x1249c5 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x1249c5 (LoadPre 0x1249c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1249c5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249c5 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1249ca (movR64M64Effect 0x1249ca 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x1249ca (LoadPre 0x1249ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1249ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249ca 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1249cf (StorePre 0x1249cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1249cf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1249cf 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1249d4 (movR64M64Effect 0x1249d4 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x1249d4 (LoadPre 0x1249d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1249d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249d4 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1249d9 (StorePre 0x1249d9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1249d9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1249d9 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1249de (movR64M64Effect 0x1249de 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x1249de (LoadPre 0x1249de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1249de + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249de 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1249e3 (StorePre 0x1249e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1249e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1249e3 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1249e8 (movR64M64Effect 0x1249e8 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x1249e8 (LoadPre 0x1249e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1249e8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249e8 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x1249ed (StorePre 0x1249ed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1249ed + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1249ed 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.terminate (.br ⟨.l1249f2, RegMap.args [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l1249bc : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x0C, 0x48, 0x8B, 0x54, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x8B,
    0x7C, 0x24, 0x20, 0x48, 0x89, 0x7C, 0x24, 0x40, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x89, 0x7C,
    0x24, 0x48, 0x48, 0x8B, 0x7C, 0x24, 0x30, 0x48, 0x89, 0x7C, 0x24, 0x50, 0x48, 0x8B, 0x7C, 0x24,
    0x38, 0x48, 0x89, 0x7C, 0x24, 0x58]

theorem code_l1249bc : ∀ x ∈ codeRange 0x1249bc bytes_l1249bc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x249bc 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Verify.LIR
