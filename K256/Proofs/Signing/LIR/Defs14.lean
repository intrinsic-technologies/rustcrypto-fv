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

@[cfg_block] def b_l11c845 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c845 (movR32Imm32Effect 0x11c845 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11c845 (fun s => s.RIP = 0x11c845) (movR32Imm32Effect 0x11c845 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11c84a (movR64R64Effect 0x11c84a 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x11c84a (fun s => s.RIP = 0x11c84a) (movR64R64Effect 0x11c84a 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x11c84d (movR64R64Effect 0x11c84d 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11c84d (fun s => s.RIP = 0x11c84d) (movR64R64Effect 0x11c84d 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.exec 0x11c850 (RepPre 0x11c850 (RepMovsqPre 0x11c850)) (repMovsqEffect 0x11c850) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11c853 (movR32Imm32Effect 0x11c853 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11c853 (fun s => s.RIP = 0x11c853) (movR32Imm32Effect 0x11c853 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11c858 (movR64R64Effect 0x11c858 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 63) (.exec 0x11c858 (fun s => s.RIP = 0x11c858) (movR64R64Effect 0x11c858 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 64) (.out 0x11c85b (movR64R64Effect 0x11c85b 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 65) (.exec 0x11c85b (fun s => s.RIP = 0x11c85b) (movR64R64Effect 0x11c85b 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 66) (.out 0x11c85e (repMovsqEffect 0x11c85e) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[64, 62, 60, 22]
    (.letOp (n := 67) (.out 0x11c85e (repMovsqEffect 0x11c85e) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[64, 62, 60, 22]
    (.letOp (n := 68) (.out 0x11c85e (repMovsqEffect 0x11c85e) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[64, 62, 60, 22]
    (.letOp (n := 69) (.exec 0x11c85e (RepPre 0x11c85e (RepMovsqPre 0x11c85e)) (repMovsqEffect 0x11c85e) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[64, 62, 60, 22]
    (.letOp (n := 70) (.out 0x11c861 (addR64Imm32Effect 0x11c861 4 0x168) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 71) (.exec 0x11c861 (fun s => s.RIP = 0x11c861) (addR64Imm32Effect 0x11c861 4 0x168) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x11c868 (popR64Effect 0x11c868 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[70]
    (.letOp (n := 73) (.out 0x11c868 (popR64Effect 0x11c868 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x11c868 (PopPre 0x11c868) (popR64Effect 0x11c868 1 3) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x11c869 (popR64Effect 0x11c869 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[73]
    (.letOp (n := 76) (.out 0x11c869 (popR64Effect 0x11c869 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x11c869 (PopPre 0x11c869) (popR64Effect 0x11c869 2 12) (Reg.operands [.gpr 4] [])) #v[73]
    (.letOp (n := 78) (.out 0x11c86b (popR64Effect 0x11c86b 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[76]
    (.letOp (n := 79) (.out 0x11c86b (popR64Effect 0x11c86b 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[76]
    (.letOp (n := 80) (.exec 0x11c86b (PopPre 0x11c86b) (popR64Effect 0x11c86b 2 13) (Reg.operands [.gpr 4] [])) #v[76]
    (.letOp (n := 81) (.out 0x11c86d (popR64Effect 0x11c86d 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[79]
    (.letOp (n := 82) (.out 0x11c86d (popR64Effect 0x11c86d 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[79]
    (.letOp (n := 83) (.exec 0x11c86d (PopPre 0x11c86d) (popR64Effect 0x11c86d 2 14) (Reg.operands [.gpr 4] [])) #v[79]
    (.letOp (n := 84) (.out 0x11c86f (popR64Effect 0x11c86f 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[82]
    (.letOp (n := 85) (.out 0x11c86f (popR64Effect 0x11c86f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[82]
    (.letOp (n := 86) (.exec 0x11c86f (PopPre 0x11c86f) (popR64Effect 0x11c86f 2 15) (Reg.operands [.gpr 4] [])) #v[82]
    (.letOp (n := 87) (.out 0x11c871 (popR64Effect 0x11c871 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[85]
    (.letOp (n := 88) (.out 0x11c871 (popR64Effect 0x11c871 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[85]
    (.letOp (n := 89) (.exec 0x11c871 (PopPre 0x11c871) (popR64Effect 0x11c871 1 5) (Reg.operands [.gpr 4] [])) #v[85]
    (.letOp (n := 90) (.out 0x11c872 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[88]
    (.letOp (n := 91) (.out 0x11c872 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[88]
    (.letOp (n := 92) (.exec 0x11c872 (RetPre 0x11c872) (retEffect) (Reg.operands [.gpr 4] [])) #v[88]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 68), (2, 2), (3, 72), (4, 91), (5, 87), (6, 66), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (13, 78), (14, 81), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)] 93) (some ⟨90, by decide⟩))))))))))))))))))))))))))))))))))))))))))

def bytes_l11c845 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xF3, 0x48, 0xA5, 0x48, 0x81, 0xC4, 0x68,
    0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l11c845 : ∀ x ∈ codeRange 0x11c845 bytes_l11c845, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c845 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c880 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c880 (pushR64Effect 0x11c880 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x11c880 (PushPre 0x11c880 1) (pushR64Effect 0x11c880 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x11c881 (pushR64Effect 0x11c881 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x11c881 (PushPre 0x11c881 2) (pushR64Effect 0x11c881 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x11c883 (pushR64Effect 0x11c883 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x11c883 (PushPre 0x11c883 2) (pushR64Effect 0x11c883 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x11c885 (pushR64Effect 0x11c885 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x11c885 (PushPre 0x11c885 2) (pushR64Effect 0x11c885 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x11c887 (pushR64Effect 0x11c887 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x11c887 (PushPre 0x11c887 2) (pushR64Effect 0x11c887 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x11c889 (pushR64Effect 0x11c889 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x11c889 (PushPre 0x11c889 1) (pushR64Effect 0x11c889 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x11c88a (subR64Imm32Effect 0x11c88a 4 0xc88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x11c88a (fun s => s.RIP = 0x11c88a) (subR64Imm32Effect 0x11c88a 4 0xc88) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x11c891 (StorePre 0x11c891 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11c891 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c891 9 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 65]
    (.letOp (n := 68) (.exec 0x11c899 (StorePre 0x11c899 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11c899 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c899 6 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 65]
    (.letOp (n := 69) (.exec 0x11c8a1 (StorePre 0x11c8a1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x248)) s (0x11c8a1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c8a1 7 (.sib 4 none 0 (.d32 0x248))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 70) (.out 0x11c8a9 (movR64M64Effect 0x11c8a9 6 (.sib 4 none 0 (.d32 0xcc0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 71) (.exec 0x11c8a9 (LoadPre 0x11c8a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc0)) s (0x11c8a9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11c8a9 6 (.sib 4 none 0 (.d32 0xcc0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 72) (.out 0x11c8b1 (testR64R64Effect 0x11c8b1 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 73) (.exec 0x11c8b1 (fun s => s.RIP = 0x11c8b1) (testR64R64Effect 0x11c8b1 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 74) (.exec 0x11c8b4 (StorePre 0x11c8b4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x11c8b4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c8b4 8 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 65]
    (.letOp (n := 75) (.exec 0x11c8bc (StorePre 0x11c8bc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x11c8bc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c8bc 2 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 65]
    (.letOp (n := 76) (.exec 0x11c8c4 (StorePre 0x11c8c4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x11c8c4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c8c4 1 (.sib 4 none 0 (.d32 0x1c0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 65]
    (.letOp (n := 77) (.pure (condOp 4)) #v[72]
    (.terminate (.condBr (Fin.last 77) ⟨.l11d731, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 70), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ ⟨.l11c8d2, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 70), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l11c880 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x88, 0x0C, 0x00,
    0x00, 0x4C, 0x89, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xB4, 0x24, 0xB0, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xBC, 0x24, 0x48, 0x02, 0x00, 0x00, 0x48, 0x8B, 0xB4, 0x24, 0xC0, 0x0C, 0x00,
    0x00, 0x48, 0x85, 0xD2, 0x4C, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24,
    0xA0, 0x01, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xC0, 0x01, 0x00, 0x00, 0x0F, 0x84, 0x5F, 0x0E,
    0x00, 0x00]

theorem code_l11c880 : ∀ x ∈ codeRange 0x11c880 bytes_l11c880, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c880 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c8d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c8d2 (movR64R64Effect 0x11c8d2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x11c8d2 (fun s => s.RIP = 0x11c8d2) (movR64R64Effect 0x11c8d2 0 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x11c8d5 (shlR64Effect 0x11c8d5 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x11c8d5 (fun s => s.RIP = 0x11c8d5) (shlR64Effect 0x11c8d5 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x11c8d9 (leaR64Effect 0x11c8d9 0 (.sib 0 (some 6) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[55, 6]
    (.letOp (n := 58) (.exec 0x11c8d9 (fun s => s.RIP = 0x11c8d9) (leaR64Effect 0x11c8d9 0 (.sib 0 (some 6) 1 .none)) (Reg.operands [.gpr 0, .gpr 6] [])) #v[55, 6]
    (.letOp (n := 59) (.exec 0x11c8dd (StorePre 0x11c8dd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11c8dd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c8dd 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x11c8e2 (imulR64R64Imm32Effect 0x11c8e2 7 0 2 0x98) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 61) (.exec 0x11c8e2 (fun s => s.RIP = 0x11c8e2) (imulR64R64Imm32Effect 0x11c8e2 7 0 2 0x98) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 62) (.exec 0x11c8e9 (StorePre 0x11c8e9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11c8e9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c8e9 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x11c8f1 (imulR64R64Imm32Effect 0x11c8f1 7 0 8 0x98) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 64) (.exec 0x11c8f1 (fun s => s.RIP = 0x11c8f1) (imulR64R64Imm32Effect 0x11c8f1 7 0 8 0x98) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 65) (.exec 0x11c8f8 (StorePre 0x11c8f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11c8f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c8f8 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x11c8fd (xorR32R32Effect 0x11c8fd 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 67) (.exec 0x11c8fd (fun s => s.RIP = 0x11c8fd) (xorR32R32Effect 0x11c8fd 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 68) (.out 0x11c900 (leaR64Effect 0x11c900 12 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 69) (.exec 0x11c900 (fun s => s.RIP = 0x11c900) (leaR64Effect 0x11c900 12 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x11c908 (leaR64Effect 0x11c908 15 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 71) (.exec 0x11c908 (fun s => s.RIP = 0x11c908) (leaR64Effect 0x11c908 15 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x11c910 (movR64R64Effect 0x11c910 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[1]
    (.letOp (n := 73) (.exec 0x11c910 (fun s => s.RIP = 0x11c910) (movR64R64Effect 0x11c910 5 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 74) (.out 0x11c913 (xorR32R32Effect 0x11c913 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 75) (.exec 0x11c913 (fun s => s.RIP = 0x11c913) (xorR32R32Effect 0x11c913 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 76) (.exec 0x11c915 (fun s => s.RIP = 0x11c915) (fun _ => nopEffect 0x11c915 11) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l11c920, RegMap.args [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (5, 72), (6, 74), (8, 8), (12, 68), (13, 13), (14, 66), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l11c8d2 : List UInt8 :=
  [0x48, 0x89, 0xF0, 0x48, 0xC1, 0xE0, 0x06, 0x48, 0x8D, 0x04, 0x70, 0x48, 0x89, 0x44, 0x24, 0x60,
    0x48, 0x69, 0xC2, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49,
    0x69, 0xC0, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x68, 0x45, 0x31, 0xF6, 0x4C, 0x8D,
    0xA4, 0x24, 0x28, 0x01, 0x00, 0x00, 0x4C, 0x8D, 0xBC, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x48, 0x89,
    0xCD, 0x31, 0xF6, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l11c8d2 : ∀ x ∈ codeRange 0x11c8d2 bytes_l11c8d2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c8d2 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c920 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11c920 (StorePre 0x11c920 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11c920 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c920 6 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 54) (.exec 0x11c928 (StorePre 0x11c928 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11c928 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11c928 5 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 55) (.exec 0x11c930 (StorePre 0x11c930 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11c930 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c930 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 56) (.out 0x11c935 (movR64M64Effect 0x11c935 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x11c935 (LoadPre 0x11c935 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11c935 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11c935 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x11c93d (leaR64Effect 0x11c93d 0 (.sib 1 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 14] []) (.reg (.gpr 0))) #v[56, 14]
    (.letOp (n := 59) (.exec 0x11c93d (fun s => s.RIP = 0x11c93d) (leaR64Effect 0x11c93d 0 (.sib 1 (some 14) 0 .none)) (Reg.operands [.gpr 1, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 60) (.exec 0x11c941 (StorePre 0x11c941 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11c941 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11c941 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x11c946 (leaR64Effect 0x11c946 5 (.sib 1 (some 14) 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1, .gpr 14] []) (.reg (.gpr 5))) #v[56, 14]
    (.letOp (n := 62) (.exec 0x11c946 (fun s => s.RIP = 0x11c946) (leaR64Effect 0x11c946 5 (.sib 1 (some 14) 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 63) (.out 0x11c94b (movR64R64Effect 0x11c94b 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 64) (.exec 0x11c94b (fun s => s.RIP = 0x11c94b) (movR64R64Effect 0x11c94b 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 65) (.out 0x11c94e (movR64R64Effect 0x11c94e 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 66) (.exec 0x11c94e (fun s => s.RIP = 0x11c94e) (movR64R64Effect 0x11c94e 6 5) (Reg.operands [.gpr 5] [])) #v[61]
    (.letOp (n := 67) (.out 0x11c951 (movR64Imm32Effect 0x11c951 2 0x202200) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 68) (.exec 0x11c951 (fun s => s.RIP = 0x11c951) (movR64Imm32Effect 0x11c951 2 0x202200) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x11c958 (callEffect (fun _ => 0x11b8f0) 0x11c95d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x11c958 (PushPre 0x11c958 5) (callEffect (fun _ => 0x11b8f0) 0x11c95d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x11c95d⟩) #v[]
    (.terminate (.call ⟨.l11b8f0, RegMap.args [(0, 58), (1, 56), (2, 67), (3, 3), (4, 69), (5, 61), (6, 65), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l11c95d, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l11c920 : List UInt8 :=
  [0x48, 0x89, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xAC, 0x24, 0xD8, 0x00, 0x00, 0x00,
    0x4C, 0x89, 0x74, 0x24, 0x08, 0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4A, 0x8D, 0x04,
    0x31, 0x48, 0x89, 0x44, 0x24, 0x38, 0x4A, 0x8D, 0x6C, 0x31, 0x78, 0x4C, 0x89, 0xE7, 0x48, 0x89,
    0xEE, 0x48, 0xC7, 0xC2, 0x00, 0x22, 0x20, 0x00, 0xE8, 0x93, 0xEF, 0xFF, 0xFF]

theorem code_l11c920 : ∀ x ∈ codeRange 0x11c920 bytes_l11c920, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c920 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c95d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c95d (leaR64Effect 0x11c95d 3 (.sib 4 none 0 (.d32 0xc10))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x11c95d (fun s => s.RIP = 0x11c95d) (leaR64Effect 0x11c95d 3 (.sib 4 none 0 (.d32 0xc10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11c965 (movR64R64Effect 0x11c965 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x11c965 (fun s => s.RIP = 0x11c965) (movR64R64Effect 0x11c965 7 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 57) (.out 0x11c968 (movR64R64Effect 0x11c968 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x11c968 (fun s => s.RIP = 0x11c968) (movR64R64Effect 0x11c968 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c96b (movR64Imm32Effect 0x11c96b 2 0x202220) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x11c96b (fun s => s.RIP = 0x11c96b) (movR64Imm32Effect 0x11c96b 2 0x202220) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x11c972 (callEffect (fun _ => 0x1099c0) 0x11c977) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x11c972 (PushPre 0x11c972 5) (callEffect (fun _ => 0x1099c0) 0x11c977) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x11c977⟩) #v[]
    (.terminate (.call ⟨.l1099c0, RegMap.args [(2, 59), (3, 53), (4, 61), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l11c977, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l11c95d : List UInt8 :=
  [0x48, 0x8D, 0x9C, 0x24, 0x10, 0x0C, 0x00, 0x00, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xE6, 0x48, 0xC7,
    0xC2, 0x20, 0x22, 0x20, 0x00, 0xE8, 0x49, 0xD0, 0xFE, 0xFF]

theorem code_l11c95d : ∀ x ∈ codeRange 0x11c95d bytes_l11c95d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c95d 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c977 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c977 (movR64R64Effect 0x11c977 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 54) (.exec 0x11c977 (fun s => s.RIP = 0x11c977) (movR64R64Effect 0x11c977 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x11c97a (movR64R64Effect 0x11c97a 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 56) (.exec 0x11c97a (fun s => s.RIP = 0x11c97a) (movR64R64Effect 0x11c97a 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x11c97d (movR64Imm32Effect 0x11c97d 2 0x202240) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x11c97d (fun s => s.RIP = 0x11c97d) (movR64Imm32Effect 0x11c97d 2 0x202240) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x11c984 (callEffect (fun _ => 0x11b8f0) 0x11c989) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11c984 (PushPre 0x11c984 5) (callEffect (fun _ => 0x11b8f0) 0x11c989) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11c989⟩) #v[]
    (.terminate (.call ⟨.l11b8f0, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l11c989, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11c977 : List UInt8 :=
  [0x4C, 0x89, 0xE7, 0x48, 0x89, 0xEE, 0x48, 0xC7, 0xC2, 0x40, 0x22, 0x20, 0x00, 0xE8, 0x67, 0xEF,
    0xFF, 0xFF]

theorem code_l11c977 : ∀ x ∈ codeRange 0x11c977 bytes_l11c977, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c977 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c989 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c989 (leaR64Effect 0x11c989 13 (.sib 4 none 0 (.d32 0x328))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 54) (.exec 0x11c989 (fun s => s.RIP = 0x11c989) (leaR64Effect 0x11c989 13 (.sib 4 none 0 (.d32 0x328))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11c991 (movR64R64Effect 0x11c991 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x11c991 (fun s => s.RIP = 0x11c991) (movR64R64Effect 0x11c991 7 13) (Reg.operands [.gpr 13] [])) #v[53]
    (.letOp (n := 57) (.out 0x11c994 (movR64R64Effect 0x11c994 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x11c994 (fun s => s.RIP = 0x11c994) (movR64R64Effect 0x11c994 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c997 (movR64Imm32Effect 0x11c997 2 0x202260) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x11c997 (fun s => s.RIP = 0x11c997) (movR64Imm32Effect 0x11c997 2 0x202260) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x11c99e (callEffect (fun _ => 0x1099c0) 0x11c9a3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x11c99e (PushPre 0x11c99e 5) (callEffect (fun _ => 0x1099c0) 0x11c9a3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x11c9a3⟩) #v[]
    (.terminate (.call ⟨.l1099c0, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l11c9a3, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l11c989 : List UInt8 :=
  [0x4C, 0x8D, 0xAC, 0x24, 0x28, 0x03, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xE6, 0x48, 0xC7,
    0xC2, 0x60, 0x22, 0x20, 0x00, 0xE8, 0x1D, 0xD0, 0xFE, 0xFF]

theorem code_l11c989 : ∀ x ∈ codeRange 0x11c989 bytes_l11c989, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c989 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c9a3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c9a3 (leaR64Effect 0x11c9a3 14 (.sib 4 none 0 (.d32 0x418))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x11c9a3 (fun s => s.RIP = 0x11c9a3) (leaR64Effect 0x11c9a3 14 (.sib 4 none 0 (.d32 0x418))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11c9ab (movR64R64Effect 0x11c9ab 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x11c9ab (fun s => s.RIP = 0x11c9ab) (movR64R64Effect 0x11c9ab 7 14) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 57) (.out 0x11c9ae (movR64R64Effect 0x11c9ae 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 58) (.exec 0x11c9ae (fun s => s.RIP = 0x11c9ae) (movR64R64Effect 0x11c9ae 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x11c9b1 (movR64R64Effect 0x11c9b1 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 60) (.exec 0x11c9b1 (fun s => s.RIP = 0x11c9b1) (movR64R64Effect 0x11c9b1 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x11c9b4 (movR64Imm32Effect 0x11c9b4 1 0x2021a0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 62) (.exec 0x11c9b4 (fun s => s.RIP = 0x11c9b4) (movR64Imm32Effect 0x11c9b4 1 0x2021a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x11c9bb (callEffect (fun _ => 0x1109b0) 0x11c9c0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x11c9bb (PushPre 0x11c9bb 5) (callEffect (fun _ => 0x1109b0) 0x11c9c0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x11c9c0⟩) #v[]
    (.terminate (.call ⟨.l1109b0, RegMap.args [(0, 0), (1, 61), (2, 59), (3, 3), (4, 63), (5, 5), (6, 57), (7, 55), (8, 8), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l11c9c0, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l11c9a3 : List UInt8 :=
  [0x4C, 0x8D, 0xB4, 0x24, 0x18, 0x04, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x48, 0x89, 0xDE, 0x4C, 0x89,
    0xEA, 0x48, 0xC7, 0xC1, 0xA0, 0x21, 0x20, 0x00, 0xE8, 0xF0, 0x3F, 0xFF, 0xFF]

theorem code_l11c9a3 : ∀ x ∈ codeRange 0x11c9a3 bytes_l11c9a3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c9a3 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c9c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c9c0 (movR64R64Effect 0x11c9c0 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 54) (.exec 0x11c9c0 (fun s => s.RIP = 0x11c9c0) (movR64R64Effect 0x11c9c0 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x11c9c3 (movR64R64Effect 0x11c9c3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x11c9c3 (fun s => s.RIP = 0x11c9c3) (movR64R64Effect 0x11c9c3 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x11c9c6 (movR64Imm32Effect 0x11c9c6 2 0x202280) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x11c9c6 (fun s => s.RIP = 0x11c9c6) (movR64Imm32Effect 0x11c9c6 2 0x202280) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x11c9cd (callEffect (fun _ => 0x1099c0) 0x11c9d2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11c9cd (PushPre 0x11c9cd 5) (callEffect (fun _ => 0x1099c0) 0x11c9d2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11c9d2⟩) #v[]
    (.terminate (.call ⟨.l1099c0, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l11c9d2, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11c9c0 : List UInt8 :=
  [0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0x48, 0xC7, 0xC2, 0x80, 0x22, 0x20, 0x00, 0xE8, 0xEE, 0xCF,
    0xFE, 0xFF]

theorem code_l11c9c0 : ∀ x ∈ codeRange 0x11c9c0 bytes_l11c9c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c9c0 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c9d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c9d2 (movR64R64Effect 0x11c9d2 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 54) (.exec 0x11c9d2 (fun s => s.RIP = 0x11c9d2) (movR64R64Effect 0x11c9d2 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x11c9d5 (movR64R64Effect 0x11c9d5 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 56) (.exec 0x11c9d5 (fun s => s.RIP = 0x11c9d5) (movR64R64Effect 0x11c9d5 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x11c9d8 (movR64R64Effect 0x11c9d8 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 58) (.exec 0x11c9d8 (fun s => s.RIP = 0x11c9d8) (movR64R64Effect 0x11c9d8 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11c9db (movR64Imm32Effect 0x11c9db 1 0x2021a0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x11c9db (fun s => s.RIP = 0x11c9db) (movR64Imm32Effect 0x11c9db 1 0x2021a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x11c9e2 (callEffect (fun _ => 0x1109b0) 0x11c9e7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x11c9e2 (PushPre 0x11c9e2 5) (callEffect (fun _ => 0x1109b0) 0x11c9e7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x11c9e7⟩) #v[]
    (.terminate (.call ⟨.l1109b0, RegMap.args [(0, 0), (1, 59), (2, 57), (3, 3), (4, 61), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l11c9e7, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l11c9d2 : List UInt8 :=
  [0x4C, 0x89, 0xFF, 0x48, 0x89, 0xEE, 0x4C, 0x89, 0xE2, 0x48, 0xC7, 0xC1, 0xA0, 0x21, 0x20, 0x00,
    0xE8, 0xC9, 0x3F, 0xFF, 0xFF]

theorem code_l11c9d2 : ∀ x ∈ codeRange 0x11c9d2 bytes_l11c9d2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c9d2 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c9e7_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.out 0x11ca6d (leaR64Effect 0x11ca6d 7 (.sib 4 none 0 (.d32 0x2b0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 87) (.exec 0x11ca6d (fun s => s.RIP = 0x11ca6d) (leaR64Effect 0x11ca6d 7 (.sib 4 none 0 (.d32 0x2b0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.out 0x11ca75 (movR64M64Effect 0x11ca75 6 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 89) (.exec 0x11ca75 (LoadPre 0x11ca75 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11ca75 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ca75 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x11ca7a (callEffect (fun _ => 0x10e010) 0x11ca7f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 91) (.exec 0x11ca7a (PushPre 0x11ca7a 5) (callEffect (fun _ => 0x10e010) 0x11ca7f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.const ⟨64, 0x11ca7f⟩) #v[]
    (.terminate (.call ⟨.l10e010, RegMap.args [(0, 83), (1, 63), (2, 55), (3, 69), (4, 90), (5, 67), (6, 88), (7, 86), (12, 73), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩ { target := .l11ca7f, kept := #v[], arity := rfl, guard := some (Fin.last 92) }))))))))

def bytes_l11c9e7_1 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x38, 0xE8, 0x91, 0x15,
    0xFF, 0xFF]

theorem code_l11c9e7_1 : ∀ x ∈ codeRange 0x11ca6d bytes_l11c9e7_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1ca6d 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11c9e7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11c9e7 (movR64M64Effect 0x11c9e7 0 (.sib 4 none 0 (.d32 0x430))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11c9e7 (LoadPre 0x11c9e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x430)) s (0x11c9e7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11c9e7 0 (.sib 4 none 0 (.d32 0x430))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11c9ef (leaR64Effect 0x11c9ef 2 (.sib 4 none 0 (.d32 0x1f0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x11c9ef (fun s => s.RIP = 0x11c9ef) (leaR64Effect 0x11c9ef 2 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x11c9f7 (StorePre 0x11c9f7 4 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x11c9f7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11c9f7 0 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 2] [])) #v[53, 55]
    (.letOp (n := 58) (.out 0x11c9fb (movR64M64Effect 0x11c9fb 0 (.sib 4 none 0 (.d32 0x428))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 59) (.exec 0x11c9fb (LoadPre 0x11c9fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x428)) s (0x11c9fb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11c9fb 0 (.sib 4 none 0 (.d32 0x428))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x11ca03 (StorePre 0x11ca03 4 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x11ca03 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ca03 0 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 2] [])) #v[58, 55]
    (.letOp (n := 61) (.out 0x11ca07 (movR64M64Effect 0x11ca07 0 (.sib 4 none 0 (.d32 0x418))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 62) (.exec 0x11ca07 (LoadPre 0x11ca07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x418)) s (0x11ca07 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca07 0 (.sib 4 none 0 (.d32 0x418))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x11ca0f (movR64M64Effect 0x11ca0f 1 (.sib 4 none 0 (.d32 0x420))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 64) (.exec 0x11ca0f (LoadPre 0x11ca0f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x420)) s (0x11ca0f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca0f 1 (.sib 4 none 0 (.d32 0x420))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x11ca17 (StorePre 0x11ca17 4 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x11ca17 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ca17 1 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[63, 55]
    (.letOp (n := 66) (.exec 0x11ca1b (StorePre 0x11ca1b 3 (fun s => AddrMode.addr (.base 2 .none) s (0x11ca1b + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11ca1b 0 (.base 2 .none)) (Reg.operands [.gpr 0, .gpr 2] [])) #v[61, 55]
    (.letOp (n := 67) (.out 0x11ca1e (movR64M64Effect 0x11ca1e 5 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 68) (.exec 0x11ca1e (LoadPre 0x11ca1e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11ca1e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca1e 5 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x11ca26 (movR64M64Effect 0x11ca26 3 (.sib 4 none 0 (.d32 0x1d8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 70) (.exec 0x11ca26 (LoadPre 0x11ca26 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x11ca26 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca26 3 (.sib 4 none 0 (.d32 0x1d8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x11ca2e (movR64M64Effect 0x11ca2e 13 (.sib 4 none 0 (.d32 0x1e0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 72) (.exec 0x11ca2e (LoadPre 0x11ca2e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x11ca2e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca2e 13 (.sib 4 none 0 (.d32 0x1e0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x11ca36 (movR64M64Effect 0x11ca36 12 (.sib 4 none 0 (.d32 0x1e8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 74) (.exec 0x11ca36 (LoadPre 0x11ca36 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x11ca36 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca36 12 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x11ca3e (movR64M64Effect 0x11ca3e 14 (.sib 4 none 0 (.d32 0x1f0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 76) (.exec 0x11ca3e (LoadPre 0x11ca3e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f0)) s (0x11ca3e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca3e 14 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x11ca46 (movR64M64Effect 0x11ca46 0 (.sib 4 none 0 (.d32 0x1f8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 78) (.exec 0x11ca46 (LoadPre 0x11ca46 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f8)) s (0x11ca46 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca46 0 (.sib 4 none 0 (.d32 0x1f8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x11ca4e (StorePre 0x11ca4e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11ca4e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ca4e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[77, 4]
    (.letOp (n := 80) (.out 0x11ca53 (movR64M64Effect 0x11ca53 0 (.sib 4 none 0 (.d32 0x200))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 81) (.exec 0x11ca53 (LoadPre 0x11ca53 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x200)) s (0x11ca53 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca53 0 (.sib 4 none 0 (.d32 0x200))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x11ca5b (StorePre 0x11ca5b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11ca5b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ca5b 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.out 0x11ca60 (movR64M64Effect 0x11ca60 0 (.sib 4 none 0 (.d32 0x208))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 84) (.exec 0x11ca60 (LoadPre 0x11ca60 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x208)) s (0x11ca60 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ca60 0 (.sib 4 none 0 (.d32 0x208))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.exec 0x11ca68 (StorePre 0x11ca68 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11ca68 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ca68 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 4]
    (b_l11c9e7_1)))))))))))))))))))))))))))))))))

def bytes_l11c9e7 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x30, 0x04, 0x00, 0x00, 0x48, 0x8D, 0x94, 0x24, 0xF0, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x42, 0x18, 0x48, 0x8B, 0x84, 0x24, 0x28, 0x04, 0x00, 0x00, 0x48, 0x89, 0x42, 0x10,
    0x48, 0x8B, 0x84, 0x24, 0x18, 0x04, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x20, 0x04, 0x00, 0x00,
    0x48, 0x89, 0x4A, 0x08, 0x48, 0x89, 0x02, 0x48, 0x8B, 0xAC, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x48,
    0x8B, 0x9C, 0x24, 0xD8, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0xAC, 0x24, 0xE0, 0x01, 0x00, 0x00, 0x4C,
    0x8B, 0xA4, 0x24, 0xE8, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0xB4, 0x24, 0xF0, 0x01, 0x00, 0x00, 0x48,
    0x8B, 0x84, 0x24, 0xF8, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x40, 0x48, 0x8B, 0x84, 0x24,
    0x00, 0x02, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x84, 0x24, 0x08, 0x02, 0x00,
    0x00, 0x48, 0x89, 0x44, 0x24, 0x28] ++ bytes_l11c9e7_1

theorem code_l11c9e7 : ∀ x ∈ codeRange 0x11c9e7 bytes_l11c9e7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1c9e7 134 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11c9e7_1

@[cfg_block] def b_l11ca7f_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.out 0x11cae5 (movR64R64Effect 0x11cae5 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 89) (.exec 0x11cae5 (fun s => s.RIP = 0x11cae5) (movR64R64Effect 0x11cae5 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 90) (.out 0x11cae8 (notR64Effect 0x11cae8 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[88]
    (.letOp (n := 91) (.exec 0x11cae8 (fun s => s.RIP = 0x11cae8) (notR64Effect 0x11cae8 1) (Reg.operands [.gpr 1] [])) #v[88]
    (.letOp (n := 92) (.out 0x11caeb (addR64R64Effect 0x11caeb 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[90, 85]
    (.letOp (n := 93) (.exec 0x11caeb (fun s => s.RIP = 0x11caeb) (addR64R64Effect 0x11caeb 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[90, 85]
    (.letOp (n := 94) (.out 0x11caee (andR64R64Effect 0x11caee 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[92, 13]
    (.letOp (n := 95) (.exec 0x11caee (fun s => s.RIP = 0x11caee) (andR64R64Effect 0x11caee 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[92, 13]
    (.letOp (n := 96) (.out 0x11caf1 (shrR64Effect 0x11caf1 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[94]
    (.letOp (n := 97) (.exec 0x11caf1 (fun s => s.RIP = 0x11caf1) (shrR64Effect 0x11caf1 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[94]
    (.letOp (n := 98) (.exec 0x11caf5 (StorePre 0x11caf5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11caf5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11caf5 1 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[96, 4]
    (.letOp (n := 99) (.out 0x11cafd (xorR32R32Effect 0x11cafd 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[85, 85]
    (.letOp (n := 100) (.exec 0x11cafd (fun s => s.RIP = 0x11cafd) (xorR32R32Effect 0x11cafd 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[85, 85]
    (.letOp (n := 101) (.out 0x11caff (subR64M64Effect 0x11caff 0 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[99, 4]
    (.letOp (n := 102) (.exec 0x11caff (LoadPre 0x11caff (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11caff + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11caff 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[99, 4]
    (.letOp (n := 103) (.out 0x11cb07 (sarR64Effect 0x11cb07 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[101]
    (.letOp (n := 104) (.exec 0x11cb07 (fun s => s.RIP = 0x11cb07) (sarR64Effect 0x11cb07 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[101]
    (.letOp (n := 105) (.out 0x11cb0b (subR64R64Effect 0x11cb0b 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[103, 12]
    (.letOp (n := 106) (.exec 0x11cb0b (fun s => s.RIP = 0x11cb0b) (subR64R64Effect 0x11cb0b 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[103, 12]
    (.letOp (n := 107) (.out 0x11cb0e (movR64Imm64Effect 0x11cb0e 3 0x7fffffffffffffff) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 108) (.exec 0x11cb0e (fun s => s.RIP = 0x11cb0e) (movR64Imm64Effect 0x11cb0e 3 0x7fffffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 109) (.out 0x11cb18 (addR64R64Effect 0x11cb18 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[105, 107]
    (.letOp (n := 110) (.exec 0x11cb18 (fun s => s.RIP = 0x11cb18) (addR64R64Effect 0x11cb18 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[105, 107]
    (.letOp (n := 111) (.out 0x11cb1b (orR64R64Effect 0x11cb1b 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[109, 12]
    (.letOp (n := 112) (.exec 0x11cb1b (fun s => s.RIP = 0x11cb1b) (orR64R64Effect 0x11cb1b 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[109, 12]
    (.letOp (n := 113) (.out 0x11cb1e (shrR64Effect 0x11cb1e 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[111]
    (.letOp (n := 114) (.exec 0x11cb1e (fun s => s.RIP = 0x11cb1e) (shrR64Effect 0x11cb1e 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[111]
    (.letOp (n := 115) (.exec 0x11cb22 (StorePre 0x11cb22 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cb22 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cb22 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[113, 4]
    (.letOp (n := 116) (.out 0x11cb2a (movzxR32M8Effect 0x11cb2a 8 0 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 117) (.exec 0x11cb2a (LoadPre 0x11cb2a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cb2a + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11cb2a 8 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 118) (.out 0x11cb32 (andAlImm8Effect 0x11cb32 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[116]
    (.letOp (n := 119) (.exec 0x11cb32 (fun s => s.RIP = 0x11cb32) (andAlImm8Effect 0x11cb32 0x1) (Reg.operands [.gpr 0] [])) #v[116]
    (.letOp (n := 120) (.out 0x11cb34 (movzxR32R8Effect 0x11cb34 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[118]
    (.letOp (n := 121) (.exec 0x11cb34 (fun s => s.RIP = 0x11cb34) (movzxR32R8Effect 0x11cb34 3 7 0) (Reg.operands [.gpr 0] [])) #v[118]
    (.letOp (n := 122) (.out 0x11cb37 (callEffect (fun _ => 0x127d50) 0x11cb3c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 123) (.exec 0x11cb37 (PushPre 0x11cb37 5) (callEffect (fun _ => 0x127d50) 0x11cb3c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 124) (.const ⟨64, 0x11cb3c⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 118), (1, 96), (2, 2), (3, 107), (4, 122), (5, 72), (6, 6), (7, 120), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 125⟩ { target := .l11cb3c, kept := #v[], arity := rfl, guard := some (Fin.last 124) }))))))))))))))))))))))))))))))))))))))

def bytes_l11ca7f_1 : List UInt8 :=
  [0x4C, 0x89, 0xE9, 0x48, 0xF7, 0xD1, 0x48, 0x01, 0xC1, 0x4C, 0x21, 0xE9, 0x48, 0xC1, 0xE9, 0x3F,
    0x48, 0x89, 0x8C, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x31, 0xC0, 0x48, 0x2B, 0x84, 0x24, 0xD0, 0x01,
    0x00, 0x00, 0x48, 0xC1, 0xF8, 0x3F, 0x4C, 0x29, 0xE0, 0x48, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x7F, 0x48, 0x01, 0xD8, 0x4C, 0x09, 0xE0, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x84,
    0x24, 0xD0, 0x01, 0x00, 0x00, 0x0F, 0xB6, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x24, 0x01, 0x0F,
    0xB6, 0xF8, 0xE8, 0x14, 0xB2, 0x00, 0x00]

theorem code_l11ca7f_1 : ∀ x ∈ codeRange 0x11cae5 bytes_l11ca7f_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1cae5 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11ca7f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11ca7f (movR64Imm64Effect 0x11ca7f 0 0xdfe92f46681b20a0) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x11ca7f (fun s => s.RIP = 0x11ca7f) (movR64Imm64Effect 0x11ca7f 0 0xdfe92f46681b20a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.exec 0x11ca89 (StorePre 0x11ca89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11ca89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11ca89 5 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 56) (.out 0x11ca8e (subR64R64Effect 0x11ca8e 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[53, 5]
    (.letOp (n := 57) (.exec 0x11ca8e (fun s => s.RIP = 0x11ca8e) (subR64R64Effect 0x11ca8e 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 58) (.out 0x11ca91 (andR64R64Effect 0x11ca91 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[56, 5]
    (.letOp (n := 59) (.exec 0x11ca91 (fun s => s.RIP = 0x11ca91) (andR64R64Effect 0x11ca91 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[56, 5]
    (.letOp (n := 60) (.out 0x11ca94 (shrR64Effect 0x11ca94 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[58]
    (.letOp (n := 61) (.exec 0x11ca94 (fun s => s.RIP = 0x11ca94) (shrR64Effect 0x11ca94 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[58]
    (.letOp (n := 62) (.exec 0x11ca98 (StorePre 0x11ca98 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11ca98 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ca98 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x11caa0 (xorR32R32Effect 0x11caa0 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[60, 60]
    (.letOp (n := 64) (.exec 0x11caa0 (fun s => s.RIP = 0x11caa0) (xorR32R32Effect 0x11caa0 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[60, 60]
    (.letOp (n := 65) (.out 0x11caa2 (subR64M64Effect 0x11caa2 0 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[63, 4]
    (.letOp (n := 66) (.exec 0x11caa2 (LoadPre 0x11caa2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11caa2 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11caa2 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 67) (.out 0x11caaa (sarR64Effect 0x11caaa 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 68) (.exec 0x11caaa (fun s => s.RIP = 0x11caaa) (sarR64Effect 0x11caaa 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 69) (.exec 0x11caae (StorePre 0x11caae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11caae + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11caae 3 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 70) (.out 0x11cab3 (subR64R64Effect 0x11cab3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[67, 3]
    (.letOp (n := 71) (.exec 0x11cab3 (fun s => s.RIP = 0x11cab3) (subR64R64Effect 0x11cab3 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 72) (.out 0x11cab6 (movR64Imm64Effect 0x11cab6 5 0x5d576e7357a4501d) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 73) (.exec 0x11cab6 (fun s => s.RIP = 0x11cab6) (movR64Imm64Effect 0x11cab6 5 0x5d576e7357a4501d) (Reg.operands [] [])) #v[]
    (.letOp (n := 74) (.out 0x11cac0 (addR64R64Effect 0x11cac0 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[70, 72]
    (.letOp (n := 75) (.exec 0x11cac0 (fun s => s.RIP = 0x11cac0) (addR64R64Effect 0x11cac0 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[70, 72]
    (.letOp (n := 76) (.out 0x11cac3 (orR64R64Effect 0x11cac3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[74, 3]
    (.letOp (n := 77) (.exec 0x11cac3 (fun s => s.RIP = 0x11cac3) (orR64R64Effect 0x11cac3 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[74, 3]
    (.letOp (n := 78) (.out 0x11cac6 (shrR64Effect 0x11cac6 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[76]
    (.letOp (n := 79) (.exec 0x11cac6 (fun s => s.RIP = 0x11cac6) (shrR64Effect 0x11cac6 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76]
    (.letOp (n := 80) (.exec 0x11caca (StorePre 0x11caca 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11caca + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11caca 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 4]
    (.letOp (n := 81) (.out 0x11cad2 (xorR32R32Effect 0x11cad2 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[78, 78]
    (.letOp (n := 82) (.exec 0x11cad2 (fun s => s.RIP = 0x11cad2) (xorR32R32Effect 0x11cad2 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[78, 78]
    (.letOp (n := 83) (.out 0x11cad4 (subR64M64Effect 0x11cad4 0 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[81, 4]
    (.letOp (n := 84) (.exec 0x11cad4 (LoadPre 0x11cad4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cad4 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11cad4 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 85) (.out 0x11cadc (sarR64Effect 0x11cadc 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[83]
    (.letOp (n := 86) (.exec 0x11cadc (fun s => s.RIP = 0x11cadc) (sarR64Effect 0x11cadc 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[83]
    (.letOp (n := 87) (.exec 0x11cae0 (StorePre 0x11cae0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11cae0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11cae0 13 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (b_l11ca7f_1)))))))))))))))))))))))))))))))))))

def bytes_l11ca7f : List UInt8 :=
  [0x48, 0xB8, 0xA0, 0x20, 0x1B, 0x68, 0x46, 0x2F, 0xE9, 0xDF, 0x48, 0x89, 0x6C, 0x24, 0x58, 0x48,
    0x29, 0xE8, 0x48, 0x21, 0xE8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x84, 0x24, 0xD0, 0x01, 0x00,
    0x00, 0x31, 0xC0, 0x48, 0x2B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x48, 0xC1, 0xF8, 0x3F, 0x48,
    0x89, 0x5C, 0x24, 0x70, 0x48, 0x29, 0xD8, 0x48, 0xBD, 0x1D, 0x50, 0xA4, 0x57, 0x73, 0x6E, 0x57,
    0x5D, 0x48, 0x01, 0xE8, 0x48, 0x09, 0xD8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x84, 0x24, 0xD0,
    0x01, 0x00, 0x00, 0x31, 0xC0, 0x48, 0x2B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x48, 0xC1, 0xF8,
    0x3F, 0x4C, 0x89, 0x6C, 0x24, 0x50] ++ bytes_l11ca7f_1

theorem code_l11ca7f : ∀ x ∈ codeRange 0x11ca7f bytes_l11ca7f, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ca7f 102 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11ca7f_1

@[cfg_block] def b_l11cb3c_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x11cb9f (movR64R64Effect 0x11cb9f 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[87]
    (.letOp (n := 90) (.exec 0x11cb9f (fun s => s.RIP = 0x11cb9f) (movR64R64Effect 0x11cb9f 1 2) (Reg.operands [.gpr 2] [])) #v[87]
    (.letOp (n := 91) (.out 0x11cba2 (notR64Effect 0x11cba2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[89]
    (.letOp (n := 92) (.exec 0x11cba2 (fun s => s.RIP = 0x11cba2) (notR64Effect 0x11cba2 1) (Reg.operands [.gpr 1] [])) #v[89]
    (.letOp (n := 93) (.out 0x11cba5 (addR64R64Effect 0x11cba5 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[91, 85]
    (.letOp (n := 94) (.exec 0x11cba5 (fun s => s.RIP = 0x11cba5) (addR64R64Effect 0x11cba5 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[91, 85]
    (.letOp (n := 95) (.out 0x11cba8 (andR64R64Effect 0x11cba8 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[93, 87]
    (.letOp (n := 96) (.exec 0x11cba8 (fun s => s.RIP = 0x11cba8) (andR64R64Effect 0x11cba8 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[93, 87]
    (.letOp (n := 97) (.out 0x11cbab (shrR64Effect 0x11cbab 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 98) (.exec 0x11cbab (fun s => s.RIP = 0x11cbab) (shrR64Effect 0x11cbab 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[95]
    (.letOp (n := 99) (.exec 0x11cbaf (StorePre 0x11cbaf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cbaf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cbaf 1 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[97, 4]
    (.letOp (n := 100) (.out 0x11cbb7 (movR64M64Effect 0x11cbb7 0 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 101) (.exec 0x11cbb7 (LoadPre 0x11cbb7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cbb7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cbb7 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 102) (.out 0x11cbbf (xorR32R32Effect 0x11cbbf 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[97, 97]
    (.letOp (n := 103) (.exec 0x11cbbf (fun s => s.RIP = 0x11cbbf) (xorR32R32Effect 0x11cbbf 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[97, 97]
    (.letOp (n := 104) (.out 0x11cbc1 (subR64R64Effect 0x11cbc1 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[102, 100]
    (.letOp (n := 105) (.exec 0x11cbc1 (fun s => s.RIP = 0x11cbc1) (subR64R64Effect 0x11cbc1 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[102, 100]
    (.letOp (n := 106) (.out 0x11cbc4 (sarR64Effect 0x11cbc4 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[104]
    (.letOp (n := 107) (.exec 0x11cbc4 (fun s => s.RIP = 0x11cbc4) (sarR64Effect 0x11cbc4 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[104]
    (.letOp (n := 108) (.out 0x11cbc8 (movR64M64Effect 0x11cbc8 5 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 109) (.exec 0x11cbc8 (LoadPre 0x11cbc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11cbc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cbc8 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 110) (.out 0x11cbcd (subR64R64Effect 0x11cbcd 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[106, 108]
    (.letOp (n := 111) (.exec 0x11cbcd (fun s => s.RIP = 0x11cbcd) (subR64R64Effect 0x11cbcd 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[106, 108]
    (.letOp (n := 112) (.out 0x11cbd0 (addR64R64Effect 0x11cbd0 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[110, 3]
    (.letOp (n := 113) (.exec 0x11cbd0 (fun s => s.RIP = 0x11cbd0) (addR64R64Effect 0x11cbd0 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[110, 3]
    (.letOp (n := 114) (.out 0x11cbd3 (orR64R64Effect 0x11cbd3 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[112, 108]
    (.letOp (n := 115) (.exec 0x11cbd3 (fun s => s.RIP = 0x11cbd3) (orR64R64Effect 0x11cbd3 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[112, 108]
    (.letOp (n := 116) (.out 0x11cbd6 (shrR64Effect 0x11cbd6 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[114]
    (.letOp (n := 117) (.exec 0x11cbd6 (fun s => s.RIP = 0x11cbd6) (shrR64Effect 0x11cbd6 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[114]
    (.letOp (n := 118) (.exec 0x11cbda (StorePre 0x11cbda 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cbda + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cbda 1 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[116, 4]
    (.letOp (n := 119) (.out 0x11cbe2 (movzxR32M8Effect 0x11cbe2 8 0 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 120) (.exec 0x11cbe2 (LoadPre 0x11cbe2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cbe2 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11cbe2 8 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 121) (.out 0x11cbea (andAlImm8Effect 0x11cbea 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[119]
    (.letOp (n := 122) (.exec 0x11cbea (fun s => s.RIP = 0x11cbea) (andAlImm8Effect 0x11cbea 0x1) (Reg.operands [.gpr 0] [])) #v[119]
    (.letOp (n := 123) (.out 0x11cbec (movzxR32R8Effect 0x11cbec 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[121]
    (.letOp (n := 124) (.exec 0x11cbec (fun s => s.RIP = 0x11cbec) (movzxR32R8Effect 0x11cbec 3 7 0) (Reg.operands [.gpr 0] [])) #v[121]
    (.letOp (n := 125) (.out 0x11cbef (callEffect (fun _ => 0x127d50) 0x11cbf4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 126) (.exec 0x11cbef (PushPre 0x11cbef 5) (callEffect (fun _ => 0x127d50) 0x11cbf4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 127) (.const ⟨64, 0x11cbf4⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 121), (1, 116), (2, 87), (3, 3), (4, 125), (5, 108), (6, 6), (7, 123), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 128⟩ { target := .l11cbf4, kept := #v[], arity := rfl, guard := some (Fin.last 127) }))))))))))))))))))))))))))))))))))))))))

def bytes_l11cb3c_1 : List UInt8 :=
  [0x48, 0x89, 0xD1, 0x48, 0xF7, 0xD1, 0x48, 0x01, 0xC1, 0x48, 0x21, 0xD1, 0x48, 0xC1, 0xE9, 0x3F,
    0x48, 0x89, 0x8C, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00,
    0x31, 0xC9, 0x48, 0x29, 0xC1, 0x48, 0xC1, 0xF9, 0x3F, 0x48, 0x8B, 0x6C, 0x24, 0x28, 0x48, 0x29,
    0xE9, 0x48, 0x01, 0xD9, 0x48, 0x09, 0xE9, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x8C, 0x24, 0xD0,
    0x01, 0x00, 0x00, 0x0F, 0xB6, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x24, 0x01, 0x0F, 0xB6, 0xF8,
    0xE8, 0x5C, 0xB1, 0x00, 0x00]

theorem code_l11cb3c_1 : ∀ x ∈ codeRange 0x11cb9f bytes_l11cb3c_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1cb9f 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11cb3c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11cb3c (StorePre 0x11cb3c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11cb3c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11cb3c 4 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x11cb40 (movR64Imm64Effect 0x11cb40 0 0xdfe92f46681b20a0) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 55) (.exec 0x11cb40 (fun s => s.RIP = 0x11cb40) (movR64Imm64Effect 0x11cb40 0 0xdfe92f46681b20a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.exec 0x11cb4a (StorePre 0x11cb4a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11cb4a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cb4a 14 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 57) (.out 0x11cb52 (subR64R64Effect 0x11cb52 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[54, 14]
    (.letOp (n := 58) (.exec 0x11cb52 (fun s => s.RIP = 0x11cb52) (subR64R64Effect 0x11cb52 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[54, 14]
    (.letOp (n := 59) (.out 0x11cb55 (andR64R64Effect 0x11cb55 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[57, 14]
    (.letOp (n := 60) (.exec 0x11cb55 (fun s => s.RIP = 0x11cb55) (andR64R64Effect 0x11cb55 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[57, 14]
    (.letOp (n := 61) (.out 0x11cb58 (shrR64Effect 0x11cb58 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 62) (.exec 0x11cb58 (fun s => s.RIP = 0x11cb58) (shrR64Effect 0x11cb58 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.exec 0x11cb5c (StorePre 0x11cb5c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cb5c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cb5c 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x11cb64 (xorR32R32Effect 0x11cb64 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[61, 61]
    (.letOp (n := 65) (.exec 0x11cb64 (fun s => s.RIP = 0x11cb64) (xorR32R32Effect 0x11cb64 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[61, 61]
    (.letOp (n := 66) (.out 0x11cb66 (subR64M64Effect 0x11cb66 0 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11cb66 (LoadPre 0x11cb66 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cb66 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11cb66 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 68) (.out 0x11cb6e (sarR64Effect 0x11cb6e 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 69) (.exec 0x11cb6e (fun s => s.RIP = 0x11cb6e) (sarR64Effect 0x11cb6e 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[66]
    (.letOp (n := 70) (.out 0x11cb72 (movR64M64Effect 0x11cb72 1 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 71) (.exec 0x11cb72 (LoadPre 0x11cb72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11cb72 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cb72 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x11cb77 (subR64R64Effect 0x11cb77 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[68, 70]
    (.letOp (n := 73) (.exec 0x11cb77 (fun s => s.RIP = 0x11cb77) (subR64R64Effect 0x11cb77 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[68, 70]
    (.letOp (n := 74) (.out 0x11cb7a (addR64R64Effect 0x11cb7a 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[72, 5]
    (.letOp (n := 75) (.exec 0x11cb7a (fun s => s.RIP = 0x11cb7a) (addR64R64Effect 0x11cb7a 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[72, 5]
    (.letOp (n := 76) (.out 0x11cb7d (orR64R64Effect 0x11cb7d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[74, 70]
    (.letOp (n := 77) (.exec 0x11cb7d (fun s => s.RIP = 0x11cb7d) (orR64R64Effect 0x11cb7d 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[74, 70]
    (.letOp (n := 78) (.out 0x11cb80 (shrR64Effect 0x11cb80 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[76]
    (.letOp (n := 79) (.exec 0x11cb80 (fun s => s.RIP = 0x11cb80) (shrR64Effect 0x11cb80 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76]
    (.letOp (n := 80) (.exec 0x11cb84 (StorePre 0x11cb84 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cb84 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cb84 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 4]
    (.letOp (n := 81) (.out 0x11cb8c (xorR32R32Effect 0x11cb8c 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[78, 78]
    (.letOp (n := 82) (.exec 0x11cb8c (fun s => s.RIP = 0x11cb8c) (xorR32R32Effect 0x11cb8c 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[78, 78]
    (.letOp (n := 83) (.out 0x11cb8e (subR64M64Effect 0x11cb8e 0 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[81, 4]
    (.letOp (n := 84) (.exec 0x11cb8e (LoadPre 0x11cb8e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cb8e + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11cb8e 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 85) (.out 0x11cb96 (sarR64Effect 0x11cb96 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[83]
    (.letOp (n := 86) (.exec 0x11cb96 (fun s => s.RIP = 0x11cb96) (sarR64Effect 0x11cb96 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[83]
    (.letOp (n := 87) (.out 0x11cb9a (movR64M64Effect 0x11cb9a 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 88) (.exec 0x11cb9a (LoadPre 0x11cb9a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11cb9a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cb9a 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11cb3c_1))))))))))))))))))))))))))))))))))))

def bytes_l11cb3c : List UInt8 :=
  [0x88, 0x44, 0x24, 0x30, 0x48, 0xB8, 0xA0, 0x20, 0x1B, 0x68, 0x46, 0x2F, 0xE9, 0xDF, 0x4C, 0x89,
    0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xF0, 0x4C, 0x21, 0xF0, 0x48, 0xC1, 0xE8, 0x3F,
    0x48, 0x89, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x31, 0xC0, 0x48, 0x2B, 0x84, 0x24, 0xD0, 0x01,
    0x00, 0x00, 0x48, 0xC1, 0xF8, 0x3F, 0x48, 0x8B, 0x4C, 0x24, 0x40, 0x48, 0x29, 0xC8, 0x48, 0x01,
    0xE8, 0x48, 0x09, 0xC8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00,
    0x31, 0xC0, 0x48, 0x2B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x48, 0xC1, 0xF8, 0x3F, 0x48, 0x8B,
    0x54, 0x24, 0x10] ++ bytes_l11cb3c_1

theorem code_l11cb3c : ∀ x ∈ codeRange 0x11cb3c bytes_l11cb3c, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1cb3c 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11cb3c_1

@[cfg_block] def b_l11cbf4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11cbf4 (StorePre 0x11cbf4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11cbf4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11cbf4 4 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x11cbf8 (movR64M64Effect 0x11cbf8 3 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 55) (.exec 0x11cbf8 (LoadPre 0x11cbf8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11cbf8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cbf8 3 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x11cbfd (StorePre 0x11cbfd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cbfd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cbfd 3 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 57) (.out 0x11cc05 (movR64M64Effect 0x11cc05 13 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 58) (.exec 0x11cc05 (LoadPre 0x11cc05 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11cc05 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cc05 13 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x11cc0a (StorePre 0x11cc0a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x11cc0a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cc0a 13 (.sib 4 none 0 (.d32 0x1d8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x11cc12 (movR64M64Effect 0x11cc12 14 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 61) (.exec 0x11cc12 (LoadPre 0x11cc12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11cc12 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cc12 14 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x11cc17 (StorePre 0x11cc17 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x11cc17 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cc17 14 (.sib 4 none 0 (.d32 0x1e0))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.exec 0x11cc1f (StorePre 0x11cc1f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x11cc1f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cc1f 12 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 64) (.out 0x11cc27 (leaR64Effect 0x11cc27 7 (.sib 4 none 0 (.d32 0x418))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 65) (.exec 0x11cc27 (fun s => s.RIP = 0x11cc27) (leaR64Effect 0x11cc27 7 (.sib 4 none 0 (.d32 0x418))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x11cc2f (movR64R64Effect 0x11cc2f 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 67) (.exec 0x11cc2f (fun s => s.RIP = 0x11cc2f) (movR64R64Effect 0x11cc2f 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 68) (.out 0x11cc32 (movR64Imm32Effect 0x11cc32 2 0x2021a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 69) (.exec 0x11cc32 (fun s => s.RIP = 0x11cc32) (movR64Imm32Effect 0x11cc32 2 0x2021a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 70) (.out 0x11cc39 (callEffect (fun _ => 0x110b80) 0x11cc3e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 71) (.exec 0x11cc39 (PushPre 0x11cc39 5) (callEffect (fun _ => 0x110b80) 0x11cc3e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.const ⟨64, 0x11cc3e⟩) #v[]
    (.terminate (.call ⟨.l110b80, RegMap.args [(0, 0), (2, 68), (3, 54), (4, 70), (5, 5), (6, 66), (7, 64), (12, 12), (13, 57), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩ { target := .l11cc3e, kept := #v[], arity := rfl, guard := some (Fin.last 72) })))))))))))))))))))))

def bytes_l11cbf4 : List UInt8 :=
  [0x88, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x5C, 0x24, 0x58, 0x48, 0x89, 0x9C, 0x24, 0xD0, 0x01, 0x00,
    0x00, 0x4C, 0x8B, 0x6C, 0x24, 0x70, 0x4C, 0x89, 0xAC, 0x24, 0xD8, 0x01, 0x00, 0x00, 0x4C, 0x8B,
    0x74, 0x24, 0x50, 0x4C, 0x89, 0xB4, 0x24, 0xE0, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xA4, 0x24, 0xE8,
    0x01, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x18, 0x04, 0x00, 0x00, 0x4C, 0x89, 0xFE, 0x48, 0xC7,
    0xC2, 0xA0, 0x21, 0x20, 0x00, 0xE8, 0x42, 0x3F, 0xFF, 0xFF]

theorem code_l11cbf4 : ∀ x ∈ codeRange 0x11cbf4 bytes_l11cbf4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1cbf4 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11cc3e_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.out 0x11ccb4 (movR64M64Effect 0x11ccb4 12 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 89) (.exec 0x11ccb4 (LoadPre 0x11ccb4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11ccb4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11ccb4 12 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.exec 0x11ccbc (StorePre 0x11ccbc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11ccbc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ccbc 12 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[88, 4]
    (.letOp (n := 91) (.out 0x11ccc4 (movR64M64Effect 0x11ccc4 13 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 92) (.exec 0x11ccc4 (LoadPre 0x11ccc4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11ccc4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ccc4 13 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 93) (.exec 0x11ccc9 (StorePre 0x11ccc9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x11ccc9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ccc9 13 (.sib 4 none 0 (.d32 0x1d8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[91, 4]
    (.letOp (n := 94) (.out 0x11ccd1 (movR64M64Effect 0x11ccd1 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 95) (.exec 0x11ccd1 (LoadPre 0x11ccd1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11ccd1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ccd1 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 96) (.exec 0x11ccd6 (StorePre 0x11ccd6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x11ccd6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ccd6 14 (.sib 4 none 0 (.d32 0x1e0))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[94, 4]
    (.letOp (n := 97) (.exec 0x11ccde (StorePre 0x11ccde 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x11ccde + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ccde 5 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 98) (.out 0x11cce6 (leaR64Effect 0x11cce6 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 99) (.exec 0x11cce6 (fun s => s.RIP = 0x11cce6) (leaR64Effect 0x11cce6 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 100) (.out 0x11ccee (movR64R64Effect 0x11ccee 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 101) (.exec 0x11ccee (fun s => s.RIP = 0x11ccee) (movR64R64Effect 0x11ccee 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 102) (.out 0x11ccf1 (movR64Imm32Effect 0x11ccf1 2 0x2021a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 103) (.exec 0x11ccf1 (fun s => s.RIP = 0x11ccf1) (movR64Imm32Effect 0x11ccf1 2 0x2021a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 104) (.out 0x11ccf8 (callEffect (fun _ => 0x110b80) 0x11ccfd) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 105) (.exec 0x11ccf8 (PushPre 0x11ccf8 5) (callEffect (fun _ => 0x110b80) 0x11ccfd) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.const ⟨64, 0x11ccfd⟩) #v[]
    (.terminate (.call ⟨.l110b80, RegMap.args [(0, 56), (1, 76), (2, 102), (3, 84), (4, 104), (5, 5), (6, 100), (7, 98), (12, 88), (13, 91), (14, 94), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)] 107⟩ { target := .l11ccfd, kept := #v[], arity := rfl, guard := some (Fin.last 106) }))))))))))))))))))))

def bytes_l11cc3e_1 : List UInt8 :=
  [0x4C, 0x8B, 0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xA4, 0x24, 0xD0, 0x01, 0x00, 0x00,
    0x4C, 0x8B, 0x6C, 0x24, 0x40, 0x4C, 0x89, 0xAC, 0x24, 0xD8, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x74,
    0x24, 0x10, 0x4C, 0x89, 0xB4, 0x24, 0xE0, 0x01, 0x00, 0x00, 0x48, 0x89, 0xAC, 0x24, 0xE8, 0x01,
    0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xFE, 0x48, 0xC7, 0xC2,
    0xA0, 0x21, 0x20, 0x00, 0xE8, 0x83, 0x3E, 0xFF, 0xFF]

theorem code_l11cc3e_1 : ∀ x ∈ codeRange 0x11ccb4 bytes_l11cc3e_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1ccb4 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11cc3e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11cc3e (movzxR32M8Effect 0x11cc3e 5 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11cc3e (LoadPre 0x11cc3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11cc3e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11cc3e 5 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11cc43 (StorePre 0x11cc43 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cc43 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x11cc43 7 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11cc4a (movzxR32M8Effect 0x11cc4a 8 0 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11cc4a (LoadPre 0x11cc4a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cc4a + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11cc4a 8 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x11cc52 (movR64M64Effect 0x11cc52 1 (.sib 4 none 0 (.d32 0x418))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x11cc52 (LoadPre 0x11cc52 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x418)) s (0x11cc52 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cc52 1 (.sib 4 none 0 (.d32 0x418))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x11cc5a (movR64M64Effect 0x11cc5a 2 (.sib 4 none 0 (.d32 0x420))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 61) (.exec 0x11cc5a (LoadPre 0x11cc5a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x420)) s (0x11cc5a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cc5a 2 (.sib 4 none 0 (.d32 0x420))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x11cc62 (testR8R8Effect 0x11cc62 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[56, 56]
    (.letOp (n := 63) (.exec 0x11cc62 (fun s => s.RIP = 0x11cc62) (testR8R8Effect 0x11cc62 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[56, 56]
    (.letOp (n := 64) (.out 0x11cc64 (atFlags (condHolds 5) (cmovR64R64Effect 0x11cc64 4 3 1)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 3))) #v[3, 58, 62]
    (.letOp (n := 65) (.exec 0x11cc64 (fun s => s.RIP = 0x11cc64) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cc64 4 3 1)) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[3, 58, 62]
    (.letOp (n := 66) (.out 0x11cc68 (testR8R8Effect 0x11cc68 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[56, 56]
    (.letOp (n := 67) (.exec 0x11cc68 (fun s => s.RIP = 0x11cc68) (testR8R8Effect 0x11cc68 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[56, 56]
    (.letOp (n := 68) (.out 0x11cc6a (atFlags (condHolds 5) (cmovR64R64Effect 0x11cc6a 4 13 2)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 13))) #v[13, 60, 66]
    (.letOp (n := 69) (.exec 0x11cc6a (fun s => s.RIP = 0x11cc6a) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cc6a 4 13 2)) (Reg.operands [.gpr 13, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[13, 60, 66]
    (.letOp (n := 70) (.out 0x11cc6e (movR64M64Effect 0x11cc6e 1 (.sib 4 none 0 (.d32 0x428))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 71) (.exec 0x11cc6e (LoadPre 0x11cc6e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x428)) s (0x11cc6e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cc6e 1 (.sib 4 none 0 (.d32 0x428))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x11cc76 (testR8R8Effect 0x11cc76 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[56, 56]
    (.letOp (n := 73) (.exec 0x11cc76 (fun s => s.RIP = 0x11cc76) (testR8R8Effect 0x11cc76 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[56, 56]
    (.letOp (n := 74) (.out 0x11cc78 (atFlags (condHolds 5) (cmovR64R64Effect 0x11cc78 4 14 1)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 14))) #v[14, 70, 72]
    (.letOp (n := 75) (.exec 0x11cc78 (fun s => s.RIP = 0x11cc78) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cc78 4 14 1)) (Reg.operands [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[14, 70, 72]
    (.letOp (n := 76) (.out 0x11cc7c (movR64M64Effect 0x11cc7c 1 (.sib 4 none 0 (.d32 0x430))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 77) (.exec 0x11cc7c (LoadPre 0x11cc7c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x430)) s (0x11cc7c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cc7c 1 (.sib 4 none 0 (.d32 0x430))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x11cc84 (testR8R8Effect 0x11cc84 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[56, 56]
    (.letOp (n := 79) (.exec 0x11cc84 (fun s => s.RIP = 0x11cc84) (testR8R8Effect 0x11cc84 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[56, 56]
    (.letOp (n := 80) (.out 0x11cc86 (atFlags (condHolds 5) (cmovR64R64Effect 0x11cc86 4 12 1)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 12))) #v[12, 76, 78]
    (.letOp (n := 81) (.exec 0x11cc86 (fun s => s.RIP = 0x11cc86) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cc86 4 12 1)) (Reg.operands [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[12, 76, 78]
    (.letOp (n := 82) (.exec 0x11cc8a (StorePre 0x11cc8a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x270)) s (0x11cc8a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cc8a 3 (.sib 4 none 0 (.d32 0x270))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 83) (.exec 0x11cc92 (StorePre 0x11cc92 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x278)) s (0x11cc92 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cc92 13 (.sib 4 none 0 (.d32 0x278))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 84) (.out 0x11cc9a (movR64Imm64Effect 0x11cc9a 3 0x3ffffffffffffc) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 85) (.exec 0x11cc9a (fun s => s.RIP = 0x11cc9a) (movR64Imm64Effect 0x11cc9a 3 0x3ffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 86) (.exec 0x11cca4 (StorePre 0x11cca4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x280)) s (0x11cca4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cca4 14 (.sib 4 none 0 (.d32 0x280))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 87) (.exec 0x11ccac (StorePre 0x11ccac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x288)) s (0x11ccac + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ccac 12 (.sib 4 none 0 (.d32 0x288))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[80, 4]
    (b_l11cc3e_1)))))))))))))))))))))))))))))))))))

def bytes_l11cc3e : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x30, 0x88, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x0F, 0xB6, 0x84, 0x24,
    0xD0, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x18, 0x04, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24,
    0x20, 0x04, 0x00, 0x00, 0x84, 0xC0, 0x48, 0x0F, 0x45, 0xD9, 0x84, 0xC0, 0x4C, 0x0F, 0x45, 0xEA,
    0x48, 0x8B, 0x8C, 0x24, 0x28, 0x04, 0x00, 0x00, 0x84, 0xC0, 0x4C, 0x0F, 0x45, 0xF1, 0x48, 0x8B,
    0x8C, 0x24, 0x30, 0x04, 0x00, 0x00, 0x84, 0xC0, 0x4C, 0x0F, 0x45, 0xE1, 0x48, 0x89, 0x9C, 0x24,
    0x70, 0x02, 0x00, 0x00, 0x4C, 0x89, 0xAC, 0x24, 0x78, 0x02, 0x00, 0x00, 0x48, 0xBB, 0xFC, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00, 0x4C, 0x89, 0xB4, 0x24, 0x80, 0x02, 0x00, 0x00, 0x4C, 0x89,
    0xA4, 0x24, 0x88, 0x02, 0x00, 0x00] ++ bytes_l11cc3e_1

theorem code_l11cc3e : ∀ x ∈ codeRange 0x11cc3e bytes_l11cc3e, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1cc3e 118 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11cc3e_1

@[cfg_block] def b_l11ccfd_4 : Block Op Label signature Reg.count 199 :=
  .letOp (n := 199) (.out 0x11ce9c (movR64M64Effect 0x11ce9c 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 200) (.exec 0x11ce9c (LoadPre 0x11ce9c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce9c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce9c 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 201) (.out 0x11cea1 (movR64M64Effect 0x11cea1 6 (.sib 10 (some 6) 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10, .gpr 6] []) (.reg (.gpr 6))) #v[92, 199]
    (.letOp (n := 202) (.exec 0x11cea1 (LoadPre 0x11cea1 (fun s => AddrMode.addr (.sib 10 (some 6) 0 .none) s (0x11cea1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11cea1 6 (.sib 10 (some 6) 0 .none)) (Reg.operands [.gpr 10, .gpr 6] [])) #v[92, 199]
    (.letOp (n := 203) (.exec 0x11cea5 (StorePre 0x11cea5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3a0)) s (0x11cea5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cea5 6 (.sib 4 none 0 (.d32 0x3a0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[201, 4]
    (.letOp (n := 204) (.out 0x11cead (movR64Imm64Effect 0x11cead 12 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 205) (.exec 0x11cead (fun s => s.RIP = 0x11cead) (movR64Imm64Effect 0x11cead 12 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 206) (.out 0x11ceb7 (andR64R64Effect 0x11ceb7 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[110, 204]
    (.letOp (n := 207) (.exec 0x11ceb7 (fun s => s.RIP = 0x11ceb7) (andR64R64Effect 0x11ceb7 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[110, 204]
    (.letOp (n := 208) (.exec 0x11ceba (StorePre 0x11ceba 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3c8)) s (0x11ceba + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ceba 0 (.sib 4 none 0 (.d32 0x3c8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[206, 4]
    (.letOp (n := 209) (.out 0x11cec2 (andR64R64Effect 0x11cec2 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[124, 204]
    (.letOp (n := 210) (.exec 0x11cec2 (fun s => s.RIP = 0x11cec2) (andR64R64Effect 0x11cec2 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[124, 204]
    (.letOp (n := 211) (.exec 0x11cec5 (StorePre 0x11cec5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3d0)) s (0x11cec5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cec5 1 (.sib 4 none 0 (.d32 0x3d0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[209, 4]
    (.letOp (n := 212) (.out 0x11cecd (andR64R64Effect 0x11cecd 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[134, 204]
    (.letOp (n := 213) (.exec 0x11cecd (fun s => s.RIP = 0x11cecd) (andR64R64Effect 0x11cecd 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[134, 204]
    (.letOp (n := 214) (.exec 0x11ced0 (StorePre 0x11ced0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3d8)) s (0x11ced0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ced0 2 (.sib 4 none 0 (.d32 0x3d8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[212, 4]
    (.letOp (n := 215) (.out 0x11ced8 (andR64R64Effect 0x11ced8 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[171, 204]
    (.letOp (n := 216) (.exec 0x11ced8 (fun s => s.RIP = 0x11ced8) (andR64R64Effect 0x11ced8 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[171, 204]
    (.letOp (n := 217) (.exec 0x11cedb (StorePre 0x11cedb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3e0)) s (0x11cedb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cedb 7 (.sib 4 none 0 (.d32 0x3e0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[215, 4]
    (.letOp (n := 218) (.exec 0x11cee3 (StorePre 0x11cee3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3e8)) s (0x11cee3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cee3 8 (.sib 4 none 0 (.d32 0x3e8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[177, 4]
    (.letOp (n := 219) (.out 0x11ceeb (movzxR32M8Effect 0x11ceeb 5 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 220) (.exec 0x11ceeb (LoadPre 0x11ceeb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11ceeb + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11ceeb 5 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 221) (.out 0x11cef0 (leaR64Effect 0x11cef0 5 (.sib 4 none 0 (.d32 0x328))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 222) (.exec 0x11cef0 (fun s => s.RIP = 0x11cef0) (leaR64Effect 0x11cef0 5 (.sib 4 none 0 (.d32 0x328))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 223) (.out 0x11cef8 (movR64R64Effect 0x11cef8 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[221]
    (.letOp (n := 224) (.exec 0x11cef8 (fun s => s.RIP = 0x11cef8) (movR64R64Effect 0x11cef8 7 5) (Reg.operands [.gpr 5] [])) #v[221]
    (.letOp (n := 225) (.out 0x11cefb (movR64M64Effect 0x11cefb 6 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 226) (.exec 0x11cefb (LoadPre 0x11cefb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11cefb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cefb 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 227) (.out 0x11cf00 (leaR64Effect 0x11cf00 2 (.sib 4 none 0 (.d32 0x3a0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 228) (.exec 0x11cf00 (fun s => s.RIP = 0x11cf00) (leaR64Effect 0x11cf00 2 (.sib 4 none 0 (.d32 0x3a0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 229) (.out 0x11cf08 (callEffect (fun _ => 0x10fcc0) 0x11cf0d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 230) (.exec 0x11cf08 (PushPre 0x11cf08 5) (callEffect (fun _ => 0x10fcc0) 0x11cf0d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 231) (.const ⟨64, 0x11cf0d⟩) #v[]
    (.terminate (.call ⟨.l10fcc0, RegMap.args [(0, 206), (1, 219), (2, 227), (3, 3), (4, 229), (5, 221), (6, 225), (7, 223), (8, 177), (9, 144), (10, 92), (12, 204), (13, 100), (14, 167), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 232⟩ { target := .l11cf0d, kept := #v[], arity := rfl, guard := some (Fin.last 231) }))))))))))))))))))))))))))))))))))

def bytes_l11ccfd_4 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x08, 0x49, 0x8B, 0x34, 0x32, 0x48, 0x89, 0xB4, 0x24, 0xA0, 0x03, 0x00,
    0x00, 0x49, 0xBC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xE0, 0x48, 0x89,
    0x84, 0x24, 0xC8, 0x03, 0x00, 0x00, 0x4C, 0x21, 0xE1, 0x48, 0x89, 0x8C, 0x24, 0xD0, 0x03, 0x00,
    0x00, 0x4C, 0x21, 0xE2, 0x48, 0x89, 0x94, 0x24, 0xD8, 0x03, 0x00, 0x00, 0x4C, 0x21, 0xE7, 0x48,
    0x89, 0xBC, 0x24, 0xE0, 0x03, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0xE8, 0x03, 0x00, 0x00, 0x0F,
    0xB6, 0x4C, 0x24, 0x30, 0x48, 0x8D, 0xAC, 0x24, 0x28, 0x03, 0x00, 0x00, 0x48, 0x89, 0xEF, 0x48,
    0x8B, 0x74, 0x24, 0x38, 0x48, 0x8D, 0x94, 0x24, 0xA0, 0x03, 0x00, 0x00, 0xE8, 0xB3, 0x2D, 0xFF,
    0xFF]

theorem code_l11ccfd_4 : ∀ x ∈ codeRange 0x11ce9c bytes_l11ccfd_4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1ce9c 113 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11ccfd_3 : Block Op Label signature Reg.count 164 :=
  .letOp (n := 164) (.out 0x11ce32 (movR64M64Effect 0x11ce32 8 (.sib 10 (some 8) 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10, .gpr 8] []) (.reg (.gpr 8))) #v[92, 162]
    (.letOp (n := 165) (.exec 0x11ce32 (LoadPre 0x11ce32 (fun s => AddrMode.addr (.sib 10 (some 8) 0 (.d8 0x50)) s (0x11ce32 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce32 8 (.sib 10 (some 8) 0 (.d8 0x50))) (Reg.operands [.gpr 10, .gpr 8] [])) #v[92, 162]
    (.letOp (n := 166) (.exec 0x11ce37 (StorePre 0x11ce37 3 (fun s => AddrMode.addr (.base 9 .none) s (0x11ce37 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11ce37 8 (.base 9 .none)) (Reg.operands [.gpr 8, .gpr 9] [])) #v[164, 144]
    (.letOp (n := 167) (.out 0x11ce3a (movR64Imm64Effect 0x11ce3a 14 0xffffffffffff) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 168) (.exec 0x11ce3a (fun s => s.RIP = 0x11ce3a) (movR64Imm64Effect 0x11ce3a 14 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 169) (.out 0x11ce44 (andR64R64Effect 0x11ce44 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[94, 167]
    (.letOp (n := 170) (.exec 0x11ce44 (fun s => s.RIP = 0x11ce44) (andR64R64Effect 0x11ce44 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[94, 167]
    (.letOp (n := 171) (.out 0x11ce47 (addR64R64Effect 0x11ce47 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[142, 3]
    (.letOp (n := 172) (.exec 0x11ce47 (fun s => s.RIP = 0x11ce47) (addR64R64Effect 0x11ce47 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[142, 3]
    (.letOp (n := 173) (.out 0x11ce4a (movR64R64Effect 0x11ce4a 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[171]
    (.letOp (n := 174) (.exec 0x11ce4a (fun s => s.RIP = 0x11ce4a) (movR64R64Effect 0x11ce4a 8 7) (Reg.operands [.gpr 7] [])) #v[171]
    (.letOp (n := 175) (.out 0x11ce4d (shrR64Effect 0x11ce4d 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[173]
    (.letOp (n := 176) (.exec 0x11ce4d (fun s => s.RIP = 0x11ce4d) (shrR64Effect 0x11ce4d 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[173]
    (.letOp (n := 177) (.out 0x11ce51 (addR64R64Effect 0x11ce51 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[175, 169]
    (.letOp (n := 178) (.exec 0x11ce51 (fun s => s.RIP = 0x11ce51) (addR64R64Effect 0x11ce51 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[175, 169]
    (.letOp (n := 179) (.out 0x11ce54 (movR64M64Effect 0x11ce54 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 180) (.exec 0x11ce54 (LoadPre 0x11ce54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce54 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce54 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 181) (.out 0x11ce59 (movR64M64Effect 0x11ce59 6 (.sib 10 (some 6) 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10, .gpr 6] []) (.reg (.gpr 6))) #v[92, 179]
    (.letOp (n := 182) (.exec 0x11ce59 (LoadPre 0x11ce59 (fun s => AddrMode.addr (.sib 10 (some 6) 0 (.d8 0x8)) s (0x11ce59 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce59 6 (.sib 10 (some 6) 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 6] [])) #v[92, 179]
    (.letOp (n := 183) (.exec 0x11ce5e (StorePre 0x11ce5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3a8)) s (0x11ce5e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ce5e 6 (.sib 4 none 0 (.d32 0x3a8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[181, 4]
    (.letOp (n := 184) (.out 0x11ce66 (movR64M64Effect 0x11ce66 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 185) (.exec 0x11ce66 (LoadPre 0x11ce66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce66 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce66 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 186) (.out 0x11ce6b (movR64M64Effect 0x11ce6b 6 (.sib 10 (some 6) 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10, .gpr 6] []) (.reg (.gpr 6))) #v[92, 184]
    (.letOp (n := 187) (.exec 0x11ce6b (LoadPre 0x11ce6b (fun s => AddrMode.addr (.sib 10 (some 6) 0 (.d8 0x10)) s (0x11ce6b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce6b 6 (.sib 10 (some 6) 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 6] [])) #v[92, 184]
    (.letOp (n := 188) (.exec 0x11ce70 (StorePre 0x11ce70 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3b0)) s (0x11ce70 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ce70 6 (.sib 4 none 0 (.d32 0x3b0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[186, 4]
    (.letOp (n := 189) (.out 0x11ce78 (movR64M64Effect 0x11ce78 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 190) (.exec 0x11ce78 (LoadPre 0x11ce78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce78 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce78 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 191) (.out 0x11ce7d (movR64M64Effect 0x11ce7d 6 (.sib 10 (some 6) 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10, .gpr 6] []) (.reg (.gpr 6))) #v[92, 189]
    (.letOp (n := 192) (.exec 0x11ce7d (LoadPre 0x11ce7d (fun s => AddrMode.addr (.sib 10 (some 6) 0 (.d8 0x18)) s (0x11ce7d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce7d 6 (.sib 10 (some 6) 0 (.d8 0x18))) (Reg.operands [.gpr 10, .gpr 6] [])) #v[92, 189]
    (.letOp (n := 193) (.exec 0x11ce82 (StorePre 0x11ce82 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3b8)) s (0x11ce82 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ce82 6 (.sib 4 none 0 (.d32 0x3b8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[191, 4]
    (.letOp (n := 194) (.out 0x11ce8a (movR64M64Effect 0x11ce8a 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 195) (.exec 0x11ce8a (LoadPre 0x11ce8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce8a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce8a 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 196) (.out 0x11ce8f (movR64M64Effect 0x11ce8f 6 (.sib 10 (some 6) 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10, .gpr 6] []) (.reg (.gpr 6))) #v[92, 194]
    (.letOp (n := 197) (.exec 0x11ce8f (LoadPre 0x11ce8f (fun s => AddrMode.addr (.sib 10 (some 6) 0 (.d8 0x20)) s (0x11ce8f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce8f 6 (.sib 10 (some 6) 0 (.d8 0x20))) (Reg.operands [.gpr 10, .gpr 6] [])) #v[92, 194]
    (.letOp (n := 198) (.exec 0x11ce94 (StorePre 0x11ce94 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3c0)) s (0x11ce94 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11ce94 6 (.sib 4 none 0 (.d32 0x3c0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[196, 4]
    (b_l11ccfd_4)))))))))))))))))))))))))))))))))))

def bytes_l11ccfd_3 : List UInt8 :=
  [0x4F, 0x8B, 0x44, 0x02, 0x50, 0x4D, 0x89, 0x01, 0x49, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x00, 0x00, 0x4C, 0x21, 0xF6, 0x48, 0x01, 0xDF, 0x49, 0x89, 0xF8, 0x49, 0xC1, 0xE8, 0x34, 0x49,
    0x01, 0xF0, 0x48, 0x8B, 0x74, 0x24, 0x08, 0x49, 0x8B, 0x74, 0x32, 0x08, 0x48, 0x89, 0xB4, 0x24,
    0xA8, 0x03, 0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x08, 0x49, 0x8B, 0x74, 0x32, 0x10, 0x48, 0x89,
    0xB4, 0x24, 0xB0, 0x03, 0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x08, 0x49, 0x8B, 0x74, 0x32, 0x18,
    0x48, 0x89, 0xB4, 0x24, 0xB8, 0x03, 0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x08, 0x49, 0x8B, 0x74,
    0x32, 0x20, 0x48, 0x89, 0xB4, 0x24, 0xC0, 0x03, 0x00, 0x00] ++ bytes_l11ccfd_4

theorem code_l11ccfd_3 : ∀ x ∈ codeRange 0x11ce32 bytes_l11ccfd_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ce32 106 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11ccfd_4

@[cfg_block] def b_l11ccfd_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x11cdd5 (shrR64Effect 0x11cdd5 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[126]
    (.letOp (n := 129) (.exec 0x11cdd5 (fun s => s.RIP = 0x11cdd5) (shrR64Effect 0x11cdd5 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[126]
    (.letOp (n := 130) (.out 0x11cdd9 (movR64M64Effect 0x11cdd9 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 131) (.exec 0x11cdd9 (LoadPre 0x11cdd9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11cdd9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cdd9 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 132) (.out 0x11cdde (subR64M64Effect 0x11cdde 2 (.sib 10 (some 7) 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10, .gpr 7] []) (.reg (.gpr 2))) #v[128, 92, 130]
    (.letOp (n := 133) (.exec 0x11cdde (LoadPre 0x11cdde (fun s => AddrMode.addr (.sib 10 (some 7) 0 (.d8 0x38)) s (0x11cdde + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11cdde 2 (.sib 10 (some 7) 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 10, .gpr 7] [])) #v[128, 92, 130]
    (.letOp (n := 134) (.out 0x11cde3 (addR64R64Effect 0x11cde3 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[132, 3]
    (.letOp (n := 135) (.exec 0x11cde3 (fun s => s.RIP = 0x11cde3) (addR64R64Effect 0x11cde3 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[132, 3]
    (.letOp (n := 136) (.out 0x11cde6 (movR64R64Effect 0x11cde6 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[134]
    (.letOp (n := 137) (.exec 0x11cde6 (fun s => s.RIP = 0x11cde6) (movR64R64Effect 0x11cde6 7 2) (Reg.operands [.gpr 2] [])) #v[134]
    (.letOp (n := 138) (.out 0x11cde9 (shrR64Effect 0x11cde9 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[136]
    (.letOp (n := 139) (.exec 0x11cde9 (fun s => s.RIP = 0x11cde9) (shrR64Effect 0x11cde9 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[136]
    (.letOp (n := 140) (.out 0x11cded (movR64M64Effect 0x11cded 9 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 141) (.exec 0x11cded (LoadPre 0x11cded (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11cded + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cded 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 142) (.out 0x11cdf2 (subR64M64Effect 0x11cdf2 7 (.sib 10 (some 9) 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10, .gpr 9] []) (.reg (.gpr 7))) #v[138, 92, 140]
    (.letOp (n := 143) (.exec 0x11cdf2 (LoadPre 0x11cdf2 (fun s => AddrMode.addr (.sib 10 (some 9) 0 (.d8 0x40)) s (0x11cdf2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11cdf2 7 (.sib 10 (some 9) 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 10, .gpr 9] [])) #v[138, 92, 140]
    (.letOp (n := 144) (.out 0x11cdf7 (leaR64Effect 0x11cdf7 9 (.sib 4 none 0 (.d32 0x3f0))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 145) (.exec 0x11cdf7 (fun s => s.RIP = 0x11cdf7) (leaR64Effect 0x11cdf7 9 (.sib 4 none 0 (.d32 0x3f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 146) (.exec 0x11cdff (StorePre 0x11cdff 4 (fun s => AddrMode.addr (.base 9 (.d8 0x20)) s (0x11cdff + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11cdff 8 (.base 9 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 9] [])) #v[122, 144]
    (.letOp (n := 147) (.out 0x11ce03 (movR64M64Effect 0x11ce03 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 148) (.exec 0x11ce03 (LoadPre 0x11ce03 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce03 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce03 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 149) (.out 0x11ce08 (movR64M64Effect 0x11ce08 8 (.sib 10 (some 8) 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10, .gpr 8] []) (.reg (.gpr 8))) #v[92, 147]
    (.letOp (n := 150) (.exec 0x11ce08 (LoadPre 0x11ce08 (fun s => AddrMode.addr (.sib 10 (some 8) 0 (.d8 0x68)) s (0x11ce08 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce08 8 (.sib 10 (some 8) 0 (.d8 0x68))) (Reg.operands [.gpr 10, .gpr 8] [])) #v[92, 147]
    (.letOp (n := 151) (.exec 0x11ce0d (StorePre 0x11ce0d 4 (fun s => AddrMode.addr (.base 9 (.d8 0x18)) s (0x11ce0d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ce0d 8 (.base 9 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 9] [])) #v[149, 144]
    (.letOp (n := 152) (.out 0x11ce11 (movR64M64Effect 0x11ce11 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 153) (.exec 0x11ce11 (LoadPre 0x11ce11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce11 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce11 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 154) (.out 0x11ce16 (movR64M64Effect 0x11ce16 8 (.sib 10 (some 8) 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10, .gpr 8] []) (.reg (.gpr 8))) #v[92, 152]
    (.letOp (n := 155) (.exec 0x11ce16 (LoadPre 0x11ce16 (fun s => AddrMode.addr (.sib 10 (some 8) 0 (.d8 0x60)) s (0x11ce16 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce16 8 (.sib 10 (some 8) 0 (.d8 0x60))) (Reg.operands [.gpr 10, .gpr 8] [])) #v[92, 152]
    (.letOp (n := 156) (.exec 0x11ce1b (StorePre 0x11ce1b 4 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x11ce1b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ce1b 8 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 9] [])) #v[154, 144]
    (.letOp (n := 157) (.out 0x11ce1f (movR64M64Effect 0x11ce1f 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 158) (.exec 0x11ce1f (LoadPre 0x11ce1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce1f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce1f 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 159) (.out 0x11ce24 (movR64M64Effect 0x11ce24 8 (.sib 10 (some 8) 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10, .gpr 8] []) (.reg (.gpr 8))) #v[92, 157]
    (.letOp (n := 160) (.exec 0x11ce24 (LoadPre 0x11ce24 (fun s => AddrMode.addr (.sib 10 (some 8) 0 (.d8 0x58)) s (0x11ce24 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce24 8 (.sib 10 (some 8) 0 (.d8 0x58))) (Reg.operands [.gpr 10, .gpr 8] [])) #v[92, 157]
    (.letOp (n := 161) (.exec 0x11ce29 (StorePre 0x11ce29 4 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x11ce29 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ce29 8 (.base 9 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 9] [])) #v[159, 144]
    (.letOp (n := 162) (.out 0x11ce2d (movR64M64Effect 0x11ce2d 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 163) (.exec 0x11ce2d (LoadPre 0x11ce2d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ce2d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ce2d 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11ccfd_3))))))))))))))))))))))))))))))))))))

def bytes_l11ccfd_2 : List UInt8 :=
  [0x48, 0xC1, 0xEA, 0x34, 0x48, 0x8B, 0x7C, 0x24, 0x08, 0x49, 0x2B, 0x54, 0x3A, 0x38, 0x48, 0x01,
    0xDA, 0x48, 0x89, 0xD7, 0x48, 0xC1, 0xEF, 0x34, 0x4C, 0x8B, 0x4C, 0x24, 0x08, 0x4B, 0x2B, 0x7C,
    0x0A, 0x40, 0x4C, 0x8D, 0x8C, 0x24, 0xF0, 0x03, 0x00, 0x00, 0x4D, 0x89, 0x41, 0x20, 0x4C, 0x8B,
    0x44, 0x24, 0x08, 0x4F, 0x8B, 0x44, 0x02, 0x68, 0x4D, 0x89, 0x41, 0x18, 0x4C, 0x8B, 0x44, 0x24,
    0x08, 0x4F, 0x8B, 0x44, 0x02, 0x60, 0x4D, 0x89, 0x41, 0x10, 0x4C, 0x8B, 0x44, 0x24, 0x08, 0x4F,
    0x8B, 0x44, 0x02, 0x58, 0x4D, 0x89, 0x41, 0x08, 0x4C, 0x8B, 0x44, 0x24, 0x08] ++ bytes_l11ccfd_3

theorem code_l11ccfd_2 : ∀ x ∈ codeRange 0x11cdd5 bytes_l11ccfd_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1cdd5 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11ccfd_3

@[cfg_block] def b_l11ccfd_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.out 0x11cd6c (movR64Imm64Effect 0x11cd6c 6 0x3fffffffffffc) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 89) (.exec 0x11cd6c (fun s => s.RIP = 0x11cd6c) (movR64Imm64Effect 0x11cd6c 6 0x3fffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 90) (.out 0x11cd76 (movR64M64Effect 0x11cd76 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 91) (.exec 0x11cd76 (LoadPre 0x11cd76 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11cd76 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cd76 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.out 0x11cd7b (movR64M64Effect 0x11cd7b 10 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 93) (.exec 0x11cd7b (LoadPre 0x11cd7b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11cd7b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cd7b 10 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 94) (.out 0x11cd83 (subR64M64Effect 0x11cd83 6 (.sib 10 (some 0) 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10, .gpr 0] []) (.reg (.gpr 6))) #v[88, 92, 90]
    (.letOp (n := 95) (.exec 0x11cd83 (LoadPre 0x11cd83 (fun s => AddrMode.addr (.sib 10 (some 0) 0 (.d8 0x48)) s (0x11cd83 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11cd83 6 (.sib 10 (some 0) 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 10, .gpr 0] [])) #v[88, 92, 90]
    (.letOp (n := 96) (.out 0x11cd88 (movR64R64Effect 0x11cd88 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[94]
    (.letOp (n := 97) (.exec 0x11cd88 (fun s => s.RIP = 0x11cd88) (movR64R64Effect 0x11cd88 0 6) (Reg.operands [.gpr 6] [])) #v[94]
    (.letOp (n := 98) (.out 0x11cd8b (shrR64Effect 0x11cd8b 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[96]
    (.letOp (n := 99) (.exec 0x11cd8b (fun s => s.RIP = 0x11cd8b) (shrR64Effect 0x11cd8b 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[96]
    (.letOp (n := 100) (.out 0x11cd8f (movR64Imm64Effect 0x11cd8f 13 0x1000003d1) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 101) (.exec 0x11cd8f (fun s => s.RIP = 0x11cd8f) (movR64Imm64Effect 0x11cd8f 13 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 102) (.out 0x11cd99 (imulR64R64Effect 0x11cd99 4 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[98, 100]
    (.letOp (n := 103) (.exec 0x11cd99 (fun s => s.RIP = 0x11cd99) (imulR64R64Effect 0x11cd99 4 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[98, 100]
    (.letOp (n := 104) (.out 0x11cd9d (movR64M64Effect 0x11cd9d 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 105) (.exec 0x11cd9d (LoadPre 0x11cd9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11cd9d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cd9d 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.out 0x11cda2 (subR64M64Effect 0x11cda2 0 (.sib 10 (some 1) 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10, .gpr 1] []) (.reg (.gpr 0))) #v[102, 92, 104]
    (.letOp (n := 107) (.exec 0x11cda2 (LoadPre 0x11cda2 (fun s => AddrMode.addr (.sib 10 (some 1) 0 (.d8 0x28)) s (0x11cda2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11cda2 0 (.sib 10 (some 1) 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 10, .gpr 1] [])) #v[102, 92, 104]
    (.letOp (n := 108) (.out 0x11cda7 (movR64Imm64Effect 0x11cda7 14 0x3ffffbfffff0bc) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 109) (.exec 0x11cda7 (fun s => s.RIP = 0x11cda7) (movR64Imm64Effect 0x11cda7 14 0x3ffffbfffff0bc) (Reg.operands [] [])) #v[]
    (.letOp (n := 110) (.out 0x11cdb1 (addR64R64Effect 0x11cdb1 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[106, 108]
    (.letOp (n := 111) (.exec 0x11cdb1 (fun s => s.RIP = 0x11cdb1) (addR64R64Effect 0x11cdb1 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[106, 108]
    (.letOp (n := 112) (.out 0x11cdb4 (movR64R64Effect 0x11cdb4 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[110]
    (.letOp (n := 113) (.exec 0x11cdb4 (fun s => s.RIP = 0x11cdb4) (movR64R64Effect 0x11cdb4 1 0) (Reg.operands [.gpr 0] [])) #v[110]
    (.letOp (n := 114) (.out 0x11cdb7 (shrR64Effect 0x11cdb7 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[112]
    (.letOp (n := 115) (.exec 0x11cdb7 (fun s => s.RIP = 0x11cdb7) (shrR64Effect 0x11cdb7 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[112]
    (.letOp (n := 116) (.out 0x11cdbb (movR64M64Effect 0x11cdbb 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 117) (.exec 0x11cdbb (LoadPre 0x11cdbb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11cdbb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cdbb 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 118) (.out 0x11cdc0 (subR64M64Effect 0x11cdc0 1 (.sib 10 (some 2) 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10, .gpr 2] []) (.reg (.gpr 1))) #v[114, 92, 116]
    (.letOp (n := 119) (.exec 0x11cdc0 (LoadPre 0x11cdc0 (fun s => AddrMode.addr (.sib 10 (some 2) 0 (.d8 0x30)) s (0x11cdc0 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11cdc0 1 (.sib 10 (some 2) 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 10, .gpr 2] [])) #v[114, 92, 116]
    (.letOp (n := 120) (.out 0x11cdc5 (movR64M64Effect 0x11cdc5 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 121) (.exec 0x11cdc5 (LoadPre 0x11cdc5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11cdc5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cdc5 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 122) (.out 0x11cdca (movR64M64Effect 0x11cdca 8 (.sib 10 (some 2) 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10, .gpr 2] []) (.reg (.gpr 8))) #v[92, 120]
    (.letOp (n := 123) (.exec 0x11cdca (LoadPre 0x11cdca (fun s => AddrMode.addr (.sib 10 (some 2) 0 (.d8 0x70)) s (0x11cdca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11cdca 8 (.sib 10 (some 2) 0 (.d8 0x70))) (Reg.operands [.gpr 10, .gpr 2] [])) #v[92, 120]
    (.letOp (n := 124) (.out 0x11cdcf (addR64R64Effect 0x11cdcf 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[118, 3]
    (.letOp (n := 125) (.exec 0x11cdcf (fun s => s.RIP = 0x11cdcf) (addR64R64Effect 0x11cdcf 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[118, 3]
    (.letOp (n := 126) (.out 0x11cdd2 (movR64R64Effect 0x11cdd2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[124]
    (.letOp (n := 127) (.exec 0x11cdd2 (fun s => s.RIP = 0x11cdd2) (movR64R64Effect 0x11cdd2 2 1) (Reg.operands [.gpr 1] [])) #v[124]
    (b_l11ccfd_2))))))))))))))))))))))))))))))))))))))))

def bytes_l11ccfd_1 : List UInt8 :=
  [0x48, 0xBE, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x4C,
    0x8B, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0x2B, 0x74, 0x02, 0x48, 0x48, 0x89, 0xF0, 0x48,
    0xC1, 0xE8, 0x30, 0x49, 0xBD, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x49, 0x0F, 0xAF,
    0xC5, 0x48, 0x8B, 0x4C, 0x24, 0x08, 0x49, 0x2B, 0x44, 0x0A, 0x28, 0x49, 0xBE, 0xBC, 0xF0, 0xFF,
    0xFF, 0xFB, 0xFF, 0x3F, 0x00, 0x4C, 0x01, 0xF0, 0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x34, 0x48,
    0x8B, 0x54, 0x24, 0x08, 0x49, 0x2B, 0x4C, 0x12, 0x30, 0x48, 0x8B, 0x54, 0x24, 0x08, 0x4D, 0x8B,
    0x44, 0x12, 0x70, 0x48, 0x01, 0xD9, 0x48, 0x89, 0xCA] ++ bytes_l11ccfd_2

theorem code_l11ccfd_1 : ∀ x ∈ codeRange 0x11cd6c bytes_l11ccfd_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1cd6c 105 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11ccfd_2

@[cfg_block] def b_l11ccfd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11ccfd (movzxR32M8Effect 0x11ccfd 5 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11ccfd (LoadPre 0x11ccfd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11ccfd + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11ccfd 5 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11cd02 (StorePre 0x11cd02 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cd02 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x11cd02 7 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11cd09 (movzxR32M8Effect 0x11cd09 8 0 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11cd09 (LoadPre 0x11cd09 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11cd09 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11cd09 8 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x11cd11 (movR64M64Effect 0x11cd11 1 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x11cd11 (LoadPre 0x11cd11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x11cd11 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cd11 1 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x11cd19 (testR8R8Effect 0x11cd19 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[56, 56]
    (.letOp (n := 61) (.exec 0x11cd19 (fun s => s.RIP = 0x11cd19) (testR8R8Effect 0x11cd19 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[56, 56]
    (.letOp (n := 62) (.out 0x11cd1b (atFlags (condHolds 5) (cmovR64R64Effect 0x11cd1b 4 12 1)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 12))) #v[12, 58, 60]
    (.letOp (n := 63) (.exec 0x11cd1b (fun s => s.RIP = 0x11cd1b) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cd1b 4 12 1)) (Reg.operands [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[12, 58, 60]
    (.letOp (n := 64) (.out 0x11cd1f (movR64M64Effect 0x11cd1f 1 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11cd1f (LoadPre 0x11cd1f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x11cd1f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cd1f 1 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x11cd27 (testR8R8Effect 0x11cd27 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[56, 56]
    (.letOp (n := 67) (.exec 0x11cd27 (fun s => s.RIP = 0x11cd27) (testR8R8Effect 0x11cd27 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[56, 56]
    (.letOp (n := 68) (.out 0x11cd29 (atFlags (condHolds 5) (cmovR64R64Effect 0x11cd29 4 13 1)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 13))) #v[13, 64, 66]
    (.letOp (n := 69) (.exec 0x11cd29 (fun s => s.RIP = 0x11cd29) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cd29 4 13 1)) (Reg.operands [.gpr 13, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[13, 64, 66]
    (.letOp (n := 70) (.out 0x11cd2d (movR64M64Effect 0x11cd2d 1 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 71) (.exec 0x11cd2d (LoadPre 0x11cd2d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x11cd2d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cd2d 1 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x11cd35 (movR64R64Effect 0x11cd35 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 73) (.exec 0x11cd35 (fun s => s.RIP = 0x11cd35) (movR64R64Effect 0x11cd35 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 74) (.out 0x11cd38 (testR8R8Effect 0x11cd38 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[56, 56]
    (.letOp (n := 75) (.exec 0x11cd38 (fun s => s.RIP = 0x11cd38) (testR8R8Effect 0x11cd38 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[56, 56]
    (.letOp (n := 76) (.out 0x11cd3a (atFlags (condHolds 5) (cmovR64R64Effect 0x11cd3a 4 2 1)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[72, 70, 74]
    (.letOp (n := 77) (.exec 0x11cd3a (fun s => s.RIP = 0x11cd3a) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cd3a 4 2 1)) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[72, 70, 74]
    (.letOp (n := 78) (.out 0x11cd3e (movR64M64Effect 0x11cd3e 1 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 79) (.exec 0x11cd3e (LoadPre 0x11cd3e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x11cd3e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11cd3e 1 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x11cd46 (testR8R8Effect 0x11cd46 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[56, 56]
    (.letOp (n := 81) (.exec 0x11cd46 (fun s => s.RIP = 0x11cd46) (testR8R8Effect 0x11cd46 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[56, 56]
    (.letOp (n := 82) (.out 0x11cd48 (atFlags (condHolds 5) (cmovR64R64Effect 0x11cd48 4 5 1)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 5))) #v[5, 78, 80]
    (.letOp (n := 83) (.exec 0x11cd48 (fun s => s.RIP = 0x11cd48) (atFlags (condHolds 5) (cmovR64R64Effect 0x11cd48 4 5 1)) (Reg.operands [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[5, 78, 80]
    (.letOp (n := 84) (.exec 0x11cd4c (StorePre 0x11cd4c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x290)) s (0x11cd4c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cd4c 12 (.sib 4 none 0 (.d32 0x290))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 85) (.exec 0x11cd54 (StorePre 0x11cd54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x298)) s (0x11cd54 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cd54 13 (.sib 4 none 0 (.d32 0x298))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 86) (.exec 0x11cd5c (StorePre 0x11cd5c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2a0)) s (0x11cd5c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cd5c 2 (.sib 4 none 0 (.d32 0x2a0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 87) (.exec 0x11cd64 (StorePre 0x11cd64 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2a8)) s (0x11cd64 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11cd64 5 (.sib 4 none 0 (.d32 0x2a8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[82, 4]
    (b_l11ccfd_1)))))))))))))))))))))))))))))))))))

def bytes_l11ccfd : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x48, 0x88, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x0F, 0xB6, 0x84, 0x24,
    0xD0, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00, 0x84, 0xC0, 0x4C, 0x0F,
    0x45, 0xE1, 0x48, 0x8B, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00, 0x84, 0xC0, 0x4C, 0x0F, 0x45, 0xE9,
    0x48, 0x8B, 0x8C, 0x24, 0x38, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF2, 0x84, 0xC0, 0x48, 0x0F, 0x45,
    0xD1, 0x48, 0x8B, 0x8C, 0x24, 0x40, 0x01, 0x00, 0x00, 0x84, 0xC0, 0x48, 0x0F, 0x45, 0xE9, 0x4C,
    0x89, 0xA4, 0x24, 0x90, 0x02, 0x00, 0x00, 0x4C, 0x89, 0xAC, 0x24, 0x98, 0x02, 0x00, 0x00, 0x48,
    0x89, 0x94, 0x24, 0xA0, 0x02, 0x00, 0x00, 0x48, 0x89, 0xAC, 0x24, 0xA8, 0x02, 0x00, 0x00] ++ bytes_l11ccfd_1

theorem code_l11ccfd : ∀ x ∈ codeRange 0x11ccfd bytes_l11ccfd, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ccfd 111 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11ccfd_1

@[cfg_block] def b_l11cf0d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11cf0d (movR32Imm32Effect 0x11cf0d 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11cf0d (fun s => s.RIP = 0x11cf0d) (movR32Imm32Effect 0x11cf0d 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11cf12 (leaR64Effect 0x11cf12 7 (.sib 4 none 0 (.d32 0x850))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x11cf12 (fun s => s.RIP = 0x11cf12) (leaR64Effect 0x11cf12 7 (.sib 4 none 0 (.d32 0x850))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11cf1a (movR64R64Effect 0x11cf1a 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 58) (.exec 0x11cf1a (fun s => s.RIP = 0x11cf1a) (movR64R64Effect 0x11cf1a 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.exec 0x11cf1d (RepPre 0x11cf1d (RepMovsqPre 0x11cf1d)) (repMovsqEffect 0x11cf1d) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11cf20 (movR32Imm32Effect 0x11cf20 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11cf20 (fun s => s.RIP = 0x11cf20) (movR32Imm32Effect 0x11cf20 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11cf25 (leaR64Effect 0x11cf25 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x11cf25 (fun s => s.RIP = 0x11cf25) (leaR64Effect 0x11cf25 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11cf2d (movR64R64Effect 0x11cf2d 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 65) (.exec 0x11cf2d (fun s => s.RIP = 0x11cf2d) (movR64R64Effect 0x11cf2d 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 66) (.exec 0x11cf30 (RepPre 0x11cf30 (RepMovsqPre 0x11cf30)) (repMovsqEffect 0x11cf30) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[64, 62, 60, 22]
    (.letOp (n := 67) (.out 0x11cf33 (movR32Imm32Effect 0x11cf33 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 68) (.exec 0x11cf33 (fun s => s.RIP = 0x11cf33) (movR32Imm32Effect 0x11cf33 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x11cf38 (movR64R64Effect 0x11cf38 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 70) (.exec 0x11cf38 (fun s => s.RIP = 0x11cf38) (movR64R64Effect 0x11cf38 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 71) (.out 0x11cf3b (movR64R64Effect 0x11cf3b 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 72) (.exec 0x11cf3b (fun s => s.RIP = 0x11cf3b) (movR64R64Effect 0x11cf3b 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 73) (.exec 0x11cf3e (RepPre 0x11cf3e (RepMovsqPre 0x11cf3e)) (repMovsqEffect 0x11cf3e) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[71, 69, 67, 22]
    (.letOp (n := 74) (.out 0x11cf41 (movR64R64Effect 0x11cf41 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 75) (.exec 0x11cf41 (fun s => s.RIP = 0x11cf41) (movR64R64Effect 0x11cf41 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 76) (.out 0x11cf44 (leaR64Effect 0x11cf44 6 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 77) (.exec 0x11cf44 (fun s => s.RIP = 0x11cf44) (leaR64Effect 0x11cf44 6 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x11cf4c (callEffect (fun _ => 0x10a410) 0x11cf51) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 79) (.exec 0x11cf4c (PushPre 0x11cf4c 5) (callEffect (fun _ => 0x10a410) 0x11cf51) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.const ⟨64, 0x11cf51⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 78), (5, 5), (6, 76), (7, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩ { target := .l11cf51, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l11cf0d : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x50, 0x08, 0x00, 0x00, 0x48, 0x89, 0xEE,
    0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00,
    0x48, 0x89, 0xEE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89,
    0xEE, 0xF3, 0x48, 0xA5, 0x4C, 0x89, 0xFF, 0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00, 0xE8,
    0xBF, 0xD4, 0xFE, 0xFF]

theorem code_l11cf0d : ∀ x ∈ codeRange 0x11cf0d bytes_l11cf0d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1cf0d 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11cf51_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x11cfa9 (callEffect (fun _ => 0x10a410) 0x11cfae) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 90) (.exec 0x11cfa9 (PushPre 0x11cfa9 5) (callEffect (fun _ => 0x10a410) 0x11cfae) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.const ⟨64, 0x11cfae⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(0, 64), (3, 3), (4, 89), (5, 5), (6, 87), (7, 85), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 92⟩ { target := .l11cfae, kept := #v[], arity := rfl, guard := some (Fin.last 91) }))))

def bytes_l11cf51_1 : List UInt8 :=
  [0xE8, 0x62, 0xD4, 0xFE, 0xFF]

theorem code_l11cf51_1 : ∀ x ∈ codeRange 0x11cfa9 bytes_l11cf51_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1cfa9 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11cf51 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11cf51 (movR32Imm32Effect 0x11cf51 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11cf51 (fun s => s.RIP = 0x11cf51) (movR32Imm32Effect 0x11cf51 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11cf56 (leaR64Effect 0x11cf56 13 (.sib 4 none 0 (.d32 0x418))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 56) (.exec 0x11cf56 (fun s => s.RIP = 0x11cf56) (leaR64Effect 0x11cf56 13 (.sib 4 none 0 (.d32 0x418))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11cf5e (movR64R64Effect 0x11cf5e 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x11cf5e (fun s => s.RIP = 0x11cf5e) (movR64R64Effect 0x11cf5e 7 13) (Reg.operands [.gpr 13] [])) #v[55]
    (.letOp (n := 59) (.out 0x11cf61 (movR64R64Effect 0x11cf61 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 60) (.exec 0x11cf61 (fun s => s.RIP = 0x11cf61) (movR64R64Effect 0x11cf61 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.exec 0x11cf64 (RepPre 0x11cf64 (RepMovsqPre 0x11cf64)) (repMovsqEffect 0x11cf64) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[59, 57, 53, 22]
    (.letOp (n := 62) (.out 0x11cf67 (movR32Imm32Effect 0x11cf67 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 63) (.exec 0x11cf67 (fun s => s.RIP = 0x11cf67) (movR32Imm32Effect 0x11cf67 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x11cf6c (leaR64Effect 0x11cf6c 0 (.sib 4 none 0 (.d32 0x8c8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 65) (.exec 0x11cf6c (fun s => s.RIP = 0x11cf6c) (leaR64Effect 0x11cf6c 0 (.sib 4 none 0 (.d32 0x8c8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x11cf74 (movR64R64Effect 0x11cf74 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[64]
    (.letOp (n := 67) (.exec 0x11cf74 (fun s => s.RIP = 0x11cf74) (movR64R64Effect 0x11cf74 7 0) (Reg.operands [.gpr 0] [])) #v[64]
    (.letOp (n := 68) (.out 0x11cf77 (movR64R64Effect 0x11cf77 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 69) (.exec 0x11cf77 (fun s => s.RIP = 0x11cf77) (movR64R64Effect 0x11cf77 6 13) (Reg.operands [.gpr 13] [])) #v[55]
    (.letOp (n := 70) (.exec 0x11cf7a (RepPre 0x11cf7a (RepMovsqPre 0x11cf7a)) (repMovsqEffect 0x11cf7a) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[68, 66, 62, 22]
    (.letOp (n := 71) (.out 0x11cf7d (movR32Imm32Effect 0x11cf7d 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 72) (.exec 0x11cf7d (fun s => s.RIP = 0x11cf7d) (movR32Imm32Effect 0x11cf7d 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x11cf82 (leaR64Effect 0x11cf82 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 74) (.exec 0x11cf82 (fun s => s.RIP = 0x11cf82) (leaR64Effect 0x11cf82 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x11cf8a (movR64R64Effect 0x11cf8a 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[64]
    (.letOp (n := 76) (.exec 0x11cf8a (fun s => s.RIP = 0x11cf8a) (movR64R64Effect 0x11cf8a 6 0) (Reg.operands [.gpr 0] [])) #v[64]
    (.letOp (n := 77) (.exec 0x11cf8d (RepPre 0x11cf8d (RepMovsqPre 0x11cf8d)) (repMovsqEffect 0x11cf8d) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[75, 73, 71, 22]
    (.letOp (n := 78) (.out 0x11cf90 (movR32Imm32Effect 0x11cf90 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 79) (.exec 0x11cf90 (fun s => s.RIP = 0x11cf90) (movR32Imm32Effect 0x11cf90 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 80) (.out 0x11cf95 (movR64R64Effect 0x11cf95 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 81) (.exec 0x11cf95 (fun s => s.RIP = 0x11cf95) (movR64R64Effect 0x11cf95 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 82) (.out 0x11cf98 (movR64R64Effect 0x11cf98 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 83) (.exec 0x11cf98 (fun s => s.RIP = 0x11cf98) (movR64R64Effect 0x11cf98 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 84) (.exec 0x11cf9b (RepPre 0x11cf9b (RepMovsqPre 0x11cf9b)) (repMovsqEffect 0x11cf9b) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[82, 80, 78, 22]
    (.letOp (n := 85) (.out 0x11cf9e (movR64R64Effect 0x11cf9e 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 86) (.exec 0x11cf9e (fun s => s.RIP = 0x11cf9e) (movR64R64Effect 0x11cf9e 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 87) (.out 0x11cfa1 (leaR64Effect 0x11cfa1 6 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 88) (.exec 0x11cfa1 (fun s => s.RIP = 0x11cfa1) (leaR64Effect 0x11cfa1 6 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11cf51_1))))))))))))))))))))))))))))))))))))

def bytes_l11cf51 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0xAC, 0x24, 0x18, 0x04, 0x00, 0x00, 0x4C, 0x89, 0xEF,
    0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0xC8,
    0x08, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x4C, 0x89, 0xEE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00,
    0x00, 0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x89, 0xC6, 0xF3, 0x48, 0xA5, 0xB9,
    0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xEE, 0xF3, 0x48, 0xA5, 0x4C, 0x89, 0xFF,
    0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00] ++ bytes_l11cf51_1

theorem code_l11cf51 : ∀ x ∈ codeRange 0x11cf51 bytes_l11cf51, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1cf51 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11cf51_1

@[cfg_block] def b_l11cfae : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11cfae (movR32Imm32Effect 0x11cfae 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11cfae (fun s => s.RIP = 0x11cfae) (movR32Imm32Effect 0x11cfae 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11cfb3 (movR64R64Effect 0x11cfb3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 56) (.exec 0x11cfb3 (fun s => s.RIP = 0x11cfb3) (movR64R64Effect 0x11cfb3 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x11cfb6 (movR64R64Effect 0x11cfb6 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11cfb6 (fun s => s.RIP = 0x11cfb6) (movR64R64Effect 0x11cfb6 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.exec 0x11cfb9 (RepPre 0x11cfb9 (RepMovsqPre 0x11cfb9)) (repMovsqEffect 0x11cfb9) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11cfbc (movR32Imm32Effect 0x11cfbc 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11cfbc (fun s => s.RIP = 0x11cfbc) (movR32Imm32Effect 0x11cfbc 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11cfc1 (leaR64Effect 0x11cfc1 0 (.sib 4 none 0 (.d32 0x940))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11cfc1 (fun s => s.RIP = 0x11cfc1) (leaR64Effect 0x11cfc1 0 (.sib 4 none 0 (.d32 0x940))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11cfc9 (movR64R64Effect 0x11cfc9 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 65) (.exec 0x11cfc9 (fun s => s.RIP = 0x11cfc9) (movR64R64Effect 0x11cfc9 7 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 66) (.out 0x11cfcc (movR64R64Effect 0x11cfcc 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 67) (.exec 0x11cfcc (fun s => s.RIP = 0x11cfcc) (movR64R64Effect 0x11cfcc 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 68) (.exec 0x11cfcf (RepPre 0x11cfcf (RepMovsqPre 0x11cfcf)) (repMovsqEffect 0x11cfcf) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[66, 64, 60, 22]
    (.letOp (n := 69) (.out 0x11cfd2 (movR32Imm32Effect 0x11cfd2 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x11cfd2 (fun s => s.RIP = 0x11cfd2) (movR32Imm32Effect 0x11cfd2 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x11cfd7 (leaR64Effect 0x11cfd7 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 72) (.exec 0x11cfd7 (fun s => s.RIP = 0x11cfd7) (leaR64Effect 0x11cfd7 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x11cfdf (movR64R64Effect 0x11cfdf 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[62]
    (.letOp (n := 74) (.exec 0x11cfdf (fun s => s.RIP = 0x11cfdf) (movR64R64Effect 0x11cfdf 6 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 75) (.exec 0x11cfe2 (RepPre 0x11cfe2 (RepMovsqPre 0x11cfe2)) (repMovsqEffect 0x11cfe2) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[73, 71, 69, 22]
    (.letOp (n := 76) (.out 0x11cfe5 (movR32Imm32Effect 0x11cfe5 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 77) (.exec 0x11cfe5 (fun s => s.RIP = 0x11cfe5) (movR32Imm32Effect 0x11cfe5 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x11cfea (movR64R64Effect 0x11cfea 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 79) (.exec 0x11cfea (fun s => s.RIP = 0x11cfea) (movR64R64Effect 0x11cfea 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 80) (.out 0x11cfed (movR64R64Effect 0x11cfed 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 81) (.exec 0x11cfed (fun s => s.RIP = 0x11cfed) (movR64R64Effect 0x11cfed 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 82) (.exec 0x11cff0 (RepPre 0x11cff0 (RepMovsqPre 0x11cff0)) (repMovsqEffect 0x11cff0) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[80, 78, 76, 22]
    (.letOp (n := 83) (.out 0x11cff3 (movR64R64Effect 0x11cff3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 84) (.exec 0x11cff3 (fun s => s.RIP = 0x11cff3) (movR64R64Effect 0x11cff3 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 85) (.out 0x11cff6 (leaR64Effect 0x11cff6 6 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 86) (.exec 0x11cff6 (fun s => s.RIP = 0x11cff6) (leaR64Effect 0x11cff6 6 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x11cffe (callEffect (fun _ => 0x10a410) 0x11d003) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 88) (.exec 0x11cffe (PushPre 0x11cffe 5) (callEffect (fun _ => 0x10a410) 0x11d003) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.const ⟨64, 0x11d003⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ { target := .l11d003, kept := #v[], arity := rfl, guard := some (Fin.last 89) }))))))))))))))))))))))))))))))))))))))

def bytes_l11cfae : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0x40, 0x09, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x4C, 0x89,
    0xEE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00,
    0x00, 0x48, 0x89, 0xC6, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48,
    0x89, 0xEE, 0xF3, 0x48, 0xA5, 0x4C, 0x89, 0xFF, 0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00,
    0xE8, 0x0D, 0xD4, 0xFE, 0xFF]

theorem code_l11cfae : ∀ x ∈ codeRange 0x11cfae bytes_l11cfae, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1cfae 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d003 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d003 (movR32Imm32Effect 0x11d003 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11d003 (fun s => s.RIP = 0x11d003) (movR32Imm32Effect 0x11d003 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d008 (movR64R64Effect 0x11d008 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 56) (.exec 0x11d008 (fun s => s.RIP = 0x11d008) (movR64R64Effect 0x11d008 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x11d00b (movR64R64Effect 0x11d00b 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11d00b (fun s => s.RIP = 0x11d00b) (movR64R64Effect 0x11d00b 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.exec 0x11d00e (RepPre 0x11d00e (RepMovsqPre 0x11d00e)) (repMovsqEffect 0x11d00e) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11d011 (movR32Imm32Effect 0x11d011 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11d011 (fun s => s.RIP = 0x11d011) (movR32Imm32Effect 0x11d011 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11d016 (leaR64Effect 0x11d016 0 (.sib 4 none 0 (.d32 0x9b8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11d016 (fun s => s.RIP = 0x11d016) (leaR64Effect 0x11d016 0 (.sib 4 none 0 (.d32 0x9b8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11d01e (movR64R64Effect 0x11d01e 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 65) (.exec 0x11d01e (fun s => s.RIP = 0x11d01e) (movR64R64Effect 0x11d01e 7 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 66) (.out 0x11d021 (movR64R64Effect 0x11d021 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 67) (.exec 0x11d021 (fun s => s.RIP = 0x11d021) (movR64R64Effect 0x11d021 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 68) (.exec 0x11d024 (RepPre 0x11d024 (RepMovsqPre 0x11d024)) (repMovsqEffect 0x11d024) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[66, 64, 60, 22]
    (.letOp (n := 69) (.out 0x11d027 (movR32Imm32Effect 0x11d027 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x11d027 (fun s => s.RIP = 0x11d027) (movR32Imm32Effect 0x11d027 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x11d02c (leaR64Effect 0x11d02c 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 72) (.exec 0x11d02c (fun s => s.RIP = 0x11d02c) (leaR64Effect 0x11d02c 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x11d034 (movR64R64Effect 0x11d034 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[62]
    (.letOp (n := 74) (.exec 0x11d034 (fun s => s.RIP = 0x11d034) (movR64R64Effect 0x11d034 6 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 75) (.exec 0x11d037 (RepPre 0x11d037 (RepMovsqPre 0x11d037)) (repMovsqEffect 0x11d037) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[73, 71, 69, 22]
    (.letOp (n := 76) (.out 0x11d03a (movR32Imm32Effect 0x11d03a 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 77) (.exec 0x11d03a (fun s => s.RIP = 0x11d03a) (movR32Imm32Effect 0x11d03a 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x11d03f (movR64R64Effect 0x11d03f 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 79) (.exec 0x11d03f (fun s => s.RIP = 0x11d03f) (movR64R64Effect 0x11d03f 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 80) (.out 0x11d042 (movR64R64Effect 0x11d042 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 81) (.exec 0x11d042 (fun s => s.RIP = 0x11d042) (movR64R64Effect 0x11d042 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 82) (.exec 0x11d045 (RepPre 0x11d045 (RepMovsqPre 0x11d045)) (repMovsqEffect 0x11d045) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[80, 78, 76, 22]
    (.letOp (n := 83) (.out 0x11d048 (movR64R64Effect 0x11d048 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 84) (.exec 0x11d048 (fun s => s.RIP = 0x11d048) (movR64R64Effect 0x11d048 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 85) (.out 0x11d04b (leaR64Effect 0x11d04b 6 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 86) (.exec 0x11d04b (fun s => s.RIP = 0x11d04b) (leaR64Effect 0x11d04b 6 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x11d053 (callEffect (fun _ => 0x10a410) 0x11d058) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 88) (.exec 0x11d053 (PushPre 0x11d053 5) (callEffect (fun _ => 0x10a410) 0x11d058) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.const ⟨64, 0x11d058⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ { target := .l11d058, kept := #v[], arity := rfl, guard := some (Fin.last 89) }))))))))))))))))))))))))))))))))))))))

def bytes_l11d003 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0xB8, 0x09, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x4C, 0x89,
    0xEE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00,
    0x00, 0x48, 0x89, 0xC6, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48,
    0x89, 0xEE, 0xF3, 0x48, 0xA5, 0x4C, 0x89, 0xFF, 0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00,
    0xE8, 0xB8, 0xD3, 0xFE, 0xFF]

theorem code_l11d003 : ∀ x ∈ codeRange 0x11d003 bytes_l11d003, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d003 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d058 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d058 (movR32Imm32Effect 0x11d058 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11d058 (fun s => s.RIP = 0x11d058) (movR32Imm32Effect 0x11d058 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d05d (movR64R64Effect 0x11d05d 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 56) (.exec 0x11d05d (fun s => s.RIP = 0x11d05d) (movR64R64Effect 0x11d05d 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x11d060 (movR64R64Effect 0x11d060 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11d060 (fun s => s.RIP = 0x11d060) (movR64R64Effect 0x11d060 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.exec 0x11d063 (RepPre 0x11d063 (RepMovsqPre 0x11d063)) (repMovsqEffect 0x11d063) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11d066 (movR32Imm32Effect 0x11d066 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11d066 (fun s => s.RIP = 0x11d066) (movR32Imm32Effect 0x11d066 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11d06b (leaR64Effect 0x11d06b 0 (.sib 4 none 0 (.d32 0xa30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11d06b (fun s => s.RIP = 0x11d06b) (leaR64Effect 0x11d06b 0 (.sib 4 none 0 (.d32 0xa30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11d073 (movR64R64Effect 0x11d073 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 65) (.exec 0x11d073 (fun s => s.RIP = 0x11d073) (movR64R64Effect 0x11d073 7 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 66) (.out 0x11d076 (movR64R64Effect 0x11d076 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 67) (.exec 0x11d076 (fun s => s.RIP = 0x11d076) (movR64R64Effect 0x11d076 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 68) (.exec 0x11d079 (RepPre 0x11d079 (RepMovsqPre 0x11d079)) (repMovsqEffect 0x11d079) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[66, 64, 60, 22]
    (.letOp (n := 69) (.out 0x11d07c (movR32Imm32Effect 0x11d07c 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x11d07c (fun s => s.RIP = 0x11d07c) (movR32Imm32Effect 0x11d07c 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x11d081 (leaR64Effect 0x11d081 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 72) (.exec 0x11d081 (fun s => s.RIP = 0x11d081) (leaR64Effect 0x11d081 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x11d089 (movR64R64Effect 0x11d089 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[62]
    (.letOp (n := 74) (.exec 0x11d089 (fun s => s.RIP = 0x11d089) (movR64R64Effect 0x11d089 6 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 75) (.exec 0x11d08c (RepPre 0x11d08c (RepMovsqPre 0x11d08c)) (repMovsqEffect 0x11d08c) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[73, 71, 69, 22]
    (.letOp (n := 76) (.out 0x11d08f (movR32Imm32Effect 0x11d08f 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 77) (.exec 0x11d08f (fun s => s.RIP = 0x11d08f) (movR32Imm32Effect 0x11d08f 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x11d094 (movR64R64Effect 0x11d094 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 79) (.exec 0x11d094 (fun s => s.RIP = 0x11d094) (movR64R64Effect 0x11d094 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 80) (.out 0x11d097 (movR64R64Effect 0x11d097 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 81) (.exec 0x11d097 (fun s => s.RIP = 0x11d097) (movR64R64Effect 0x11d097 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 82) (.exec 0x11d09a (RepPre 0x11d09a (RepMovsqPre 0x11d09a)) (repMovsqEffect 0x11d09a) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[80, 78, 76, 22]
    (.letOp (n := 83) (.out 0x11d09d (movR64R64Effect 0x11d09d 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 84) (.exec 0x11d09d (fun s => s.RIP = 0x11d09d) (movR64R64Effect 0x11d09d 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 85) (.out 0x11d0a0 (leaR64Effect 0x11d0a0 6 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 86) (.exec 0x11d0a0 (fun s => s.RIP = 0x11d0a0) (leaR64Effect 0x11d0a0 6 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x11d0a8 (callEffect (fun _ => 0x10a410) 0x11d0ad) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 88) (.exec 0x11d0a8 (PushPre 0x11d0a8 5) (callEffect (fun _ => 0x10a410) 0x11d0ad) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.const ⟨64, 0x11d0ad⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ { target := .l11d0ad, kept := #v[], arity := rfl, guard := some (Fin.last 89) }))))))))))))))))))))))))))))))))))))))

def bytes_l11d058 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0x30, 0x0A, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x4C, 0x89,
    0xEE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00,
    0x00, 0x48, 0x89, 0xC6, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48,
    0x89, 0xEE, 0xF3, 0x48, 0xA5, 0x4C, 0x89, 0xFF, 0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00,
    0xE8, 0x63, 0xD3, 0xFE, 0xFF]

theorem code_l11d058 : ∀ x ∈ codeRange 0x11d058 bytes_l11d058, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d058 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d0ad : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d0ad (movR32Imm32Effect 0x11d0ad 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11d0ad (fun s => s.RIP = 0x11d0ad) (movR32Imm32Effect 0x11d0ad 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d0b2 (movR64R64Effect 0x11d0b2 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 56) (.exec 0x11d0b2 (fun s => s.RIP = 0x11d0b2) (movR64R64Effect 0x11d0b2 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x11d0b5 (movR64R64Effect 0x11d0b5 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11d0b5 (fun s => s.RIP = 0x11d0b5) (movR64R64Effect 0x11d0b5 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.exec 0x11d0b8 (RepPre 0x11d0b8 (RepMovsqPre 0x11d0b8)) (repMovsqEffect 0x11d0b8) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11d0bb (movR32Imm32Effect 0x11d0bb 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11d0bb (fun s => s.RIP = 0x11d0bb) (movR32Imm32Effect 0x11d0bb 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11d0c0 (leaR64Effect 0x11d0c0 0 (.sib 4 none 0 (.d32 0xaa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11d0c0 (fun s => s.RIP = 0x11d0c0) (leaR64Effect 0x11d0c0 0 (.sib 4 none 0 (.d32 0xaa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11d0c8 (movR64R64Effect 0x11d0c8 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 65) (.exec 0x11d0c8 (fun s => s.RIP = 0x11d0c8) (movR64R64Effect 0x11d0c8 7 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 66) (.out 0x11d0cb (movR64R64Effect 0x11d0cb 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 67) (.exec 0x11d0cb (fun s => s.RIP = 0x11d0cb) (movR64R64Effect 0x11d0cb 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 68) (.exec 0x11d0ce (RepPre 0x11d0ce (RepMovsqPre 0x11d0ce)) (repMovsqEffect 0x11d0ce) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[66, 64, 60, 22]
    (.letOp (n := 69) (.out 0x11d0d1 (movR32Imm32Effect 0x11d0d1 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x11d0d1 (fun s => s.RIP = 0x11d0d1) (movR32Imm32Effect 0x11d0d1 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x11d0d6 (leaR64Effect 0x11d0d6 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 72) (.exec 0x11d0d6 (fun s => s.RIP = 0x11d0d6) (leaR64Effect 0x11d0d6 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x11d0de (movR64R64Effect 0x11d0de 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[62]
    (.letOp (n := 74) (.exec 0x11d0de (fun s => s.RIP = 0x11d0de) (movR64R64Effect 0x11d0de 6 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 75) (.exec 0x11d0e1 (RepPre 0x11d0e1 (RepMovsqPre 0x11d0e1)) (repMovsqEffect 0x11d0e1) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[73, 71, 69, 22]
    (.letOp (n := 76) (.out 0x11d0e4 (movR32Imm32Effect 0x11d0e4 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 77) (.exec 0x11d0e4 (fun s => s.RIP = 0x11d0e4) (movR32Imm32Effect 0x11d0e4 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x11d0e9 (movR64R64Effect 0x11d0e9 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 79) (.exec 0x11d0e9 (fun s => s.RIP = 0x11d0e9) (movR64R64Effect 0x11d0e9 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 80) (.out 0x11d0ec (movR64R64Effect 0x11d0ec 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 81) (.exec 0x11d0ec (fun s => s.RIP = 0x11d0ec) (movR64R64Effect 0x11d0ec 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 82) (.exec 0x11d0ef (RepPre 0x11d0ef (RepMovsqPre 0x11d0ef)) (repMovsqEffect 0x11d0ef) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[80, 78, 76, 22]
    (.letOp (n := 83) (.out 0x11d0f2 (movR64R64Effect 0x11d0f2 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 84) (.exec 0x11d0f2 (fun s => s.RIP = 0x11d0f2) (movR64R64Effect 0x11d0f2 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 85) (.out 0x11d0f5 (leaR64Effect 0x11d0f5 6 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 86) (.exec 0x11d0f5 (fun s => s.RIP = 0x11d0f5) (leaR64Effect 0x11d0f5 6 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x11d0fd (callEffect (fun _ => 0x10a410) 0x11d102) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 88) (.exec 0x11d0fd (PushPre 0x11d0fd 5) (callEffect (fun _ => 0x10a410) 0x11d102) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.const ⟨64, 0x11d102⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ { target := .l11d102, kept := #v[], arity := rfl, guard := some (Fin.last 89) }))))))))))))))))))))))))))))))))))))))

def bytes_l11d0ad : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0xA8, 0x0A, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x4C, 0x89,
    0xEE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00,
    0x00, 0x48, 0x89, 0xC6, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48,
    0x89, 0xEE, 0xF3, 0x48, 0xA5, 0x4C, 0x89, 0xFF, 0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00,
    0xE8, 0x0E, 0xD3, 0xFE, 0xFF]

theorem code_l11d0ad : ∀ x ∈ codeRange 0x11d0ad bytes_l11d0ad, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d0ad 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d102 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d102 (movR32Imm32Effect 0x11d102 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11d102 (fun s => s.RIP = 0x11d102) (movR32Imm32Effect 0x11d102 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d107 (movR64R64Effect 0x11d107 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 56) (.exec 0x11d107 (fun s => s.RIP = 0x11d107) (movR64R64Effect 0x11d107 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x11d10a (movR64R64Effect 0x11d10a 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11d10a (fun s => s.RIP = 0x11d10a) (movR64R64Effect 0x11d10a 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.exec 0x11d10d (RepPre 0x11d10d (RepMovsqPre 0x11d10d)) (repMovsqEffect 0x11d10d) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11d110 (movR32Imm32Effect 0x11d110 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11d110 (fun s => s.RIP = 0x11d110) (movR32Imm32Effect 0x11d110 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11d115 (leaR64Effect 0x11d115 0 (.sib 4 none 0 (.d32 0xb20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11d115 (fun s => s.RIP = 0x11d115) (leaR64Effect 0x11d115 0 (.sib 4 none 0 (.d32 0xb20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11d11d (movR64R64Effect 0x11d11d 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 65) (.exec 0x11d11d (fun s => s.RIP = 0x11d11d) (movR64R64Effect 0x11d11d 7 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 66) (.out 0x11d120 (movR64R64Effect 0x11d120 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 67) (.exec 0x11d120 (fun s => s.RIP = 0x11d120) (movR64R64Effect 0x11d120 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 68) (.exec 0x11d123 (RepPre 0x11d123 (RepMovsqPre 0x11d123)) (repMovsqEffect 0x11d123) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[66, 64, 60, 22]
    (.letOp (n := 69) (.out 0x11d126 (movR32Imm32Effect 0x11d126 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x11d126 (fun s => s.RIP = 0x11d126) (movR32Imm32Effect 0x11d126 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x11d12b (leaR64Effect 0x11d12b 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 72) (.exec 0x11d12b (fun s => s.RIP = 0x11d12b) (leaR64Effect 0x11d12b 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x11d133 (movR64R64Effect 0x11d133 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[62]
    (.letOp (n := 74) (.exec 0x11d133 (fun s => s.RIP = 0x11d133) (movR64R64Effect 0x11d133 6 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 75) (.exec 0x11d136 (RepPre 0x11d136 (RepMovsqPre 0x11d136)) (repMovsqEffect 0x11d136) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[73, 71, 69, 22]
    (.letOp (n := 76) (.out 0x11d139 (movR32Imm32Effect 0x11d139 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 77) (.exec 0x11d139 (fun s => s.RIP = 0x11d139) (movR32Imm32Effect 0x11d139 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x11d13e (movR64R64Effect 0x11d13e 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 79) (.exec 0x11d13e (fun s => s.RIP = 0x11d13e) (movR64R64Effect 0x11d13e 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 80) (.out 0x11d141 (movR64R64Effect 0x11d141 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 81) (.exec 0x11d141 (fun s => s.RIP = 0x11d141) (movR64R64Effect 0x11d141 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 82) (.exec 0x11d144 (RepPre 0x11d144 (RepMovsqPre 0x11d144)) (repMovsqEffect 0x11d144) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[80, 78, 76, 22]
    (.letOp (n := 83) (.out 0x11d147 (movR64R64Effect 0x11d147 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 84) (.exec 0x11d147 (fun s => s.RIP = 0x11d147) (movR64R64Effect 0x11d147 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 85) (.out 0x11d14a (leaR64Effect 0x11d14a 6 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 86) (.exec 0x11d14a (fun s => s.RIP = 0x11d14a) (leaR64Effect 0x11d14a 6 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x11d152 (callEffect (fun _ => 0x10a410) 0x11d157) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 88) (.exec 0x11d152 (PushPre 0x11d152 5) (callEffect (fun _ => 0x10a410) 0x11d157) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.const ⟨64, 0x11d157⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ { target := .l11d157, kept := #v[], arity := rfl, guard := some (Fin.last 89) }))))))))))))))))))))))))))))))))))))))

def bytes_l11d102 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0x20, 0x0B, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x4C, 0x89,
    0xEE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00,
    0x00, 0x48, 0x89, 0xC6, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48,
    0x89, 0xEE, 0xF3, 0x48, 0xA5, 0x4C, 0x89, 0xFF, 0x48, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00,
    0xE8, 0xB9, 0xD2, 0xFE, 0xFF]

theorem code_l11d102 : ∀ x ∈ codeRange 0x11d102 bytes_l11d102, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d102 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d157_3 : Block Op Label signature Reg.count 160 :=
  .letOp (n := 160) (.exec 0x11d293 (StorePre 0x11d293 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x358)) s (0x11d293 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d293 2 (.sib 4 none 0 (.d32 0x358))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[158, 4]
    (.letOp (n := 161) (.out 0x11d29b (andR64R64Effect 0x11d29b 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[118, 12]
    (.letOp (n := 162) (.exec 0x11d29b (fun s => s.RIP = 0x11d29b) (andR64R64Effect 0x11d29b 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[118, 12]
    (.letOp (n := 163) (.exec 0x11d29e (StorePre 0x11d29e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x360)) s (0x11d29e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d29e 6 (.sib 4 none 0 (.d32 0x360))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[161, 4]
    (.letOp (n := 164) (.out 0x11d2a6 (andR64R64Effect 0x11d2a6 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[147, 12]
    (.letOp (n := 165) (.exec 0x11d2a6 (fun s => s.RIP = 0x11d2a6) (andR64R64Effect 0x11d2a6 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[147, 12]
    (.letOp (n := 166) (.out 0x11d2a9 (leaR64Effect 0x11d2a9 12 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 167) (.exec 0x11d2a9 (fun s => s.RIP = 0x11d2a9) (leaR64Effect 0x11d2a9 12 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 168) (.exec 0x11d2b1 (StorePre 0x11d2b1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x368)) s (0x11d2b1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d2b1 7 (.sib 4 none 0 (.d32 0x368))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[164, 4]
    (.letOp (n := 169) (.exec 0x11d2b9 (StorePre 0x11d2b9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x370)) s (0x11d2b9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d2b9 8 (.sib 4 none 0 (.d32 0x370))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[153, 4]
    (.letOp (n := 170) (.out 0x11d2c1 (movzxR32M8Effect 0x11d2c1 5 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 171) (.exec 0x11d2c1 (LoadPre 0x11d2c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11d2c1 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11d2c1 5 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 172) (.out 0x11d2c6 (leaR64Effect 0x11d2c6 3 (.sib 4 none 0 (.d32 0xc10))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 173) (.exec 0x11d2c6 (fun s => s.RIP = 0x11d2c6) (leaR64Effect 0x11d2c6 3 (.sib 4 none 0 (.d32 0xc10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 174) (.out 0x11d2ce (movR64R64Effect 0x11d2ce 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[172]
    (.letOp (n := 175) (.exec 0x11d2ce (fun s => s.RIP = 0x11d2ce) (movR64R64Effect 0x11d2ce 7 3) (Reg.operands [.gpr 3] [])) #v[172]
    (.letOp (n := 176) (.out 0x11d2d1 (leaR64Effect 0x11d2d1 6 (.sib 4 none 0 (.d32 0x2b0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 177) (.exec 0x11d2d1 (fun s => s.RIP = 0x11d2d1) (leaR64Effect 0x11d2d1 6 (.sib 4 none 0 (.d32 0x2b0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 178) (.out 0x11d2d9 (movR64R64Effect 0x11d2d9 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 179) (.exec 0x11d2d9 (fun s => s.RIP = 0x11d2d9) (movR64R64Effect 0x11d2d9 2 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 180) (.out 0x11d2dc (callEffect (fun _ => 0x10fcc0) 0x11d2e1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 181) (.exec 0x11d2dc (PushPre 0x11d2dc 5) (callEffect (fun _ => 0x10fcc0) 0x11d2e1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 182) (.const ⟨64, 0x11d2e1⟩) #v[]
    (.terminate (.call ⟨.l10fcc0, RegMap.args [(0, 155), (1, 170), (2, 178), (3, 172), (4, 180), (5, 5), (6, 176), (7, 174), (8, 153), (9, 126), (10, 130), (11, 83), (12, 166), (13, 13), (14, 102), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 183⟩ { target := .l11d2e1, kept := #v[], arity := rfl, guard := some (Fin.last 182) }))))))))))))))))))))))))

def bytes_l11d157_3 : List UInt8 :=
  [0x48, 0x89, 0x94, 0x24, 0x58, 0x03, 0x00, 0x00, 0x4C, 0x21, 0xE6, 0x48, 0x89, 0xB4, 0x24, 0x60,
    0x03, 0x00, 0x00, 0x4C, 0x21, 0xE7, 0x4C, 0x8D, 0xA4, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x89,
    0xBC, 0x24, 0x68, 0x03, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0x70, 0x03, 0x00, 0x00, 0x0F, 0xB6,
    0x4C, 0x24, 0x48, 0x48, 0x8D, 0x9C, 0x24, 0x10, 0x0C, 0x00, 0x00, 0x48, 0x89, 0xDF, 0x48, 0x8D,
    0xB4, 0x24, 0xB0, 0x02, 0x00, 0x00, 0x48, 0x89, 0xEA, 0xE8, 0xDF, 0x29, 0xFF, 0xFF]

theorem code_l11d157_3 : ∀ x ∈ codeRange 0x11d293 bytes_l11d157_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d293 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d157_2 : Block Op Label signature Reg.count 126 :=
  .letOp (n := 126) (.out 0x11d23f (leaR64Effect 0x11d23f 9 (.sib 4 none 0 (.d32 0x300))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 127) (.exec 0x11d23f (fun s => s.RIP = 0x11d23f) (leaR64Effect 0x11d23f 9 (.sib 4 none 0 (.d32 0x300))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 128) (.out 0x11d247 (movR64M64Effect 0x11d247 8 (.base 9 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[126]
    (.letOp (n := 129) (.exec 0x11d247 (LoadPre 0x11d247 (fun s => AddrMode.addr (.base 9 (.d8 0x20)) s (0x11d247 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11d247 8 (.base 9 (.d8 0x20))) (Reg.operands [.gpr 9] [])) #v[126]
    (.letOp (n := 130) (.out 0x11d24b (leaR64Effect 0x11d24b 10 (.sib 4 none 0 (.d32 0x378))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 131) (.exec 0x11d24b (fun s => s.RIP = 0x11d24b) (leaR64Effect 0x11d24b 10 (.sib 4 none 0 (.d32 0x378))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 132) (.exec 0x11d253 (StorePre 0x11d253 4 (fun s => AddrMode.addr (.base 10 (.d8 0x20)) s (0x11d253 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11d253 8 (.base 10 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 10] [])) #v[128, 130]
    (.letOp (n := 133) (.out 0x11d257 (movR64M64Effect 0x11d257 8 (.base 9 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[126]
    (.letOp (n := 134) (.exec 0x11d257 (LoadPre 0x11d257 (fun s => AddrMode.addr (.base 9 (.d8 0x18)) s (0x11d257 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11d257 8 (.base 9 (.d8 0x18))) (Reg.operands [.gpr 9] [])) #v[126]
    (.letOp (n := 135) (.exec 0x11d25b (StorePre 0x11d25b 4 (fun s => AddrMode.addr (.base 10 (.d8 0x18)) s (0x11d25b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11d25b 8 (.base 10 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 10] [])) #v[133, 130]
    (.letOp (n := 136) (.out 0x11d25f (movR64M64Effect 0x11d25f 8 (.base 9 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[126]
    (.letOp (n := 137) (.exec 0x11d25f (LoadPre 0x11d25f (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x11d25f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11d25f 8 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 9] [])) #v[126]
    (.letOp (n := 138) (.exec 0x11d263 (StorePre 0x11d263 4 (fun s => AddrMode.addr (.base 10 (.d8 0x10)) s (0x11d263 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11d263 8 (.base 10 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 10] [])) #v[136, 130]
    (.letOp (n := 139) (.out 0x11d267 (movR64M64Effect 0x11d267 8 (.base 9 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[126]
    (.letOp (n := 140) (.exec 0x11d267 (LoadPre 0x11d267 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x11d267 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11d267 8 (.base 9 (.d8 0x8))) (Reg.operands [.gpr 9] [])) #v[126]
    (.letOp (n := 141) (.exec 0x11d26b (StorePre 0x11d26b 4 (fun s => AddrMode.addr (.base 10 (.d8 0x8)) s (0x11d26b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11d26b 8 (.base 10 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 10] [])) #v[139, 130]
    (.letOp (n := 142) (.out 0x11d26f (movR64M64Effect 0x11d26f 8 (.base 9 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[126]
    (.letOp (n := 143) (.exec 0x11d26f (LoadPre 0x11d26f (fun s => AddrMode.addr (.base 9 .none) s (0x11d26f + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11d26f 8 (.base 9 .none)) (Reg.operands [.gpr 9] [])) #v[126]
    (.letOp (n := 144) (.exec 0x11d272 (StorePre 0x11d272 3 (fun s => AddrMode.addr (.base 10 .none) s (0x11d272 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11d272 8 (.base 10 .none)) (Reg.operands [.gpr 8, .gpr 10] [])) #v[142, 130]
    (.letOp (n := 145) (.out 0x11d275 (andR64R64Effect 0x11d275 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[85, 83]
    (.letOp (n := 146) (.exec 0x11d275 (fun s => s.RIP = 0x11d275) (andR64R64Effect 0x11d275 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[85, 83]
    (.letOp (n := 147) (.out 0x11d278 (addR64R64Effect 0x11d278 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[124, 3]
    (.letOp (n := 148) (.exec 0x11d278 (fun s => s.RIP = 0x11d278) (addR64R64Effect 0x11d278 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[124, 3]
    (.letOp (n := 149) (.out 0x11d27b (movR64R64Effect 0x11d27b 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[147]
    (.letOp (n := 150) (.exec 0x11d27b (fun s => s.RIP = 0x11d27b) (movR64R64Effect 0x11d27b 8 7) (Reg.operands [.gpr 7] [])) #v[147]
    (.letOp (n := 151) (.out 0x11d27e (shrR64Effect 0x11d27e 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[149]
    (.letOp (n := 152) (.exec 0x11d27e (fun s => s.RIP = 0x11d27e) (shrR64Effect 0x11d27e 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[149]
    (.letOp (n := 153) (.out 0x11d282 (addR64R64Effect 0x11d282 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[151, 145]
    (.letOp (n := 154) (.exec 0x11d282 (fun s => s.RIP = 0x11d282) (addR64R64Effect 0x11d282 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[151, 145]
    (.letOp (n := 155) (.out 0x11d285 (andR64R64Effect 0x11d285 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[100, 12]
    (.letOp (n := 156) (.exec 0x11d285 (fun s => s.RIP = 0x11d285) (andR64R64Effect 0x11d285 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[100, 12]
    (.letOp (n := 157) (.exec 0x11d288 (StorePre 0x11d288 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x350)) s (0x11d288 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d288 0 (.sib 4 none 0 (.d32 0x350))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[155, 4]
    (.letOp (n := 158) (.out 0x11d290 (andR64R64Effect 0x11d290 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[110, 12]
    (.letOp (n := 159) (.exec 0x11d290 (fun s => s.RIP = 0x11d290) (andR64R64Effect 0x11d290 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[110, 12]
    (b_l11d157_3))))))))))))))))))))))))))))))))))

def bytes_l11d157_2 : List UInt8 :=
  [0x4C, 0x8D, 0x8C, 0x24, 0x00, 0x03, 0x00, 0x00, 0x4D, 0x8B, 0x41, 0x20, 0x4C, 0x8D, 0x94, 0x24,
    0x78, 0x03, 0x00, 0x00, 0x4D, 0x89, 0x42, 0x20, 0x4D, 0x8B, 0x41, 0x18, 0x4D, 0x89, 0x42, 0x18,
    0x4D, 0x8B, 0x41, 0x10, 0x4D, 0x89, 0x42, 0x10, 0x4D, 0x8B, 0x41, 0x08, 0x4D, 0x89, 0x42, 0x08,
    0x4D, 0x8B, 0x01, 0x4D, 0x89, 0x02, 0x4C, 0x21, 0xD9, 0x48, 0x01, 0xDF, 0x49, 0x89, 0xF8, 0x49,
    0xC1, 0xE8, 0x34, 0x49, 0x01, 0xC8, 0x4C, 0x21, 0xE0, 0x48, 0x89, 0x84, 0x24, 0x50, 0x03, 0x00,
    0x00, 0x4C, 0x21, 0xE2] ++ bytes_l11d157_3

theorem code_l11d157_2 : ∀ x ∈ codeRange 0x11d23f bytes_l11d157_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1d23f 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d157_3

@[cfg_block] def b_l11d157_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.out 0x11d1d5 (movR64R64Effect 0x11d1d5 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[85]
    (.letOp (n := 88) (.exec 0x11d1d5 (fun s => s.RIP = 0x11d1d5) (movR64R64Effect 0x11d1d5 0 1) (Reg.operands [.gpr 1] [])) #v[85]
    (.letOp (n := 89) (.out 0x11d1d8 (shrR64Effect 0x11d1d8 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[87]
    (.letOp (n := 90) (.exec 0x11d1d8 (fun s => s.RIP = 0x11d1d8) (shrR64Effect 0x11d1d8 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.out 0x11d1dc (movR64Imm64Effect 0x11d1dc 6 0x1000003d1) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 92) (.exec 0x11d1dc (fun s => s.RIP = 0x11d1dc) (movR64Imm64Effect 0x11d1dc 6 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 93) (.out 0x11d1e6 (imulR64R64Effect 0x11d1e6 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[89, 91]
    (.letOp (n := 94) (.exec 0x11d1e6 (fun s => s.RIP = 0x11d1e6) (imulR64R64Effect 0x11d1e6 4 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[89, 91]
    (.letOp (n := 95) (.out 0x11d1ea (subR64M64Effect 0x11d1ea 0 (.sib 4 none 0 (.d32 0x2d8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[93, 4]
    (.letOp (n := 96) (.exec 0x11d1ea (LoadPre 0x11d1ea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2d8)) s (0x11d1ea + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11d1ea 0 (.sib 4 none 0 (.d32 0x2d8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[93, 4]
    (.letOp (n := 97) (.exec 0x11d1f2 (StorePre 0x11d1f2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x328)) s (0x11d1f2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d1f2 2 (.sib 4 none 0 (.d32 0x328))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 98) (.out 0x11d1fa (movR64Imm64Effect 0x11d1fa 2 0x3ffffbfffff0bc) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 99) (.exec 0x11d1fa (fun s => s.RIP = 0x11d1fa) (movR64Imm64Effect 0x11d1fa 2 0x3ffffbfffff0bc) (Reg.operands [] [])) #v[]
    (.letOp (n := 100) (.out 0x11d204 (addR64R64Effect 0x11d204 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[95, 98]
    (.letOp (n := 101) (.exec 0x11d204 (fun s => s.RIP = 0x11d204) (addR64R64Effect 0x11d204 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[95, 98]
    (.letOp (n := 102) (.out 0x11d207 (movR64M64Effect 0x11d207 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 103) (.exec 0x11d207 (LoadPre 0x11d207 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11d207 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11d207 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 104) (.out 0x11d20c (movR64R64Effect 0x11d20c 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[100]
    (.letOp (n := 105) (.exec 0x11d20c (fun s => s.RIP = 0x11d20c) (movR64R64Effect 0x11d20c 2 0) (Reg.operands [.gpr 0] [])) #v[100]
    (.letOp (n := 106) (.out 0x11d20f (shrR64Effect 0x11d20f 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[104]
    (.letOp (n := 107) (.exec 0x11d20f (fun s => s.RIP = 0x11d20f) (shrR64Effect 0x11d20f 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[104]
    (.letOp (n := 108) (.out 0x11d213 (subR64M64Effect 0x11d213 2 (.sib 4 none 0 (.d32 0x2e0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[106, 4]
    (.letOp (n := 109) (.exec 0x11d213 (LoadPre 0x11d213 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2e0)) s (0x11d213 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11d213 2 (.sib 4 none 0 (.d32 0x2e0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[106, 4]
    (.letOp (n := 110) (.out 0x11d21b (addR64R64Effect 0x11d21b 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[108, 3]
    (.letOp (n := 111) (.exec 0x11d21b (fun s => s.RIP = 0x11d21b) (addR64R64Effect 0x11d21b 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[108, 3]
    (.letOp (n := 112) (.out 0x11d21e (movR64R64Effect 0x11d21e 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[110]
    (.letOp (n := 113) (.exec 0x11d21e (fun s => s.RIP = 0x11d21e) (movR64R64Effect 0x11d21e 6 2) (Reg.operands [.gpr 2] [])) #v[110]
    (.letOp (n := 114) (.out 0x11d221 (shrR64Effect 0x11d221 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[112]
    (.letOp (n := 115) (.exec 0x11d221 (fun s => s.RIP = 0x11d221) (shrR64Effect 0x11d221 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[112]
    (.letOp (n := 116) (.out 0x11d225 (subR64M64Effect 0x11d225 6 (.sib 4 none 0 (.d32 0x2e8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[114, 4]
    (.letOp (n := 117) (.exec 0x11d225 (LoadPre 0x11d225 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2e8)) s (0x11d225 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11d225 6 (.sib 4 none 0 (.d32 0x2e8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[114, 4]
    (.letOp (n := 118) (.out 0x11d22d (addR64R64Effect 0x11d22d 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[116, 3]
    (.letOp (n := 119) (.exec 0x11d22d (fun s => s.RIP = 0x11d22d) (addR64R64Effect 0x11d22d 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[116, 3]
    (.letOp (n := 120) (.out 0x11d230 (movR64R64Effect 0x11d230 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[118]
    (.letOp (n := 121) (.exec 0x11d230 (fun s => s.RIP = 0x11d230) (movR64R64Effect 0x11d230 7 6) (Reg.operands [.gpr 6] [])) #v[118]
    (.letOp (n := 122) (.out 0x11d233 (shrR64Effect 0x11d233 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[120]
    (.letOp (n := 123) (.exec 0x11d233 (fun s => s.RIP = 0x11d233) (shrR64Effect 0x11d233 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[120]
    (.letOp (n := 124) (.out 0x11d237 (subR64M64Effect 0x11d237 7 (.sib 4 none 0 (.d32 0x2f0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[122, 4]
    (.letOp (n := 125) (.exec 0x11d237 (LoadPre 0x11d237 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2f0)) s (0x11d237 + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11d237 7 (.sib 4 none 0 (.d32 0x2f0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[122, 4]
    (b_l11d157_2)))))))))))))))))))))))))))))))))))))))

def bytes_l11d157_1 : List UInt8 :=
  [0x48, 0x89, 0xC8, 0x48, 0xC1, 0xE8, 0x30, 0x48, 0xBE, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00,
    0x00, 0x48, 0x0F, 0xAF, 0xC6, 0x48, 0x2B, 0x84, 0x24, 0xD8, 0x02, 0x00, 0x00, 0x48, 0x89, 0x94,
    0x24, 0x28, 0x03, 0x00, 0x00, 0x48, 0xBA, 0xBC, 0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00, 0x48,
    0x01, 0xD0, 0x4C, 0x8B, 0x74, 0x24, 0x08, 0x48, 0x89, 0xC2, 0x48, 0xC1, 0xEA, 0x34, 0x48, 0x2B,
    0x94, 0x24, 0xE0, 0x02, 0x00, 0x00, 0x48, 0x01, 0xDA, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xEE, 0x34,
    0x48, 0x2B, 0xB4, 0x24, 0xE8, 0x02, 0x00, 0x00, 0x48, 0x01, 0xDE, 0x48, 0x89, 0xF7, 0x48, 0xC1,
    0xEF, 0x34, 0x48, 0x2B, 0xBC, 0x24, 0xF0, 0x02, 0x00, 0x00] ++ bytes_l11d157_2

theorem code_l11d157_1 : ∀ x ∈ codeRange 0x11d1d5 bytes_l11d157_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1d1d5 106 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d157_2

@[cfg_block] def b_l11d157 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d157 (movR32Imm32Effect 0x11d157 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11d157 (fun s => s.RIP = 0x11d157) (movR32Imm32Effect 0x11d157 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d15c (movR64R64Effect 0x11d15c 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 56) (.exec 0x11d15c (fun s => s.RIP = 0x11d15c) (movR64R64Effect 0x11d15c 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x11d15f (movR64R64Effect 0x11d15f 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11d15f (fun s => s.RIP = 0x11d15f) (movR64R64Effect 0x11d15f 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.exec 0x11d162 (RepPre 0x11d162 (RepMovsqPre 0x11d162)) (repMovsqEffect 0x11d162) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11d165 (movR32Imm32Effect 0x11d165 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11d165 (fun s => s.RIP = 0x11d165) (movR32Imm32Effect 0x11d165 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11d16a (leaR64Effect 0x11d16a 7 (.sib 4 none 0 (.d32 0xb98))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x11d16a (fun s => s.RIP = 0x11d16a) (leaR64Effect 0x11d16a 7 (.sib 4 none 0 (.d32 0xb98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11d172 (movR64R64Effect 0x11d172 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 65) (.exec 0x11d172 (fun s => s.RIP = 0x11d172) (movR64R64Effect 0x11d172 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 66) (.exec 0x11d175 (RepPre 0x11d175 (RepMovsqPre 0x11d175)) (repMovsqEffect 0x11d175) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[64, 62, 60, 22]
    (.letOp (n := 67) (.out 0x11d178 (movR64M64Effect 0x11d178 0 (.sib 4 none 0 (.d32 0x2d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 68) (.exec 0x11d178 (LoadPre 0x11d178 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2d0)) s (0x11d178 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d178 0 (.sib 4 none 0 (.d32 0x2d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x11d180 (StorePre 0x11d180 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x348)) s (0x11d180 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d180 0 (.sib 4 none 0 (.d32 0x348))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x11d188 (movR64M64Effect 0x11d188 0 (.sib 4 none 0 (.d32 0x2c8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 71) (.exec 0x11d188 (LoadPre 0x11d188 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2c8)) s (0x11d188 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d188 0 (.sib 4 none 0 (.d32 0x2c8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x11d190 (StorePre 0x11d190 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x340)) s (0x11d190 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d190 0 (.sib 4 none 0 (.d32 0x340))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x11d198 (movR64M64Effect 0x11d198 0 (.sib 4 none 0 (.d32 0x2c0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 74) (.exec 0x11d198 (LoadPre 0x11d198 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2c0)) s (0x11d198 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d198 0 (.sib 4 none 0 (.d32 0x2c0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x11d1a0 (StorePre 0x11d1a0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x338)) s (0x11d1a0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d1a0 0 (.sib 4 none 0 (.d32 0x338))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x11d1a8 (movR64M64Effect 0x11d1a8 2 (.sib 4 none 0 (.d32 0x2b0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 77) (.exec 0x11d1a8 (LoadPre 0x11d1a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2b0)) s (0x11d1a8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d1a8 2 (.sib 4 none 0 (.d32 0x2b0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x11d1b0 (movR64M64Effect 0x11d1b0 0 (.sib 4 none 0 (.d32 0x2b8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 79) (.exec 0x11d1b0 (LoadPre 0x11d1b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2b8)) s (0x11d1b0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d1b0 0 (.sib 4 none 0 (.d32 0x2b8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.exec 0x11d1b8 (StorePre 0x11d1b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x330)) s (0x11d1b8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d1b8 0 (.sib 4 none 0 (.d32 0x330))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 4]
    (.letOp (n := 81) (.out 0x11d1c0 (movR64Imm64Effect 0x11d1c0 1 0x3fffffffffffc) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 82) (.exec 0x11d1c0 (fun s => s.RIP = 0x11d1c0) (movR64Imm64Effect 0x11d1c0 1 0x3fffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 83) (.out 0x11d1ca (movR64R64Effect 0x11d1ca 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 14] []) (.reg (.gpr 11))) #v[14]
    (.letOp (n := 84) (.exec 0x11d1ca (fun s => s.RIP = 0x11d1ca) (movR64R64Effect 0x11d1ca 11 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 85) (.out 0x11d1cd (subR64M64Effect 0x11d1cd 1 (.sib 4 none 0 (.d32 0x2f8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[81, 4]
    (.letOp (n := 86) (.exec 0x11d1cd (LoadPre 0x11d1cd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x2f8)) s (0x11d1cd + BitVec.ofNat 64 8)) 8) (subR64M64Effect 0x11d1cd 1 (.sib 4 none 0 (.d32 0x2f8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[81, 4]
    (b_l11d157_1))))))))))))))))))))))))))))))))))

def bytes_l11d157 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x98, 0x0B, 0x00, 0x00, 0x4C, 0x89, 0xEE, 0xF3, 0x48,
    0xA5, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x02, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x48, 0x03, 0x00,
    0x00, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x02, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x40, 0x03, 0x00,
    0x00, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x02, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x38, 0x03, 0x00,
    0x00, 0x48, 0x8B, 0x94, 0x24, 0xB0, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xB8, 0x02, 0x00,
    0x00, 0x48, 0x89, 0x84, 0x24, 0x30, 0x03, 0x00, 0x00, 0x48, 0xB9, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x03, 0x00, 0x4D, 0x89, 0xF3, 0x48, 0x2B, 0x8C, 0x24, 0xF8, 0x02, 0x00, 0x00] ++ bytes_l11d157_1

theorem code_l11d157 : ∀ x ∈ codeRange 0x11d157 bytes_l11d157, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1d157 126 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d157_1

@[cfg_block] def b_l11d2e1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d2e1 (movR32Imm32Effect 0x11d2e1 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11d2e1 (fun s => s.RIP = 0x11d2e1) (movR32Imm32Effect 0x11d2e1 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d2e6 (leaR64Effect 0x11d2e6 13 (.sib 4 none 0 (.d32 0x490))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 56) (.exec 0x11d2e6 (fun s => s.RIP = 0x11d2e6) (leaR64Effect 0x11d2e6 13 (.sib 4 none 0 (.d32 0x490))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11d2ee (movR64R64Effect 0x11d2ee 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x11d2ee (fun s => s.RIP = 0x11d2ee) (movR64R64Effect 0x11d2ee 7 13) (Reg.operands [.gpr 13] [])) #v[55]
    (.letOp (n := 59) (.out 0x11d2f1 (movR64R64Effect 0x11d2f1 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 60) (.exec 0x11d2f1 (fun s => s.RIP = 0x11d2f1) (movR64R64Effect 0x11d2f1 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 61) (.exec 0x11d2f4 (RepPre 0x11d2f4 (RepMovsqPre 0x11d2f4)) (repMovsqEffect 0x11d2f4) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[59, 57, 53, 22]
    (.letOp (n := 62) (.out 0x11d2f7 (movR32Imm32Effect 0x11d2f7 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 63) (.exec 0x11d2f7 (fun s => s.RIP = 0x11d2f7) (movR32Imm32Effect 0x11d2f7 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x11d2fc (movR64R64Effect 0x11d2fc 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 65) (.exec 0x11d2fc (fun s => s.RIP = 0x11d2fc) (movR64R64Effect 0x11d2fc 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 66) (.out 0x11d2ff (movR64R64Effect 0x11d2ff 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 67) (.exec 0x11d2ff (fun s => s.RIP = 0x11d2ff) (movR64R64Effect 0x11d2ff 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 68) (.exec 0x11d302 (RepPre 0x11d302 (RepMovsqPre 0x11d302)) (repMovsqEffect 0x11d302) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[66, 64, 62, 22]
    (.letOp (n := 69) (.out 0x11d305 (movR32Imm32Effect 0x11d305 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x11d305 (fun s => s.RIP = 0x11d305) (movR32Imm32Effect 0x11d305 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x11d30a (movR64R64Effect 0x11d30a 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 72) (.exec 0x11d30a (fun s => s.RIP = 0x11d30a) (movR64R64Effect 0x11d30a 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 73) (.out 0x11d30d (movR64R64Effect 0x11d30d 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 74) (.exec 0x11d30d (fun s => s.RIP = 0x11d30d) (movR64R64Effect 0x11d30d 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 75) (.exec 0x11d310 (RepPre 0x11d310 (RepMovsqPre 0x11d310)) (repMovsqEffect 0x11d310) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[73, 71, 69, 22]
    (.letOp (n := 76) (.out 0x11d313 (movR64R64Effect 0x11d313 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 77) (.exec 0x11d313 (fun s => s.RIP = 0x11d313) (movR64R64Effect 0x11d313 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 78) (.out 0x11d316 (movR64R64Effect 0x11d316 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 79) (.exec 0x11d316 (fun s => s.RIP = 0x11d316) (movR64R64Effect 0x11d316 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 80) (.out 0x11d319 (callEffect (fun _ => 0x10a410) 0x11d31e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 81) (.exec 0x11d319 (PushPre 0x11d319 5) (callEffect (fun _ => 0x10a410) 0x11d31e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.const ⟨64, 0x11d31e⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 80), (5, 5), (6, 78), (7, 76), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩ { target := .l11d31e, kept := #v[], arity := rfl, guard := some (Fin.last 82) })))))))))))))))))))))))))))))))

def bytes_l11d2e1 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0xAC, 0x24, 0x90, 0x04, 0x00, 0x00, 0x4C, 0x89, 0xEF,
    0x48, 0x89, 0xDE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0x48, 0x89,
    0xDE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xDE, 0xF3,
    0x48, 0xA5, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xE6, 0xE8, 0xF2, 0xD0, 0xFE, 0xFF]

theorem code_l11d2e1 : ∀ x ∈ codeRange 0x11d2e1 bytes_l11d2e1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d2e1 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d31e_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x11d36c (callEffect (fun _ => 0x10a410) 0x11d371) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 90) (.exec 0x11d36c (PushPre 0x11d36c 5) (callEffect (fun _ => 0x10a410) 0x11d371) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.const ⟨64, 0x11d371⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(0, 64), (3, 3), (4, 89), (5, 55), (6, 87), (7, 85), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 92⟩ { target := .l11d371, kept := #v[], arity := rfl, guard := some (Fin.last 91) }))))

def bytes_l11d31e_1 : List UInt8 :=
  [0xE8, 0x9F, 0xD0, 0xFE, 0xFF]

theorem code_l11d31e_1 : ∀ x ∈ codeRange 0x11d36c bytes_l11d31e_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d36c 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d31e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d31e (movR32Imm32Effect 0x11d31e 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11d31e (fun s => s.RIP = 0x11d31e) (movR32Imm32Effect 0x11d31e 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d323 (leaR64Effect 0x11d323 5 (.sib 4 none 0 (.d32 0x418))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 56) (.exec 0x11d323 (fun s => s.RIP = 0x11d323) (leaR64Effect 0x11d323 5 (.sib 4 none 0 (.d32 0x418))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11d32b (movR64R64Effect 0x11d32b 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x11d32b (fun s => s.RIP = 0x11d32b) (movR64R64Effect 0x11d32b 7 5) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 59) (.out 0x11d32e (movR64R64Effect 0x11d32e 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 60) (.exec 0x11d32e (fun s => s.RIP = 0x11d32e) (movR64R64Effect 0x11d32e 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.exec 0x11d331 (RepPre 0x11d331 (RepMovsqPre 0x11d331)) (repMovsqEffect 0x11d331) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[59, 57, 53, 22]
    (.letOp (n := 62) (.out 0x11d334 (movR32Imm32Effect 0x11d334 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 63) (.exec 0x11d334 (fun s => s.RIP = 0x11d334) (movR32Imm32Effect 0x11d334 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x11d339 (leaR64Effect 0x11d339 0 (.sib 4 none 0 (.d32 0x508))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 65) (.exec 0x11d339 (fun s => s.RIP = 0x11d339) (leaR64Effect 0x11d339 0 (.sib 4 none 0 (.d32 0x508))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x11d341 (movR64R64Effect 0x11d341 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[64]
    (.letOp (n := 67) (.exec 0x11d341 (fun s => s.RIP = 0x11d341) (movR64R64Effect 0x11d341 7 0) (Reg.operands [.gpr 0] [])) #v[64]
    (.letOp (n := 68) (.out 0x11d344 (movR64R64Effect 0x11d344 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 69) (.exec 0x11d344 (fun s => s.RIP = 0x11d344) (movR64R64Effect 0x11d344 6 5) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 70) (.exec 0x11d347 (RepPre 0x11d347 (RepMovsqPre 0x11d347)) (repMovsqEffect 0x11d347) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[68, 66, 62, 22]
    (.letOp (n := 71) (.out 0x11d34a (movR32Imm32Effect 0x11d34a 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 72) (.exec 0x11d34a (fun s => s.RIP = 0x11d34a) (movR32Imm32Effect 0x11d34a 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x11d34f (movR64R64Effect 0x11d34f 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 74) (.exec 0x11d34f (fun s => s.RIP = 0x11d34f) (movR64R64Effect 0x11d34f 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 75) (.out 0x11d352 (movR64R64Effect 0x11d352 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[64]
    (.letOp (n := 76) (.exec 0x11d352 (fun s => s.RIP = 0x11d352) (movR64R64Effect 0x11d352 6 0) (Reg.operands [.gpr 0] [])) #v[64]
    (.letOp (n := 77) (.exec 0x11d355 (RepPre 0x11d355 (RepMovsqPre 0x11d355)) (repMovsqEffect 0x11d355) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[75, 73, 71, 22]
    (.letOp (n := 78) (.out 0x11d358 (movR32Imm32Effect 0x11d358 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 79) (.exec 0x11d358 (fun s => s.RIP = 0x11d358) (movR32Imm32Effect 0x11d358 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 80) (.out 0x11d35d (movR64R64Effect 0x11d35d 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 81) (.exec 0x11d35d (fun s => s.RIP = 0x11d35d) (movR64R64Effect 0x11d35d 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 82) (.out 0x11d360 (movR64R64Effect 0x11d360 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 83) (.exec 0x11d360 (fun s => s.RIP = 0x11d360) (movR64R64Effect 0x11d360 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 84) (.exec 0x11d363 (RepPre 0x11d363 (RepMovsqPre 0x11d363)) (repMovsqEffect 0x11d363) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[82, 80, 78, 22]
    (.letOp (n := 85) (.out 0x11d366 (movR64R64Effect 0x11d366 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 86) (.exec 0x11d366 (fun s => s.RIP = 0x11d366) (movR64R64Effect 0x11d366 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 87) (.out 0x11d369 (movR64R64Effect 0x11d369 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 88) (.exec 0x11d369 (fun s => s.RIP = 0x11d369) (movR64R64Effect 0x11d369 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (b_l11d31e_1))))))))))))))))))))))))))))))))))))

def bytes_l11d31e : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xAC, 0x24, 0x18, 0x04, 0x00, 0x00, 0x48, 0x89, 0xEF,
    0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0x08,
    0x05, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x48, 0x89, 0xEE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00,
    0x00, 0x4C, 0x89, 0xE7, 0x48, 0x89, 0xC6, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C,
    0x89, 0xFF, 0x48, 0x89, 0xDE, 0xF3, 0x48, 0xA5, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xE6] ++ bytes_l11d31e_1

theorem code_l11d31e : ∀ x ∈ codeRange 0x11d31e bytes_l11d31e, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1d31e 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d31e_1

@[cfg_block] def b_l11d371 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d371 (movR32Imm32Effect 0x11d371 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11d371 (fun s => s.RIP = 0x11d371) (movR32Imm32Effect 0x11d371 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d376 (movR64R64Effect 0x11d376 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 56) (.exec 0x11d376 (fun s => s.RIP = 0x11d376) (movR64R64Effect 0x11d376 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x11d379 (movR64R64Effect 0x11d379 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11d379 (fun s => s.RIP = 0x11d379) (movR64R64Effect 0x11d379 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.exec 0x11d37c (RepPre 0x11d37c (RepMovsqPre 0x11d37c)) (repMovsqEffect 0x11d37c) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11d37f (movR32Imm32Effect 0x11d37f 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11d37f (fun s => s.RIP = 0x11d37f) (movR32Imm32Effect 0x11d37f 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11d384 (leaR64Effect 0x11d384 0 (.sib 4 none 0 (.d32 0x580))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11d384 (fun s => s.RIP = 0x11d384) (leaR64Effect 0x11d384 0 (.sib 4 none 0 (.d32 0x580))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11d38c (movR64R64Effect 0x11d38c 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 65) (.exec 0x11d38c (fun s => s.RIP = 0x11d38c) (movR64R64Effect 0x11d38c 7 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 66) (.out 0x11d38f (movR64R64Effect 0x11d38f 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 67) (.exec 0x11d38f (fun s => s.RIP = 0x11d38f) (movR64R64Effect 0x11d38f 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 68) (.exec 0x11d392 (RepPre 0x11d392 (RepMovsqPre 0x11d392)) (repMovsqEffect 0x11d392) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[66, 64, 60, 22]
    (.letOp (n := 69) (.out 0x11d395 (movR32Imm32Effect 0x11d395 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x11d395 (fun s => s.RIP = 0x11d395) (movR32Imm32Effect 0x11d395 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x11d39a (movR64R64Effect 0x11d39a 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 72) (.exec 0x11d39a (fun s => s.RIP = 0x11d39a) (movR64R64Effect 0x11d39a 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 73) (.out 0x11d39d (movR64R64Effect 0x11d39d 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[62]
    (.letOp (n := 74) (.exec 0x11d39d (fun s => s.RIP = 0x11d39d) (movR64R64Effect 0x11d39d 6 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 75) (.exec 0x11d3a0 (RepPre 0x11d3a0 (RepMovsqPre 0x11d3a0)) (repMovsqEffect 0x11d3a0) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[73, 71, 69, 22]
    (.letOp (n := 76) (.out 0x11d3a3 (movR32Imm32Effect 0x11d3a3 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 77) (.exec 0x11d3a3 (fun s => s.RIP = 0x11d3a3) (movR32Imm32Effect 0x11d3a3 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x11d3a8 (movR64R64Effect 0x11d3a8 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 79) (.exec 0x11d3a8 (fun s => s.RIP = 0x11d3a8) (movR64R64Effect 0x11d3a8 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 80) (.out 0x11d3ab (movR64R64Effect 0x11d3ab 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 81) (.exec 0x11d3ab (fun s => s.RIP = 0x11d3ab) (movR64R64Effect 0x11d3ab 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 82) (.exec 0x11d3ae (RepPre 0x11d3ae (RepMovsqPre 0x11d3ae)) (repMovsqEffect 0x11d3ae) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[80, 78, 76, 22]
    (.letOp (n := 83) (.out 0x11d3b1 (movR64R64Effect 0x11d3b1 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 84) (.exec 0x11d3b1 (fun s => s.RIP = 0x11d3b1) (movR64R64Effect 0x11d3b1 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 85) (.out 0x11d3b4 (movR64R64Effect 0x11d3b4 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 86) (.exec 0x11d3b4 (fun s => s.RIP = 0x11d3b4) (movR64R64Effect 0x11d3b4 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 87) (.out 0x11d3b7 (callEffect (fun _ => 0x10a410) 0x11d3bc) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 88) (.exec 0x11d3b7 (PushPre 0x11d3b7 5) (callEffect (fun _ => 0x10a410) 0x11d3bc) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.const ⟨64, 0x11d3bc⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ { target := .l11d3bc, kept := #v[], arity := rfl, guard := some (Fin.last 89) }))))))))))))))))))))))))))))))))))))))

def bytes_l11d371 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0x80, 0x05, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x48, 0x89,
    0xEE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0x48, 0x89, 0xC6, 0xF3,
    0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xDE, 0xF3, 0x48, 0xA5,
    0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xE6, 0xE8, 0x54, 0xD0, 0xFE, 0xFF]

theorem code_l11d371 : ∀ x ∈ codeRange 0x11d371 bytes_l11d371, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d371 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d3bc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d3bc (movR32Imm32Effect 0x11d3bc 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11d3bc (fun s => s.RIP = 0x11d3bc) (movR32Imm32Effect 0x11d3bc 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d3c1 (movR64R64Effect 0x11d3c1 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 56) (.exec 0x11d3c1 (fun s => s.RIP = 0x11d3c1) (movR64R64Effect 0x11d3c1 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x11d3c4 (movR64R64Effect 0x11d3c4 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11d3c4 (fun s => s.RIP = 0x11d3c4) (movR64R64Effect 0x11d3c4 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.exec 0x11d3c7 (RepPre 0x11d3c7 (RepMovsqPre 0x11d3c7)) (repMovsqEffect 0x11d3c7) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11d3ca (movR32Imm32Effect 0x11d3ca 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11d3ca (fun s => s.RIP = 0x11d3ca) (movR32Imm32Effect 0x11d3ca 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11d3cf (leaR64Effect 0x11d3cf 0 (.sib 4 none 0 (.d32 0x5f8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11d3cf (fun s => s.RIP = 0x11d3cf) (leaR64Effect 0x11d3cf 0 (.sib 4 none 0 (.d32 0x5f8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11d3d7 (movR64R64Effect 0x11d3d7 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 65) (.exec 0x11d3d7 (fun s => s.RIP = 0x11d3d7) (movR64R64Effect 0x11d3d7 7 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 66) (.out 0x11d3da (movR64R64Effect 0x11d3da 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 67) (.exec 0x11d3da (fun s => s.RIP = 0x11d3da) (movR64R64Effect 0x11d3da 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 68) (.exec 0x11d3dd (RepPre 0x11d3dd (RepMovsqPre 0x11d3dd)) (repMovsqEffect 0x11d3dd) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[66, 64, 60, 22]
    (.letOp (n := 69) (.out 0x11d3e0 (movR32Imm32Effect 0x11d3e0 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x11d3e0 (fun s => s.RIP = 0x11d3e0) (movR32Imm32Effect 0x11d3e0 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x11d3e5 (movR64R64Effect 0x11d3e5 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 72) (.exec 0x11d3e5 (fun s => s.RIP = 0x11d3e5) (movR64R64Effect 0x11d3e5 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 73) (.out 0x11d3e8 (movR64R64Effect 0x11d3e8 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[62]
    (.letOp (n := 74) (.exec 0x11d3e8 (fun s => s.RIP = 0x11d3e8) (movR64R64Effect 0x11d3e8 6 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 75) (.exec 0x11d3eb (RepPre 0x11d3eb (RepMovsqPre 0x11d3eb)) (repMovsqEffect 0x11d3eb) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[73, 71, 69, 22]
    (.letOp (n := 76) (.out 0x11d3ee (movR32Imm32Effect 0x11d3ee 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 77) (.exec 0x11d3ee (fun s => s.RIP = 0x11d3ee) (movR32Imm32Effect 0x11d3ee 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x11d3f3 (movR64R64Effect 0x11d3f3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 79) (.exec 0x11d3f3 (fun s => s.RIP = 0x11d3f3) (movR64R64Effect 0x11d3f3 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 80) (.out 0x11d3f6 (movR64R64Effect 0x11d3f6 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 81) (.exec 0x11d3f6 (fun s => s.RIP = 0x11d3f6) (movR64R64Effect 0x11d3f6 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 82) (.exec 0x11d3f9 (RepPre 0x11d3f9 (RepMovsqPre 0x11d3f9)) (repMovsqEffect 0x11d3f9) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[80, 78, 76, 22]
    (.letOp (n := 83) (.out 0x11d3fc (movR64R64Effect 0x11d3fc 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 84) (.exec 0x11d3fc (fun s => s.RIP = 0x11d3fc) (movR64R64Effect 0x11d3fc 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 85) (.out 0x11d3ff (movR64R64Effect 0x11d3ff 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 86) (.exec 0x11d3ff (fun s => s.RIP = 0x11d3ff) (movR64R64Effect 0x11d3ff 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 87) (.out 0x11d402 (callEffect (fun _ => 0x10a410) 0x11d407) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 88) (.exec 0x11d402 (PushPre 0x11d402 5) (callEffect (fun _ => 0x10a410) 0x11d407) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.const ⟨64, 0x11d407⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ { target := .l11d407, kept := #v[], arity := rfl, guard := some (Fin.last 89) }))))))))))))))))))))))))))))))))))))))

def bytes_l11d3bc : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0xF8, 0x05, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x48, 0x89,
    0xEE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0x48, 0x89, 0xC6, 0xF3,
    0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xDE, 0xF3, 0x48, 0xA5,
    0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xE6, 0xE8, 0x09, 0xD0, 0xFE, 0xFF]

theorem code_l11d3bc : ∀ x ∈ codeRange 0x11d3bc bytes_l11d3bc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d3bc 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d407 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d407 (movR32Imm32Effect 0x11d407 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11d407 (fun s => s.RIP = 0x11d407) (movR32Imm32Effect 0x11d407 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d40c (movR64R64Effect 0x11d40c 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 56) (.exec 0x11d40c (fun s => s.RIP = 0x11d40c) (movR64R64Effect 0x11d40c 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x11d40f (movR64R64Effect 0x11d40f 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11d40f (fun s => s.RIP = 0x11d40f) (movR64R64Effect 0x11d40f 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.exec 0x11d412 (RepPre 0x11d412 (RepMovsqPre 0x11d412)) (repMovsqEffect 0x11d412) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11d415 (movR32Imm32Effect 0x11d415 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11d415 (fun s => s.RIP = 0x11d415) (movR32Imm32Effect 0x11d415 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11d41a (leaR64Effect 0x11d41a 0 (.sib 4 none 0 (.d32 0x670))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11d41a (fun s => s.RIP = 0x11d41a) (leaR64Effect 0x11d41a 0 (.sib 4 none 0 (.d32 0x670))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11d422 (movR64R64Effect 0x11d422 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 65) (.exec 0x11d422 (fun s => s.RIP = 0x11d422) (movR64R64Effect 0x11d422 7 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 66) (.out 0x11d425 (movR64R64Effect 0x11d425 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 67) (.exec 0x11d425 (fun s => s.RIP = 0x11d425) (movR64R64Effect 0x11d425 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 68) (.exec 0x11d428 (RepPre 0x11d428 (RepMovsqPre 0x11d428)) (repMovsqEffect 0x11d428) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[66, 64, 60, 22]
    (.letOp (n := 69) (.out 0x11d42b (movR32Imm32Effect 0x11d42b 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x11d42b (fun s => s.RIP = 0x11d42b) (movR32Imm32Effect 0x11d42b 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x11d430 (movR64R64Effect 0x11d430 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 72) (.exec 0x11d430 (fun s => s.RIP = 0x11d430) (movR64R64Effect 0x11d430 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 73) (.out 0x11d433 (movR64R64Effect 0x11d433 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[62]
    (.letOp (n := 74) (.exec 0x11d433 (fun s => s.RIP = 0x11d433) (movR64R64Effect 0x11d433 6 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 75) (.exec 0x11d436 (RepPre 0x11d436 (RepMovsqPre 0x11d436)) (repMovsqEffect 0x11d436) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[73, 71, 69, 22]
    (.letOp (n := 76) (.out 0x11d439 (movR32Imm32Effect 0x11d439 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 77) (.exec 0x11d439 (fun s => s.RIP = 0x11d439) (movR32Imm32Effect 0x11d439 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x11d43e (movR64R64Effect 0x11d43e 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 79) (.exec 0x11d43e (fun s => s.RIP = 0x11d43e) (movR64R64Effect 0x11d43e 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 80) (.out 0x11d441 (movR64R64Effect 0x11d441 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 81) (.exec 0x11d441 (fun s => s.RIP = 0x11d441) (movR64R64Effect 0x11d441 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 82) (.exec 0x11d444 (RepPre 0x11d444 (RepMovsqPre 0x11d444)) (repMovsqEffect 0x11d444) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[80, 78, 76, 22]
    (.letOp (n := 83) (.out 0x11d447 (movR64R64Effect 0x11d447 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 84) (.exec 0x11d447 (fun s => s.RIP = 0x11d447) (movR64R64Effect 0x11d447 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 85) (.out 0x11d44a (movR64R64Effect 0x11d44a 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 86) (.exec 0x11d44a (fun s => s.RIP = 0x11d44a) (movR64R64Effect 0x11d44a 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 87) (.out 0x11d44d (callEffect (fun _ => 0x10a410) 0x11d452) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 88) (.exec 0x11d44d (PushPre 0x11d44d 5) (callEffect (fun _ => 0x10a410) 0x11d452) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.const ⟨64, 0x11d452⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ { target := .l11d452, kept := #v[], arity := rfl, guard := some (Fin.last 89) }))))))))))))))))))))))))))))))))))))))

def bytes_l11d407 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0x70, 0x06, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x48, 0x89,
    0xEE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0x48, 0x89, 0xC6, 0xF3,
    0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xDE, 0xF3, 0x48, 0xA5,
    0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xE6, 0xE8, 0xBE, 0xCF, 0xFE, 0xFF]

theorem code_l11d407 : ∀ x ∈ codeRange 0x11d407 bytes_l11d407, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d407 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d452 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d452 (movR32Imm32Effect 0x11d452 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11d452 (fun s => s.RIP = 0x11d452) (movR32Imm32Effect 0x11d452 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d457 (movR64R64Effect 0x11d457 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 56) (.exec 0x11d457 (fun s => s.RIP = 0x11d457) (movR64R64Effect 0x11d457 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x11d45a (movR64R64Effect 0x11d45a 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11d45a (fun s => s.RIP = 0x11d45a) (movR64R64Effect 0x11d45a 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.exec 0x11d45d (RepPre 0x11d45d (RepMovsqPre 0x11d45d)) (repMovsqEffect 0x11d45d) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11d460 (movR32Imm32Effect 0x11d460 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11d460 (fun s => s.RIP = 0x11d460) (movR32Imm32Effect 0x11d460 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11d465 (leaR64Effect 0x11d465 0 (.sib 4 none 0 (.d32 0x6e8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11d465 (fun s => s.RIP = 0x11d465) (leaR64Effect 0x11d465 0 (.sib 4 none 0 (.d32 0x6e8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11d46d (movR64R64Effect 0x11d46d 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 65) (.exec 0x11d46d (fun s => s.RIP = 0x11d46d) (movR64R64Effect 0x11d46d 7 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 66) (.out 0x11d470 (movR64R64Effect 0x11d470 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 67) (.exec 0x11d470 (fun s => s.RIP = 0x11d470) (movR64R64Effect 0x11d470 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 68) (.exec 0x11d473 (RepPre 0x11d473 (RepMovsqPre 0x11d473)) (repMovsqEffect 0x11d473) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[66, 64, 60, 22]
    (.letOp (n := 69) (.out 0x11d476 (movR32Imm32Effect 0x11d476 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x11d476 (fun s => s.RIP = 0x11d476) (movR32Imm32Effect 0x11d476 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x11d47b (movR64R64Effect 0x11d47b 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 72) (.exec 0x11d47b (fun s => s.RIP = 0x11d47b) (movR64R64Effect 0x11d47b 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 73) (.out 0x11d47e (movR64R64Effect 0x11d47e 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[62]
    (.letOp (n := 74) (.exec 0x11d47e (fun s => s.RIP = 0x11d47e) (movR64R64Effect 0x11d47e 6 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 75) (.exec 0x11d481 (RepPre 0x11d481 (RepMovsqPre 0x11d481)) (repMovsqEffect 0x11d481) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[73, 71, 69, 22]
    (.letOp (n := 76) (.out 0x11d484 (movR32Imm32Effect 0x11d484 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 77) (.exec 0x11d484 (fun s => s.RIP = 0x11d484) (movR32Imm32Effect 0x11d484 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x11d489 (movR64R64Effect 0x11d489 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 79) (.exec 0x11d489 (fun s => s.RIP = 0x11d489) (movR64R64Effect 0x11d489 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 80) (.out 0x11d48c (movR64R64Effect 0x11d48c 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 81) (.exec 0x11d48c (fun s => s.RIP = 0x11d48c) (movR64R64Effect 0x11d48c 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 82) (.exec 0x11d48f (RepPre 0x11d48f (RepMovsqPre 0x11d48f)) (repMovsqEffect 0x11d48f) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[80, 78, 76, 22]
    (.letOp (n := 83) (.out 0x11d492 (movR64R64Effect 0x11d492 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 84) (.exec 0x11d492 (fun s => s.RIP = 0x11d492) (movR64R64Effect 0x11d492 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 85) (.out 0x11d495 (movR64R64Effect 0x11d495 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 86) (.exec 0x11d495 (fun s => s.RIP = 0x11d495) (movR64R64Effect 0x11d495 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 87) (.out 0x11d498 (callEffect (fun _ => 0x10a410) 0x11d49d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 88) (.exec 0x11d498 (PushPre 0x11d498 5) (callEffect (fun _ => 0x10a410) 0x11d49d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.const ⟨64, 0x11d49d⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ { target := .l11d49d, kept := #v[], arity := rfl, guard := some (Fin.last 89) }))))))))))))))))))))))))))))))))))))))

def bytes_l11d452 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0xE8, 0x06, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x48, 0x89,
    0xEE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0x48, 0x89, 0xC6, 0xF3,
    0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xDE, 0xF3, 0x48, 0xA5,
    0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xE6, 0xE8, 0x73, 0xCF, 0xFE, 0xFF]

theorem code_l11d452 : ∀ x ∈ codeRange 0x11d452 bytes_l11d452, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d452 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d49d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d49d (movR32Imm32Effect 0x11d49d 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11d49d (fun s => s.RIP = 0x11d49d) (movR32Imm32Effect 0x11d49d 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d4a2 (movR64R64Effect 0x11d4a2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 56) (.exec 0x11d4a2 (fun s => s.RIP = 0x11d4a2) (movR64R64Effect 0x11d4a2 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x11d4a5 (movR64R64Effect 0x11d4a5 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11d4a5 (fun s => s.RIP = 0x11d4a5) (movR64R64Effect 0x11d4a5 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.exec 0x11d4a8 (RepPre 0x11d4a8 (RepMovsqPre 0x11d4a8)) (repMovsqEffect 0x11d4a8) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11d4ab (movR32Imm32Effect 0x11d4ab 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11d4ab (fun s => s.RIP = 0x11d4ab) (movR32Imm32Effect 0x11d4ab 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11d4b0 (leaR64Effect 0x11d4b0 0 (.sib 4 none 0 (.d32 0x760))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11d4b0 (fun s => s.RIP = 0x11d4b0) (leaR64Effect 0x11d4b0 0 (.sib 4 none 0 (.d32 0x760))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11d4b8 (movR64R64Effect 0x11d4b8 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 65) (.exec 0x11d4b8 (fun s => s.RIP = 0x11d4b8) (movR64R64Effect 0x11d4b8 7 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 66) (.out 0x11d4bb (movR64R64Effect 0x11d4bb 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 67) (.exec 0x11d4bb (fun s => s.RIP = 0x11d4bb) (movR64R64Effect 0x11d4bb 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 68) (.exec 0x11d4be (RepPre 0x11d4be (RepMovsqPre 0x11d4be)) (repMovsqEffect 0x11d4be) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[66, 64, 60, 22]
    (.letOp (n := 69) (.out 0x11d4c1 (movR32Imm32Effect 0x11d4c1 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x11d4c1 (fun s => s.RIP = 0x11d4c1) (movR32Imm32Effect 0x11d4c1 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x11d4c6 (movR64R64Effect 0x11d4c6 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 72) (.exec 0x11d4c6 (fun s => s.RIP = 0x11d4c6) (movR64R64Effect 0x11d4c6 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 73) (.out 0x11d4c9 (movR64R64Effect 0x11d4c9 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[62]
    (.letOp (n := 74) (.exec 0x11d4c9 (fun s => s.RIP = 0x11d4c9) (movR64R64Effect 0x11d4c9 6 0) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 75) (.exec 0x11d4cc (RepPre 0x11d4cc (RepMovsqPre 0x11d4cc)) (repMovsqEffect 0x11d4cc) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[73, 71, 69, 22]
    (.letOp (n := 76) (.out 0x11d4cf (movR32Imm32Effect 0x11d4cf 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 77) (.exec 0x11d4cf (fun s => s.RIP = 0x11d4cf) (movR32Imm32Effect 0x11d4cf 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x11d4d4 (movR64R64Effect 0x11d4d4 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 79) (.exec 0x11d4d4 (fun s => s.RIP = 0x11d4d4) (movR64R64Effect 0x11d4d4 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 80) (.out 0x11d4d7 (movR64R64Effect 0x11d4d7 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 81) (.exec 0x11d4d7 (fun s => s.RIP = 0x11d4d7) (movR64R64Effect 0x11d4d7 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 82) (.exec 0x11d4da (RepPre 0x11d4da (RepMovsqPre 0x11d4da)) (repMovsqEffect 0x11d4da) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[80, 78, 76, 22]
    (.letOp (n := 83) (.out 0x11d4dd (movR64R64Effect 0x11d4dd 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 84) (.exec 0x11d4dd (fun s => s.RIP = 0x11d4dd) (movR64R64Effect 0x11d4dd 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 85) (.out 0x11d4e0 (movR64R64Effect 0x11d4e0 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 86) (.exec 0x11d4e0 (fun s => s.RIP = 0x11d4e0) (movR64R64Effect 0x11d4e0 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 87) (.out 0x11d4e3 (callEffect (fun _ => 0x10a410) 0x11d4e8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 88) (.exec 0x11d4e3 (PushPre 0x11d4e3 5) (callEffect (fun _ => 0x10a410) 0x11d4e8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.const ⟨64, 0x11d4e8⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(0, 62), (3, 3), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ { target := .l11d4e8, kept := #v[], arity := rfl, guard := some (Fin.last 89) }))))))))))))))))))))))))))))))))))))))

def bytes_l11d49d : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0x60, 0x07, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x48, 0x89,
    0xEE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0x48, 0x89, 0xC6, 0xF3,
    0x48, 0xA5, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xDE, 0xF3, 0x48, 0xA5,
    0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xE6, 0xE8, 0x28, 0xCF, 0xFE, 0xFF]

theorem code_l11d49d : ∀ x ∈ codeRange 0x11d49d bytes_l11d49d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d49d 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d4e8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d4e8 (movR32Imm32Effect 0x11d4e8 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x11d4e8 (fun s => s.RIP = 0x11d4e8) (movR32Imm32Effect 0x11d4e8 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d4ed (movR64R64Effect 0x11d4ed 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 56) (.exec 0x11d4ed (fun s => s.RIP = 0x11d4ed) (movR64R64Effect 0x11d4ed 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x11d4f0 (movR64R64Effect 0x11d4f0 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11d4f0 (fun s => s.RIP = 0x11d4f0) (movR64R64Effect 0x11d4f0 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.exec 0x11d4f3 (RepPre 0x11d4f3 (RepMovsqPre 0x11d4f3)) (repMovsqEffect 0x11d4f3) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 53, 22]
    (.letOp (n := 60) (.out 0x11d4f6 (movR32Imm32Effect 0x11d4f6 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x11d4f6 (fun s => s.RIP = 0x11d4f6) (movR32Imm32Effect 0x11d4f6 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x11d4fb (leaR64Effect 0x11d4fb 7 (.sib 4 none 0 (.d32 0x7d8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x11d4fb (fun s => s.RIP = 0x11d4fb) (leaR64Effect 0x11d4fb 7 (.sib 4 none 0 (.d32 0x7d8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11d503 (movR64R64Effect 0x11d503 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 65) (.exec 0x11d503 (fun s => s.RIP = 0x11d503) (movR64R64Effect 0x11d503 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 66) (.exec 0x11d506 (RepPre 0x11d506 (RepMovsqPre 0x11d506)) (repMovsqEffect 0x11d506) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[64, 62, 60, 22]
    (.letOp (n := 67) (.out 0x11d509 (cmpMREffect 0x11d509 5 64 14 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 4] []) (.flag .ZF)) #v[14, 4]
    (.letOp (n := 68) (.exec 0x11d509 (LoadPre 0x11d509 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11d509 + BitVec.ofNat 64 5)) 8) (cmpMREffect 0x11d509 5 64 14 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 69) (.pure (condOp 4)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l11f71f, RegMap.args [(4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l11d514, RegMap.args [(4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l11d4e8 : List UInt8 :=
  [0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0xB9, 0x0F,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0xD8, 0x07, 0x00, 0x00, 0x48, 0x89, 0xEE, 0xF3, 0x48,
    0xA5, 0x4C, 0x39, 0x74, 0x24, 0x68, 0x0F, 0x84, 0x0B, 0x22, 0x00, 0x00]

theorem code_l11d4e8 : ∀ x ∈ codeRange 0x11d4e8 bytes_l11d4e8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d4e8 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d514 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d514 (movR32Imm32Effect 0x11d514 5 2 0x3c0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x11d514 (fun s => s.RIP = 0x11d514) (movR32Imm32Effect 0x11d514 5 2 0x3c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d519 (movR64M64Effect 0x11d519 5 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 56) (.exec 0x11d519 (LoadPre 0x11d519 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11d519 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d519 5 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11d521 (movR64R64Effect 0x11d521 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x11d521 (fun s => s.RIP = 0x11d521) (movR64R64Effect 0x11d521 7 5) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 59) (.out 0x11d524 (leaR64Effect 0x11d524 6 (.sib 4 none 0 (.d32 0x850))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x11d524 (fun s => s.RIP = 0x11d524) (leaR64Effect 0x11d524 6 (.sib 4 none 0 (.d32 0x850))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x11d52c (leaR64Effect 0x11d52c 3 (.rip 0xd2ed)) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 62) (.exec 0x11d52c (fun s => s.RIP = 0x11d52c) (leaR64Effect 0x11d52c 3 (.rip 0xd2ed)) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x11d533 (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d535) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 61]
    (.letOp (n := 64) (.exec 0x11d533 (GoesTo (CallPre 0x11d533 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d535) 0x12a820) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d535) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 61]
    (.letOp (n := 65) (.const ⟨64, 0x11d535⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 53), (3, 61), (4, 63), (5, 55), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l11d535, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l11d514 : List UInt8 :=
  [0xBA, 0xC0, 0x03, 0x00, 0x00, 0x48, 0x8B, 0xAC, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEF,
    0x48, 0x8D, 0xB4, 0x24, 0x50, 0x08, 0x00, 0x00, 0x48, 0x8D, 0x1D, 0xED, 0xD2, 0x00, 0x00, 0xFF,
    0xD3]

theorem code_l11d514 : ∀ x ∈ codeRange 0x11d514 bytes_l11d514, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d514 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d535 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d535 (leaR64Effect 0x11d535 7 (.base 5 (.d32 0x3c0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 54) (.exec 0x11d535 (fun s => s.RIP = 0x11d535) (leaR64Effect 0x11d535 7 (.base 5 (.d32 0x3c0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x11d53c (movR32Imm32Effect 0x11d53c 5 2 0x3c0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x11d53c (fun s => s.RIP = 0x11d53c) (movR32Imm32Effect 0x11d53c 5 2 0x3c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x11d541 (movR64R64Effect 0x11d541 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 58) (.exec 0x11d541 (fun s => s.RIP = 0x11d541) (movR64R64Effect 0x11d541 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x11d544 (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d546) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 60) (.exec 0x11d544 (GoesTo (CallPre 0x11d544 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d546) 0x12a820) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d546) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 61) (.const ⟨64, 0x11d546⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l11d546, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11d535 : List UInt8 :=
  [0x48, 0x8D, 0xBD, 0xC0, 0x03, 0x00, 0x00, 0xBA, 0xC0, 0x03, 0x00, 0x00, 0x4C, 0x89, 0xEE, 0xFF,
    0xD3]

theorem code_l11d535 : ∀ x ∈ codeRange 0x11d535 bytes_l11d535, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d535 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d546 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d546 (movR64R64Effect 0x11d546 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 54) (.exec 0x11d546 (fun s => s.RIP = 0x11d546) (movR64R64Effect 0x11d546 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x11d549 (leaR64Effect 0x11d549 6 (.sib 4 none 0 (.d32 0x270))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x11d549 (fun s => s.RIP = 0x11d549) (leaR64Effect 0x11d549 6 (.sib 4 none 0 (.d32 0x270))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11d551 (callEffect (fun _ => 0x11aa40) 0x11d556) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x11d551 (PushPre 0x11d551 5) (callEffect (fun _ => 0x11aa40) 0x11d556) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x11d556⟩) #v[]
    (.terminate (.call ⟨.l11aa40, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l11d556, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l11d546 : List UInt8 :=
  [0x4C, 0x89, 0xE7, 0x48, 0x8D, 0xB4, 0x24, 0x70, 0x02, 0x00, 0x00, 0xE8, 0xEA, 0xD4, 0xFF, 0xFF]

theorem code_l11d546 : ∀ x ∈ codeRange 0x11d546 bytes_l11d546, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d546 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d556 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d556 (movR64R64Effect 0x11d556 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 54) (.exec 0x11d556 (fun s => s.RIP = 0x11d556) (movR64R64Effect 0x11d556 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x11d559 (leaR64Effect 0x11d559 6 (.sib 4 none 0 (.d32 0x290))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x11d559 (fun s => s.RIP = 0x11d559) (leaR64Effect 0x11d559 6 (.sib 4 none 0 (.d32 0x290))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11d561 (callEffect (fun _ => 0x11aa40) 0x11d566) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x11d561 (PushPre 0x11d561 5) (callEffect (fun _ => 0x11aa40) 0x11d566) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x11d566⟩) #v[]
    (.terminate (.call ⟨.l11aa40, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l11d566, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l11d556 : List UInt8 :=
  [0x4C, 0x89, 0xFF, 0x48, 0x8D, 0xB4, 0x24, 0x90, 0x02, 0x00, 0x00, 0xE8, 0xDA, 0xD4, 0xFF, 0xFF]

theorem code_l11d556 : ∀ x ∈ codeRange 0x11d556 bytes_l11d556, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d556 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d566 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d566 (movR64M64Effect 0x11d566 6 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x11d566 (LoadPre 0x11d566 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x11d566 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d566 6 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11d56e (cmpMREffect 0x11d56e 5 64 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 4] []) (.flag .ZF)) #v[53, 4]
    (.letOp (n := 56) (.exec 0x11d56e (LoadPre 0x11d56e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11d56e + BitVec.ofNat 64 5)) 8) (cmpMREffect 0x11d56e 5 64 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l11f736, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l11d579, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l11d566 : List UInt8 :=
  [0x48, 0x8B, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x39, 0x74, 0x24, 0x60, 0x0F, 0x84, 0xBD,
    0x21, 0x00, 0x00]

theorem code_l11d566 : ∀ x ∈ codeRange 0x11d566 bytes_l11d566, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d566 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d579_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x11d5fc (StorePre 0x11d5fc 4 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x41)) s (0x11d5fc + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11d5fc 4 0 (.sib 2 (some 6) 0 (.d8 0x41))) (Reg.operands [.gpr 0, .gpr 2, .gpr 6] [])) #v[82, 55, 6]
    (.letOp (n := 85) (.out 0x11d600 (addR64Imm8Effect 0x11d600 6 0x42) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 86) (.exec 0x11d600 (fun s => s.RIP = 0x11d600) (addR64Imm8Effect 0x11d600 6 0x42) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 87) (.out 0x11d604 (addR64Imm32Effect 0x11d604 14 0x98) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 88) (.exec 0x11d604 (fun s => s.RIP = 0x11d604) (addR64Imm32Effect 0x11d604 14 0x98) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 89) (.out 0x11d60b (addR64Imm32Effect 0x11d60b 5 0x780) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 90) (.exec 0x11d60b (fun s => s.RIP = 0x11d60b) (addR64Imm32Effect 0x11d60b 5 0x780) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 91) (.out 0x11d612 (cmpMREffect 0x11d612 8 64 14 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 4] []) (.flag .ZF)) #v[87, 4]
    (.letOp (n := 92) (.exec 0x11d612 (LoadPre 0x11d612 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11d612 + BitVec.ofNat 64 8)) 8) (cmpMREffect 0x11d612 8 64 14 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 93) (.pure (condOp 5)) #v[91]
    (.terminate (.condBr (Fin.last 93) ⟨.l11c920, RegMap.args [(0, 82), (1, 72), (2, 55), (3, 3), (4, 4), (5, 89), (6, 85), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 87), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩ ⟨.l11d620, RegMap.args [(0, 82), (1, 72), (2, 55), (3, 3), (4, 4), (5, 89), (6, 85), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 87), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩)))))))))))

def bytes_l11d579_1 : List UInt8 :=
  [0x88, 0x44, 0x32, 0x41, 0x48, 0x83, 0xC6, 0x42, 0x49, 0x81, 0xC6, 0x98, 0x00, 0x00, 0x00, 0x48,
    0x81, 0xC5, 0x80, 0x07, 0x00, 0x00, 0x4C, 0x39, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x0F, 0x85,
    0x00, 0xF3, 0xFF, 0xFF]

theorem code_l11d579_1 : ∀ x ∈ codeRange 0x11d5fc bytes_l11d579_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d5fc 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d579 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d579 (movzxR32M8Effect 0x11d579 8 0 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11d579 (LoadPre 0x11d579 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x11d579 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11d579 8 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11d581 (movR64M64Effect 0x11d581 2 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x11d581 (LoadPre 0x11d581 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11d581 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d581 2 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x11d589 (StorePre 0x11d589 4 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x20)) s (0x11d589 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11d589 4 0 (.sib 2 (some 6) 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 2, .gpr 6] [])) #v[53, 55, 6]
    (.letOp (n := 58) (.out 0x11d58d (movR64M64Effect 0x11d58d 0 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 59) (.exec 0x11d58d (LoadPre 0x11d58d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x11d58d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d58d 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x11d595 (StorePre 0x11d595 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x18)) s (0x11d595 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d595 0 (.sib 2 (some 6) 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 2, .gpr 6] [])) #v[58, 55, 6]
    (.letOp (n := 61) (.out 0x11d59a (movR64M64Effect 0x11d59a 0 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 62) (.exec 0x11d59a (LoadPre 0x11d59a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x11d59a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d59a 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x11d5a2 (StorePre 0x11d5a2 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x10)) s (0x11d5a2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d5a2 0 (.sib 2 (some 6) 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 2, .gpr 6] [])) #v[61, 55, 6]
    (.letOp (n := 64) (.out 0x11d5a7 (movR64M64Effect 0x11d5a7 0 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 65) (.exec 0x11d5a7 (LoadPre 0x11d5a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x11d5a7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d5a7 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x11d5af (movR64M64Effect 0x11d5af 1 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 67) (.exec 0x11d5af (LoadPre 0x11d5af (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x11d5af + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d5af 1 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x11d5b7 (StorePre 0x11d5b7 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x8)) s (0x11d5b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d5b7 1 (.sib 2 (some 6) 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 2, .gpr 6] [])) #v[66, 55, 6]
    (.letOp (n := 69) (.exec 0x11d5bc (StorePre 0x11d5bc 4 (fun s => AddrMode.addr (.sib 2 (some 6) 0 .none) s (0x11d5bc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11d5bc 0 (.sib 2 (some 6) 0 .none)) (Reg.operands [.gpr 0, .gpr 2, .gpr 6] [])) #v[64, 55, 6]
    (.letOp (n := 70) (.out 0x11d5c0 (movR64M64Effect 0x11d5c0 0 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 71) (.exec 0x11d5c0 (LoadPre 0x11d5c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x11d5c0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d5c0 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x11d5c8 (movR64M64Effect 0x11d5c8 1 (.sib 4 none 0 (.d32 0x1d8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 73) (.exec 0x11d5c8 (LoadPre 0x11d5c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x11d5c8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d5c8 1 (.sib 4 none 0 (.d32 0x1d8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x11d5d0 (StorePre 0x11d5d0 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x21)) s (0x11d5d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d5d0 0 (.sib 2 (some 6) 0 (.d8 0x21))) (Reg.operands [.gpr 0, .gpr 2, .gpr 6] [])) #v[70, 55, 6]
    (.letOp (n := 75) (.exec 0x11d5d5 (StorePre 0x11d5d5 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x29)) s (0x11d5d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d5d5 1 (.sib 2 (some 6) 0 (.d8 0x29))) (Reg.operands [.gpr 1, .gpr 2, .gpr 6] [])) #v[72, 55, 6]
    (.letOp (n := 76) (.out 0x11d5da (movR64M64Effect 0x11d5da 0 (.sib 4 none 0 (.d32 0x1e0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 77) (.exec 0x11d5da (LoadPre 0x11d5da (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x11d5da + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d5da 0 (.sib 4 none 0 (.d32 0x1e0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x11d5e2 (StorePre 0x11d5e2 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x31)) s (0x11d5e2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d5e2 0 (.sib 2 (some 6) 0 (.d8 0x31))) (Reg.operands [.gpr 0, .gpr 2, .gpr 6] [])) #v[76, 55, 6]
    (.letOp (n := 79) (.out 0x11d5e7 (movR64M64Effect 0x11d5e7 0 (.sib 4 none 0 (.d32 0x1e8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 80) (.exec 0x11d5e7 (LoadPre 0x11d5e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x11d5e7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d5e7 0 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x11d5ef (StorePre 0x11d5ef 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0x39)) s (0x11d5ef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d5ef 0 (.sib 2 (some 6) 0 (.d8 0x39))) (Reg.operands [.gpr 0, .gpr 2, .gpr 6] [])) #v[79, 55, 6]
    (.letOp (n := 82) (.out 0x11d5f4 (movzxR32M8Effect 0x11d5f4 8 0 (.sib 4 none 0 (.d32 0x1f0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 83) (.exec 0x11d5f4 (LoadPre 0x11d5f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f0)) s (0x11d5f4 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11d5f4 8 0 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11d579_1)))))))))))))))))))))))))))))))

def bytes_l11d579 : List UInt8 :=
  [0x0F, 0xB6, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00,
    0x88, 0x44, 0x32, 0x20, 0x48, 0x8B, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x32,
    0x18, 0x48, 0x8B, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x32, 0x10, 0x48, 0x8B,
    0x84, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00, 0x48, 0x89,
    0x4C, 0x32, 0x08, 0x48, 0x89, 0x04, 0x32, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x48,
    0x8B, 0x8C, 0x24, 0xD8, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x32, 0x21, 0x48, 0x89, 0x4C, 0x32,
    0x29, 0x48, 0x8B, 0x84, 0x24, 0xE0, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x32, 0x31, 0x48, 0x8B,
    0x84, 0x24, 0xE8, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x32, 0x39, 0x0F, 0xB6, 0x84, 0x24, 0xF0,
    0x01, 0x00, 0x00] ++ bytes_l11d579_1

theorem code_l11d579 : ∀ x ∈ codeRange 0x11d579 bytes_l11d579, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1d579 131 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d579_1

@[cfg_block] def b_l11d620 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d620 (leaR64Effect 0x11d620 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x11d620 (fun s => s.RIP = 0x11d620) (leaR64Effect 0x11d620 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11d628 (movR32Imm32Effect 0x11d628 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x11d628 (fun s => s.RIP = 0x11d628) (movR32Imm32Effect 0x11d628 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x11d62d (movR64Imm32Effect 0x11d62d 6 0x203258) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x11d62d (fun s => s.RIP = 0x11d62d) (movR64Imm32Effect 0x11d62d 6 0x203258) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x11d634 (RepPre 0x11d634 (RepMovsqPre 0x11d634)) (repMovsqEffect 0x11d634) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.out 0x11d637 (movR64M64Effect 0x11d637 1 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 61) (.exec 0x11d637 (LoadPre 0x11d637 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x11d637 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d637 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x11d63f (movR64R64Effect 0x11d63f 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[60]
    (.letOp (n := 63) (.exec 0x11d63f (fun s => s.RIP = 0x11d63f) (movR64R64Effect 0x11d63f 0 1) (Reg.operands [.gpr 1] [])) #v[60]
    (.letOp (n := 64) (.out 0x11d642 (shlR64Effect 0x11d642 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[62]
    (.letOp (n := 65) (.exec 0x11d642 (fun s => s.RIP = 0x11d642) (shlR64Effect 0x11d642 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[62]
    (.letOp (n := 66) (.out 0x11d646 (leaR64Effect 0x11d646 0 (.sib 0 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[64, 60]
    (.letOp (n := 67) (.exec 0x11d646 (fun s => s.RIP = 0x11d646) (leaR64Effect 0x11d646 0 (.sib 0 (some 1) 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[64, 60]
    (.letOp (n := 68) (.exec 0x11d64a (StorePre 0x11d64a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11d64a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d64a 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x11d64f (movR64M64Effect 0x11d64f 1 (.sib 4 none 0 (.d32 0x1a0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 70) (.exec 0x11d64f (LoadPre 0x11d64f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x11d64f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d64f 1 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x11d657 (movR64R64Effect 0x11d657 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 72) (.exec 0x11d657 (fun s => s.RIP = 0x11d657) (movR64R64Effect 0x11d657 0 1) (Reg.operands [.gpr 1] [])) #v[69]
    (.letOp (n := 73) (.out 0x11d65a (shlR64Effect 0x11d65a 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[71]
    (.letOp (n := 74) (.exec 0x11d65a (fun s => s.RIP = 0x11d65a) (shlR64Effect 0x11d65a 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 75) (.out 0x11d65e (leaR64Effect 0x11d65e 0 (.sib 0 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[73, 69]
    (.letOp (n := 76) (.exec 0x11d65e (fun s => s.RIP = 0x11d65e) (leaR64Effect 0x11d65e 0 (.sib 0 (some 1) 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[73, 69]
    (.letOp (n := 77) (.exec 0x11d662 (StorePre 0x11d662 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11d662 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d662 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x11d667 (xorR32R32Effect 0x11d667 2 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 5] []) (.reg (.gpr 5))) #v[5, 5]
    (.letOp (n := 79) (.exec 0x11d667 (fun s => s.RIP = 0x11d667) (xorR32R32Effect 0x11d667 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 80) (.out 0x11d669 (leaR64Effect 0x11d669 15 (.sib 4 none 0 (.d32 0x490))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 81) (.exec 0x11d669 (fun s => s.RIP = 0x11d669) (leaR64Effect 0x11d669 15 (.sib 4 none 0 (.d32 0x490))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.out 0x11d671 (leaR64Effect 0x11d671 12 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 83) (.exec 0x11d671 (fun s => s.RIP = 0x11d671) (leaR64Effect 0x11d671 12 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.out 0x11d679 (movR64M64Effect 0x11d679 13 (.sib 4 none 0 (.d32 0x1c0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 85) (.exec 0x11d679 (LoadPre 0x11d679 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x11d679 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d679 13 (.sib 4 none 0 (.d32 0x1c0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.exec 0x11d681 (fun s => s.RIP = 0x11d681) (fun _ => nopEffect 0x11d681 15) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l11d690, RegMap.args [(0, 75), (1, 69), (4, 4), (5, 78), (9, 9), (10, 10), (11, 11), (12, 82), (13, 84), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)] 87⟩)))))))))))))))))))))))))))))))))))

def bytes_l11d620 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6,
    0x58, 0x32, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8B, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48,
    0x89, 0xC8, 0x48, 0xC1, 0xE0, 0x06, 0x48, 0x8D, 0x04, 0x48, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48,
    0x8B, 0x8C, 0x24, 0xA0, 0x01, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x48, 0xC1, 0xE0, 0x06, 0x48, 0x8D,
    0x04, 0x48, 0x48, 0x89, 0x44, 0x24, 0x38, 0x31, 0xED, 0x4C, 0x8D, 0xBC, 0x24, 0x90, 0x04, 0x00,
    0x00, 0x4C, 0x8D, 0xA4, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0xAC, 0x24, 0xC0, 0x01, 0x00,
    0x00, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l11d620 : ∀ x ∈ codeRange 0x11d620 bytes_l11d620, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d620 112 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d690 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d690 (cmpMREffect 0x11d690 5 64 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 4] []) (.flag .ZF)) #v[5, 4]
    (.letOp (n := 54) (.exec 0x11d690 (LoadPre 0x11d690 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11d690 + BitVec.ofNat 64 5)) 8) (cmpMREffect 0x11d690 5 64 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11f74d, RegMap.args [(4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11d69b, RegMap.args [(4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11d690 : List UInt8 :=
  [0x48, 0x39, 0x6C, 0x24, 0x60, 0x0F, 0x84, 0xB2, 0x20, 0x00, 0x00]

theorem code_l11d690 : ∀ x ∈ codeRange 0x11d690 bytes_l11d690, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d690 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d69b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d69b (cmpMREffect 0x11d69b 5 64 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 4] []) (.flag .ZF)) #v[5, 4]
    (.letOp (n := 54) (.exec 0x11d69b (LoadPre 0x11d69b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11d69b + BitVec.ofNat 64 5)) 8) (cmpMREffect 0x11d69b 5 64 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11f764, RegMap.args [(4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11d6a6, RegMap.args [(4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11d69b : List UInt8 :=
  [0x48, 0x39, 0x6C, 0x24, 0x08, 0x0F, 0x84, 0xBE, 0x20, 0x00, 0x00]

theorem code_l11d69b : ∀ x ∈ codeRange 0x11d69b bytes_l11d69b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d69b 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d6a6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d6a6 (movR32Imm32Effect 0x11d6a6 5 2 0x3c0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x11d6a6 (fun s => s.RIP = 0x11d6a6) (movR32Imm32Effect 0x11d6a6 5 2 0x3c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11d6ab (leaR64Effect 0x11d6ab 14 (.sib 4 none 0 (.d32 0x850))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 56) (.exec 0x11d6ab (fun s => s.RIP = 0x11d6ab) (leaR64Effect 0x11d6ab 14 (.sib 4 none 0 (.d32 0x850))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11d6b3 (movR64R64Effect 0x11d6b3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x11d6b3 (fun s => s.RIP = 0x11d6b3) (movR64R64Effect 0x11d6b3 7 14) (Reg.operands [.gpr 14] [])) #v[55]
    (.letOp (n := 59) (.out 0x11d6b6 (movR64R64Effect 0x11d6b6 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 60) (.exec 0x11d6b6 (fun s => s.RIP = 0x11d6b6) (movR64R64Effect 0x11d6b6 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x11d6b9 (leaR64Effect 0x11d6b9 3 (.rip 0xd160)) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 62) (.exec 0x11d6b9 (fun s => s.RIP = 0x11d6b9) (leaR64Effect 0x11d6b9 3 (.rip 0xd160)) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x11d6c0 (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d6c2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 61]
    (.letOp (n := 64) (.exec 0x11d6c0 (GoesTo (CallPre 0x11d6c0 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d6c2) 0x12a820) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d6c2) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 61]
    (.letOp (n := 65) (.const ⟨64, 0x11d6c2⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 53), (3, 61), (4, 63), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l11d6c2, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l11d6a6 : List UInt8 :=
  [0xBA, 0xC0, 0x03, 0x00, 0x00, 0x4C, 0x8D, 0xB4, 0x24, 0x50, 0x08, 0x00, 0x00, 0x4C, 0x89, 0xF7,
    0x4C, 0x89, 0xEE, 0x48, 0x8D, 0x1D, 0x60, 0xD1, 0x00, 0x00, 0xFF, 0xD3]

theorem code_l11d6a6 : ∀ x ∈ codeRange 0x11d6a6 bytes_l11d6a6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d6a6 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d6c2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d6c2 (leaR64Effect 0x11d6c2 6 (.base 13 (.d32 0x3c0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 54) (.exec 0x11d6c2 (fun s => s.RIP = 0x11d6c2) (leaR64Effect 0x11d6c2 6 (.base 13 (.d32 0x3c0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x11d6c9 (movR32Imm32Effect 0x11d6c9 5 2 0x3c0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x11d6c9 (fun s => s.RIP = 0x11d6c9) (movR32Imm32Effect 0x11d6c9 5 2 0x3c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x11d6ce (movR64R64Effect 0x11d6ce 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 58) (.exec 0x11d6ce (fun s => s.RIP = 0x11d6ce) (movR64R64Effect 0x11d6ce 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x11d6d1 (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d6d3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 60) (.exec 0x11d6d1 (GoesTo (CallPre 0x11d6d1 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d6d3) 0x12a820) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x11d6d3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 61) (.const ⟨64, 0x11d6d3⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 59), (5, 5), (6, 53), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l11d6d3, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11d6c2 : List UInt8 :=
  [0x49, 0x8D, 0xB5, 0xC0, 0x03, 0x00, 0x00, 0xBA, 0xC0, 0x03, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0xFF,
    0xD3]

theorem code_l11d6c2 : ∀ x ∈ codeRange 0x11d6c2 bytes_l11d6c2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d6c2 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d6d3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d6d3 (movR64M64Effect 0x11d6d3 3 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x11d6d3 (LoadPre 0x11d6d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11d6d3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d6d3 3 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11d6db (movzxR32M8Effect 0x11d6db 5 2 (.sib 3 (some 5) 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 5] []) (.reg (.gpr 2))) #v[53, 5]
    (.letOp (n := 56) (.exec 0x11d6db (LoadPre 0x11d6db (fun s => AddrMode.addr (.sib 3 (some 5) 0 (.d8 0x20)) s (0x11d6db + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11d6db 5 2 (.sib 3 (some 5) 0 (.d8 0x20))) (Reg.operands [.gpr 3, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 57) (.out 0x11d6e0 (movR64R64Effect 0x11d6e0 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 58) (.exec 0x11d6e0 (fun s => s.RIP = 0x11d6e0) (movR64R64Effect 0x11d6e0 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11d6e3 (movR64R64Effect 0x11d6e3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x11d6e3 (fun s => s.RIP = 0x11d6e3) (movR64R64Effect 0x11d6e3 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x11d6e6 (callEffect (fun _ => 0x11c510) 0x11d6eb) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x11d6e6 (PushPre 0x11d6e6 5) (callEffect (fun _ => 0x11c510) 0x11d6eb) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x11d6eb⟩) #v[]
    (.terminate (.call ⟨.l11c510, RegMap.args [(2, 55), (3, 53), (4, 61), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l11d6eb, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l11d6d3 : List UInt8 :=
  [0x48, 0x8B, 0x9C, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x54, 0x2B, 0x20, 0x4C, 0x89, 0xE7,
    0x4C, 0x89, 0xF6, 0xE8, 0x25, 0xEE, 0xFF, 0xFF]

theorem code_l11d6d3 : ∀ x ∈ codeRange 0x11d6d3 bytes_l11d6d3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d6d3 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d6eb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d6eb (leaR64Effect 0x11d6eb 14 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x11d6eb (fun s => s.RIP = 0x11d6eb) (leaR64Effect 0x11d6eb 14 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11d6f3 (movR64R64Effect 0x11d6f3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x11d6f3 (fun s => s.RIP = 0x11d6f3) (movR64R64Effect 0x11d6f3 7 14) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 57) (.out 0x11d6f6 (movR64R64Effect 0x11d6f6 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x11d6f6 (fun s => s.RIP = 0x11d6f6) (movR64R64Effect 0x11d6f6 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11d6f9 (callEffect (fun _ => 0x10a410) 0x11d6fe) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11d6f9 (PushPre 0x11d6f9 5) (callEffect (fun _ => 0x10a410) 0x11d6fe) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11d6fe⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l11d6fe, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11d6eb : List UInt8 :=
  [0x4C, 0x8D, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0xE8, 0x12,
    0xCD, 0xFE, 0xFF]

theorem code_l11d6eb : ∀ x ∈ codeRange 0x11d6eb bytes_l11d6eb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d6eb 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d6fe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d6fe (movzxR32M8Effect 0x11d6fe 5 2 (.sib 3 (some 5) 0 (.d8 0x41))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 5] []) (.reg (.gpr 2))) #v[3, 5]
    (.letOp (n := 54) (.exec 0x11d6fe (LoadPre 0x11d6fe (fun s => AddrMode.addr (.sib 3 (some 5) 0 (.d8 0x41)) s (0x11d6fe + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11d6fe 5 2 (.sib 3 (some 5) 0 (.d8 0x41))) (Reg.operands [.gpr 3, .gpr 5] [])) #v[3, 5]
    (.letOp (n := 55) (.out 0x11d703 (movR64R64Effect 0x11d703 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 56) (.exec 0x11d703 (fun s => s.RIP = 0x11d703) (movR64R64Effect 0x11d703 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x11d706 (movR64R64Effect 0x11d706 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x11d706 (fun s => s.RIP = 0x11d706) (movR64R64Effect 0x11d706 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x11d709 (callEffect (fun _ => 0x11c510) 0x11d70e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11d709 (PushPre 0x11d709 5) (callEffect (fun _ => 0x11c510) 0x11d70e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11d70e⟩) #v[]
    (.terminate (.call ⟨.l11c510, RegMap.args [(2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l11d70e, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11d6fe : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x2B, 0x41, 0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xFE, 0xE8, 0x02, 0xEE, 0xFF, 0xFF]

theorem code_l11d6fe : ∀ x ∈ codeRange 0x11d6fe bytes_l11d6fe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d6fe 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d70e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d70e (movR64R64Effect 0x11d70e 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x11d70e (fun s => s.RIP = 0x11d70e) (movR64R64Effect 0x11d70e 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x11d711 (movR64R64Effect 0x11d711 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 56) (.exec 0x11d711 (fun s => s.RIP = 0x11d711) (movR64R64Effect 0x11d711 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x11d714 (callEffect (fun _ => 0x10a410) 0x11d719) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x11d714 (PushPre 0x11d714 5) (callEffect (fun _ => 0x10a410) 0x11d719) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x11d719⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l11d719, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l11d70e : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0xE8, 0xF7, 0xCC, 0xFE, 0xFF]

theorem code_l11d70e : ∀ x ∈ codeRange 0x11d70e bytes_l11d70e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d70e 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d719 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d719 (addR64Imm8Effect 0x11d719 5 0x42) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x11d719 (fun s => s.RIP = 0x11d719) (addR64Imm8Effect 0x11d719 5 0x42) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x11d71d (addR64Imm32Effect 0x11d71d 13 0x780) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 56) (.exec 0x11d71d (fun s => s.RIP = 0x11d71d) (addR64Imm32Effect 0x11d71d 13 0x780) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x11d724 (cmpMREffect 0x11d724 5 64 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 4] []) (.flag .ZF)) #v[53, 4]
    (.letOp (n := 58) (.exec 0x11d724 (LoadPre 0x11d724 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11d724 + BitVec.ofNat 64 5)) 8) (cmpMREffect 0x11d724 5 64 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l11d690, RegMap.args [(3, 3), (4, 4), (5, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l11d72f, RegMap.args [(3, 3), (4, 4), (5, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l11d719 : List UInt8 :=
  [0x48, 0x83, 0xC5, 0x42, 0x49, 0x81, 0xC5, 0x80, 0x07, 0x00, 0x00, 0x48, 0x39, 0x6C, 0x24, 0x38,
    0x0F, 0x85, 0x61, 0xFF, 0xFF, 0xFF]

theorem code_l11d719 : ∀ x ∈ codeRange 0x11d719 bytes_l11d719, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d719 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d72f : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l11d748, RegMap.args (entryMap (live .l11d72f)) 53⟩)

def bytes_l11d72f : List UInt8 :=
  [0xEB, 0x17]

theorem code_l11d72f : ∀ x ∈ codeRange 0x11d72f bytes_l11d72f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d72f 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d731 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d731 (leaR64Effect 0x11d731 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x11d731 (fun s => s.RIP = 0x11d731) (leaR64Effect 0x11d731 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11d739 (movR32Imm32Effect 0x11d739 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x11d739 (fun s => s.RIP = 0x11d739) (movR32Imm32Effect 0x11d739 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x11d73e (movR64Imm32Effect 0x11d73e 6 0x203258) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x11d73e (fun s => s.RIP = 0x11d73e) (movR64Imm32Effect 0x11d73e 6 0x203258) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x11d745 (RepPre 0x11d745 (RepMovsqPre 0x11d745)) (repMovsqEffect 0x11d745) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.terminate (.br ⟨.l11d748, RegMap.args [(3, 3), (4, 4), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l11d731 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6,
    0x58, 0x32, 0x20, 0x00, 0xF3, 0x48, 0xA5]

theorem code_l11d731 : ∀ x ∈ codeRange 0x11d731 bytes_l11d731, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d731 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d748_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.out 0x11d7bc (addR64Imm8Effect 0x11d7bc 0 0xf9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[88]
    (.letOp (n := 91) (.exec 0x11d7bc (fun s => s.RIP = 0x11d7bc) (addR64Imm8Effect 0x11d7bc 0 0xf9) (Reg.operands [.gpr 0] [])) #v[88]
    (.letOp (n := 92) (.exec 0x11d7c0 (StorePre 0x11d7c0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x11d7c0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d7c0 0 (.sib 4 none 0 (.d32 0x1c8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[90, 4]
    (.terminate (.br ⟨.l11d7ef, RegMap.args [(0, 90), (1, 84), (2, 55), (3, 3), (4, 4), (12, 86), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩))))

def bytes_l11d748_1 : List UInt8 :=
  [0x48, 0x83, 0xC0, 0xF9, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x01, 0x00, 0x00, 0xEB, 0x25]

theorem code_l11d748_1 : ∀ x ∈ codeRange 0x11d7bc bytes_l11d748_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d7bc 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d748 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d748 (movR64M64Effect 0x11d748 2 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x11d748 (LoadPre 0x11d748 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11d748 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d748 2 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11d750 (addR64Imm8Effect 0x11d750 2 0x40) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 56) (.exec 0x11d750 (fun s => s.RIP = 0x11d750) (addR64Imm8Effect 0x11d750 2 0x40) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.out 0x11d754 (movR64M64Effect 0x11d754 1 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x11d754 (LoadPre 0x11d754 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x11d754 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d754 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x11d75c (movR64R64Effect 0x11d75c 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x11d75c (fun s => s.RIP = 0x11d75c) (movR64R64Effect 0x11d75c 0 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 61) (.out 0x11d75f (shlR64Effect 0x11d75f 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 62) (.exec 0x11d75f (fun s => s.RIP = 0x11d75f) (shlR64Effect 0x11d75f 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.out 0x11d763 (leaR64Effect 0x11d763 0 (.sib 0 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[61, 57]
    (.letOp (n := 64) (.exec 0x11d763 (fun s => s.RIP = 0x11d763) (leaR64Effect 0x11d763 0 (.sib 0 (some 1) 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[61, 57]
    (.letOp (n := 65) (.exec 0x11d767 (StorePre 0x11d767 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x260)) s (0x11d767 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d767 0 (.sib 4 none 0 (.d32 0x260))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x11d76f (movR64M64Effect 0x11d76f 1 (.sib 4 none 0 (.d32 0xcc0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 67) (.exec 0x11d76f (LoadPre 0x11d76f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc0)) s (0x11d76f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d76f 1 (.sib 4 none 0 (.d32 0xcc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x11d777 (movR64R64Effect 0x11d777 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 69) (.exec 0x11d777 (fun s => s.RIP = 0x11d777) (movR64R64Effect 0x11d777 0 1) (Reg.operands [.gpr 1] [])) #v[66]
    (.letOp (n := 70) (.out 0x11d77a (shlR64Effect 0x11d77a 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 71) (.exec 0x11d77a (fun s => s.RIP = 0x11d77a) (shlR64Effect 0x11d77a 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[68]
    (.letOp (n := 72) (.out 0x11d77e (leaR64Effect 0x11d77e 0 (.sib 0 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[70, 66]
    (.letOp (n := 73) (.exec 0x11d77e (fun s => s.RIP = 0x11d77e) (leaR64Effect 0x11d77e 0 (.sib 0 (some 1) 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[70, 66]
    (.letOp (n := 74) (.exec 0x11d782 (StorePre 0x11d782 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x268)) s (0x11d782 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d782 0 (.sib 4 none 0 (.d32 0x268))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x11d78a (movR64M64Effect 0x11d78a 1 (.sib 4 none 0 (.d32 0x1a0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 76) (.exec 0x11d78a (LoadPre 0x11d78a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x11d78a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d78a 1 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x11d792 (movR64R64Effect 0x11d792 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[75]
    (.letOp (n := 78) (.exec 0x11d792 (fun s => s.RIP = 0x11d792) (movR64R64Effect 0x11d792 0 1) (Reg.operands [.gpr 1] [])) #v[75]
    (.letOp (n := 79) (.out 0x11d795 (shlR64Effect 0x11d795 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[77]
    (.letOp (n := 80) (.exec 0x11d795 (fun s => s.RIP = 0x11d795) (shlR64Effect 0x11d795 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.out 0x11d799 (leaR64Effect 0x11d799 0 (.sib 0 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[79, 75]
    (.letOp (n := 82) (.exec 0x11d799 (fun s => s.RIP = 0x11d799) (leaR64Effect 0x11d799 0 (.sib 0 (some 1) 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[79, 75]
    (.letOp (n := 83) (.exec 0x11d79d (StorePre 0x11d79d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x258)) s (0x11d79d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d79d 0 (.sib 4 none 0 (.d32 0x258))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 84) (.out 0x11d7a5 (movR32Imm32Effect 0x11d7a5 5 1 0x20) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 85) (.exec 0x11d7a5 (fun s => s.RIP = 0x11d7a5) (movR32Imm32Effect 0x11d7a5 5 1 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 86) (.out 0x11d7aa (leaR64Effect 0x11d7aa 12 (.sib 4 none 0 (.d32 0x490))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 87) (.exec 0x11d7aa (fun s => s.RIP = 0x11d7aa) (leaR64Effect 0x11d7aa 12 (.sib 4 none 0 (.d32 0x490))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.out 0x11d7b2 (movR64Imm64Effect 0x11d7b2 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 89) (.exec 0x11d7b2 (fun s => s.RIP = 0x11d7b2) (movR64Imm64Effect 0x11d7b2 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (b_l11d748_1)))))))))))))))))))))))))))))))))))))

def bytes_l11d748 : List UInt8 :=
  [0x48, 0x8B, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x83, 0xC2, 0x40, 0x48, 0x8B, 0x8C, 0x24,
    0x00, 0x01, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x48, 0xC1, 0xE0, 0x06, 0x48, 0x8D, 0x04, 0x48, 0x48,
    0x89, 0x84, 0x24, 0x60, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0xC0, 0x0C, 0x00, 0x00, 0x48,
    0x89, 0xC8, 0x48, 0xC1, 0xE0, 0x06, 0x48, 0x8D, 0x04, 0x48, 0x48, 0x89, 0x84, 0x24, 0x68, 0x02,
    0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0xA0, 0x01, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x48, 0xC1, 0xE0,
    0x06, 0x48, 0x8D, 0x04, 0x48, 0x48, 0x89, 0x84, 0x24, 0x58, 0x02, 0x00, 0x00, 0xB9, 0x20, 0x00,
    0x00, 0x00, 0x4C, 0x8D, 0xA4, 0x24, 0x90, 0x04, 0x00, 0x00, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x00, 0x00] ++ bytes_l11d748_1

theorem code_l11d748 : ∀ x ∈ codeRange 0x11d748 bytes_l11d748, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1d748 116 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11d748_1

@[cfg_block] def b_l11d7d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d7d0 (movR64M64Effect 0x11d7d0 1 (.sib 4 none 0 (.d32 0x250))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x11d7d0 (LoadPre 0x11d7d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x250)) s (0x11d7d0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d7d0 1 (.sib 4 none 0 (.d32 0x250))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11d7d8 (decR64Effect 0x11d7d8 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x11d7d8 (fun s => s.RIP = 0x11d7d8) (decR64Effect 0x11d7d8 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x11d7db (movR64M64Effect 0x11d7db 2 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x11d7db (LoadPre 0x11d7db (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11d7db + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d7db 2 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x11d7e3 (decR64Effect 0x11d7e3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x11d7e3 (fun s => s.RIP = 0x11d7e3) (decR64Effect 0x11d7e3 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x11d7e6 (testR64R64Effect 0x11d7e6 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 62) (.exec 0x11d7e6 (fun s => s.RIP = 0x11d7e6) (testR64R64Effect 0x11d7e6 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 63) (.pure (condOp 4)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l11f6c4, RegMap.args [(1, 55), (2, 59), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l11d7ef, RegMap.args [(1, 55), (2, 59), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l11d7d0 : List UInt8 :=
  [0x48, 0x8B, 0x8C, 0x24, 0x50, 0x02, 0x00, 0x00, 0x48, 0xFF, 0xC9, 0x48, 0x8B, 0x94, 0x24, 0xF0,
    0x00, 0x00, 0x00, 0x48, 0xFF, 0xCA, 0x48, 0x85, 0xC9, 0x0F, 0x84, 0xD5, 0x1E, 0x00, 0x00]

theorem code_l11d7d0 : ∀ x ∈ codeRange 0x11d7d0 bytes_l11d7d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d7d0 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d7ef : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11d7ef (StorePre 0x11d7ef 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x250)) s (0x11d7ef + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d7ef 1 (.sib 4 none 0 (.d32 0x250))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 54) (.exec 0x11d7f7 (StorePre 0x11d7f7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x11d7f7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d7f7 2 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 55) (.out 0x11d7ff (movR32Imm32Effect 0x11d7ff 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x11d7ff (fun s => s.RIP = 0x11d7ff) (movR32Imm32Effect 0x11d7ff 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x11d804 (movR64Imm64Effect 0x11d804 5 0x1000003d10) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 58) (.exec 0x11d804 (fun s => s.RIP = 0x11d804) (movR64Imm64Effect 0x11d804 5 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x11d80e (fun s => s.RIP = 0x11d80e) (fun _ => nopEffect 0x11d80e 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l11d810, RegMap.args [(1, 55), (2, 2), (3, 3), (4, 4), (5, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l11d7ef : List UInt8 :=
  [0x48, 0x89, 0x8C, 0x24, 0x50, 0x02, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00,
    0xB9, 0x04, 0x00, 0x00, 0x00, 0x48, 0xBD, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x66,
    0x90]

theorem code_l11d7ef : ∀ x ∈ codeRange 0x11d7ef bytes_l11d7ef, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d7ef 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d810 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11d810 (StorePre 0x11d810 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1bc)) s (0x11d810 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x11d810 1 (.sib 4 none 0 (.d32 0x1bc))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 54) (.out 0x11d817 (leaR64Effect 0x11d817 7 (.sib 4 none 0 (.d32 0x850))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x11d817 (fun s => s.RIP = 0x11d817) (leaR64Effect 0x11d817 7 (.sib 4 none 0 (.d32 0x850))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x11d81f (leaR64Effect 0x11d81f 6 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 57) (.exec 0x11d81f (fun s => s.RIP = 0x11d81f) (leaR64Effect 0x11d81f 6 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x11d827 (callEffect (fun _ => 0x1145f0) 0x11d82c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 59) (.exec 0x11d827 (PushPre 0x11d827 5) (callEffect (fun _ => 0x1145f0) 0x11d82c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.const ⟨64, 0x11d82c⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(1, 1), (3, 3), (4, 58), (5, 5), (6, 56), (7, 54), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ { target := .l11d82c, kept := #v[], arity := rfl, guard := some (Fin.last 60) })))))))))

def bytes_l11d810 : List UInt8 :=
  [0x89, 0x8C, 0x24, 0xBC, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x50, 0x08, 0x00, 0x00, 0x48,
    0x8D, 0xB4, 0x24, 0x50, 0x01, 0x00, 0x00, 0xE8, 0xC4, 0x6D, 0xFF, 0xFF]

theorem code_l11d810 : ∀ x ∈ codeRange 0x11d810 bytes_l11d810, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d810 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11d82c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11d82c (movR64M64Effect 0x11d82c 0 (.sib 4 none 0 (.d32 0x850))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11d82c (LoadPre 0x11d82c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x850)) s (0x11d82c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d82c 0 (.sib 4 none 0 (.d32 0x850))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11d834 (StorePre 0x11d834 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11d834 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11d834 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11d83c (movR64M64Effect 0x11d83c 0 (.sib 4 none 0 (.d32 0x858))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11d83c (LoadPre 0x11d83c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x858)) s (0x11d83c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d83c 0 (.sib 4 none 0 (.d32 0x858))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11d844 (StorePre 0x11d844 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11d844 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d844 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11d849 (movR64M64Effect 0x11d849 0 (.sib 4 none 0 (.d32 0x860))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11d849 (LoadPre 0x11d849 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x860)) s (0x11d849 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d849 0 (.sib 4 none 0 (.d32 0x860))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11d851 (StorePre 0x11d851 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11d851 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d851 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11d856 (movR64M64Effect 0x11d856 0 (.sib 4 none 0 (.d32 0x868))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11d856 (LoadPre 0x11d856 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x868)) s (0x11d856 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d856 0 (.sib 4 none 0 (.d32 0x868))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x11d85e (StorePre 0x11d85e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11d85e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d85e 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x11d863 (movR64M64Effect 0x11d863 0 (.sib 4 none 0 (.d32 0x870))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x11d863 (LoadPre 0x11d863 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x870)) s (0x11d863 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11d863 0 (.sib 4 none 0 (.d32 0x870))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x11d86b (StorePre 0x11d86b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11d86b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11d86b 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x11d870 (movR64R64Effect 0x11d870 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 69) (.exec 0x11d870 (fun s => s.RIP = 0x11d870) (movR64R64Effect 0x11d870 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 70) (.out 0x11d873 (leaR64Effect 0x11d873 6 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x11d873 (fun s => s.RIP = 0x11d873) (leaR64Effect 0x11d873 6 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x11d87b (callEffect (fun _ => 0x1145f0) 0x11d880) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11d87b (PushPre 0x11d87b 5) (callEffect (fun _ => 0x1145f0) 0x11d880) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11d880⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 65), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11d880, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11d82c : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x50, 0x08, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x58, 0x08, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x84,
    0x24, 0x60, 0x08, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0x8B, 0x84, 0x24, 0x68, 0x08,
    0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x8B, 0x84, 0x24, 0x70, 0x08, 0x00, 0x00, 0x48,
    0x89, 0x44, 0x24, 0x40, 0x4C, 0x89, 0xE7, 0x48, 0x8D, 0xB4, 0x24, 0x78, 0x01, 0x00, 0x00, 0xE8,
    0x70, 0x6D, 0xFF, 0xFF]

theorem code_l11d82c : ∀ x ∈ codeRange 0x11d82c bytes_l11d82c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d82c 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Signing.LIR
