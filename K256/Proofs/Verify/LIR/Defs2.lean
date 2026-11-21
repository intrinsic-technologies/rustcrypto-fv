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

@[cfg_block] def b_l103306_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.exec 0x103358 (StorePre 0x103358 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x103358 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x103358 7 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 90) (.exec 0x10335f (StorePre 0x10335f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x10335f + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x10335f 8 (.sib 4 none 0 (.d32 0x94))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 91) (.exec 0x103367 (StorePre 0x103367 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x103367 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x103367 9 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 92) (.exec 0x10336f (StorePre 0x10336f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x10336f + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x10336f 10 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 93) (.out 0x103377 (leaR64Effect 0x103377 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 94) (.exec 0x103377 (fun s => s.RIP = 0x103377) (leaR64Effect 0x103377 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x10337f (leaR64Effect 0x10337f 6 (.sib 4 none 0 (.d32 0x1a0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 96) (.exec 0x10337f (fun s => s.RIP = 0x10337f) (leaR64Effect 0x10337f 6 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.out 0x103387 (movR32Imm32Effect 0x103387 5 1 0xb) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 98) (.exec 0x103387 (fun s => s.RIP = 0x103387) (movR32Imm32Effect 0x103387 5 1 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 99) (.out 0x10338c (movR64R64Effect 0x10338c 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[93]
    (.letOp (n := 100) (.exec 0x10338c (fun s => s.RIP = 0x10338c) (movR64R64Effect 0x10338c 7 0) (Reg.operands [.gpr 0] [])) #v[93]
    (.letOp (n := 101) (.out 0x10338f (repMovsqEffect 0x10338f) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[95, 99, 97, 22]
    (.letOp (n := 102) (.exec 0x10338f (RepPre 0x10338f (RepMovsqPre 0x10338f)) (repMovsqEffect 0x10338f) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[95, 99, 97, 22]
    (.letOp (n := 103) (.out 0x103392 (leaR64Effect 0x103392 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 104) (.exec 0x103392 (fun s => s.RIP = 0x103392) (leaR64Effect 0x103392 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.out 0x103397 (movR64R64Effect 0x103397 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[103]
    (.letOp (n := 106) (.exec 0x103397 (fun s => s.RIP = 0x103397) (movR64R64Effect 0x103397 7 3) (Reg.operands [.gpr 3] [])) #v[103]
    (.letOp (n := 107) (.out 0x10339a (movR64R64Effect 0x10339a 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[93]
    (.letOp (n := 108) (.exec 0x10339a (fun s => s.RIP = 0x10339a) (movR64R64Effect 0x10339a 6 0) (Reg.operands [.gpr 0] [])) #v[93]
    (.letOp (n := 109) (.out 0x10339d (callEffect (fun _ => 0x10fa10) 0x1033a2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 110) (.exec 0x10339d (PushPre 0x10339d 5) (callEffect (fun _ => 0x10fa10) 0x1033a2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 111) (.const ⟨64, 0x1033a2⟩) #v[]
    (.terminate (.call ⟨.l10fa10, RegMap.args [(0, 93), (1, 101), (2, 63), (3, 103), (4, 109), (5, 5), (6, 107), (7, 105), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 112⟩ { target := .l1033a2, kept := #v[], arity := rfl, guard := some (Fin.last 111) }))))))))))))))))))))))))

def bytes_l103306_1 : List UInt8 :=
  [0x89, 0xBC, 0x24, 0x90, 0x00, 0x00, 0x00, 0x44, 0x89, 0x84, 0x24, 0x94, 0x00, 0x00, 0x00, 0x44,
    0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x44, 0x89, 0x94, 0x24, 0x9C, 0x00, 0x00, 0x00, 0x48,
    0x8D, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x01, 0x00, 0x00, 0xB9,
    0x0B, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC7, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0x5C, 0x24, 0x08, 0x48,
    0x89, 0xDF, 0x48, 0x89, 0xC6, 0xE8, 0x6E, 0xC6, 0x00, 0x00]

theorem code_l103306_1 : ∀ x ∈ codeRange 0x103358 bytes_l103306_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3358 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103306 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103306 (movR32M32LowEffect 0x103306 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x103306 (LoadPre 0x103306 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103306 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103306 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10330a (movR32M32LowEffect 0x10330a 1 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x10330a (LoadPre 0x10330a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x10330a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10330a 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10330e (bswapR32Effect 0x10330e 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 58) (.exec 0x10330e (fun s => s.RIP = 0x10330e) (bswapR32Effect 0x10330e 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x103310 (bswapR32Effect 0x103310 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 60) (.exec 0x103310 (fun s => s.RIP = 0x103310) (bswapR32Effect 0x103310 2 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 61) (.out 0x103312 (movR32M32LowEffect 0x103312 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x103312 (LoadPre 0x103312 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x103312 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103312 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x103316 (bswapR32Effect 0x103316 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 64) (.exec 0x103316 (fun s => s.RIP = 0x103316) (bswapR32Effect 0x103316 2 2) (Reg.operands [.gpr 2] [])) #v[61]
    (.letOp (n := 65) (.out 0x103318 (movR32M32LowEffect 0x103318 6 (.sib 4 none 0 (.d8 0x54))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x103318 (LoadPre 0x103318 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x103318 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103318 6 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x10331c (bswapR32Effect 0x10331c 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 68) (.exec 0x10331c (fun s => s.RIP = 0x10331c) (bswapR32Effect 0x10331c 2 6) (Reg.operands [.gpr 6] [])) #v[65]
    (.letOp (n := 69) (.out 0x10331e (movR32M32LowEffect 0x10331e 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x10331e (LoadPre 0x10331e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10331e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10331e 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x103322 (bswapR32Effect 0x103322 2 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[69]
    (.letOp (n := 72) (.exec 0x103322 (fun s => s.RIP = 0x103322) (bswapR32Effect 0x103322 2 7) (Reg.operands [.gpr 7] [])) #v[69]
    (.letOp (n := 73) (.out 0x103324 (movR32M32Effect 0x103324 8 (.sib 4 none 0 (.d8 0x5c))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 74) (.exec 0x103324 (LoadPre 0x103324 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x103324 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x103324 8 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x103329 (bswapR32Effect 0x103329 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[73]
    (.letOp (n := 76) (.exec 0x103329 (fun s => s.RIP = 0x103329) (bswapR32Effect 0x103329 3 8) (Reg.operands [.gpr 8] [])) #v[73]
    (.letOp (n := 77) (.out 0x10332c (movR32M32Effect 0x10332c 9 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 78) (.exec 0x10332c (LoadPre 0x10332c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10332c + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x10332c 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x103331 (bswapR32Effect 0x103331 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[77]
    (.letOp (n := 80) (.exec 0x103331 (fun s => s.RIP = 0x103331) (bswapR32Effect 0x103331 3 9) (Reg.operands [.gpr 9] [])) #v[77]
    (.letOp (n := 81) (.out 0x103334 (movR32M32Effect 0x103334 10 (.sib 4 none 0 (.d8 0x64))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 82) (.exec 0x103334 (LoadPre 0x103334 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x103334 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x103334 10 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x103339 (bswapR32Effect 0x103339 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[81]
    (.letOp (n := 84) (.exec 0x103339 (fun s => s.RIP = 0x103339) (bswapR32Effect 0x103339 3 10) (Reg.operands [.gpr 10] [])) #v[81]
    (.letOp (n := 85) (.exec 0x10333c (StorePre 0x10333c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10333c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10333c 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 86) (.exec 0x103343 (StorePre 0x103343 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x103343 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x103343 1 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 87) (.exec 0x10334a (StorePre 0x10334a 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10334a + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10334a 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 88) (.exec 0x103351 (StorePre 0x103351 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x103351 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x103351 6 (.sib 4 none 0 (.d32 0x8c))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[67, 4]
    (b_l103306_1))))))))))))))))))))))))))))))))))))

def bytes_l103306 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x48, 0x8B, 0x4C, 0x24, 0x4C, 0x0F, 0xC8, 0x0F, 0xC9, 0x8B, 0x54, 0x24, 0x50,
    0x0F, 0xCA, 0x8B, 0x74, 0x24, 0x54, 0x0F, 0xCE, 0x8B, 0x7C, 0x24, 0x58, 0x0F, 0xCF, 0x44, 0x8B,
    0x44, 0x24, 0x5C, 0x41, 0x0F, 0xC8, 0x44, 0x8B, 0x4C, 0x24, 0x60, 0x41, 0x0F, 0xC9, 0x44, 0x8B,
    0x54, 0x24, 0x64, 0x41, 0x0F, 0xCA, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x89, 0x8C, 0x24,
    0x84, 0x00, 0x00, 0x00, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x89, 0xB4, 0x24, 0x8C, 0x00,
    0x00, 0x00] ++ bytes_l103306_1

theorem code_l103306 : ∀ x ∈ codeRange 0x103306 bytes_l103306, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x3306 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l103306_1

@[cfg_block] def b_l1033a2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1033a2 (leaR64Effect 0x1033a2 7 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1033a2 (fun s => s.RIP = 0x1033a2) (leaR64Effect 0x1033a2 7 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1033aa (leaR64Effect 0x1033aa 2 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x1033aa (fun s => s.RIP = 0x1033aa) (leaR64Effect 0x1033aa 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1033b2 (leaR64Effect 0x1033b2 8 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 58) (.exec 0x1033b2 (fun s => s.RIP = 0x1033b2) (leaR64Effect 0x1033b2 8 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1033ba (movR32Imm32Effect 0x1033ba 5 1 0x20) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x1033ba (fun s => s.RIP = 0x1033ba) (movR32Imm32Effect 0x1033ba 5 1 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x1033bf (movR64R64Effect 0x1033bf 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 62) (.exec 0x1033bf (fun s => s.RIP = 0x1033bf) (movR64R64Effect 0x1033bf 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 63) (.out 0x1033c2 (callEffect (fun _ => 0x104f20) 0x1033c7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x1033c2 (PushPre 0x1033c2 5) (callEffect (fun _ => 0x104f20) 0x1033c7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x1033c7⟩) #v[]
    (.terminate (.call ⟨.l104f20, RegMap.args [(1, 59), (2, 55), (3, 3), (4, 63), (5, 5), (6, 61), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l1033c7, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l1033a2 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x4C, 0x8D, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00, 0xB9, 0x20, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDE,
    0xE8, 0x59, 0x1B, 0x00, 0x00]

theorem code_l1033a2 : ∀ x ∈ codeRange 0x1033a2 bytes_l1033a2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x33a2 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1033c7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1033c7 (movR64M64Effect 0x1033c7 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1033c7 (LoadPre 0x1033c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1033c7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1033c7 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1033cf (testR64R64Effect 0x1033cf 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 56) (.exec 0x1033cf (fun s => s.RIP = 0x1033cf) (testR64R64Effect 0x1033cf 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1033f9, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1033d4, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1033c7 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x85, 0xC0, 0x74, 0x25]

theorem code_l1033c7 : ∀ x ∈ codeRange 0x1033c7 bytes_l1033c7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x33c7 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1033d4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1033d4 (movR64M64Effect 0x1033d4 7 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1033d4 (LoadPre 0x1033d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1033d4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1033d4 7 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1033dc (testR64R64Effect 0x1033dc 7 7) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 7] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 56) (.exec 0x1033dc (fun s => s.RIP = 0x1033dc) (testR64R64Effect 0x1033dc 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[53, 53]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1033f9, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1033e1, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1033d4 : List UInt8 :=
  [0x48, 0x8B, 0xBC, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x85, 0xFF, 0x74, 0x18]

theorem code_l1033d4 : ∀ x ∈ codeRange 0x1033d4 bytes_l1033d4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x33d4 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1033e1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1033e1 (movR64M64Effect 0x1033e1 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1033e1 (LoadPre 0x1033e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1033e1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1033e1 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1033e9 (movR64M64Effect 0x1033e9 1 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x1033e9 (LoadPre 0x1033e9 (fun s => AddrMode.addr (.base 1 .none) s (0x1033e9 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1033e9 1 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x1033ec (testR64R64Effect 0x1033ec 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 58) (.exec 0x1033ec (fun s => s.RIP = 0x1033ec) (testR64R64Effect 0x1033ec 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1033f9, RegMap.args [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1033f1, RegMap.args [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1033e1 : List UInt8 :=
  [0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x09, 0x48, 0x85, 0xC9, 0x74, 0x08]

theorem code_l1033e1 : ∀ x ∈ codeRange 0x1033e1 bytes_l1033e1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x33e1 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1033f1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1033f1 (fun s => s.RIP = 0x1033f1) (movR64R64Effect 0x1033f1 3 0) (Reg.operands [.gpr 0] [])) #v[0]
    (cutBlock 0x1033f4)

def bytes_l1033f1 : List UInt8 :=
  [0x48, 0x89, 0xC3, 0xFF, 0xD1]

theorem code_l1033f1 : ∀ x ∈ codeRange 0x1033f1 bytes_l1033f1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x33f1 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1033f6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1033f6 (movR64R64Effect 0x1033f6 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1033f6 (fun s => s.RIP = 0x1033f6) (movR64R64Effect 0x1033f6 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l1033f9, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1033f6 : List UInt8 :=
  [0x48, 0x89, 0xD8]

theorem code_l1033f6 : ∀ x ∈ codeRange 0x1033f6 bytes_l1033f6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x33f6 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1033f9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1033f9 (addR64Imm32Effect 0x1033f9 4 0x1f8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x1033f9 (fun s => s.RIP = 0x1033f9) (addR64Imm32Effect 0x1033f9 4 0x1f8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x103400 (popR64Effect 0x103400 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x103400 (popR64Effect 0x103400 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x103400 (PopPre 0x103400) (popR64Effect 0x103400 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x103401 (popR64Effect 0x103401 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x103401 (popR64Effect 0x103401 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x103401 (PopPre 0x103401) (popR64Effect 0x103401 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x103403 (popR64Effect 0x103403 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[59]
    (.letOp (n := 62) (.out 0x103403 (popR64Effect 0x103403 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x103403 (PopPre 0x103403) (popR64Effect 0x103403 2 14) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x103405 (popR64Effect 0x103405 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[62]
    (.letOp (n := 65) (.out 0x103405 (popR64Effect 0x103405 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x103405 (PopPre 0x103405) (popR64Effect 0x103405 2 15) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x103407 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[65]
    (.letOp (n := 68) (.out 0x103407 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x103407 (RetPre 0x103407) (retEffect) (Reg.operands [.gpr 4] [])) #v[65]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 70) (some ⟨67, by decide⟩)))))))))))))))))))

def bytes_l1033f9 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0xF8, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5E, 0x41, 0x5F, 0xC3]

theorem code_l1033f9 : ∀ x ∈ codeRange 0x1033f9 bytes_l1033f9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x33f9 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103408 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103408 (StorePre 0x103408 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x103408 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103408 (.sib 4 none 0 (.d32 0x100)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x103414 (StorePre 0x103414 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x103414 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103414 (.sib 4 none 0 (.d32 0xf8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x103420 (leaR64Effect 0x103420 7 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x103420 (fun s => s.RIP = 0x103420) (leaR64Effect 0x103420 7 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x103428 (callEffect (fun _ => 0x100240) 0x10342d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x103428 (PushPre 0x103428 5) (callEffect (fun _ => 0x100240) 0x10342d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x10342d⟩) #v[]
    (.terminate (.call ⟨.l100240, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l10342d, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l103408 : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0xF8, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0xF8, 0x00, 0x00, 0x00,
    0xE8, 0x13, 0xCE, 0xFF, 0xFF]

theorem code_l103408 : ∀ x ∈ codeRange 0x103408 bytes_l103408, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3408 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10342d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10342d (PushPre 0x10342d 5) (callEffect (fun _ => 0x100a30) 0x103432) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.const ⟨64, 0x103432⟩) #v[]
    (.terminate (.call ⟨.l100a30, RegMap.args [] 55⟩ { target := .l103432, kept := #v[], arity := rfl, guard := some (Fin.last 54) })))

def bytes_l10342d : List UInt8 :=
  [0xE8, 0xFE, 0xD5, 0xFF, 0xFF]

theorem code_l10342d : ∀ x ∈ codeRange 0x10342d bytes_l10342d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x342d 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103432 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103432 (leaR64Effect 0x103432 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x103432 (fun s => s.RIP = 0x103432) (leaR64Effect 0x103432 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x103437 (callEffect (fun _ => 0x100180) 0x10343c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x103437 (PushPre 0x103437 5) (callEffect (fun _ => 0x100180) 0x10343c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x10343c⟩) #v[]
    (.terminate (.call ⟨.l100180, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l10343c, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l103432 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0xE8, 0x44, 0xCD, 0xFF, 0xFF]

theorem code_l103432 : ∀ x ∈ codeRange 0x103432 bytes_l103432, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3432 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10343c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10343c (PushPre 0x10343c 5) (callEffect (fun _ => 0x100a30) 0x103441) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.const ⟨64, 0x103441⟩) #v[]
    (.terminate (.call ⟨.l100a30, RegMap.args [] 55⟩ { target := .l103441, kept := #v[], arity := rfl, guard := some (Fin.last 54) })))

def bytes_l10343c : List UInt8 :=
  [0xE8, 0xEF, 0xD5, 0xFF, 0xFF]

theorem code_l10343c : ∀ x ∈ codeRange 0x10343c bytes_l10343c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x343c 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103441 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103441 (fun s => s.RIP = 0x103441) (fun _ => nopEffect 0x103441 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x10344b (fun s => s.RIP = 0x10344b) (fun _ => nopEffect 0x10344b 5) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103450, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l103441 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l103441 : ∀ x ∈ codeRange 0x103441 bytes_l103441, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3441 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103450 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103450 (pushR64Effect 0x103450 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x103450 (PushPre 0x103450 2) (pushR64Effect 0x103450 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x103452 (pushR64Effect 0x103452 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x103452 (PushPre 0x103452 2) (pushR64Effect 0x103452 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x103454 (pushR64Effect 0x103454 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[55, 3]
    (.letOp (n := 58) (.exec 0x103454 (PushPre 0x103454 1) (pushR64Effect 0x103454 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 59) (.out 0x103455 (subR64Imm32Effect 0x103455 4 0xc0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x103455 (fun s => s.RIP = 0x103455) (subR64Imm32Effect 0x103455 4 0xc0) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x10345c (movR64R64Effect 0x10345c 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 62) (.exec 0x10345c (fun s => s.RIP = 0x10345c) (movR64R64Effect 0x10345c 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 63) (.out 0x10345f (movR64R64Effect 0x10345f 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 64) (.exec 0x10345f (fun s => s.RIP = 0x10345f) (movR64R64Effect 0x10345f 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 65) (.out 0x103462 (leaR64Effect 0x103462 15 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[59]
    (.letOp (n := 66) (.exec 0x103462 (fun s => s.RIP = 0x103462) (leaR64Effect 0x103462 15 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 67) (.out 0x10346a (movR64R64Effect 0x10346a 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 68) (.exec 0x10346a (fun s => s.RIP = 0x10346a) (movR64R64Effect 0x10346a 7 15) (Reg.operands [.gpr 15] [])) #v[65]
    (.letOp (n := 69) (.out 0x10346d (callEffect (fun _ => 0x11c3c0) 0x103472) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 70) (.exec 0x10346d (PushPre 0x10346d 5) (callEffect (fun _ => 0x11c3c0) 0x103472) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 71) (.const ⟨64, 0x103472⟩) #v[]
    (.terminate (.call ⟨.l11c3c0, RegMap.args [(2, 2), (3, 63), (4, 69), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l103472, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l103450 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x53, 0x48, 0x81, 0xEC, 0xC0, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD6, 0x48,
    0x89, 0xFB, 0x4C, 0x8D, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0xE8, 0x4E, 0x8F,
    0x01, 0x00]

theorem code_l103450 : ∀ x ∈ codeRange 0x103450 bytes_l103450, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3450 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103472 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103472 (movR64R64Effect 0x103472 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x103472 (fun s => s.RIP = 0x103472) (movR64R64Effect 0x103472 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x103475 (movR32Imm32Effect 0x103475 5 2 0x20) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x103475 (fun s => s.RIP = 0x103475) (movR32Imm32Effect 0x103475 5 2 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10347a (movR64R64Effect 0x10347a 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x10347a (fun s => s.RIP = 0x10347a) (movR64R64Effect 0x10347a 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x10347d (callEffect (fun _ => 0x107730) 0x103482) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10347d (PushPre 0x10347d 5) (callEffect (fun _ => 0x107730) 0x103482) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x103482⟩) #v[]
    (.terminate (.call ⟨.l107730, RegMap.args [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l103482, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l103472 : List UInt8 :=
  [0x48, 0x89, 0xE7, 0xBA, 0x20, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFE, 0xE8, 0xAE, 0x42, 0x00, 0x00]

theorem code_l103472 : ∀ x ∈ codeRange 0x103472 bytes_l103472, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3472 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103482 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103482 (cmpMImm8Effect 0x103482 4 32 (.sib 4 none 0 .none) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x103482 (LoadPre 0x103482 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103482 + BitVec.ofNat 64 4)) 4) (cmpMImm8Effect 0x103482 4 32 (.sib 4 none 0 .none) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1035cd, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10348c, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103482 : List UInt8 :=
  [0x83, 0x3C, 0x24, 0x01, 0x0F, 0x84, 0x41, 0x01, 0x00, 0x00]

theorem code_l103482 : ∀ x ∈ codeRange 0x103482 bytes_l103482, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3482 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10348c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10348c (movR64M64Effect 0x10348c 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10348c (LoadPre 0x10348c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10348c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10348c 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x103491 (movR64M64Effect 0x103491 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x103491 (LoadPre 0x103491 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103491 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103491 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x103496 (movR64M64Effect 0x103496 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x103496 (LoadPre 0x103496 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103496 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103496 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x10349b (StorePre 0x10349b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10349b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10349b 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x1034a0 (movR64M64Effect 0x1034a0 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 61) (.exec 0x1034a0 (LoadPre 0x1034a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1034a0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1034a0 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x1034a5 (StorePre 0x1034a5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1034a5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1034a5 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.exec 0x1034aa (StorePre 0x1034aa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1034aa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1034aa 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 64) (.exec 0x1034af (StorePre 0x1034af 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1034af + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1034af 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 65) (.out 0x1034b4 (movR64M64Effect 0x1034b4 0 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 66) (.exec 0x1034b4 (LoadPre 0x1034b4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1034b4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034b4 0 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 67) (.exec 0x1034b8 (StorePre 0x1034b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1034b8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1034b8 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1034c0 (movR64M64Effect 0x1034c0 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 69) (.exec 0x1034c0 (LoadPre 0x1034c0 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1034c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034c0 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 70) (.exec 0x1034c4 (StorePre 0x1034c4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1034c4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1034c4 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x1034cc (movR64M64Effect 0x1034cc 0 (.base 14 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 72) (.exec 0x1034cc (LoadPre 0x1034cc (fun s => AddrMode.addr (.base 14 .none) s (0x1034cc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1034cc 0 (.base 14 .none)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 73) (.out 0x1034cf (movR64M64Effect 0x1034cf 1 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 74) (.exec 0x1034cf (LoadPre 0x1034cf (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1034cf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034cf 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 75) (.exec 0x1034d3 (StorePre 0x1034d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1034d3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1034d3 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.exec 0x1034db (StorePre 0x1034db 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1034db + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1034db 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 77) (.out 0x1034e3 (leaR64Effect 0x1034e3 14 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 78) (.exec 0x1034e3 (fun s => s.RIP = 0x1034e3) (leaR64Effect 0x1034e3 14 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x1034eb (leaR64Effect 0x1034eb 6 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 80) (.exec 0x1034eb (fun s => s.RIP = 0x1034eb) (leaR64Effect 0x1034eb 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x1034f3 (movR64R64Effect 0x1034f3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[77]
    (.letOp (n := 82) (.exec 0x1034f3 (fun s => s.RIP = 0x1034f3) (movR64R64Effect 0x1034f3 7 14) (Reg.operands [.gpr 14] [])) #v[77]
    (.letOp (n := 83) (.out 0x1034f6 (callEffect (fun _ => 0x11c3c0) 0x1034fb) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x1034f6 (PushPre 0x1034f6 5) (callEffect (fun _ => 0x11c3c0) 0x1034fb) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.const ⟨64, 0x1034fb⟩) #v[]
    (.terminate (.call ⟨.l11c3c0, RegMap.args [(0, 71), (1, 73), (2, 60), (3, 3), (4, 83), (5, 5), (6, 79), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l1034fb, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l10348c : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x8B, 0x54, 0x24, 0x18, 0x48,
    0x89, 0x54, 0x24, 0x50, 0x48, 0x8B, 0x54, 0x24, 0x20, 0x48, 0x89, 0x54, 0x24, 0x58, 0x48, 0x89,
    0x44, 0x24, 0x40, 0x48, 0x89, 0x4C, 0x24, 0x48, 0x49, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x84, 0x24,
    0x98, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x49, 0x8B, 0x06, 0x49, 0x8B, 0x4E, 0x08, 0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48,
    0x8D, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0xE8, 0xC5, 0x8E, 0x01, 0x00]

theorem code_l10348c : ∀ x ∈ codeRange 0x10348c bytes_l10348c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x348c 111 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1034fb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1034fb (movR64R64Effect 0x1034fb 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1034fb (fun s => s.RIP = 0x1034fb) (movR64R64Effect 0x1034fb 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1034fe (movR32Imm32Effect 0x1034fe 5 2 0x20) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x1034fe (fun s => s.RIP = 0x1034fe) (movR32Imm32Effect 0x1034fe 5 2 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x103503 (movR64R64Effect 0x103503 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x103503 (fun s => s.RIP = 0x103503) (movR64R64Effect 0x103503 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x103506 (callEffect (fun _ => 0x107730) 0x10350b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x103506 (PushPre 0x103506 5) (callEffect (fun _ => 0x107730) 0x10350b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10350b⟩) #v[]
    (.terminate (.call ⟨.l107730, RegMap.args [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10350b, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1034fb : List UInt8 :=
  [0x48, 0x89, 0xE7, 0xBA, 0x20, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xE8, 0x25, 0x42, 0x00, 0x00]

theorem code_l1034fb : ∀ x ∈ codeRange 0x1034fb bytes_l1034fb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x34fb 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10350b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10350b (cmpMImm8Effect 0x10350b 4 32 (.sib 4 none 0 .none) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x10350b (LoadPre 0x10350b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10350b + BitVec.ofNat 64 4)) 4) (cmpMImm8Effect 0x10350b 4 32 (.sib 4 none 0 .none) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1035cd, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l103515, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10350b : List UInt8 :=
  [0x83, 0x3C, 0x24, 0x01, 0x0F, 0x84, 0xB8, 0x00, 0x00, 0x00]

theorem code_l10350b : ∀ x ∈ codeRange 0x10350b bytes_l10350b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x350b 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103515 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103515 (movR64M64Effect 0x103515 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x103515 (LoadPre 0x103515 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103515 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103515 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10351a (movR64M64Effect 0x10351a 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x10351a (LoadPre 0x10351a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10351a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10351a 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10351f (movR64M64Effect 0x10351f 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x10351f (LoadPre 0x10351f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10351f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10351f 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x103524 (StorePre 0x103524 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x103524 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103524 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x103529 (movR64M64Effect 0x103529 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 61) (.exec 0x103529 (LoadPre 0x103529 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103529 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103529 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x10352e (StorePre 0x10352e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10352e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10352e 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.exec 0x103533 (StorePre 0x103533 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x103533 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103533 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 64) (.exec 0x103538 (StorePre 0x103538 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x103538 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103538 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 65) (.exec 0x10353d (StorePre 0x10353d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10353d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10353d (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x103546 (StorePre 0x103546 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103546 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103546 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x10354f (StorePre 0x10354f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10354f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10354f (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x103558 (StorePre 0x103558 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103558 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x103558 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x103560 (leaR64Effect 0x103560 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x103560 (fun s => s.RIP = 0x103560) (leaR64Effect 0x103560 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x103565 (movR64R64Effect 0x103565 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 72) (.exec 0x103565 (fun s => s.RIP = 0x103565) (movR64R64Effect 0x103565 2 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x103568 (movR32Imm32Effect 0x103568 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 74) (.exec 0x103568 (fun s => s.RIP = 0x103568) (movR32Imm32Effect 0x103568 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x10356d (movR32Imm32Effect 0x10356d 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 76) (.exec 0x10356d (fun s => s.RIP = 0x10356d) (movR32Imm32Effect 0x10356d 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x103572 (callEffect (fun _ => 0x127f50) 0x103577) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 78) (.exec 0x103572 (PushPre 0x103572 5) (callEffect (fun _ => 0x127f50) 0x103577) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.const ⟨64, 0x103577⟩) #v[]
    (.terminate (.call ⟨.l127f50, RegMap.args [(0, 53), (1, 75), (2, 71), (3, 3), (4, 77), (5, 5), (6, 73), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩ { target := .l103577, kept := #v[], arity := rfl, guard := some (Fin.last 79) }))))))))))))))))))))))))))))

def bytes_l103515 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x8B, 0x54, 0x24, 0x18, 0x48,
    0x89, 0x54, 0x24, 0x70, 0x48, 0x8B, 0x54, 0x24, 0x20, 0x48, 0x89, 0x54, 0x24, 0x78, 0x48, 0x89,
    0x44, 0x24, 0x60, 0x48, 0x89, 0x4C, 0x24, 0x68, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00,
    0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00,
    0x00, 0x00, 0x00, 0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x40,
    0x48, 0x89, 0xE2, 0xBE, 0x04, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0xE8, 0xD9, 0x49,
    0x02, 0x00]

theorem code_l103515 : ∀ x ∈ codeRange 0x103515 bytes_l103515, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3515 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103577 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103577 (andAlImm8Effect 0x103577 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x103577 (fun s => s.RIP = 0x103577) (andAlImm8Effect 0x103577 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x103579 (movzxR32R8Effect 0x103579 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x103579 (fun s => s.RIP = 0x103579) (movzxR32R8Effect 0x103579 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x10357c (callEffect (fun _ => 0x127d50) 0x103581) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10357c (PushPre 0x10357c 5) (callEffect (fun _ => 0x127d50) 0x103581) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x103581⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l103581, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l103577 : List UInt8 :=
  [0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0xCF, 0x47, 0x02, 0x00]

theorem code_l103577 : ∀ x ∈ codeRange 0x103577 bytes_l103577, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3577 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103581 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103581 (testR8R8Effect 0x103581 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x103581 (fun s => s.RIP = 0x103581) (testR8R8Effect 0x103581 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1035cd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l103585, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103581 : List UInt8 :=
  [0x84, 0xC0, 0x75, 0x48]

theorem code_l103581 : ∀ x ∈ codeRange 0x103581 bytes_l103581, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3581 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103585 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103585 (StorePre 0x103585 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103585 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103585 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x10358e (StorePre 0x10358e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10358e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10358e (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x103597 (StorePre 0x103597 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103597 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103597 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1035a0 (StorePre 0x1035a0 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1035a0 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1035a0 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1035a8 (leaR64Effect 0x1035a8 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x1035a8 (fun s => s.RIP = 0x1035a8) (leaR64Effect 0x1035a8 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1035ad (movR64R64Effect 0x1035ad 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x1035ad (fun s => s.RIP = 0x1035ad) (movR64R64Effect 0x1035ad 2 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1035b0 (movR32Imm32Effect 0x1035b0 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 62) (.exec 0x1035b0 (fun s => s.RIP = 0x1035b0) (movR32Imm32Effect 0x1035b0 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x1035b5 (movR32Imm32Effect 0x1035b5 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 64) (.exec 0x1035b5 (fun s => s.RIP = 0x1035b5) (movR32Imm32Effect 0x1035b5 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x1035ba (callEffect (fun _ => 0x127f50) 0x1035bf) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x1035ba (PushPre 0x1035ba 5) (callEffect (fun _ => 0x127f50) 0x1035bf) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x1035bf⟩) #v[]
    (.terminate (.call ⟨.l127f50, RegMap.args [(0, 0), (1, 63), (2, 59), (3, 3), (4, 65), (5, 5), (6, 61), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l1035bf, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l103585 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x04, 0x24, 0x00,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x60, 0x48, 0x89, 0xE2, 0xBE, 0x04, 0x00, 0x00, 0x00,
    0xB9, 0x04, 0x00, 0x00, 0x00, 0xE8, 0x91, 0x49, 0x02, 0x00]

theorem code_l103585 : ∀ x ∈ codeRange 0x103585 bytes_l103585, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3585 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1035bf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1035bf (andAlImm8Effect 0x1035bf 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x1035bf (fun s => s.RIP = 0x1035bf) (andAlImm8Effect 0x1035bf 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1035c1 (movzxR32R8Effect 0x1035c1 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x1035c1 (fun s => s.RIP = 0x1035c1) (movzxR32R8Effect 0x1035c1 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1035c4 (callEffect (fun _ => 0x127d50) 0x1035c9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1035c4 (PushPre 0x1035c4 5) (callEffect (fun _ => 0x127d50) 0x1035c9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1035c9⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l1035c9, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1035bf : List UInt8 :=
  [0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x87, 0x47, 0x02, 0x00]

theorem code_l1035bf : ∀ x ∈ codeRange 0x1035bf bytes_l1035bf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x35bf 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1035c9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1035c9 (testR8R8Effect 0x1035c9 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1035c9 (fun s => s.RIP = 0x1035c9) (testR8R8Effect 0x1035c9 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1035ec, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1035cd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1035c9 : List UInt8 :=
  [0x84, 0xC0, 0x74, 0x1F]

theorem code_l1035c9 : ∀ x ∈ codeRange 0x1035c9 bytes_l1035c9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x35c9 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1035cd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1035cd (StorePre 0x1035cd 8 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1035cd + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1035cd (.base 3 (.d8 0x8)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 54) (.exec 0x1035d5 (StorePre 0x1035d5 7 (fun s => AddrMode.addr (.base 3 .none) s (0x1035d5 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x1035d5 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l1035dc, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1035cd : List UInt8 :=
  [0x48, 0xC7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00]

theorem code_l1035cd : ∀ x ∈ codeRange 0x1035cd bytes_l1035cd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x35cd 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1035dc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1035dc (movR64R64Effect 0x1035dc 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1035dc (fun s => s.RIP = 0x1035dc) (movR64R64Effect 0x1035dc 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1035df (addR64Imm32Effect 0x1035df 4 0xc0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x1035df (fun s => s.RIP = 0x1035df) (addR64Imm32Effect 0x1035df 4 0xc0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1035e6 (popR64Effect 0x1035e6 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x1035e6 (popR64Effect 0x1035e6 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x1035e6 (PopPre 0x1035e6) (popR64Effect 0x1035e6 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x1035e7 (popR64Effect 0x1035e7 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.out 0x1035e7 (popR64Effect 0x1035e7 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x1035e7 (PopPre 0x1035e7) (popR64Effect 0x1035e7 2 14) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x1035e9 (popR64Effect 0x1035e9 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[61]
    (.letOp (n := 64) (.out 0x1035e9 (popR64Effect 0x1035e9 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x1035e9 (PopPre 0x1035e9) (popR64Effect 0x1035e9 2 15) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x1035eb (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[64]
    (.letOp (n := 67) (.out 0x1035eb (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x1035eb (RetPre 0x1035eb) (retEffect) (Reg.operands [.gpr 4] [])) #v[64]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 69) (some ⟨66, by decide⟩))))))))))))))))))

def bytes_l1035dc : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xC0, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5E, 0x41, 0x5F, 0xC3]

theorem code_l1035dc : ∀ x ∈ codeRange 0x1035dc bytes_l1035dc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x35dc 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1035ec_1 : Block Op Label signature Reg.count 81 :=
  .letOp (n := 81) (.exec 0x10364b (StorePre 0x10364b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10364b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10364b 0 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 82) (.exec 0x10364f (StorePre 0x10364f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10364f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10364f 1 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 83) (.exec 0x103653 (StorePre 0x103653 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x103653 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103653 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 84) (.exec 0x103657 (StorePre 0x103657 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x103657 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103657 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 85) (.exec 0x10365b (StorePre 0x10365b 7 (fun s => AddrMode.addr (.base 3 .none) s (0x10365b + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x10365b (.base 3 .none) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l1035dc, RegMap.args [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩))))))

def bytes_l1035ec_1 : List UInt8 :=
  [0x48, 0x89, 0x43, 0x20, 0x48, 0x89, 0x4B, 0x18, 0x48, 0x89, 0x73, 0x10, 0x48, 0x89, 0x53, 0x08,
    0x48, 0xC7, 0x03, 0x00, 0x00, 0x00, 0x00, 0xE9, 0x75, 0xFF, 0xFF, 0xFF]

theorem code_l1035ec_1 : ∀ x ∈ codeRange 0x10364b bytes_l1035ec_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x364b 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1035ec : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1035ec (movR64M64Effect 0x1035ec 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1035ec (LoadPre 0x1035ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1035ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1035ec 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1035f1 (StorePre 0x1035f1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1035f1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1035f1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1035f6 (movR64M64Effect 0x1035f6 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x1035f6 (LoadPre 0x1035f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1035f6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1035f6 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1035fb (StorePre 0x1035fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1035fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1035fb 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x103600 (movR64M64Effect 0x103600 2 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x103600 (LoadPre 0x103600 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103600 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103600 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x103605 (movR64M64Effect 0x103605 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x103605 (LoadPre 0x103605 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103605 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103605 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x10360a (StorePre 0x10360a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10360a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10360a 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x10360f (StorePre 0x10360f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10360f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10360f 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x103613 (movR64M64Effect 0x103613 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x103613 (LoadPre 0x103613 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x103613 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103613 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x103618 (movR64M64Effect 0x103618 8 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 68) (.exec 0x103618 (LoadPre 0x103618 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x103618 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103618 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x10361d (StorePre 0x10361d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10361d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10361d 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 70) (.exec 0x103622 (StorePre 0x103622 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x103622 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103622 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 71) (.out 0x103627 (movR64M64Effect 0x103627 9 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 72) (.exec 0x103627 (LoadPre 0x103627 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x103627 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103627 9 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x10362c (StorePre 0x10362c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10362c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10362c 9 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x103631 (movR64M64Effect 0x103631 10 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 75) (.exec 0x103631 (LoadPre 0x103631 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x103631 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103631 10 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x103636 (StorePre 0x103636 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x103636 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103636 10 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.exec 0x10363b (StorePre 0x10363b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x10363b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10363b 10 (.base 3 (.d8 0x40))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[74, 3]
    (.letOp (n := 78) (.exec 0x10363f (StorePre 0x10363f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x10363f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10363f 9 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 79) (.exec 0x103643 (StorePre 0x103643 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x103643 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103643 8 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 80) (.exec 0x103647 (StorePre 0x103647 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x103647 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103647 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[65, 3]
    (b_l1035ec_1))))))))))))))))))))))))))))

def bytes_l1035ec : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x4C, 0x24, 0x50, 0x48,
    0x89, 0x4C, 0x24, 0x10, 0x48, 0x8B, 0x54, 0x24, 0x40, 0x48, 0x8B, 0x74, 0x24, 0x48, 0x48, 0x89,
    0x74, 0x24, 0x08, 0x48, 0x89, 0x14, 0x24, 0x48, 0x8B, 0x7C, 0x24, 0x60, 0x4C, 0x8B, 0x44, 0x24,
    0x68, 0x48, 0x89, 0x7C, 0x24, 0x20, 0x4C, 0x89, 0x44, 0x24, 0x28, 0x4C, 0x8B, 0x4C, 0x24, 0x70,
    0x4C, 0x89, 0x4C, 0x24, 0x30, 0x4C, 0x8B, 0x54, 0x24, 0x78, 0x4C, 0x89, 0x54, 0x24, 0x38, 0x4C,
    0x89, 0x53, 0x40, 0x4C, 0x89, 0x4B, 0x38, 0x4C, 0x89, 0x43, 0x30, 0x48, 0x89, 0x7B, 0x28] ++ bytes_l1035ec_1

theorem code_l1035ec : ∀ x ∈ codeRange 0x1035ec bytes_l1035ec, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x35ec 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1035ec_1

@[cfg_block] def b_l103670 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103670 (pushR64Effect 0x103670 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x103670 (PushPre 0x103670 1) (pushR64Effect 0x103670 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x103671 (pushR64Effect 0x103671 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x103671 (PushPre 0x103671 2) (pushR64Effect 0x103671 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x103673 (pushR64Effect 0x103673 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x103673 (PushPre 0x103673 2) (pushR64Effect 0x103673 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x103675 (pushR64Effect 0x103675 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x103675 (PushPre 0x103675 2) (pushR64Effect 0x103675 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x103677 (pushR64Effect 0x103677 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x103677 (PushPre 0x103677 2) (pushR64Effect 0x103677 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x103679 (pushR64Effect 0x103679 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x103679 (PushPre 0x103679 1) (pushR64Effect 0x103679 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10367a (subR64Imm32Effect 0x10367a 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10367a (fun s => s.RIP = 0x10367a) (subR64Imm32Effect 0x10367a 4 0x88) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x103681 (movR64R64Effect 0x103681 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x103681 (fun s => s.RIP = 0x103681) (movR64R64Effect 0x103681 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x103684 (movR32M32Effect 0x103684 15 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 70) (.exec 0x103684 (LoadPre 0x103684 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x103684 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x103684 15 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x103688 (movR32M32LowEffect 0x103688 5 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 72) (.exec 0x103688 (LoadPre 0x103688 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x103688 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x103688 5 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.out 0x10368b (addR32R32Effect 0x10368b 3 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[71, 69]
    (.letOp (n := 74) (.out 0x10368b (addR32R32Effect 0x10368b 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[71, 69]
    (.letOp (n := 75) (.exec 0x10368b (fun s => s.RIP = 0x10368b) (addR32R32Effect 0x10368b 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[71, 69]
    (.letOp (n := 76) (.pure (condOp 2)) #v[74]
    (.terminate (.condBr (Fin.last 76) ⟨.l1038a0, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩ ⟨.l103694, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l103670 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x88, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xFB, 0x44, 0x8B, 0x7E, 0x1C, 0x8B, 0x6A, 0x08, 0x44, 0x01, 0xFD, 0x0F, 0x82,
    0x0C, 0x02, 0x00, 0x00]

theorem code_l103670 : ∀ x ∈ codeRange 0x103670 bytes_l103670, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3670 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103694 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103694 (movR64R64Effect 0x103694 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 54) (.exec 0x103694 (fun s => s.RIP = 0x103694) (movR64R64Effect 0x103694 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x103697 (movR64R64Effect 0x103697 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 56) (.exec 0x103697 (fun s => s.RIP = 0x103697) (movR64R64Effect 0x103697 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x10369a (movR64M64Effect 0x10369a 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 58) (.exec 0x10369a (LoadPre 0x10369a (fun s => AddrMode.addr (.base 6 .none) s (0x10369a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10369a 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x10369d (movR64M64Effect 0x10369d 12 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 60) (.exec 0x10369d (LoadPre 0x10369d (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x10369d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10369d 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[55]
    (.letOp (n := 61) (.out 0x1036a1 (leaR64Effect 0x1036a1 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x1036a1 (fun s => s.RIP = 0x1036a1) (leaR64Effect 0x1036a1 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x1036a6 (StorePre 0x1036a6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1036a6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1036a6 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 64) (.out 0x1036ab (movR64R64Effect 0x1036ab 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 65) (.exec 0x1036ab (fun s => s.RIP = 0x1036ab) (movR64R64Effect 0x1036ab 2 12) (Reg.operands [.gpr 12] [])) #v[59]
    (.letOp (n := 66) (.out 0x1036ae (movR32R32Effect 0x1036ae 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 67) (.exec 0x1036ae (fun s => s.RIP = 0x1036ae) (movR32R32Effect 0x1036ae 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 68) (.out 0x1036b0 (callEffect (fun _ => 0x127c50) 0x1036b5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 69) (.exec 0x1036b0 (PushPre 0x1036b0 5) (callEffect (fun _ => 0x127c50) 0x1036b5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.const ⟨64, 0x1036b5⟩) #v[]
    (.terminate (.call ⟨.l127c50, RegMap.args [(1, 66), (2, 64), (3, 3), (4, 68), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l1036b5, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l103694 : List UInt8 :=
  [0x49, 0x89, 0xD5, 0x49, 0x89, 0xF6, 0x48, 0x8B, 0x36, 0x4D, 0x8B, 0x66, 0x08, 0x48, 0x8D, 0x7C,
    0x24, 0x30, 0x48, 0x89, 0x74, 0x24, 0x68, 0x4C, 0x89, 0xE2, 0x89, 0xE9, 0xE8, 0x9B, 0x45, 0x02,
    0x00]

theorem code_l103694 : ∀ x ∈ codeRange 0x103694 bytes_l103694, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3694 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1036b5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1036b5 (movR32M32LowEffect 0x1036b5 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1036b5 (LoadPre 0x1036b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1036b5 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1036b5 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1036b9 (cmpR32Imm8Effect 0x1036b9 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1036b9 (fun s => s.RIP = 0x1036b9) (cmpR32Imm8Effect 0x1036b9 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1036e0, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1036be, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1036b5 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x30, 0x83, 0xFA, 0x02, 0x75, 0x22]

theorem code_l1036b5 : ∀ x ∈ codeRange 0x1036b5 bytes_l1036b5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x36b5 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1036be : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1036be (movR64M64Effect 0x1036be 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1036be (LoadPre 0x1036be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1036be + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036be 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1036c3 (movR64M64Effect 0x1036c3 1 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1036c3 (LoadPre 0x1036c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1036c3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036c3 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1036c8 (StorePre 0x1036c8 3 (fun s => AddrMode.addr (.base 14 .none) s (0x1036c8 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1036c8 0 (.base 14 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.exec 0x1036cb (StorePre 0x1036cb 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1036cb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1036cb 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1036cf (movR64M64Effect 0x1036cf 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 60) (.exec 0x1036cf (LoadPre 0x1036cf (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1036cf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1036cf 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x1036d3 (cmpR64Imm8Effect 0x1036d3 0 0x3f) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x1036d3 (cmpR64Imm8Effect 0x1036d3 0 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x1036d3 (fun s => s.RIP = 0x1036d3) (cmpR64Imm8Effect 0x1036d3 0 0x3f) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 6)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l103724, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l1036d9, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l1036be : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x8B, 0x4C, 0x24, 0x40, 0x49, 0x89, 0x06, 0x49, 0x89, 0x4E,
    0x08, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x83, 0xF8, 0x3F, 0x76, 0x4B]

theorem code_l1036be : ∀ x ∈ codeRange 0x1036be bytes_l1036be, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x36be 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1036d9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1036d9 (movR32Imm32Effect 0x1036d9 5 0 0x6) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1036d9 (fun s => s.RIP = 0x1036d9) (movR32Imm32Effect 0x1036d9 5 0 0x6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103740, RegMap.args [(0, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1036d9 : List UInt8 :=
  [0xB8, 0x06, 0x00, 0x00, 0x00, 0xEB, 0x60]

theorem code_l1036d9 : ∀ x ∈ codeRange 0x1036d9 bytes_l1036d9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x36d9 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1036e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1036e0 (movR32M32LowEffect 0x1036e0 1 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1036e0 (LoadPre 0x1036e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1036e0 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1036e0 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1036e4 (movR64M64Effect 0x1036e4 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1036e4 (LoadPre 0x1036e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1036e4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036e4 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1036e9 (movR64M64Effect 0x1036e9 6 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x1036e9 (LoadPre 0x1036e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1036e9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036e9 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1036ee (movR64M64Effect 0x1036ee 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x1036ee (LoadPre 0x1036ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1036ee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036ee 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1036f3 (StorePre 0x1036f3 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1036f3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1036f3 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1036f7 (movR64M64Effect 0x1036f7 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x1036f7 (LoadPre 0x1036f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1036f7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036f7 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1036fc (StorePre 0x1036fc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1036fc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1036fc 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x103701 (movR64M64Effect 0x103701 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x103701 (LoadPre 0x103701 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x103701 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103701 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x103706 (StorePre 0x103706 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103706 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103706 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x10370b (movR64M64Effect 0x10370b 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x10370b (LoadPre 0x10370b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10370b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10370b 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x103710 (StorePre 0x103710 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103710 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103710 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.terminate (.br ⟨.l103715, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l1036e0 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x34, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x8B, 0x74, 0x24, 0x40, 0x48, 0x8B,
    0x7C, 0x24, 0x48, 0x48, 0x89, 0x3C, 0x24, 0x48, 0x8B, 0x7C, 0x24, 0x50, 0x48, 0x89, 0x7C, 0x24,
    0x08, 0x48, 0x8B, 0x7C, 0x24, 0x58, 0x48, 0x89, 0x7C, 0x24, 0x10, 0x48, 0x8B, 0x7C, 0x24, 0x60,
    0x48, 0x89, 0x7C, 0x24, 0x18]

theorem code_l1036e0 : ∀ x ∈ codeRange 0x1036e0 bytes_l1036e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x36e0 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103715 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103715 (movR64Imm64Effect 0x103715 7 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x103715 (fun s => s.RIP = 0x103715) (movR64Imm64Effect 0x103715 7 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10371f (andR64R64Effect 0x10371f 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[53, 6]
    (.letOp (n := 56) (.exec 0x10371f (fun s => s.RIP = 0x10371f) (andR64R64Effect 0x10371f 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[53, 6]
    (.terminate (.br ⟨.l10374d, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l103715 : List UInt8 :=
  [0x48, 0xBF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x48, 0x21, 0xF7, 0xEB, 0x29]

theorem code_l103715 : ∀ x ∈ codeRange 0x103715 bytes_l103715, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3715 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103724 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103724 (incR64Effect 0x103724 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x103724 (fun s => s.RIP = 0x103724) (incR64Effect 0x103724 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 55) (.exec 0x103727 (StorePre 0x103727 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x103727 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103727 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 56) (.out 0x10372b (movR32M32Effect 0x10372b 15 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 57) (.exec 0x10372b (LoadPre 0x10372b (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x10372b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x10372b 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x10372f (cmpR32R32Effect 0x10372f 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[5, 56]
    (.letOp (n := 59) (.out 0x10372f (cmpR32R32Effect 0x10372f 3 5 15) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 15] []) (.flag .ZF)) #v[5, 56]
    (.letOp (n := 60) (.exec 0x10372f (fun s => s.RIP = 0x10372f) (cmpR32R32Effect 0x10372f 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[5, 56]
    (.letOp (n := 61) (.pure (condOp 6)) #v[58, 59]
    (.terminate (.condBr (Fin.last 61) ⟨.l1037ab, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l103734, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l103724 : List UInt8 :=
  [0x48, 0xFF, 0xC0, 0x49, 0x89, 0x46, 0x10, 0x45, 0x8B, 0x7E, 0x18, 0x44, 0x39, 0xFD, 0x76, 0x77]

theorem code_l103724 : ∀ x ∈ codeRange 0x103724 bytes_l103724, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3724 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103734 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103734 (leaR32Effect 0x103734 4 0 (.base 15 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x103734 (fun s => s.RIP = 0x103734) (leaR32Effect 0x103734 4 0 (.base 15 (.d8 0x1))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x103738 (shlR64Effect 0x103738 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x103738 (fun s => s.RIP = 0x103738) (shlR64Effect 0x103738 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x10373c (orR64Imm8Effect 0x10373c 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x10373c (fun s => s.RIP = 0x10373c) (orR64Imm8Effect 0x10373c 0 0x3) (Reg.operands [.gpr 0] [])) #v[55]
    (.terminate (.br ⟨.l103740, RegMap.args [(0, 57), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l103734 : List UInt8 :=
  [0x41, 0x8D, 0x47, 0x01, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x03]

theorem code_l103734 : ∀ x ∈ codeRange 0x103734 bytes_l103734, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3734 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103740 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103740 (movR32Imm32Effect 0x103740 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x103740 (fun s => s.RIP = 0x103740) (movR32Imm32Effect 0x103740 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x103745 (xorR32R32Effect 0x103745 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 56) (.exec 0x103745 (fun s => s.RIP = 0x103745) (xorR32R32Effect 0x103745 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 57) (.out 0x103747 (movR32R32Effect 0x103747 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 58) (.exec 0x103747 (fun s => s.RIP = 0x103747) (movR32R32Effect 0x103747 3 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x10374a (movR32R32Effect 0x10374a 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 60) (.exec 0x10374a (fun s => s.RIP = 0x10374a) (movR32R32Effect 0x10374a 3 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l10374d, RegMap.args [(0, 0), (1, 57), (2, 53), (3, 3), (4, 4), (6, 59), (7, 55), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l103740 : List UInt8 :=
  [0xBA, 0x01, 0x00, 0x00, 0x00, 0x31, 0xFF, 0x44, 0x89, 0xF9, 0x44, 0x89, 0xFE]

theorem code_l103740 : ∀ x ∈ codeRange 0x103740 bytes_l103740, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3740 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10374d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10374d (movR32R32Effect 0x10374d 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 54) (.exec 0x10374d (fun s => s.RIP = 0x10374d) (movR32R32Effect 0x10374d 2 6 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x10374f (orR64R64Effect 0x10374f 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[53, 7]
    (.letOp (n := 56) (.exec 0x10374f (fun s => s.RIP = 0x10374f) (orR64R64Effect 0x10374f 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[53, 7]
    (.letOp (n := 57) (.out 0x103752 (movR64M64Effect 0x103752 7 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x103752 (LoadPre 0x103752 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103752 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103752 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x103756 (movR64M64Effect 0x103756 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 60) (.exec 0x103756 (LoadPre 0x103756 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103756 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103756 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x10375b (StorePre 0x10375b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10375b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10375b 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.exec 0x103760 (StorePre 0x103760 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103760 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103760 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 63) (.out 0x103765 (movR64M64Effect 0x103765 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x103765 (LoadPre 0x103765 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103765 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103765 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x10376a (StorePre 0x10376a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x10376a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10376a 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 66) (.out 0x10376e (movR64M64Effect 0x10376e 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 67) (.exec 0x10376e (LoadPre 0x10376e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10376e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10376e 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x103773 (StorePre 0x103773 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x103773 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103773 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[66, 3]
    (.letOp (n := 69) (.out 0x103777 (movR64M64Effect 0x103777 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x103777 (LoadPre 0x103777 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103777 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103777 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x10377c (movR64M64Effect 0x10377c 8 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 72) (.exec 0x10377c (LoadPre 0x10377c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10377c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10377c 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x103781 (StorePre 0x103781 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x103781 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103781 8 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 74) (.exec 0x103785 (StorePre 0x103785 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x103785 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103785 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[69, 3]
    (.letOp (n := 75) (.exec 0x103789 (StorePre 0x103789 2 (fun s => AddrMode.addr (.base 3 .none) s (0x103789 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x103789 2 (.base 3 .none)) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 76) (.exec 0x10378b (StorePre 0x10378b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x10378b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x10378b 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 77) (.exec 0x10378e (StorePre 0x10378e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10378e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10378e 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 78) (.exec 0x103792 (StorePre 0x103792 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x103792 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103792 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[55, 3]
    (.terminate (.br ⟨.l103796, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 69), (8, 71), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l10374d : List UInt8 :=
  [0x89, 0xF6, 0x48, 0x09, 0xFE, 0x48, 0x8B, 0x3C, 0x24, 0x4C, 0x8B, 0x44, 0x24, 0x08, 0x4C, 0x89,
    0x44, 0x24, 0x28, 0x48, 0x89, 0x7C, 0x24, 0x20, 0x48, 0x8B, 0x7C, 0x24, 0x18, 0x48, 0x89, 0x7B,
    0x30, 0x48, 0x8B, 0x7C, 0x24, 0x10, 0x48, 0x89, 0x7B, 0x28, 0x48, 0x8B, 0x7C, 0x24, 0x20, 0x4C,
    0x8B, 0x44, 0x24, 0x28, 0x4C, 0x89, 0x43, 0x20, 0x48, 0x89, 0x7B, 0x18, 0x89, 0x13, 0x89, 0x4B,
    0x04, 0x48, 0x89, 0x43, 0x08, 0x48, 0x89, 0x73, 0x10]

theorem code_l10374d : ∀ x ∈ codeRange 0x10374d bytes_l10374d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x374d 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103796 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103796 (movR64R64Effect 0x103796 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x103796 (fun s => s.RIP = 0x103796) (movR64R64Effect 0x103796 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x103799 (addR64Imm32Effect 0x103799 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x103799 (fun s => s.RIP = 0x103799) (addR64Imm32Effect 0x103799 4 0x88) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1037a0 (popR64Effect 0x1037a0 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x1037a0 (popR64Effect 0x1037a0 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x1037a0 (PopPre 0x1037a0) (popR64Effect 0x1037a0 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x1037a1 (popR64Effect 0x1037a1 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x1037a1 (popR64Effect 0x1037a1 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x1037a1 (PopPre 0x1037a1) (popR64Effect 0x1037a1 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x1037a3 (popR64Effect 0x1037a3 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x1037a3 (popR64Effect 0x1037a3 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x1037a3 (PopPre 0x1037a3) (popR64Effect 0x1037a3 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x1037a5 (popR64Effect 0x1037a5 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x1037a5 (popR64Effect 0x1037a5 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x1037a5 (PopPre 0x1037a5) (popR64Effect 0x1037a5 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x1037a7 (popR64Effect 0x1037a7 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x1037a7 (popR64Effect 0x1037a7 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x1037a7 (PopPre 0x1037a7) (popR64Effect 0x1037a7 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x1037a9 (popR64Effect 0x1037a9 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x1037a9 (popR64Effect 0x1037a9 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x1037a9 (PopPre 0x1037a9) (popR64Effect 0x1037a9 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x1037aa (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x1037aa (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x1037aa (RetPre 0x1037aa) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l103796 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l103796 : ∀ x ∈ codeRange 0x103796 bytes_l103796, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3796 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1037ab : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1037ab (StorePre 0x1037ab 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1037ab + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1037ab 5 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 14] [])) #v[5, 14]
    (.letOp (n := 54) (.exec 0x1037af (fun s => s.RIP = 0x1037af) (leaR64Effect 0x1037af 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1037b4 (movR64M64Effect 0x1037b4 0 (.base 13 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 56) (.exec 0x1037b4 (LoadPre 0x1037b4 (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x1037b4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1037b4 0 (.base 13 (.d8 0x0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x1037b8 (movR64M64Effect 0x1037b8 1 (.base 13 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 58) (.exec 0x1037b8 (LoadPre 0x1037b8 (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x1037b8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1037b8 1 (.base 13 (.d8 0x8))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.exec 0x1037bc (StorePre 0x1037bc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1037bc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1037bc 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.exec 0x1037c4 (StorePre 0x1037c4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1037c4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1037c4 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 61) (.exec 0x1037c9 (StorePre 0x1037c9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1037c9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1037c9 14 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 62) (.out 0x1037ce (leaR64Effect 0x1037ce 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x1037ce (fun s => s.RIP = 0x1037ce) (leaR64Effect 0x1037ce 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1037d3 (movR64R64Effect 0x1037d3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 65) (.exec 0x1037d3 (fun s => s.RIP = 0x1037d3) (movR64R64Effect 0x1037d3 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 66) (.out 0x1037d6 (callEffect (fun _ => 0x100510) 0x1037db) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 67) (.exec 0x1037d6 (PushPre 0x1037d6 5) (callEffect (fun _ => 0x100510) 0x1037db) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.const ⟨64, 0x1037db⟩) #v[]
    (.terminate (.call ⟨.l100510, RegMap.args [(0, 55), (1, 57), (3, 3), (4, 66), (5, 5), (6, 64), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l1037db, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l1037ab : List UInt8 :=
  [0x41, 0x89, 0x6E, 0x18, 0x48, 0x8D, 0x54, 0x24, 0x78, 0x49, 0x8B, 0x45, 0x00, 0x49, 0x8B, 0x4D,
    0x08, 0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x78, 0x4C, 0x89,
    0x74, 0x24, 0x70, 0x48, 0x8D, 0x7C, 0x24, 0x30, 0x4C, 0x89, 0xF6, 0xE8, 0x35, 0xCD, 0xFF, 0xFF]

theorem code_l1037ab : ∀ x ∈ codeRange 0x1037ab bytes_l1037ab, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x37ab 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1037db : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1037db (movR32M32Effect 0x1037db 6 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 54) (.exec 0x1037db (LoadPre 0x1037db (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1037db + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1037db 6 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x1037df (movR32M32Effect 0x1037df 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 56) (.exec 0x1037df (LoadPre 0x1037df (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1037df + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1037df 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x1037e3 (subR32R32Effect 0x1037e3 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[53, 55]
    (.letOp (n := 58) (.out 0x1037e3 (subR32R32Effect 0x1037e3 2 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 59) (.out 0x1037e3 (subR32R32Effect 0x1037e3 2 6 1) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 1] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 60) (.exec 0x1037e3 (fun s => s.RIP = 0x1037e3) (subR32R32Effect 0x1037e3 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[53, 55]
    (.letOp (n := 61) (.out 0x1037e5 (atFlags (condHolds 6) (setccR8Effect 0x1037e5 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[0, 58, 59]
    (.letOp (n := 62) (.exec 0x1037e5 (fun s => s.RIP = 0x1037e5) (atFlags (condHolds 6) (setccR8Effect 0x1037e5 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[0, 58, 59]
    (.letOp (n := 63) (.out 0x1037e8 (movR64M64Effect 0x1037e8 2 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x1037e8 (LoadPre 0x1037e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1037e8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1037e8 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x1037ed (StorePre 0x1037ed 3 (fun s => AddrMode.addr (.base 14 .none) s (0x1037ed + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1037ed 2 (.base 14 .none)) (Reg.operands [.gpr 2, .gpr 14] [])) #v[63, 14]
    (.letOp (n := 66) (.exec 0x1037f0 (StorePre 0x1037f0 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1037f0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1037f0 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 14] [])) #v[12, 14]
    (.letOp (n := 67) (.exec 0x1037f4 (StorePre 0x1037f4 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1037f4 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1037f4 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 14] [])) #v[15, 14]
    (.letOp (n := 68) (.out 0x1037f8 (movR64M64Effect 0x1037f8 2 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 69) (.exec 0x1037f8 (LoadPre 0x1037f8 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1037f8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1037f8 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 70) (.out 0x1037fc (cmpR64Imm8Effect 0x1037fc 2 0x1) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[68]
    (.letOp (n := 71) (.exec 0x1037fc (fun s => s.RIP = 0x1037fc) (cmpR64Imm8Effect 0x1037fc 2 0x1) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 72) (.out 0x103800 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x103800 2 0xff)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[68, 70]
    (.letOp (n := 73) (.exec 0x103800 (fun s => s.RIP = 0x103800) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x103800 2 0xff)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[68, 70]
    (.letOp (n := 74) (.exec 0x103804 (StorePre 0x103804 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x103804 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103804 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[72, 14]
    (.letOp (n := 75) (.out 0x103808 (movR32M32LowEffect 0x103808 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 76) (.exec 0x103808 (LoadPre 0x103808 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x103808 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103808 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x10380c (cmpR32Imm8Effect 0x10380c 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[75]
    (.letOp (n := 78) (.exec 0x10380c (fun s => s.RIP = 0x10380c) (cmpR32Imm8Effect 0x10380c 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[75]
    (.letOp (n := 79) (.out 0x10380f (atFlags (condHolds 5) (setccR8Effect 0x10380f 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[7, 77]
    (.letOp (n := 80) (.exec 0x10380f (fun s => s.RIP = 0x10380f) (atFlags (condHolds 5) (setccR8Effect 0x10380f 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[7, 77]
    (.letOp (n := 81) (.out 0x103813 (orR8R8Effect 0x103813 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[79, 61]
    (.letOp (n := 82) (.out 0x103813 (orR8R8Effect 0x103813 3 7 0) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 0] []) (.flag .ZF)) #v[79, 61]
    (.letOp (n := 83) (.exec 0x103813 (fun s => s.RIP = 0x103813) (orR8R8Effect 0x103813 3 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[79, 61]
    (.letOp (n := 84) (.pure (condOp 4)) #v[82]
    (.terminate (.condBr (Fin.last 84) ⟨.l103884, RegMap.args [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ ⟨.l103818, RegMap.args [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l1037db : List UInt8 :=
  [0x41, 0x8B, 0x76, 0x18, 0x41, 0x8B, 0x4E, 0x1C, 0x29, 0xCE, 0x0F, 0x96, 0xC0, 0x48, 0x8B, 0x54,
    0x24, 0x68, 0x49, 0x89, 0x16, 0x4D, 0x89, 0x66, 0x08, 0x45, 0x89, 0x7E, 0x18, 0x49, 0x8B, 0x56,
    0x10, 0x48, 0x83, 0xFA, 0x01, 0x48, 0x83, 0xD2, 0xFF, 0x49, 0x89, 0x56, 0x10, 0x8B, 0x54, 0x24,
    0x30, 0x83, 0xFA, 0x02, 0x40, 0x0F, 0x95, 0xC7, 0x40, 0x08, 0xC7, 0x74, 0x6C]

theorem code_l1037db : ∀ x ∈ codeRange 0x1037db bytes_l1037db, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x37db 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103818 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103818 (movR32M32LowEffect 0x103818 1 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x103818 (LoadPre 0x103818 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x103818 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103818 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10381c (movR64M64Effect 0x10381c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x10381c (LoadPre 0x10381c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10381c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10381c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x103821 (movR64M64Effect 0x103821 6 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x103821 (LoadPre 0x103821 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103821 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103821 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x103826 (movR64M64Effect 0x103826 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x103826 (LoadPre 0x103826 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103826 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103826 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x10382b (StorePre 0x10382b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10382b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10382b 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x10382f (movR64M64Effect 0x10382f 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x10382f (LoadPre 0x10382f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10382f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10382f 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x103834 (StorePre 0x103834 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103834 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103834 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x103839 (movR64M64Effect 0x103839 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x103839 (LoadPre 0x103839 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x103839 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103839 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x10383e (StorePre 0x10383e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10383e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10383e 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x103843 (movR64M64Effect 0x103843 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x103843 (LoadPre 0x103843 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x103843 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103843 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x103848 (StorePre 0x103848 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103848 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103848 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x10384d (cmpR32Imm8Effect 0x10384d 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 72) (.exec 0x10384d (fun s => s.RIP = 0x10384d) (cmpR32Imm8Effect 0x10384d 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.pure (condOp 5)) #v[71]
    (.terminate (.condBr (Fin.last 73) ⟨.l103715, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ ⟨.l103856, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l103818 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x34, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x8B, 0x74, 0x24, 0x40, 0x48, 0x8B,
    0x7C, 0x24, 0x48, 0x48, 0x89, 0x3C, 0x24, 0x48, 0x8B, 0x7C, 0x24, 0x50, 0x48, 0x89, 0x7C, 0x24,
    0x08, 0x48, 0x8B, 0x7C, 0x24, 0x58, 0x48, 0x89, 0x7C, 0x24, 0x10, 0x48, 0x8B, 0x7C, 0x24, 0x60,
    0x48, 0x89, 0x7C, 0x24, 0x18, 0x83, 0xFA, 0x02, 0x0F, 0x85, 0xBF, 0xFE, 0xFF, 0xFF]

theorem code_l103818 : ∀ x ∈ codeRange 0x103818 bytes_l103818, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3818 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103856 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103856 (movR64M64Effect 0x103856 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x103856 (LoadPre 0x103856 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103856 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103856 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10385a (movR64M64Effect 0x10385a 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x10385a (LoadPre 0x10385a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10385a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10385a 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x10385f (StorePre 0x10385f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10385f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10385f 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x103864 (StorePre 0x103864 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103864 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103864 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.exec 0x103869 (StorePre 0x103869 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x103869 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103869 2 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 60) (.exec 0x10386d (StorePre 0x10386d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10386d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10386d 1 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 61) (.exec 0x103871 (StorePre 0x103871 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x103871 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103871 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 62) (.exec 0x103875 (StorePre 0x103875 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x103875 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103875 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 63) (.exec 0x103879 (StorePre 0x103879 6 (fun s => AddrMode.addr (.base 3 .none) s (0x103879 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x103879 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l103796, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l103856 : List UInt8 :=
  [0x48, 0x8B, 0x0C, 0x24, 0x48, 0x8B, 0x54, 0x24, 0x08, 0x48, 0x89, 0x54, 0x24, 0x28, 0x48, 0x89,
    0x4C, 0x24, 0x20, 0x48, 0x89, 0x53, 0x20, 0x48, 0x89, 0x4B, 0x18, 0x48, 0x89, 0x43, 0x08, 0x48,
    0x89, 0x73, 0x10, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0x12, 0xFF, 0xFF, 0xFF]

theorem code_l103856 : ∀ x ∈ codeRange 0x103856 bytes_l103856, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3856 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103884 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103884 (StorePre 0x103884 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x103884 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x103884 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x103889 (movR64R64Effect 0x103889 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 55) (.exec 0x103889 (fun s => s.RIP = 0x103889) (movR64R64Effect 0x103889 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 56) (.out 0x10388c (shlR64Effect 0x10388c 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 57) (.exec 0x10388c (fun s => s.RIP = 0x10388c) (shlR64Effect 0x10388c 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[54]
    (.letOp (n := 58) (.out 0x103890 (orR64Imm8Effect 0x103890 0 0x13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 59) (.exec 0x103890 (fun s => s.RIP = 0x103890) (orR64Imm8Effect 0x103890 0 0x13) (Reg.operands [.gpr 0] [])) #v[56]
    (.letOp (n := 60) (.out 0x103894 (movR32Imm32Effect 0x103894 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 61) (.exec 0x103894 (fun s => s.RIP = 0x103894) (movR32Imm32Effect 0x103894 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x103899 (xorR32R32Effect 0x103899 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 63) (.exec 0x103899 (fun s => s.RIP = 0x103899) (xorR32R32Effect 0x103899 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l10374d, RegMap.args [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 62), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l103884 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x48, 0x89, 0xC8, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x13,
    0xBA, 0x01, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xE9, 0xAD, 0xFE, 0xFF, 0xFF]

theorem code_l103884 : ∀ x ∈ codeRange 0x103884 bytes_l103884, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3884 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1038a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1038a0 (xorR32R32Effect 0x1038a0 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x1038a0 (fun s => s.RIP = 0x1038a0) (xorR32R32Effect 0x1038a0 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.out 0x1038a2 (movR32Imm32Effect 0x1038a2 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x1038a2 (fun s => s.RIP = 0x1038a2) (movR32Imm32Effect 0x1038a2 5 0 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1038a7 (xorR32R32Effect 0x1038a7 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 58) (.exec 0x1038a7 (fun s => s.RIP = 0x1038a7) (xorR32R32Effect 0x1038a7 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l10374d, RegMap.args [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1038a0 : List UInt8 :=
  [0x31, 0xD2, 0xB8, 0x0C, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xE9, 0x9F, 0xFE, 0xFF, 0xFF]

theorem code_l1038a0 : ∀ x ∈ codeRange 0x1038a0 bytes_l1038a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38a0 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1038b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1038b0 (pushR64Effect 0x1038b0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1038b0 (PushPre 0x1038b0 1) (pushR64Effect 0x1038b0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1038b1 (pushR64Effect 0x1038b1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1038b1 (PushPre 0x1038b1 2) (pushR64Effect 0x1038b1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1038b3 (pushR64Effect 0x1038b3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1038b3 (PushPre 0x1038b3 2) (pushR64Effect 0x1038b3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1038b5 (pushR64Effect 0x1038b5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1038b5 (PushPre 0x1038b5 2) (pushR64Effect 0x1038b5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1038b7 (pushR64Effect 0x1038b7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1038b7 (PushPre 0x1038b7 2) (pushR64Effect 0x1038b7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1038b9 (pushR64Effect 0x1038b9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1038b9 (PushPre 0x1038b9 1) (pushR64Effect 0x1038b9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1038ba (subR64Imm8Effect 0x1038ba 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1038ba (fun s => s.RIP = 0x1038ba) (subR64Imm8Effect 0x1038ba 4 0x78) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1038be (movR64R64Effect 0x1038be 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x1038be (fun s => s.RIP = 0x1038be) (movR64R64Effect 0x1038be 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x1038c1 (movR32M32Effect 0x1038c1 15 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 70) (.exec 0x1038c1 (LoadPre 0x1038c1 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x1038c1 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1038c1 15 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x1038c5 (movR32M32LowEffect 0x1038c5 5 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 72) (.exec 0x1038c5 (LoadPre 0x1038c5 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1038c5 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1038c5 5 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.out 0x1038c8 (addR32R32Effect 0x1038c8 3 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[71, 69]
    (.letOp (n := 74) (.out 0x1038c8 (addR32R32Effect 0x1038c8 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[71, 69]
    (.letOp (n := 75) (.exec 0x1038c8 (fun s => s.RIP = 0x1038c8) (addR32R32Effect 0x1038c8 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[71, 69]
    (.letOp (n := 76) (.pure (condOp 2)) #v[74]
    (.terminate (.condBr (Fin.last 76) ⟨.l103aa8, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩ ⟨.l1038d1, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l1038b0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x78, 0x48, 0x89,
    0xFB, 0x44, 0x8B, 0x7E, 0x1C, 0x8B, 0x6A, 0x08, 0x44, 0x01, 0xFD, 0x0F, 0x82, 0xD7, 0x01, 0x00,
    0x00]

theorem code_l1038b0 : ∀ x ∈ codeRange 0x1038b0 bytes_l1038b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38b0 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1038d1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1038d1 (movR64R64Effect 0x1038d1 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 54) (.exec 0x1038d1 (fun s => s.RIP = 0x1038d1) (movR64R64Effect 0x1038d1 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x1038d4 (movR64R64Effect 0x1038d4 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 56) (.exec 0x1038d4 (fun s => s.RIP = 0x1038d4) (movR64R64Effect 0x1038d4 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x1038d7 (movR64M64Effect 0x1038d7 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 58) (.exec 0x1038d7 (LoadPre 0x1038d7 (fun s => AddrMode.addr (.base 6 .none) s (0x1038d7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1038d7 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x1038da (movR64M64Effect 0x1038da 12 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 60) (.exec 0x1038da (LoadPre 0x1038da (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1038da + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1038da 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[55]
    (.letOp (n := 61) (.out 0x1038de (leaR64Effect 0x1038de 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x1038de (fun s => s.RIP = 0x1038de) (leaR64Effect 0x1038de 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x1038e3 (StorePre 0x1038e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1038e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1038e3 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 64) (.out 0x1038e8 (movR64R64Effect 0x1038e8 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 65) (.exec 0x1038e8 (fun s => s.RIP = 0x1038e8) (movR64R64Effect 0x1038e8 2 12) (Reg.operands [.gpr 12] [])) #v[59]
    (.letOp (n := 66) (.out 0x1038eb (movR32R32Effect 0x1038eb 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 67) (.exec 0x1038eb (fun s => s.RIP = 0x1038eb) (movR32R32Effect 0x1038eb 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 68) (.out 0x1038ed (callEffect (fun _ => 0x127c50) 0x1038f2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 69) (.exec 0x1038ed (PushPre 0x1038ed 5) (callEffect (fun _ => 0x127c50) 0x1038f2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.const ⟨64, 0x1038f2⟩) #v[]
    (.terminate (.call ⟨.l127c50, RegMap.args [(1, 66), (2, 64), (3, 3), (4, 68), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l1038f2, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l1038d1 : List UInt8 :=
  [0x49, 0x89, 0xD5, 0x49, 0x89, 0xF6, 0x48, 0x8B, 0x36, 0x4D, 0x8B, 0x66, 0x08, 0x48, 0x8D, 0x7C,
    0x24, 0x20, 0x48, 0x89, 0x74, 0x24, 0x58, 0x4C, 0x89, 0xE2, 0x89, 0xE9, 0xE8, 0x5E, 0x43, 0x02,
    0x00]

theorem code_l1038d1 : ∀ x ∈ codeRange 0x1038d1 bytes_l1038d1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38d1 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1038f2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1038f2 (movR32M32LowEffect 0x1038f2 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1038f2 (LoadPre 0x1038f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1038f2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1038f2 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1038f6 (cmpR32Imm8Effect 0x1038f6 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1038f6 (fun s => s.RIP = 0x1038f6) (cmpR32Imm8Effect 0x1038f6 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l10391d, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1038fb, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1038f2 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x20, 0x83, 0xFA, 0x02, 0x75, 0x22]

theorem code_l1038f2 : ∀ x ∈ codeRange 0x1038f2 bytes_l1038f2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38f2 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1038fb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1038fb (movR64M64Effect 0x1038fb 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1038fb (LoadPre 0x1038fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1038fb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1038fb 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x103900 (movR64M64Effect 0x103900 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x103900 (LoadPre 0x103900 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x103900 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103900 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x103905 (StorePre 0x103905 3 (fun s => AddrMode.addr (.base 14 .none) s (0x103905 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x103905 0 (.base 14 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.exec 0x103908 (StorePre 0x103908 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x103908 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103908 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x10390c (movR64M64Effect 0x10390c 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 60) (.exec 0x10390c (LoadPre 0x10390c (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x10390c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10390c 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x103910 (cmpR64Imm8Effect 0x103910 0 0x3f) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x103910 (cmpR64Imm8Effect 0x103910 0 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x103910 (fun s => s.RIP = 0x103910) (cmpR64Imm8Effect 0x103910 0 0x3f) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 6)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l103961, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l103916, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l1038fb : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x49, 0x89, 0x06, 0x49, 0x89, 0x4E,
    0x08, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x83, 0xF8, 0x3F, 0x76, 0x4B]

theorem code_l1038fb : ∀ x ∈ codeRange 0x1038fb bytes_l1038fb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38fb 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103916 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103916 (movR32Imm32Effect 0x103916 5 0 0x6) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x103916 (fun s => s.RIP = 0x103916) (movR32Imm32Effect 0x103916 5 0 0x6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l10397d, RegMap.args [(0, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l103916 : List UInt8 :=
  [0xB8, 0x06, 0x00, 0x00, 0x00, 0xEB, 0x60]

theorem code_l103916 : ∀ x ∈ codeRange 0x103916 bytes_l103916, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3916 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10391d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10391d (movR32M32LowEffect 0x10391d 1 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x10391d (LoadPre 0x10391d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x10391d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10391d 1 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x103921 (movR64M64Effect 0x103921 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x103921 (LoadPre 0x103921 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x103921 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103921 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x103926 (movR64M64Effect 0x103926 6 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x103926 (LoadPre 0x103926 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x103926 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103926 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10392b (movR64M64Effect 0x10392b 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x10392b (LoadPre 0x10392b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10392b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10392b 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x103930 (StorePre 0x103930 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103930 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103930 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x103934 (movR64M64Effect 0x103934 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x103934 (LoadPre 0x103934 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103934 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103934 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x103939 (StorePre 0x103939 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103939 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103939 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x10393e (movR64M64Effect 0x10393e 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x10393e (LoadPre 0x10393e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10393e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10393e 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x103943 (StorePre 0x103943 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103943 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103943 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x103948 (movR64M64Effect 0x103948 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x103948 (LoadPre 0x103948 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x103948 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103948 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x10394d (StorePre 0x10394d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10394d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10394d 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.terminate (.br ⟨.l103952, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l10391d : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x24, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x74, 0x24, 0x30, 0x48, 0x8B,
    0x7C, 0x24, 0x38, 0x48, 0x89, 0x3C, 0x24, 0x48, 0x8B, 0x7C, 0x24, 0x40, 0x48, 0x89, 0x7C, 0x24,
    0x08, 0x48, 0x8B, 0x7C, 0x24, 0x48, 0x48, 0x89, 0x7C, 0x24, 0x10, 0x48, 0x8B, 0x7C, 0x24, 0x50,
    0x48, 0x89, 0x7C, 0x24, 0x18]

theorem code_l10391d : ∀ x ∈ codeRange 0x10391d bytes_l10391d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x391d 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103952 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103952 (movR64Imm64Effect 0x103952 7 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x103952 (fun s => s.RIP = 0x103952) (movR64Imm64Effect 0x103952 7 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10395c (andR64R64Effect 0x10395c 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[53, 6]
    (.letOp (n := 56) (.exec 0x10395c (fun s => s.RIP = 0x10395c) (andR64R64Effect 0x10395c 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[53, 6]
    (.terminate (.br ⟨.l10398a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l103952 : List UInt8 :=
  [0x48, 0xBF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x48, 0x21, 0xF7, 0xEB, 0x29]

theorem code_l103952 : ∀ x ∈ codeRange 0x103952 bytes_l103952, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3952 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103961 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103961 (incR64Effect 0x103961 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x103961 (fun s => s.RIP = 0x103961) (incR64Effect 0x103961 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 55) (.exec 0x103964 (StorePre 0x103964 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x103964 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103964 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 56) (.out 0x103968 (movR32M32Effect 0x103968 15 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 57) (.exec 0x103968 (LoadPre 0x103968 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x103968 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x103968 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x10396c (cmpR32R32Effect 0x10396c 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[5, 56]
    (.letOp (n := 59) (.out 0x10396c (cmpR32R32Effect 0x10396c 3 5 15) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 15] []) (.flag .ZF)) #v[5, 56]
    (.letOp (n := 60) (.exec 0x10396c (fun s => s.RIP = 0x10396c) (cmpR32R32Effect 0x10396c 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[5, 56]
    (.letOp (n := 61) (.pure (condOp 6)) #v[58, 59]
    (.terminate (.condBr (Fin.last 61) ⟨.l1039d1, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l103971, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l103961 : List UInt8 :=
  [0x48, 0xFF, 0xC0, 0x49, 0x89, 0x46, 0x10, 0x45, 0x8B, 0x7E, 0x18, 0x44, 0x39, 0xFD, 0x76, 0x60]

theorem code_l103961 : ∀ x ∈ codeRange 0x103961 bytes_l103961, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3961 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103971 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103971 (leaR32Effect 0x103971 4 0 (.base 15 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x103971 (fun s => s.RIP = 0x103971) (leaR32Effect 0x103971 4 0 (.base 15 (.d8 0x1))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x103975 (shlR64Effect 0x103975 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x103975 (fun s => s.RIP = 0x103975) (shlR64Effect 0x103975 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x103979 (orR64Imm8Effect 0x103979 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x103979 (fun s => s.RIP = 0x103979) (orR64Imm8Effect 0x103979 0 0x3) (Reg.operands [.gpr 0] [])) #v[55]
    (.terminate (.br ⟨.l10397d, RegMap.args [(0, 57), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l103971 : List UInt8 :=
  [0x41, 0x8D, 0x47, 0x01, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x03]

theorem code_l103971 : ∀ x ∈ codeRange 0x103971 bytes_l103971, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3971 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10397d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10397d (movR32Imm32Effect 0x10397d 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x10397d (fun s => s.RIP = 0x10397d) (movR32Imm32Effect 0x10397d 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x103982 (xorR32R32Effect 0x103982 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 56) (.exec 0x103982 (fun s => s.RIP = 0x103982) (xorR32R32Effect 0x103982 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 57) (.out 0x103984 (movR32R32Effect 0x103984 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 58) (.exec 0x103984 (fun s => s.RIP = 0x103984) (movR32R32Effect 0x103984 3 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x103987 (movR32R32Effect 0x103987 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 60) (.exec 0x103987 (fun s => s.RIP = 0x103987) (movR32R32Effect 0x103987 3 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l10398a, RegMap.args [(0, 0), (1, 57), (2, 53), (3, 3), (4, 4), (6, 59), (7, 55), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l10397d : List UInt8 :=
  [0xBA, 0x01, 0x00, 0x00, 0x00, 0x31, 0xFF, 0x44, 0x89, 0xF9, 0x44, 0x89, 0xFE]

theorem code_l10397d : ∀ x ∈ codeRange 0x10397d bytes_l10397d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x397d 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10398a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10398a (movR32R32Effect 0x10398a 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 54) (.exec 0x10398a (fun s => s.RIP = 0x10398a) (movR32R32Effect 0x10398a 2 6 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x10398c (orR64R64Effect 0x10398c 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[53, 7]
    (.letOp (n := 56) (.exec 0x10398c (fun s => s.RIP = 0x10398c) (orR64R64Effect 0x10398c 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[53, 7]
    (.letOp (n := 57) (.out 0x10398f (movR64M64Effect 0x10398f 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x10398f (LoadPre 0x10398f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10398f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10398f 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x103994 (StorePre 0x103994 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x103994 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103994 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 60) (.out 0x103998 (movR64M64Effect 0x103998 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 61) (.exec 0x103998 (LoadPre 0x103998 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103998 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103998 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x10399d (StorePre 0x10399d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x10399d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10399d 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[60, 3]
    (.letOp (n := 63) (.out 0x1039a1 (movR64M64Effect 0x1039a1 7 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x1039a1 (LoadPre 0x1039a1 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1039a1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1039a1 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1039a5 (movR64M64Effect 0x1039a5 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 66) (.exec 0x1039a5 (LoadPre 0x1039a5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1039a5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1039a5 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1039aa (StorePre 0x1039aa 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1039aa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1039aa 8 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.exec 0x1039ae (StorePre 0x1039ae 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1039ae + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1039ae 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 69) (.exec 0x1039b2 (StorePre 0x1039b2 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1039b2 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1039b2 2 (.base 3 .none)) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 70) (.exec 0x1039b4 (StorePre 0x1039b4 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1039b4 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1039b4 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 71) (.exec 0x1039b7 (StorePre 0x1039b7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1039b7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1039b7 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 72) (.exec 0x1039bb (StorePre 0x1039bb 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1039bb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1039bb 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[55, 3]
    (.terminate (.br ⟨.l1039bf, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l10398a : List UInt8 :=
  [0x89, 0xF6, 0x48, 0x09, 0xFE, 0x48, 0x8B, 0x7C, 0x24, 0x18, 0x48, 0x89, 0x7B, 0x30, 0x48, 0x8B,
    0x7C, 0x24, 0x10, 0x48, 0x89, 0x7B, 0x28, 0x48, 0x8B, 0x3C, 0x24, 0x4C, 0x8B, 0x44, 0x24, 0x08,
    0x4C, 0x89, 0x43, 0x20, 0x48, 0x89, 0x7B, 0x18, 0x89, 0x13, 0x89, 0x4B, 0x04, 0x48, 0x89, 0x43,
    0x08, 0x48, 0x89, 0x73, 0x10]

theorem code_l10398a : ∀ x ∈ codeRange 0x10398a bytes_l10398a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x398a 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1039bf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1039bf (movR64R64Effect 0x1039bf 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1039bf (fun s => s.RIP = 0x1039bf) (movR64R64Effect 0x1039bf 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1039c2 (addR64Imm8Effect 0x1039c2 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x1039c2 (fun s => s.RIP = 0x1039c2) (addR64Imm8Effect 0x1039c2 4 0x78) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1039c6 (popR64Effect 0x1039c6 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x1039c6 (popR64Effect 0x1039c6 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x1039c6 (PopPre 0x1039c6) (popR64Effect 0x1039c6 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x1039c7 (popR64Effect 0x1039c7 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x1039c7 (popR64Effect 0x1039c7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x1039c7 (PopPre 0x1039c7) (popR64Effect 0x1039c7 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x1039c9 (popR64Effect 0x1039c9 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x1039c9 (popR64Effect 0x1039c9 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x1039c9 (PopPre 0x1039c9) (popR64Effect 0x1039c9 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x1039cb (popR64Effect 0x1039cb 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x1039cb (popR64Effect 0x1039cb 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x1039cb (PopPre 0x1039cb) (popR64Effect 0x1039cb 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x1039cd (popR64Effect 0x1039cd 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x1039cd (popR64Effect 0x1039cd 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x1039cd (PopPre 0x1039cd) (popR64Effect 0x1039cd 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x1039cf (popR64Effect 0x1039cf 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x1039cf (popR64Effect 0x1039cf 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x1039cf (PopPre 0x1039cf) (popR64Effect 0x1039cf 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x1039d0 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x1039d0 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x1039d0 (RetPre 0x1039d0) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l1039bf : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x78, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l1039bf : ∀ x ∈ codeRange 0x1039bf bytes_l1039bf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x39bf 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1039d1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1039d1 (StorePre 0x1039d1 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1039d1 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1039d1 5 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 14] [])) #v[5, 14]
    (.letOp (n := 54) (.out 0x1039d5 (leaR64Effect 0x1039d5 2 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 55) (.exec 0x1039d5 (fun s => s.RIP = 0x1039d5) (leaR64Effect 0x1039d5 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1039da (movR64M64Effect 0x1039da 0 (.base 13 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 57) (.exec 0x1039da (LoadPre 0x1039da (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x1039da + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1039da 0 (.base 13 (.d8 0x0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 58) (.out 0x1039de (movR64M64Effect 0x1039de 1 (.base 13 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 59) (.exec 0x1039de (LoadPre 0x1039de (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x1039de + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1039de 1 (.base 13 (.d8 0x8))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 60) (.exec 0x1039e2 (StorePre 0x1039e2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1039e2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1039e2 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.exec 0x1039e7 (StorePre 0x1039e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1039e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1039e7 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 62) (.exec 0x1039ec (StorePre 0x1039ec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1039ec + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1039ec 14 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 63) (.out 0x1039f1 (leaR64Effect 0x1039f1 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x1039f1 (fun s => s.RIP = 0x1039f1) (leaR64Effect 0x1039f1 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1039f6 (movR64R64Effect 0x1039f6 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 66) (.exec 0x1039f6 (fun s => s.RIP = 0x1039f6) (movR64R64Effect 0x1039f6 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 67) (.out 0x1039f9 (callEffect (fun _ => 0x1002f0) 0x1039fe) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x1039f9 (PushPre 0x1039f9 5) (callEffect (fun _ => 0x1002f0) 0x1039fe) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x1039fe⟩) #v[]
    (.terminate (.call ⟨.l1002f0, RegMap.args [(0, 56), (1, 58), (2, 54), (3, 3), (4, 67), (5, 5), (6, 65), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l1039fe, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l1039d1 : List UInt8 :=
  [0x41, 0x89, 0x6E, 0x18, 0x48, 0x8D, 0x54, 0x24, 0x68, 0x49, 0x8B, 0x45, 0x00, 0x49, 0x8B, 0x4D,
    0x08, 0x48, 0x89, 0x4C, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x68, 0x4C, 0x89, 0x74, 0x24, 0x60,
    0x48, 0x8D, 0x7C, 0x24, 0x20, 0x4C, 0x89, 0xF6, 0xE8, 0xF2, 0xC8, 0xFF, 0xFF]

theorem code_l1039d1 : ∀ x ∈ codeRange 0x1039d1 bytes_l1039d1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x39d1 45 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1039fe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1039fe (movR32M32Effect 0x1039fe 6 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 54) (.exec 0x1039fe (LoadPre 0x1039fe (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1039fe + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1039fe 6 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x103a02 (movR32M32Effect 0x103a02 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 56) (.exec 0x103a02 (LoadPre 0x103a02 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x103a02 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x103a02 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x103a06 (subR32R32Effect 0x103a06 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[53, 55]
    (.letOp (n := 58) (.out 0x103a06 (subR32R32Effect 0x103a06 2 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 59) (.out 0x103a06 (subR32R32Effect 0x103a06 2 6 1) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 1] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 60) (.exec 0x103a06 (fun s => s.RIP = 0x103a06) (subR32R32Effect 0x103a06 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[53, 55]
    (.letOp (n := 61) (.out 0x103a08 (atFlags (condHolds 6) (setccR8Effect 0x103a08 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[0, 58, 59]
    (.letOp (n := 62) (.exec 0x103a08 (fun s => s.RIP = 0x103a08) (atFlags (condHolds 6) (setccR8Effect 0x103a08 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[0, 58, 59]
    (.letOp (n := 63) (.out 0x103a0b (movR64M64Effect 0x103a0b 2 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x103a0b (LoadPre 0x103a0b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x103a0b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a0b 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x103a10 (StorePre 0x103a10 3 (fun s => AddrMode.addr (.base 14 .none) s (0x103a10 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x103a10 2 (.base 14 .none)) (Reg.operands [.gpr 2, .gpr 14] [])) #v[63, 14]
    (.letOp (n := 66) (.exec 0x103a13 (StorePre 0x103a13 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x103a13 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103a13 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 14] [])) #v[12, 14]
    (.letOp (n := 67) (.exec 0x103a17 (StorePre 0x103a17 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x103a17 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x103a17 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 14] [])) #v[15, 14]
    (.letOp (n := 68) (.out 0x103a1b (movR64M64Effect 0x103a1b 2 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 69) (.exec 0x103a1b (LoadPre 0x103a1b (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x103a1b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103a1b 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 70) (.out 0x103a1f (cmpR64Imm8Effect 0x103a1f 2 0x1) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[68]
    (.letOp (n := 71) (.exec 0x103a1f (fun s => s.RIP = 0x103a1f) (cmpR64Imm8Effect 0x103a1f 2 0x1) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 72) (.out 0x103a23 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x103a23 2 0xff)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[68, 70]
    (.letOp (n := 73) (.exec 0x103a23 (fun s => s.RIP = 0x103a23) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x103a23 2 0xff)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[68, 70]
    (.letOp (n := 74) (.exec 0x103a27 (StorePre 0x103a27 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x103a27 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103a27 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[72, 14]
    (.letOp (n := 75) (.out 0x103a2b (movR32M32LowEffect 0x103a2b 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 76) (.exec 0x103a2b (LoadPre 0x103a2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103a2b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103a2b 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x103a2f (cmpR32Imm8Effect 0x103a2f 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[75]
    (.letOp (n := 78) (.exec 0x103a2f (fun s => s.RIP = 0x103a2f) (cmpR32Imm8Effect 0x103a2f 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[75]
    (.letOp (n := 79) (.out 0x103a32 (atFlags (condHolds 5) (setccR8Effect 0x103a32 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[7, 77]
    (.letOp (n := 80) (.exec 0x103a32 (fun s => s.RIP = 0x103a32) (atFlags (condHolds 5) (setccR8Effect 0x103a32 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[7, 77]
    (.letOp (n := 81) (.out 0x103a36 (orR8R8Effect 0x103a36 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[79, 61]
    (.letOp (n := 82) (.out 0x103a36 (orR8R8Effect 0x103a36 3 7 0) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 0] []) (.flag .ZF)) #v[79, 61]
    (.letOp (n := 83) (.exec 0x103a36 (fun s => s.RIP = 0x103a36) (orR8R8Effect 0x103a36 3 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[79, 61]
    (.letOp (n := 84) (.pure (condOp 4)) #v[82]
    (.terminate (.condBr (Fin.last 84) ⟨.l103a8c, RegMap.args [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ ⟨.l103a3b, RegMap.args [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l1039fe : List UInt8 :=
  [0x41, 0x8B, 0x76, 0x18, 0x41, 0x8B, 0x4E, 0x1C, 0x29, 0xCE, 0x0F, 0x96, 0xC0, 0x48, 0x8B, 0x54,
    0x24, 0x58, 0x49, 0x89, 0x16, 0x4D, 0x89, 0x66, 0x08, 0x45, 0x89, 0x7E, 0x18, 0x49, 0x8B, 0x56,
    0x10, 0x48, 0x83, 0xFA, 0x01, 0x48, 0x83, 0xD2, 0xFF, 0x49, 0x89, 0x56, 0x10, 0x8B, 0x54, 0x24,
    0x20, 0x83, 0xFA, 0x02, 0x40, 0x0F, 0x95, 0xC7, 0x40, 0x08, 0xC7, 0x74, 0x51]

theorem code_l1039fe : ∀ x ∈ codeRange 0x1039fe bytes_l1039fe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x39fe 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103a3b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103a3b (movR32M32LowEffect 0x103a3b 1 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x103a3b (LoadPre 0x103a3b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x103a3b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103a3b 1 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x103a3f (movR64M64Effect 0x103a3f 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x103a3f (LoadPre 0x103a3f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x103a3f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a3f 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x103a44 (movR64M64Effect 0x103a44 6 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x103a44 (LoadPre 0x103a44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x103a44 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a44 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x103a49 (movR64M64Effect 0x103a49 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x103a49 (LoadPre 0x103a49 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x103a49 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a49 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x103a4e (StorePre 0x103a4e 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103a4e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103a4e 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x103a52 (movR64M64Effect 0x103a52 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x103a52 (LoadPre 0x103a52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103a52 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a52 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x103a57 (StorePre 0x103a57 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103a57 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103a57 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x103a5c (movR64M64Effect 0x103a5c 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x103a5c (LoadPre 0x103a5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103a5c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a5c 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x103a61 (StorePre 0x103a61 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103a61 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103a61 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x103a66 (movR64M64Effect 0x103a66 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x103a66 (LoadPre 0x103a66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x103a66 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103a66 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x103a6b (StorePre 0x103a6b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103a6b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103a6b 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x103a70 (cmpR32Imm8Effect 0x103a70 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 72) (.exec 0x103a70 (fun s => s.RIP = 0x103a70) (cmpR32Imm8Effect 0x103a70 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.pure (condOp 5)) #v[71]
    (.terminate (.condBr (Fin.last 73) ⟨.l103952, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ ⟨.l103a79, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l103a3b : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x24, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x74, 0x24, 0x30, 0x48, 0x8B,
    0x7C, 0x24, 0x38, 0x48, 0x89, 0x3C, 0x24, 0x48, 0x8B, 0x7C, 0x24, 0x40, 0x48, 0x89, 0x7C, 0x24,
    0x08, 0x48, 0x8B, 0x7C, 0x24, 0x48, 0x48, 0x89, 0x7C, 0x24, 0x10, 0x48, 0x8B, 0x7C, 0x24, 0x50,
    0x48, 0x89, 0x7C, 0x24, 0x18, 0x83, 0xFA, 0x02, 0x0F, 0x85, 0xD9, 0xFE, 0xFF, 0xFF]

theorem code_l103a3b : ∀ x ∈ codeRange 0x103a3b bytes_l103a3b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3a3b 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103a79 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103a79 (StorePre 0x103a79 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x103a79 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103a79 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 54) (.exec 0x103a7d (StorePre 0x103a7d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x103a7d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103a7d 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 55) (.exec 0x103a81 (StorePre 0x103a81 6 (fun s => AddrMode.addr (.base 3 .none) s (0x103a81 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x103a81 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l1039bf, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103a79 : List UInt8 :=
  [0x48, 0x89, 0x43, 0x08, 0x48, 0x89, 0x73, 0x10, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0x33,
    0xFF, 0xFF, 0xFF]

theorem code_l103a79 : ∀ x ∈ codeRange 0x103a79 bytes_l103a79, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3a79 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103a8c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103a8c (StorePre 0x103a8c 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x103a8c + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x103a8c (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x103a91 (movR64R64Effect 0x103a91 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 55) (.exec 0x103a91 (fun s => s.RIP = 0x103a91) (movR64R64Effect 0x103a91 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 56) (.out 0x103a94 (shlR64Effect 0x103a94 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 57) (.exec 0x103a94 (fun s => s.RIP = 0x103a94) (shlR64Effect 0x103a94 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[54]
    (.letOp (n := 58) (.out 0x103a98 (orR64Imm8Effect 0x103a98 0 0x13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 59) (.exec 0x103a98 (fun s => s.RIP = 0x103a98) (orR64Imm8Effect 0x103a98 0 0x13) (Reg.operands [.gpr 0] [])) #v[56]
    (.letOp (n := 60) (.out 0x103a9c (movR32Imm32Effect 0x103a9c 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 61) (.exec 0x103a9c (fun s => s.RIP = 0x103a9c) (movR32Imm32Effect 0x103a9c 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x103aa1 (xorR32R32Effect 0x103aa1 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 63) (.exec 0x103aa1 (fun s => s.RIP = 0x103aa1) (xorR32R32Effect 0x103aa1 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l10398a, RegMap.args [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 62), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l103a8c : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x48, 0x89, 0xC8, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x13,
    0xBA, 0x01, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xE9, 0xE2, 0xFE, 0xFF, 0xFF]

theorem code_l103a8c : ∀ x ∈ codeRange 0x103a8c bytes_l103a8c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3a8c 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103aa8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103aa8 (xorR32R32Effect 0x103aa8 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x103aa8 (fun s => s.RIP = 0x103aa8) (xorR32R32Effect 0x103aa8 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.out 0x103aaa (movR32Imm32Effect 0x103aaa 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x103aaa (fun s => s.RIP = 0x103aaa) (movR32Imm32Effect 0x103aaa 5 0 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x103aaf (xorR32R32Effect 0x103aaf 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 58) (.exec 0x103aaf (fun s => s.RIP = 0x103aaf) (xorR32R32Effect 0x103aaf 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l10398a, RegMap.args [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l103aa8 : List UInt8 :=
  [0x31, 0xD2, 0xB8, 0x0C, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xE9, 0xD4, 0xFE, 0xFF, 0xFF]

theorem code_l103aa8 : ∀ x ∈ codeRange 0x103aa8 bytes_l103aa8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3aa8 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103ac0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103ac0 (pushR64Effect 0x103ac0 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 14]
    (.letOp (n := 54) (.exec 0x103ac0 (PushPre 0x103ac0 2) (pushR64Effect 0x103ac0 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 55) (.out 0x103ac2 (pushR64Effect 0x103ac2 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x103ac2 (PushPre 0x103ac2 1) (pushR64Effect 0x103ac2 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x103ac3 (subR64Imm32Effect 0x103ac3 4 0xa8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 58) (.exec 0x103ac3 (fun s => s.RIP = 0x103ac3) (subR64Imm32Effect 0x103ac3 4 0xa8) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 59) (.out 0x103aca (movR64R64Effect 0x103aca 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 60) (.exec 0x103aca (fun s => s.RIP = 0x103aca) (movR64R64Effect 0x103aca 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x103acd (movR64R64Effect 0x103acd 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 62) (.exec 0x103acd (fun s => s.RIP = 0x103acd) (movR64R64Effect 0x103acd 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.out 0x103ad0 (movR64M64Effect 0x103ad0 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 64) (.exec 0x103ad0 (LoadPre 0x103ad0 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x103ad0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103ad0 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.exec 0x103ad4 (StorePre 0x103ad4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x103ad4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103ad4 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 57]
    (.letOp (n := 66) (.out 0x103ad9 (movR64M64Effect 0x103ad9 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 67) (.exec 0x103ad9 (LoadPre 0x103ad9 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x103ad9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103ad9 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 68) (.exec 0x103add (StorePre 0x103add 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x103add + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103add 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 57]
    (.letOp (n := 69) (.out 0x103ae2 (movR64M64Effect 0x103ae2 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 70) (.exec 0x103ae2 (LoadPre 0x103ae2 (fun s => AddrMode.addr (.base 6 .none) s (0x103ae2 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x103ae2 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x103ae5 (movR64M64Effect 0x103ae5 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 72) (.exec 0x103ae5 (LoadPre 0x103ae5 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x103ae5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103ae5 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.exec 0x103ae9 (StorePre 0x103ae9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x103ae9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103ae9 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[71, 57]
    (.letOp (n := 74) (.exec 0x103aee (StorePre 0x103aee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103aee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103aee 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 57]
    (.letOp (n := 75) (.out 0x103af3 (leaR64Effect 0x103af3 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 76) (.exec 0x103af3 (fun s => s.RIP = 0x103af3) (leaR64Effect 0x103af3 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 77) (.out 0x103af8 (leaR64Effect 0x103af8 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[57]
    (.letOp (n := 78) (.exec 0x103af8 (fun s => s.RIP = 0x103af8) (leaR64Effect 0x103af8 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 79) (.out 0x103afd (movR32Imm32Effect 0x103afd 5 2 0x20) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 80) (.exec 0x103afd (fun s => s.RIP = 0x103afd) (movR32Imm32Effect 0x103afd 5 2 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 81) (.out 0x103b02 (callEffect (fun _ => 0x107730) 0x103b07) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 82) (.exec 0x103b02 (PushPre 0x103b02 5) (callEffect (fun _ => 0x107730) 0x103b07) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 83) (.const ⟨64, 0x103b07⟩) #v[]
    (.terminate (.call ⟨.l107730, RegMap.args [(0, 69), (1, 71), (2, 79), (3, 61), (4, 81), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩ { target := .l103b07, kept := #v[], arity := rfl, guard := some (Fin.last 83) }))))))))))))))))))))))))))))))))

def bytes_l103ac0 : List UInt8 :=
  [0x41, 0x56, 0x53, 0x48, 0x81, 0xEC, 0xA8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFB,
    0x48, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x44,
    0x24, 0x58, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x48, 0x89, 0x4C, 0x24, 0x50, 0x48, 0x89,
    0x44, 0x24, 0x48, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0x8D, 0x74, 0x24, 0x48, 0xBA, 0x20, 0x00,
    0x00, 0x00, 0xE8, 0x29, 0x3C, 0x00, 0x00]

theorem code_l103ac0 : ∀ x ∈ codeRange 0x103ac0 bytes_l103ac0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ac0 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103b07 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103b07 (cmpMImm8Effect 0x103b07 5 32 (.sib 4 none 0 (.d8 0x8)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x103b07 (LoadPre 0x103b07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103b07 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x103b07 5 32 (.sib 4 none 0 (.d8 0x8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103c4d, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l103b12, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103b07 : List UInt8 :=
  [0x83, 0x7C, 0x24, 0x08, 0x01, 0x0F, 0x84, 0x3B, 0x01, 0x00, 0x00]

theorem code_l103b07 : ∀ x ∈ codeRange 0x103b07 bytes_l103b07, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3b07 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103b12 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103b12 (movR64M64Effect 0x103b12 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x103b12 (LoadPre 0x103b12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103b12 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b12 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x103b17 (movR64M64Effect 0x103b17 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x103b17 (LoadPre 0x103b17 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103b17 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b17 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x103b1c (movR64M64Effect 0x103b1c 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x103b1c (LoadPre 0x103b1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103b1c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b1c 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x103b21 (StorePre 0x103b21 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x103b21 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b21 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x103b26 (movR64M64Effect 0x103b26 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 61) (.exec 0x103b26 (LoadPre 0x103b26 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x103b26 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b26 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x103b2b (StorePre 0x103b2b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x103b2b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103b2b 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.exec 0x103b33 (StorePre 0x103b33 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x103b33 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b33 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 64) (.exec 0x103b38 (StorePre 0x103b38 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x103b38 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b38 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 65) (.out 0x103b3d (movR64M64Effect 0x103b3d 0 (.base 14 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 66) (.exec 0x103b3d (LoadPre 0x103b3d (fun s => AddrMode.addr (.base 14 (.d8 0x38)) s (0x103b3d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103b3d 0 (.base 14 (.d8 0x38))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 67) (.exec 0x103b41 (StorePre 0x103b41 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x103b41 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b41 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x103b46 (movR64M64Effect 0x103b46 0 (.base 14 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 69) (.exec 0x103b46 (LoadPre 0x103b46 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x103b46 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103b46 0 (.base 14 (.d8 0x30))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 70) (.exec 0x103b4a (StorePre 0x103b4a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x103b4a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b4a 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x103b4f (movR64M64Effect 0x103b4f 0 (.base 14 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 72) (.exec 0x103b4f (LoadPre 0x103b4f (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x103b4f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103b4f 0 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 73) (.out 0x103b53 (movR64M64Effect 0x103b53 1 (.base 14 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 74) (.exec 0x103b53 (LoadPre 0x103b53 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x103b53 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103b53 1 (.base 14 (.d8 0x28))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 75) (.exec 0x103b57 (StorePre 0x103b57 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x103b57 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b57 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.exec 0x103b5c (StorePre 0x103b5c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103b5c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103b5c 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 77) (.out 0x103b61 (leaR64Effect 0x103b61 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 78) (.exec 0x103b61 (fun s => s.RIP = 0x103b61) (leaR64Effect 0x103b61 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x103b66 (leaR64Effect 0x103b66 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 80) (.exec 0x103b66 (fun s => s.RIP = 0x103b66) (leaR64Effect 0x103b66 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x103b6b (movR32Imm32Effect 0x103b6b 5 2 0x20) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 82) (.exec 0x103b6b (fun s => s.RIP = 0x103b6b) (movR32Imm32Effect 0x103b6b 5 2 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 83) (.out 0x103b70 (callEffect (fun _ => 0x107730) 0x103b75) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x103b70 (PushPre 0x103b70 5) (callEffect (fun _ => 0x107730) 0x103b75) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.const ⟨64, 0x103b75⟩) #v[]
    (.terminate (.call ⟨.l107730, RegMap.args [(0, 71), (1, 73), (2, 81), (3, 3), (4, 83), (5, 5), (6, 79), (7, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l103b75, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l103b12 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x48, 0x8B, 0x54, 0x24, 0x20, 0x48,
    0x89, 0x54, 0x24, 0x78, 0x48, 0x8B, 0x54, 0x24, 0x28, 0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x89, 0x4C, 0x24, 0x70, 0x49, 0x8B, 0x46, 0x38, 0x48,
    0x89, 0x44, 0x24, 0x60, 0x49, 0x8B, 0x46, 0x30, 0x48, 0x89, 0x44, 0x24, 0x58, 0x49, 0x8B, 0x46,
    0x20, 0x49, 0x8B, 0x4E, 0x28, 0x48, 0x89, 0x4C, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48,
    0x8D, 0x7C, 0x24, 0x08, 0x48, 0x8D, 0x74, 0x24, 0x48, 0xBA, 0x20, 0x00, 0x00, 0x00, 0xE8, 0xBB,
    0x3B, 0x00, 0x00]

theorem code_l103b12 : ∀ x ∈ codeRange 0x103b12 bytes_l103b12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3b12 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103b75 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103b75 (cmpMImm8Effect 0x103b75 5 32 (.sib 4 none 0 (.d8 0x8)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x103b75 (LoadPre 0x103b75 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103b75 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x103b75 5 32 (.sib 4 none 0 (.d8 0x8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103c4d, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l103b80, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103b75 : List UInt8 :=
  [0x83, 0x7C, 0x24, 0x08, 0x01, 0x0F, 0x84, 0xCD, 0x00, 0x00, 0x00]

theorem code_l103b75 : ∀ x ∈ codeRange 0x103b75 bytes_l103b75, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3b75 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103b80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103b80 (movR64M64Effect 0x103b80 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x103b80 (LoadPre 0x103b80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103b80 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b80 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x103b85 (movR64M64Effect 0x103b85 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x103b85 (LoadPre 0x103b85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103b85 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b85 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x103b8a (movR64M64Effect 0x103b8a 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x103b8a (LoadPre 0x103b8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103b8a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b8a 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x103b8f (StorePre 0x103b8f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x103b8f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103b8f 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x103b97 (movR64M64Effect 0x103b97 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 61) (.exec 0x103b97 (LoadPre 0x103b97 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x103b97 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103b97 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x103b9c (StorePre 0x103b9c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x103b9c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103b9c 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.exec 0x103ba4 (StorePre 0x103ba4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x103ba4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103ba4 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 64) (.exec 0x103bac (StorePre 0x103bac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x103bac + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103bac 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 65) (.exec 0x103bb4 (StorePre 0x103bb4 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103bb4 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103bb4 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x103bbd (StorePre 0x103bbd 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103bbd + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103bbd (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x103bc6 (StorePre 0x103bc6 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103bc6 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103bc6 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x103bcf (StorePre 0x103bcf 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103bcf + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103bcf (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x103bd8 (leaR64Effect 0x103bd8 7 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x103bd8 (fun s => s.RIP = 0x103bd8) (leaR64Effect 0x103bd8 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x103bdd (leaR64Effect 0x103bdd 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 72) (.exec 0x103bdd (fun s => s.RIP = 0x103bdd) (leaR64Effect 0x103bdd 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x103be2 (movR32Imm32Effect 0x103be2 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 74) (.exec 0x103be2 (fun s => s.RIP = 0x103be2) (movR32Imm32Effect 0x103be2 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x103be7 (movR32Imm32Effect 0x103be7 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 76) (.exec 0x103be7 (fun s => s.RIP = 0x103be7) (movR32Imm32Effect 0x103be7 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x103bec (callEffect (fun _ => 0x127f50) 0x103bf1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 78) (.exec 0x103bec (PushPre 0x103bec 5) (callEffect (fun _ => 0x127f50) 0x103bf1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.const ⟨64, 0x103bf1⟩) #v[]
    (.terminate (.call ⟨.l127f50, RegMap.args [(0, 53), (1, 75), (2, 71), (3, 3), (4, 77), (5, 5), (6, 73), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩ { target := .l103bf1, kept := #v[], arity := rfl, guard := some (Fin.last 79) }))))))))))))))))))))))))))))

def bytes_l103b80 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x48, 0x8B, 0x54, 0x24, 0x20, 0x48,
    0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x28, 0x48, 0x89, 0x94, 0x24,
    0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x68, 0x48, 0x8D, 0x54,
    0x24, 0x08, 0xBE, 0x04, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0xE8, 0x5F, 0x43, 0x02,
    0x00]

theorem code_l103b80 : ∀ x ∈ codeRange 0x103b80 bytes_l103b80, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3b80 113 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103bf1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103bf1 (andAlImm8Effect 0x103bf1 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x103bf1 (fun s => s.RIP = 0x103bf1) (andAlImm8Effect 0x103bf1 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x103bf3 (movzxR32R8Effect 0x103bf3 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x103bf3 (fun s => s.RIP = 0x103bf3) (movzxR32R8Effect 0x103bf3 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x103bf6 (callEffect (fun _ => 0x127d50) 0x103bfb) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x103bf6 (PushPre 0x103bf6 5) (callEffect (fun _ => 0x127d50) 0x103bfb) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x103bfb⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l103bfb, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l103bf1 : List UInt8 :=
  [0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x55, 0x41, 0x02, 0x00]

theorem code_l103bf1 : ∀ x ∈ codeRange 0x103bf1 bytes_l103bf1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3bf1 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103bfb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103bfb (testR8R8Effect 0x103bfb 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x103bfb (fun s => s.RIP = 0x103bfb) (testR8R8Effect 0x103bfb 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103c4d, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l103bff, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103bfb : List UInt8 :=
  [0x84, 0xC0, 0x75, 0x4E]

theorem code_l103bfb : ∀ x ∈ codeRange 0x103bfb bytes_l103bfb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3bfb 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103bff : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103bff (StorePre 0x103bff 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103bff + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103bff (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x103c08 (StorePre 0x103c08 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103c08 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103c08 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x103c11 (StorePre 0x103c11 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103c11 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103c11 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x103c1a (StorePre 0x103c1a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103c1a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103c1a (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x103c23 (leaR64Effect 0x103c23 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x103c23 (fun s => s.RIP = 0x103c23) (leaR64Effect 0x103c23 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x103c2b (leaR64Effect 0x103c2b 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x103c2b (fun s => s.RIP = 0x103c2b) (leaR64Effect 0x103c2b 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x103c30 (movR32Imm32Effect 0x103c30 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 62) (.exec 0x103c30 (fun s => s.RIP = 0x103c30) (movR32Imm32Effect 0x103c30 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x103c35 (movR32Imm32Effect 0x103c35 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 64) (.exec 0x103c35 (fun s => s.RIP = 0x103c35) (movR32Imm32Effect 0x103c35 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x103c3a (callEffect (fun _ => 0x127f50) 0x103c3f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x103c3a (PushPre 0x103c3a 5) (callEffect (fun _ => 0x127f50) 0x103c3f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x103c3f⟩) #v[]
    (.terminate (.call ⟨.l127f50, RegMap.args [(0, 0), (1, 63), (2, 59), (3, 3), (4, 65), (5, 5), (6, 61), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l103c3f, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l103bff : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08,
    0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x54, 0x24,
    0x08, 0xBE, 0x04, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0xE8, 0x11, 0x43, 0x02, 0x00]

theorem code_l103bff : ∀ x ∈ codeRange 0x103bff bytes_l103bff, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3bff 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103c3f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103c3f (andAlImm8Effect 0x103c3f 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x103c3f (fun s => s.RIP = 0x103c3f) (andAlImm8Effect 0x103c3f 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x103c41 (movzxR32R8Effect 0x103c41 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x103c41 (fun s => s.RIP = 0x103c41) (movzxR32R8Effect 0x103c41 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x103c44 (callEffect (fun _ => 0x127d50) 0x103c49) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x103c44 (PushPre 0x103c44 5) (callEffect (fun _ => 0x127d50) 0x103c49) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x103c49⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l103c49, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l103c3f : List UInt8 :=
  [0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x07, 0x41, 0x02, 0x00]

theorem code_l103c3f : ∀ x ∈ codeRange 0x103c3f bytes_l103c3f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3c3f 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103c49 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103c49 (testR8R8Effect 0x103c49 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x103c49 (fun s => s.RIP = 0x103c49) (testR8R8Effect 0x103c49 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103c6a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l103c4d, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103c49 : List UInt8 :=
  [0x84, 0xC0, 0x74, 0x1D]

theorem code_l103c49 : ∀ x ∈ codeRange 0x103c49 bytes_l103c49, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3c49 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103c4d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103c4d (StorePre 0x103c4d 8 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x103c4d + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x103c4d (.base 3 (.d8 0x8)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 54) (.exec 0x103c55 (StorePre 0x103c55 7 (fun s => AddrMode.addr (.base 3 .none) s (0x103c55 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x103c55 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l103c5c, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l103c4d : List UInt8 :=
  [0x48, 0xC7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00]

theorem code_l103c4d : ∀ x ∈ codeRange 0x103c4d bytes_l103c4d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3c4d 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103c5c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103c5c (movR64R64Effect 0x103c5c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x103c5c (fun s => s.RIP = 0x103c5c) (movR64R64Effect 0x103c5c 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x103c5f (addR64Imm32Effect 0x103c5f 4 0xa8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x103c5f (fun s => s.RIP = 0x103c5f) (addR64Imm32Effect 0x103c5f 4 0xa8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x103c66 (popR64Effect 0x103c66 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x103c66 (popR64Effect 0x103c66 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x103c66 (PopPre 0x103c66) (popR64Effect 0x103c66 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x103c67 (popR64Effect 0x103c67 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.out 0x103c67 (popR64Effect 0x103c67 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x103c67 (PopPre 0x103c67) (popR64Effect 0x103c67 2 14) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x103c69 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[61]
    (.letOp (n := 64) (.out 0x103c69 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x103c69 (RetPre 0x103c69) (retEffect) (Reg.operands [.gpr 4] [])) #v[61]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66) (some ⟨63, by decide⟩)))))))))))))))

def bytes_l103c5c : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xA8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5E, 0xC3]

theorem code_l103c5c : ∀ x ∈ codeRange 0x103c5c bytes_l103c5c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3c5c 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103c6a_1 : Block Op Label signature Reg.count 81 :=
  .letOp (n := 81) (.exec 0x103cd9 (StorePre 0x103cd9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x103cd9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cd9 0 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 82) (.exec 0x103cdd (StorePre 0x103cdd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x103cdd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cdd 1 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 83) (.exec 0x103ce1 (StorePre 0x103ce1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x103ce1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103ce1 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 84) (.exec 0x103ce5 (StorePre 0x103ce5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x103ce5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103ce5 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 85) (.exec 0x103ce9 (StorePre 0x103ce9 7 (fun s => AddrMode.addr (.base 3 .none) s (0x103ce9 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x103ce9 (.base 3 .none) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l103c5c, RegMap.args [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩))))))

def bytes_l103c6a_1 : List UInt8 :=
  [0x48, 0x89, 0x43, 0x20, 0x48, 0x89, 0x4B, 0x18, 0x48, 0x89, 0x73, 0x10, 0x48, 0x89, 0x53, 0x08,
    0x48, 0xC7, 0x03, 0x00, 0x00, 0x00, 0x00, 0xE9, 0x67, 0xFF, 0xFF, 0xFF]

theorem code_l103c6a_1 : ∀ x ∈ codeRange 0x103cd9 bytes_l103c6a_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3cd9 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103c6a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103c6a (movR64M64Effect 0x103c6a 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x103c6a (LoadPre 0x103c6a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x103c6a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x103c6a 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x103c72 (StorePre 0x103c72 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103c72 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103c72 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x103c77 (movR64M64Effect 0x103c77 1 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x103c77 (LoadPre 0x103c77 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x103c77 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103c77 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x103c7c (StorePre 0x103c7c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103c7c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103c7c 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x103c81 (movR64M64Effect 0x103c81 2 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x103c81 (LoadPre 0x103c81 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x103c81 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103c81 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x103c86 (movR64M64Effect 0x103c86 6 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x103c86 (LoadPre 0x103c86 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x103c86 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103c86 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x103c8b (StorePre 0x103c8b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103c8b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103c8b 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x103c90 (StorePre 0x103c90 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103c90 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103c90 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x103c95 (movR64M64Effect 0x103c95 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x103c95 (LoadPre 0x103c95 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x103c95 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x103c95 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x103c9d (movR64M64Effect 0x103c9d 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 68) (.exec 0x103c9d (LoadPre 0x103c9d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x103c9d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x103c9d 8 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x103ca5 (StorePre 0x103ca5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x103ca5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103ca5 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 70) (.exec 0x103caa (StorePre 0x103caa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x103caa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103caa 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 71) (.out 0x103caf (movR64M64Effect 0x103caf 9 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 72) (.exec 0x103caf (LoadPre 0x103caf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x103caf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x103caf 9 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x103cb7 (StorePre 0x103cb7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x103cb7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103cb7 9 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x103cbc (movR64M64Effect 0x103cbc 10 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 75) (.exec 0x103cbc (LoadPre 0x103cbc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x103cbc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x103cbc 10 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x103cc4 (StorePre 0x103cc4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103cc4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103cc4 10 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.exec 0x103cc9 (StorePre 0x103cc9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x103cc9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cc9 10 (.base 3 (.d8 0x40))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[74, 3]
    (.letOp (n := 78) (.exec 0x103ccd (StorePre 0x103ccd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x103ccd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103ccd 9 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 79) (.exec 0x103cd1 (StorePre 0x103cd1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x103cd1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cd1 8 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 80) (.exec 0x103cd5 (StorePre 0x103cd5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x103cd5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cd5 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[65, 3]
    (b_l103c6a_1))))))))))))))))))))))))))))

def bytes_l103c6a : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x4C,
    0x24, 0x78, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x48, 0x8B, 0x54, 0x24, 0x68, 0x48, 0x8B, 0x74, 0x24,
    0x70, 0x48, 0x89, 0x74, 0x24, 0x10, 0x48, 0x89, 0x54, 0x24, 0x08, 0x48, 0x8B, 0xBC, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x4C, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x7C, 0x24, 0x28,
    0x4C, 0x89, 0x44, 0x24, 0x30, 0x4C, 0x8B, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x4C,
    0x24, 0x38, 0x4C, 0x8B, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x54, 0x24, 0x40, 0x4C,
    0x89, 0x53, 0x40, 0x4C, 0x89, 0x4B, 0x38, 0x4C, 0x89, 0x43, 0x30, 0x48, 0x89, 0x7B, 0x28] ++ bytes_l103c6a_1

theorem code_l103c6a : ∀ x ∈ codeRange 0x103c6a bytes_l103c6a, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x3c6a 111 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l103c6a_1

@[cfg_block] def b_l103ec0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103ec0 (pushR64Effect 0x103ec0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x103ec0 (PushPre 0x103ec0 1) (pushR64Effect 0x103ec0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x103ec1 (pushR64Effect 0x103ec1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x103ec1 (PushPre 0x103ec1 2) (pushR64Effect 0x103ec1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x103ec3 (pushR64Effect 0x103ec3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x103ec3 (PushPre 0x103ec3 2) (pushR64Effect 0x103ec3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x103ec5 (pushR64Effect 0x103ec5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x103ec5 (PushPre 0x103ec5 2) (pushR64Effect 0x103ec5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x103ec7 (pushR64Effect 0x103ec7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x103ec7 (PushPre 0x103ec7 2) (pushR64Effect 0x103ec7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x103ec9 (pushR64Effect 0x103ec9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x103ec9 (PushPre 0x103ec9 1) (pushR64Effect 0x103ec9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x103eca (pushR64Effect 0x103eca 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[63, 0]
    (.letOp (n := 66) (.exec 0x103eca (PushPre 0x103eca 1) (pushR64Effect 0x103eca 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[63, 0]
    (.letOp (n := 67) (.out 0x103ecb (movR64R64Effect 0x103ecb 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x103ecb (fun s => s.RIP = 0x103ecb) (movR64R64Effect 0x103ecb 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x103ece (testR64R64Effect 0x103ece 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 70) (.exec 0x103ece (fun s => s.RIP = 0x103ece) (testR64R64Effect 0x103ece 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 71) (.pure (condOp 4)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l103f0e, RegMap.args [(0, 0), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l103ed3, RegMap.args [(0, 0), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l103ec0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x50, 0x48, 0x89, 0xFB, 0x48, 0x85,
    0xD2, 0x74, 0x3B]

theorem code_l103ec0 : ∀ x ∈ codeRange 0x103ec0 bytes_l103ec0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ec0 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103ed3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103ed3 (movR64R64Effect 0x103ed3 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 54) (.exec 0x103ed3 (fun s => s.RIP = 0x103ed3) (movR64R64Effect 0x103ed3 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x103ed6 (movR64R64Effect 0x103ed6 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 56) (.exec 0x103ed6 (fun s => s.RIP = 0x103ed6) (movR64R64Effect 0x103ed6 12 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x103ed9 (leaR64Effect 0x103ed9 5 (.rip 0x26940)) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 58) (.exec 0x103ed9 (fun s => s.RIP = 0x103ed9) (leaR64Effect 0x103ed9 5 (.rip 0x26940)) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103ee0, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l103ed3 : List UInt8 :=
  [0x49, 0x89, 0xD6, 0x49, 0x89, 0xF4, 0x48, 0x8D, 0x2D, 0x40, 0x69, 0x02, 0x00]

theorem code_l103ed3 : ∀ x ∈ codeRange 0x103ed3 bytes_l103ed3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ed3 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103ee0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103ee0 (cmpR64Imm8Effect 0x103ee0 14 0x20) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[14]
    (.letOp (n := 54) (.exec 0x103ee0 (fun s => s.RIP = 0x103ee0) (cmpR64Imm8Effect 0x103ee0 14 0x20) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x103ee4 (movR32Imm32Effect 0x103ee4 6 13 0x20) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 56) (.exec 0x103ee4 (fun s => s.RIP = 0x103ee4) (movR32Imm32Effect 0x103ee4 6 13 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x103eea (atFlags (condHolds 2) (cmovR64R64Effect 0x103eea 4 13 14)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[55, 14, 53]
    (.letOp (n := 58) (.exec 0x103eea (fun s => s.RIP = 0x103eea) (atFlags (condHolds 2) (cmovR64R64Effect 0x103eea 4 13 14)) (Reg.operands [.gpr 13, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[55, 14, 53]
    (.letOp (n := 59) (.out 0x103eee (leaR64Effect 0x103eee 15 (.sib 12 (some 13) 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12, .gpr 13] []) (.reg (.gpr 15))) #v[12, 57]
    (.letOp (n := 60) (.exec 0x103eee (fun s => s.RIP = 0x103eee) (leaR64Effect 0x103eee 15 (.sib 12 (some 13) 0 .none)) (Reg.operands [.gpr 12, .gpr 13] [])) #v[12, 57]
    (.letOp (n := 61) (.out 0x103ef2 (movR64R64Effect 0x103ef2 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 62) (.exec 0x103ef2 (fun s => s.RIP = 0x103ef2) (movR64R64Effect 0x103ef2 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 63) (.out 0x103ef5 (callEffect (fun _ => 0x104970) 0x103efa) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x103ef5 (PushPre 0x103ef5 5) (callEffect (fun _ => 0x104970) 0x103efa) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x103efa⟩) #v[]
    (.terminate (.call ⟨.l104970, RegMap.args [(3, 3), (4, 63), (5, 5), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 59), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l103efa, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l103ee0 : List UInt8 :=
  [0x49, 0x83, 0xFE, 0x20, 0x41, 0xBD, 0x20, 0x00, 0x00, 0x00, 0x4D, 0x0F, 0x42, 0xEE, 0x4F, 0x8D,
    0x3C, 0x2C, 0x48, 0x89, 0xDF, 0xE8, 0x76, 0x0A, 0x00, 0x00]

theorem code_l103ee0 : ∀ x ∈ codeRange 0x103ee0 bytes_l103ee0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ee0 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103efa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103efa (movR64R64Effect 0x103efa 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 54) (.exec 0x103efa (fun s => s.RIP = 0x103efa) (movR64R64Effect 0x103efa 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x103efd (leaR64Effect 0x103efd 6 (.base 3 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 56) (.exec 0x103efd (fun s => s.RIP = 0x103efd) (leaR64Effect 0x103efd 6 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x103f01 (movR64R64Effect 0x103f01 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 58) (.exec 0x103f01 (fun s => s.RIP = 0x103f01) (movR64R64Effect 0x103f01 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x103f04 (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x103f06) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 60) (.exec 0x103f04 (GoesTo (CallPre 0x103f04 2 (fun s => (Operand.reg 5 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x103f06) 0x12a820) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x103f06) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 61) (.const ⟨64, 0x103f06⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l103f06, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l103efa : List UInt8 :=
  [0x4C, 0x89, 0xE7, 0x48, 0x8D, 0x73, 0x20, 0x4C, 0x89, 0xEA, 0xFF, 0xD5]

theorem code_l103efa : ∀ x ∈ codeRange 0x103efa bytes_l103efa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3efa 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103f06 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103f06 (movR64R64Effect 0x103f06 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15] []) (.reg (.gpr 12))) #v[15]
    (.letOp (n := 54) (.exec 0x103f06 (fun s => s.RIP = 0x103f06) (movR64R64Effect 0x103f06 12 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x103f09 (subR64R64Effect 0x103f09 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[14, 13]
    (.letOp (n := 56) (.out 0x103f09 (subR64R64Effect 0x103f09 14 13) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 13] []) (.flag .ZF)) #v[14, 13]
    (.letOp (n := 57) (.exec 0x103f09 (fun s => s.RIP = 0x103f09) (subR64R64Effect 0x103f09 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[14, 13]
    (.letOp (n := 58) (.pure (condOp 5)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l103ee0, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 55), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l103f0e, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 55), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l103f06 : List UInt8 :=
  [0x4D, 0x89, 0xFC, 0x4D, 0x29, 0xEE, 0x75, 0xD2]

theorem code_l103f06 : ∀ x ∈ codeRange 0x103f06 bytes_l103f06, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3f06 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103f0e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103f0e (movR32Imm32Effect 0x103f0e 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x103f0e (fun s => s.RIP = 0x103f0e) (movR32Imm32Effect 0x103f0e 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x103f13 (movR64R64Effect 0x103f13 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 56) (.exec 0x103f13 (fun s => s.RIP = 0x103f13) (movR64R64Effect 0x103f13 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x103f16 (xorR32R32Effect 0x103f16 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x103f16 (fun s => s.RIP = 0x103f16) (xorR32R32Effect 0x103f16 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x103f18 (addR64Imm8Effect 0x103f18 4 0x8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x103f18 (fun s => s.RIP = 0x103f18) (addR64Imm8Effect 0x103f18 4 0x8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x103f1c (popR64Effect 0x103f1c 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[59]
    (.letOp (n := 62) (.out 0x103f1c (popR64Effect 0x103f1c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x103f1c (PopPre 0x103f1c) (popR64Effect 0x103f1c 1 3) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x103f1d (popR64Effect 0x103f1d 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[62]
    (.letOp (n := 65) (.out 0x103f1d (popR64Effect 0x103f1d 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x103f1d (PopPre 0x103f1d) (popR64Effect 0x103f1d 2 12) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x103f1f (popR64Effect 0x103f1f 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 68) (.out 0x103f1f (popR64Effect 0x103f1f 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x103f1f (PopPre 0x103f1f) (popR64Effect 0x103f1f 2 13) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x103f21 (popR64Effect 0x103f21 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[68]
    (.letOp (n := 71) (.out 0x103f21 (popR64Effect 0x103f21 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x103f21 (PopPre 0x103f21) (popR64Effect 0x103f21 2 14) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x103f23 (popR64Effect 0x103f23 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[71]
    (.letOp (n := 74) (.out 0x103f23 (popR64Effect 0x103f23 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x103f23 (PopPre 0x103f23) (popR64Effect 0x103f23 2 15) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x103f25 (popR64Effect 0x103f25 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[74]
    (.letOp (n := 77) (.out 0x103f25 (popR64Effect 0x103f25 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x103f25 (PopPre 0x103f25) (popR64Effect 0x103f25 1 5) (Reg.operands [.gpr 4] [])) #v[74]
    (.terminate (.br ⟨.l103f30, RegMap.args [(2, 57), (3, 61), (4, 77), (5, 76), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 70), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l103f0e : List UInt8 :=
  [0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0x31, 0xD2, 0x48, 0x83, 0xC4, 0x08, 0x5B, 0x41,
    0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xE9, 0x05, 0x00, 0x00, 0x00]

theorem code_l103f0e : ∀ x ∈ codeRange 0x103f0e bytes_l103f0e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3f0e 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103f30_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.exec 0x103f99 (StorePre 0x103f99 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x103f99 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103f99 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[79, 65]
    (.letOp (n := 88) (.exec 0x103fa1 (StorePre 0x103fa1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x103fa1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103fa1 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[77, 65]
    (.letOp (n := 89) (.exec 0x103fa9 (StorePre 0x103fa9 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x103fa9 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103fa9 (.sib 4 none 0 (.d32 0xc0)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 90) (.exec 0x103fb5 (StorePre 0x103fb5 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x103fb5 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103fb5 (.sib 4 none 0 (.d32 0xc8)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 91) (.exec 0x103fc1 (StorePre 0x103fc1 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x103fc1 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103fc1 (.sib 4 none 0 (.d32 0xd0)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 92) (.exec 0x103fcd (StorePre 0x103fcd 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x103fcd + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103fcd (.sib 4 none 0 (.d32 0xd8)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 93) (.out 0x103fd9 (movR32Imm32Effect 0x103fd9 5 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 94) (.exec 0x103fd9 (fun s => s.RIP = 0x103fd9) (movR32Imm32Effect 0x103fd9 5 0 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 95) (.exec 0x103fde (fun s => s.RIP = 0x103fde) (fun _ => nopEffect 0x103fde 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103fe0, RegMap.args [(0, 93), (1, 79), (2, 81), (3, 3), (4, 65), (5, 71), (6, 83), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩))))))))))

def bytes_l103f30_1 : List UInt8 :=
  [0x48, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0xC8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xB8, 0x03, 0x00, 0x00, 0x00, 0x66, 0x90]

theorem code_l103f30_1 : ∀ x ∈ codeRange 0x103f99 bytes_l103f30_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3f99 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103f30 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103f30 (pushR64Effect 0x103f30 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x103f30 (PushPre 0x103f30 1) (pushR64Effect 0x103f30 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x103f31 (pushR64Effect 0x103f31 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x103f31 (PushPre 0x103f31 2) (pushR64Effect 0x103f31 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x103f33 (pushR64Effect 0x103f33 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x103f33 (PushPre 0x103f33 2) (pushR64Effect 0x103f33 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x103f35 (pushR64Effect 0x103f35 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x103f35 (PushPre 0x103f35 2) (pushR64Effect 0x103f35 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x103f37 (pushR64Effect 0x103f37 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x103f37 (PushPre 0x103f37 2) (pushR64Effect 0x103f37 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x103f39 (pushR64Effect 0x103f39 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x103f39 (PushPre 0x103f39 1) (pushR64Effect 0x103f39 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x103f3a (subR64Imm32Effect 0x103f3a 4 0x298) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x103f3a (fun s => s.RIP = 0x103f3a) (subR64Imm32Effect 0x103f3a 4 0x298) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x103f41 (movR64R64Effect 0x103f41 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2]
    (.letOp (n := 68) (.exec 0x103f41 (fun s => s.RIP = 0x103f41) (movR64R64Effect 0x103f41 15 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x103f44 (movR64R64Effect 0x103f44 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 70) (.exec 0x103f44 (fun s => s.RIP = 0x103f44) (movR64R64Effect 0x103f44 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x103f47 (movR64R64Effect 0x103f47 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 7] []) (.reg (.gpr 5))) #v[7]
    (.letOp (n := 72) (.exec 0x103f47 (fun s => s.RIP = 0x103f47) (movR64R64Effect 0x103f47 5 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.exec 0x103f4a (StorePre 0x103f4a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x103f4a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103f4a (.sib 4 none 0 (.d32 0x228)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 74) (.exec 0x103f56 (StorePre 0x103f56 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x220)) s (0x103f56 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103f56 (.sib 4 none 0 (.d32 0x220)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.exec 0x103f62 (StorePre 0x103f62 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x218)) s (0x103f62 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103f62 (.sib 4 none 0 (.d32 0x218)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 76) (.exec 0x103f6e (StorePre 0x103f6e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x210)) s (0x103f6e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103f6e (.sib 4 none 0 (.d32 0x210)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 77) (.out 0x103f7a (movR64M64Effect 0x103f7a 0 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 78) (.exec 0x103f7a (LoadPre 0x103f7a (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x103f7a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103f7a 0 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 79) (.out 0x103f7e (movR64M64Effect 0x103f7e 1 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 80) (.exec 0x103f7e (LoadPre 0x103f7e (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x103f7e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103f7e 1 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 81) (.out 0x103f82 (movR64M64Effect 0x103f82 2 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 82) (.exec 0x103f82 (LoadPre 0x103f82 (fun s => AddrMode.addr (.base 7 .none) s (0x103f82 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x103f82 2 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 83) (.out 0x103f85 (movR64M64Effect 0x103f85 6 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 84) (.exec 0x103f85 (LoadPre 0x103f85 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x103f85 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103f85 6 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 85) (.exec 0x103f89 (StorePre 0x103f89 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x103f89 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103f89 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[81, 65]
    (.letOp (n := 86) (.exec 0x103f91 (StorePre 0x103f91 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x103f91 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103f91 6 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[83, 65]
    (b_l103f30_1))))))))))))))))))))))))))))))))))

def bytes_l103f30 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x98, 0x02, 0x00,
    0x00, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFD, 0x48, 0xC7, 0x84, 0x24, 0x28, 0x02,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x20, 0x02, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x18, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0x84, 0x24, 0x10, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x47, 0x18, 0x48, 0x8B,
    0x4F, 0x10, 0x48, 0x8B, 0x17, 0x48, 0x8B, 0x77, 0x08, 0x48, 0x89, 0x94, 0x24, 0xA0, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00] ++ bytes_l103f30_1

theorem code_l103f30 : ∀ x ∈ codeRange 0x103f30 bytes_l103f30, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x3f30 105 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l103f30_1

@[cfg_block] def b_l103fe0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103fe0 (StorePre 0x103fe0 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x9d)) s (0x103fe0 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x103fe0 8 (.sib 4 (some 0) 0 (.d32 0x9d)) 0x36) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 54) (.exec 0x103fe8 (StorePre 0x103fe8 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x9e)) s (0x103fe8 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x103fe8 8 (.sib 4 (some 0) 0 (.d32 0x9e)) 0x36) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.exec 0x103ff0 (StorePre 0x103ff0 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x9f)) s (0x103ff0 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x103ff0 8 (.sib 4 (some 0) 0 (.d32 0x9f)) 0x36) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 56) (.exec 0x103ff8 (StorePre 0x103ff8 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0xa0)) s (0x103ff8 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x103ff8 8 (.sib 4 (some 0) 0 (.d32 0xa0)) 0x36) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 57) (.out 0x104000 (addR64Imm8Effect 0x104000 0 0x4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 58) (.exec 0x104000 (fun s => s.RIP = 0x104000) (addR64Imm8Effect 0x104000 0 0x4) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x104004 (cmpR64Imm8Effect 0x104004 0 0x43) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[57]
    (.letOp (n := 60) (.exec 0x104004 (fun s => s.RIP = 0x104004) (cmpR64Imm8Effect 0x104004 0 0x43) (Reg.operands [.gpr 0] [])) #v[57]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l103fe0, RegMap.args [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l10400a, RegMap.args [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l103fe0 : List UInt8 :=
  [0x80, 0xB4, 0x04, 0x9D, 0x00, 0x00, 0x00, 0x36, 0x80, 0xB4, 0x04, 0x9E, 0x00, 0x00, 0x00, 0x36,
    0x80, 0xB4, 0x04, 0x9F, 0x00, 0x00, 0x00, 0x36, 0x80, 0xB4, 0x04, 0xA0, 0x00, 0x00, 0x00, 0x36,
    0x48, 0x83, 0xC0, 0x04, 0x48, 0x83, 0xF8, 0x43, 0x75, 0xD6]

theorem code_l103fe0 : ∀ x ∈ codeRange 0x103fe0 bytes_l103fe0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3fe0 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10400a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10400a (leaR64Effect 0x10400a 7 (.sib 4 none 0 (.d32 0x188))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10400a (fun s => s.RIP = 0x10400a) (leaR64Effect 0x10400a 7 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104012 (movR64Imm64Effect 0x104012 0 0x5be0cd191f83d9ab) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x104012 (fun s => s.RIP = 0x104012) (movR64Imm64Effect 0x104012 0 0x5be0cd191f83d9ab) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.exec 0x10401c (StorePre 0x10401c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x10401c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10401c 0 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x104024 (movR64Imm64Effect 0x104024 0 0x9b05688c510e527f) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 59) (.exec 0x104024 (fun s => s.RIP = 0x104024) (movR64Imm64Effect 0x104024 0 0x9b05688c510e527f) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.exec 0x10402e (StorePre 0x10402e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x10402e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10402e 0 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x104036 (movR64Imm64Effect 0x104036 0 0xa54ff53a3c6ef372) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 62) (.exec 0x104036 (fun s => s.RIP = 0x104036) (movR64Imm64Effect 0x104036 0 0xa54ff53a3c6ef372) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.exec 0x104040 (StorePre 0x104040 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x104040 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104040 0 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x104048 (movR64Imm64Effect 0x104048 0 0xbb67ae856a09e667) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 65) (.exec 0x104048 (fun s => s.RIP = 0x104048) (movR64Imm64Effect 0x104048 0 0xbb67ae856a09e667) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.exec 0x104052 (StorePre 0x104052 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x104052 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104052 0 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x10405a (StorePre 0x10405a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x187)) s (0x10405a + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x10405a (.sib 4 none 0 (.d32 0x187)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x104062 (StorePre 0x104062 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x104062 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x104062 (.sib 4 none 0 (.d32 0x1a8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x10406e (leaR64Effect 0x10406e 6 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x10406e (fun s => s.RIP = 0x10406e) (leaR64Effect 0x10406e 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x104076 (movR32Imm32Effect 0x104076 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 72) (.exec 0x104076 (fun s => s.RIP = 0x104076) (movR32Imm32Effect 0x104076 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x10407b (callEffect (fun _ => 0x1218e0) 0x104080) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 74) (.exec 0x10407b (PushPre 0x10407b 5) (callEffect (fun _ => 0x1218e0) 0x104080) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.const ⟨64, 0x104080⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 64), (1, 1), (2, 71), (3, 3), (4, 73), (5, 5), (6, 69), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ { target := .l104080, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l10400a : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x01, 0x00, 0x00, 0x48, 0xB8, 0xAB, 0xD9, 0x83, 0x1F, 0x19, 0xCD,
    0xE0, 0x5B, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x01, 0x00, 0x00, 0x48, 0xB8, 0x7F, 0x52, 0x0E, 0x51,
    0x8C, 0x68, 0x05, 0x9B, 0x48, 0x89, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00, 0x48, 0xB8, 0x72, 0xF3,
    0x6E, 0x3C, 0x3A, 0xF5, 0x4F, 0xA5, 0x48, 0x89, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00, 0x48, 0xB8,
    0x67, 0xE6, 0x09, 0x6A, 0x85, 0xAE, 0x67, 0xBB, 0x48, 0x89, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00,
    0xC6, 0x84, 0x24, 0x87, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xA8, 0x01, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0xBA, 0x01, 0x00, 0x00,
    0x00, 0xE8, 0x60, 0xD8, 0x01, 0x00]

theorem code_l10400a : ∀ x ∈ codeRange 0x10400a bytes_l10400a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x400a 118 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104080 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104080 (StorePre 0x104080 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x187)) s (0x104080 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x104080 (.sib 4 none 0 (.d32 0x187)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x104088 (movR32Imm32Effect 0x104088 5 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 55) (.exec 0x104088 (fun s => s.RIP = 0x104088) (movR32Imm32Effect 0x104088 5 0 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.exec 0x10408d (fun s => s.RIP = 0x10408d) (fun _ => nopEffect 0x10408d 3) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l104090, RegMap.args [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l104080 : List UInt8 :=
  [0xC6, 0x84, 0x24, 0x87, 0x01, 0x00, 0x00, 0x00, 0xB8, 0x03, 0x00, 0x00, 0x00, 0x0F, 0x1F, 0x00]

theorem code_l104080 : ∀ x ∈ codeRange 0x104080 bytes_l104080, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4080 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104090 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104090 (StorePre 0x104090 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x9d)) s (0x104090 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x104090 8 (.sib 4 (some 0) 0 (.d32 0x9d)) 0x6a) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 54) (.exec 0x104098 (StorePre 0x104098 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x9e)) s (0x104098 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x104098 8 (.sib 4 (some 0) 0 (.d32 0x9e)) 0x6a) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.exec 0x1040a0 (StorePre 0x1040a0 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x9f)) s (0x1040a0 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x1040a0 8 (.sib 4 (some 0) 0 (.d32 0x9f)) 0x6a) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 56) (.exec 0x1040a8 (StorePre 0x1040a8 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0xa0)) s (0x1040a8 + BitVec.ofNat 64 8)) 1) (xorM8Imm8Effect 0x1040a8 8 (.sib 4 (some 0) 0 (.d32 0xa0)) 0x6a) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 57) (.out 0x1040b0 (addR64Imm8Effect 0x1040b0 0 0x4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 58) (.exec 0x1040b0 (fun s => s.RIP = 0x1040b0) (addR64Imm8Effect 0x1040b0 0 0x4) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x1040b4 (cmpR64Imm8Effect 0x1040b4 0 0x43) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[57]
    (.letOp (n := 60) (.exec 0x1040b4 (fun s => s.RIP = 0x1040b4) (cmpR64Imm8Effect 0x1040b4 0 0x43) (Reg.operands [.gpr 0] [])) #v[57]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l104090, RegMap.args [(0, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l1040ba, RegMap.args [(0, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l104090 : List UInt8 :=
  [0x80, 0xB4, 0x04, 0x9D, 0x00, 0x00, 0x00, 0x6A, 0x80, 0xB4, 0x04, 0x9E, 0x00, 0x00, 0x00, 0x6A,
    0x80, 0xB4, 0x04, 0x9F, 0x00, 0x00, 0x00, 0x6A, 0x80, 0xB4, 0x04, 0xA0, 0x00, 0x00, 0x00, 0x6A,
    0x48, 0x83, 0xC0, 0x04, 0x48, 0x83, 0xF8, 0x43, 0x75, 0xD6]

theorem code_l104090 : ∀ x ∈ codeRange 0x104090 bytes_l104090, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4090 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1040ba_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x104152 (leaR64Effect 0x104152 7 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 85) (.exec 0x104152 (fun s => s.RIP = 0x104152) (leaR64Effect 0x104152 7 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.out 0x10415a (leaR64Effect 0x10415a 6 (.sib 4 none 0 (.d32 0x1f0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 87) (.exec 0x10415a (fun s => s.RIP = 0x10415a) (leaR64Effect 0x10415a 6 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.out 0x104162 (movR32Imm32Effect 0x104162 5 2 0xa8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 89) (.exec 0x104162 (fun s => s.RIP = 0x104162) (movR32Imm32Effect 0x104162 5 2 0xa8) (Reg.operands [] [])) #v[]
    (.letOp (n := 90) (.out 0x104167 (callEffect (callMemPtr 0x104167 (.rip 0xffc63)) (0x104167 + BitVec.ofNat 64 (callMemLen (.rip 0xffc63)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 91) (.exec 0x104167 (GoesTo (CallMemPre 0x104167 (.rip 0xffc63)) (callEffect (callMemPtr 0x104167 (.rip 0xffc63)) (0x104167 + BitVec.ofNat 64 (callMemLen (.rip 0xffc63)))) 0x12a820) (callEffect (callMemPtr 0x104167 (.rip 0xffc63)) (0x104167 + BitVec.ofNat 64 (callMemLen (.rip 0xffc63)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.const ⟨64, 0x10416d⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 78), (1, 80), (2, 88), (3, 3), (4, 90), (5, 5), (6, 86), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩ { target := .l10416d, kept := #v[], arity := rfl, guard := some (Fin.last 92) }))))))))))

def bytes_l1040ba_1 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0xF0, 0x01, 0x00, 0x00,
    0xBA, 0xA8, 0x00, 0x00, 0x00, 0xFF, 0x15, 0x63, 0xFC, 0x0F, 0x00]

theorem code_l1040ba_1 : ∀ x ∈ codeRange 0x104152 bytes_l1040ba_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4152 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1040ba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1040ba (leaR64Effect 0x1040ba 7 (.sib 4 none 0 (.d32 0x230))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1040ba (fun s => s.RIP = 0x1040ba) (leaR64Effect 0x1040ba 7 (.sib 4 none 0 (.d32 0x230))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1040c2 (leaR64Effect 0x1040c2 6 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x1040c2 (fun s => s.RIP = 0x1040c2) (leaR64Effect 0x1040c2 6 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1040ca (movR32Imm32Effect 0x1040ca 5 1 0xd) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x1040ca (fun s => s.RIP = 0x1040ca) (movR32Imm32Effect 0x1040ca 5 1 0xd) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x1040cf (RepPre 0x1040cf (RepMovsqPre 0x1040cf)) (repMovsqEffect 0x1040cf) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[55, 53, 57, 22]
    (.letOp (n := 60) (.out 0x1040d2 (movR64M64Effect 0x1040d2 0 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 61) (.exec 0x1040d2 (LoadPre 0x1040d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1040d2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1040d2 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x1040da (StorePre 0x1040da 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x1040da + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1040da 0 (.sib 4 none 0 (.d32 0x228))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x1040e2 (movR64M64Effect 0x1040e2 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x1040e2 (LoadPre 0x1040e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1040e2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1040e2 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x1040ea (StorePre 0x1040ea 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x220)) s (0x1040ea + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1040ea 0 (.sib 4 none 0 (.d32 0x220))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x1040f2 (movR64M64Effect 0x1040f2 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 67) (.exec 0x1040f2 (LoadPre 0x1040f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1040f2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1040f2 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x1040fa (StorePre 0x1040fa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x218)) s (0x1040fa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1040fa 0 (.sib 4 none 0 (.d32 0x218))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x104102 (movR64M64Effect 0x104102 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 70) (.exec 0x104102 (LoadPre 0x104102 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x104102 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104102 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x10410a (StorePre 0x10410a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x210)) s (0x10410a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10410a 0 (.sib 4 none 0 (.d32 0x210))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.out 0x104112 (movR64M64Effect 0x104112 0 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 73) (.exec 0x104112 (LoadPre 0x104112 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x104112 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104112 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x10411a (StorePre 0x10411a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x208)) s (0x10411a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10411a 0 (.sib 4 none 0 (.d32 0x208))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x104122 (movR64M64Effect 0x104122 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 76) (.exec 0x104122 (LoadPre 0x104122 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x104122 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104122 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x10412a (StorePre 0x10412a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x200)) s (0x10412a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10412a 0 (.sib 4 none 0 (.d32 0x200))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x104132 (movR64M64Effect 0x104132 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 79) (.exec 0x104132 (LoadPre 0x104132 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x104132 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104132 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x10413a (movR64M64Effect 0x10413a 1 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 81) (.exec 0x10413a (LoadPre 0x10413a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10413a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10413a 1 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x104142 (StorePre 0x104142 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f8)) s (0x104142 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104142 1 (.sib 4 none 0 (.d32 0x1f8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.exec 0x10414a (StorePre 0x10414a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f0)) s (0x10414a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10414a 0 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 4]
    (b_l1040ba_1)))))))))))))))))))))))))))))))

def bytes_l1040ba : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x30, 0x02, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x48, 0x01, 0x00, 0x00,
    0xB9, 0x0D, 0x00, 0x00, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0x28, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0x20, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0x18, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0x10, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0x08, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0x00, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xF8, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0xF0, 0x01, 0x00, 0x00] ++ bytes_l1040ba_1

theorem code_l1040ba : ∀ x ∈ codeRange 0x1040ba bytes_l1040ba, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x40ba 152 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1040ba_1

@[cfg_block] def b_l10416d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10416d (leaR64Effect 0x10416d 6 (.base 5 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 54) (.exec 0x10416d (fun s => s.RIP = 0x10416d) (leaR64Effect 0x10416d 6 (.base 5 (.d8 0x20))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x104171 (leaR64Effect 0x104171 13 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 56) (.exec 0x104171 (fun s => s.RIP = 0x104171) (leaR64Effect 0x104171 13 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x104179 (movzxR32M8Effect 0x104179 8 3 (.sib 4 none 0 (.d32 0x11f))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 58) (.exec 0x104179 (LoadPre 0x104179 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x104179 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x104179 8 3 (.sib 4 none 0 (.d32 0x11f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x104181 (cmpR64Imm8Effect 0x104181 3 0x1f) (EffectPart.reads (.flag .CF) [.gpr 3] []) (.flag .CF)) #v[57]
    (.letOp (n := 60) (.out 0x104181 (cmpR64Imm8Effect 0x104181 3 0x1f) (EffectPart.reads (.flag .ZF) [.gpr 3] []) (.flag .ZF)) #v[57]
    (.letOp (n := 61) (.exec 0x104181 (fun s => s.RIP = 0x104181) (cmpR64Imm8Effect 0x104181 3 0x1f) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 62) (.exec 0x104185 (StorePre 0x104185 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x104185 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104185 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 63) (.pure (condOp 7)) #v[59, 60]
    (.terminate (.condBr (Fin.last 63) ⟨.l1045e4, RegMap.args [(3, 57), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (16, 59), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l104190, RegMap.args [(3, 57), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (16, 59), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l10416d : List UInt8 :=
  [0x48, 0x8D, 0x75, 0x20, 0x4C, 0x8D, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x9C, 0x24,
    0x1F, 0x01, 0x00, 0x00, 0x48, 0x83, 0xFB, 0x1F, 0x48, 0x89, 0x74, 0x24, 0x70, 0x0F, 0x87, 0x54,
    0x04, 0x00, 0x00]

theorem code_l10416d : ∀ x ∈ codeRange 0x10416d bytes_l10416d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x416d 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104190 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104190 (movR64M64Effect 0x104190 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x104190 (LoadPre 0x104190 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x104190 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104190 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.exec 0x104194 (StorePre 0x104194 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x18)) s (0x104194 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104194 0 (.sib 13 (some 3) 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 13, .gpr 3] [])) #v[53, 13, 3]
    (.letOp (n := 56) (.out 0x104199 (movR64M64Effect 0x104199 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 57) (.exec 0x104199 (LoadPre 0x104199 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x104199 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104199 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 58) (.exec 0x10419d (StorePre 0x10419d 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x10)) s (0x10419d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10419d 0 (.sib 13 (some 3) 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 13, .gpr 3] [])) #v[56, 13, 3]
    (.letOp (n := 59) (.out 0x1041a2 (movR64M64Effect 0x1041a2 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 60) (.exec 0x1041a2 (LoadPre 0x1041a2 (fun s => AddrMode.addr (.base 6 .none) s (0x1041a2 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1041a2 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x1041a5 (movR64M64Effect 0x1041a5 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 62) (.exec 0x1041a5 (LoadPre 0x1041a5 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1041a5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1041a5 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.exec 0x1041a9 (StorePre 0x1041a9 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x8)) s (0x1041a9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1041a9 1 (.sib 13 (some 3) 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 13, .gpr 3] [])) #v[61, 13, 3]
    (.letOp (n := 64) (.exec 0x1041ae (StorePre 0x1041ae 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x0)) s (0x1041ae + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1041ae 0 (.sib 13 (some 3) 0 (.d8 0x0))) (Reg.operands [.gpr 0, .gpr 13, .gpr 3] [])) #v[59, 13, 3]
    (.letOp (n := 65) (.out 0x1041b3 (orR8Imm8Effect 0x1041b3 3 3 0x20) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 66) (.exec 0x1041b3 (fun s => s.RIP = 0x1041b3) (orR8Imm8Effect 0x1041b3 3 3 0x20) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 67) (.exec 0x1041b6 (StorePre 0x1041b6 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x1041b6 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1041b6 7 3 (.sib 4 none 0 (.d32 0x11f))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1041bd (movzxR32R8Effect 0x1041bd 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 69) (.exec 0x1041bd (fun s => s.RIP = 0x1041bd) (movzxR32R8Effect 0x1041bd 3 0 3) (Reg.operands [.gpr 3] [])) #v[65]
    (.letOp (n := 70) (.out 0x1041c0 (cmpAlImm8Effect 0x1041c0 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[68]
    (.letOp (n := 71) (.exec 0x1041c0 (fun s => s.RIP = 0x1041c0) (cmpAlImm8Effect 0x1041c0 0x3f) (Reg.operands [.gpr 0] [])) #v[68]
    (.letOp (n := 72) (.pure (condOp 4)) #v[70]
    (.terminate (.condBr (Fin.last 72) ⟨.l10465f, RegMap.args [(0, 68), (1, 61), (3, 65), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩ ⟨.l1041c8, RegMap.args [(0, 68), (1, 61), (3, 65), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l104190 : List UInt8 :=
  [0x48, 0x8B, 0x46, 0x18, 0x49, 0x89, 0x44, 0x1D, 0x18, 0x48, 0x8B, 0x46, 0x10, 0x49, 0x89, 0x44,
    0x1D, 0x10, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x49, 0x89, 0x4C, 0x1D, 0x08, 0x49, 0x89,
    0x44, 0x1D, 0x00, 0x80, 0xCB, 0x20, 0x88, 0x9C, 0x24, 0x1F, 0x01, 0x00, 0x00, 0x0F, 0xB6, 0xC3,
    0x3C, 0x3F, 0x0F, 0x84, 0x97, 0x04, 0x00, 0x00]

theorem code_l104190 : ∀ x ∈ codeRange 0x104190 bytes_l104190, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4190 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1041c8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1041c8 (StorePre 0x1041c8 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0xe0)) s (0x1041c8 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x1041c8 (.sib 4 (some 0) 0 (.d32 0xe0)) 0x0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 54) (.out 0x1041d0 (leaR32Effect 0x1041d0 3 3 (.base 0 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[0]
    (.letOp (n := 55) (.exec 0x1041d0 (fun s => s.RIP = 0x1041d0) (leaR32Effect 0x1041d0 3 3 (.base 0 (.d8 0x1))) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 56) (.exec 0x1041d3 (StorePre 0x1041d3 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x1041d3 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1041d3 7 3 (.sib 4 none 0 (.d32 0x11f))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 57) (.out 0x1041da (testR64R64Effect 0x1041da 15 15) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 15] []) (.flag .ZF)) #v[15, 15]
    (.letOp (n := 58) (.exec 0x1041da (fun s => s.RIP = 0x1041da) (testR64R64Effect 0x1041da 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1046a2, RegMap.args [(0, 0), (3, 54), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1041e3, RegMap.args [(0, 0), (3, 54), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1041c8 : List UInt8 :=
  [0xC6, 0x84, 0x04, 0xE0, 0x00, 0x00, 0x00, 0x00, 0x8D, 0x58, 0x01, 0x88, 0x9C, 0x24, 0x1F, 0x01,
    0x00, 0x00, 0x4D, 0x85, 0xFF, 0x0F, 0x84, 0xBF, 0x04, 0x00, 0x00]

theorem code_l1041c8 : ∀ x ∈ codeRange 0x1041c8 bytes_l1041c8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x41c8 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1041e3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1041e3 (StorePre 0x1041e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1041e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1041e3 5 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 54) (.out 0x1041e8 (shlR64Effect 0x1041e8 4 15 4) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 55) (.exec 0x1041e8 (fun s => s.RIP = 0x1041e8) (shlR64Effect 0x1041e8 4 15 4) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[15]
    (.letOp (n := 56) (.out 0x1041ec (addR64R64Effect 0x1041ec 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[54, 14]
    (.letOp (n := 57) (.exec 0x1041ec (fun s => s.RIP = 0x1041ec) (addR64R64Effect 0x1041ec 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[54, 14]
    (.letOp (n := 58) (.exec 0x1041ef (StorePre 0x1041ef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1041ef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1041ef 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1041f4 (movR64R64Effect 0x1041f4 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 60) (.exec 0x1041f4 (fun s => s.RIP = 0x1041f4) (movR64R64Effect 0x1041f4 15 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.terminate (.br ⟨.l10422b, RegMap.args [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1041e3 : List UInt8 :=
  [0x48, 0x89, 0x6C, 0x24, 0x78, 0x49, 0xC1, 0xE7, 0x04, 0x4D, 0x01, 0xF7, 0x4C, 0x89, 0x7C, 0x24,
    0x08, 0x4D, 0x89, 0xF7, 0xEB, 0x32]

theorem code_l1041e3 : ∀ x ∈ codeRange 0x1041e3 bytes_l1041e3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x41e3 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104200 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104200 (movR32R32Effect 0x104200 2 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 7] []) (.reg (.gpr 5))) #v[7]
    (.letOp (n := 54) (.exec 0x104200 (fun s => s.RIP = 0x104200) (movR32R32Effect 0x104200 2 5 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x104202 (addR64R64Effect 0x104202 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[7, 13]
    (.letOp (n := 56) (.exec 0x104202 (fun s => s.RIP = 0x104202) (addR64R64Effect 0x104202 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[7, 13]
    (.letOp (n := 57) (.out 0x104205 (movR64R64Effect 0x104205 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 58) (.exec 0x104205 (fun s => s.RIP = 0x104205) (movR64R64Effect 0x104205 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x104208 (movR64R64Effect 0x104208 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 60) (.exec 0x104208 (fun s => s.RIP = 0x104208) (movR64R64Effect 0x104208 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 61) (.out 0x10420b (callEffect (callMemPtr 0x10420b (.rip 0xffbbf)) (0x10420b + BitVec.ofNat 64 (callMemLen (.rip 0xffbbf)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x10420b (GoesTo (CallMemPre 0x10420b (.rip 0xffbbf)) (callEffect (callMemPtr 0x10420b (.rip 0xffbbf)) (0x10420b + BitVec.ofNat 64 (callMemLen (.rip 0xffbbf)))) 0x12a820) (callEffect (callMemPtr 0x10420b (.rip 0xffbbf)) (0x10420b + BitVec.ofNat 64 (callMemLen (.rip 0xffbbf)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x104211⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 53), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l104211, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l104200 : List UInt8 :=
  [0x89, 0xFD, 0x4C, 0x01, 0xEF, 0x48, 0x89, 0xDE, 0x4C, 0x89, 0xE2, 0xFF, 0x15, 0xBF, 0xFB, 0x0F,
    0x00]

theorem code_l104200 : ∀ x ∈ codeRange 0x104200 bytes_l104200, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4200 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104211 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104211 (addR8R8Effect 0x104211 3 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[12, 5]
    (.letOp (n := 54) (.exec 0x104211 (fun s => s.RIP = 0x104211) (addR8R8Effect 0x104211 3 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[12, 5]
    (.letOp (n := 55) (.exec 0x104214 (StorePre 0x104214 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x104214 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x104214 8 12 (.sib 4 none 0 (.d32 0x11f))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10421c (addR64Imm8Effect 0x10421c 15 0x10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 57) (.exec 0x10421c (fun s => s.RIP = 0x10421c) (addR64Imm8Effect 0x10421c 15 0x10) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 58) (.out 0x104220 (cmpR64M64Effect 0x104220 15 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 4] []) (.flag .ZF)) #v[56, 4]
    (.letOp (n := 59) (.exec 0x104220 (LoadPre 0x104220 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104220 + BitVec.ofNat 64 5)) 8) (cmpR64M64Effect 0x104220 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 60) (.pure (condOp 4)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l10430c, RegMap.args [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 56), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l10422b, RegMap.args [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 56), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l104211 : List UInt8 :=
  [0x41, 0x00, 0xEC, 0x44, 0x88, 0xA4, 0x24, 0x1F, 0x01, 0x00, 0x00, 0x49, 0x83, 0xC7, 0x10, 0x4C,
    0x3B, 0x7C, 0x24, 0x08, 0x0F, 0x84, 0xE1, 0x00, 0x00, 0x00]

theorem code_l104211 : ∀ x ∈ codeRange 0x104211 bytes_l104211, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4211 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10422b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10422b (movR64M64Effect 0x10422b 3 (.base 15 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[15]
    (.letOp (n := 54) (.exec 0x10422b (LoadPre 0x10422b (fun s => AddrMode.addr (.base 15 .none) s (0x10422b + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10422b 3 (.base 15 .none)) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x10422e (movR64M64Effect 0x10422e 12 (.base 15 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15] []) (.reg (.gpr 12))) #v[15]
    (.letOp (n := 56) (.exec 0x10422e (LoadPre 0x10422e (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x10422e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10422e 12 (.base 15 (.d8 0x8))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x104232 (movzxR32M8Effect 0x104232 8 7 (.sib 4 none 0 (.d32 0x11f))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x104232 (LoadPre 0x104232 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x104232 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x104232 8 7 (.sib 4 none 0 (.d32 0x11f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10423a (movR32Imm32Effect 0x10423a 5 2 0x40) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x10423a (fun s => s.RIP = 0x10423a) (movR32Imm32Effect 0x10423a 5 2 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10423f (subR64R64Effect 0x10423f 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x10423f (fun s => s.RIP = 0x10423f) (subR64R64Effect 0x10423f 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x104242 (movR64R64Effect 0x104242 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 12] []) (.reg (.gpr 5))) #v[55]
    (.letOp (n := 64) (.exec 0x104242 (fun s => s.RIP = 0x104242) (movR64R64Effect 0x104242 5 12) (Reg.operands [.gpr 12] [])) #v[55]
    (.letOp (n := 65) (.out 0x104245 (subR64R64Effect 0x104245 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[63, 61]
    (.letOp (n := 66) (.out 0x104245 (subR64R64Effect 0x104245 5 2) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 2] []) (.flag .CF)) #v[63, 61]
    (.letOp (n := 67) (.exec 0x104245 (fun s => s.RIP = 0x104245) (subR64R64Effect 0x104245 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[63, 61]
    (.letOp (n := 68) (.pure (condOp 2)) #v[66]
    (.terminate (.condBr (Fin.last 68) ⟨.l104200, RegMap.args [(0, 0), (2, 61), (3, 53), (4, 4), (5, 65), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (16, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ ⟨.l10424a, RegMap.args [(0, 0), (2, 61), (3, 53), (4, 4), (5, 65), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (16, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l10422b : List UInt8 :=
  [0x49, 0x8B, 0x1F, 0x4D, 0x8B, 0x67, 0x08, 0x0F, 0xB6, 0xBC, 0x24, 0x1F, 0x01, 0x00, 0x00, 0xBA,
    0x40, 0x00, 0x00, 0x00, 0x48, 0x29, 0xFA, 0x4C, 0x89, 0xE5, 0x48, 0x29, 0xD5, 0x72, 0xB6]

theorem code_l10422b : ∀ x ∈ codeRange 0x10422b bytes_l10422b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x422b 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10424a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10424a (testR64R64Effect 0x10424a 7 7) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 7] []) (.flag .ZF)) #v[7, 7]
    (.letOp (n := 54) (.exec 0x10424a (fun s => s.RIP = 0x10424a) (testR64R64Effect 0x10424a 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1042f4, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l104253, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10424a : List UInt8 :=
  [0x48, 0x85, 0xFF, 0x0F, 0x84, 0xA1, 0x00, 0x00, 0x00]

theorem code_l10424a : ∀ x ∈ codeRange 0x10424a bytes_l10424a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x424a 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104253 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104253 (leaR64Effect 0x104253 12 (.sib 3 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3, .gpr 2] []) (.reg (.gpr 12))) #v[3, 2]
    (.letOp (n := 54) (.exec 0x104253 (fun s => s.RIP = 0x104253) (leaR64Effect 0x104253 12 (.sib 3 (some 2) 0 .none)) (Reg.operands [.gpr 3, .gpr 2] [])) #v[3, 2]
    (.letOp (n := 55) (.out 0x104257 (addR64R64Effect 0x104257 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[7, 13]
    (.letOp (n := 56) (.exec 0x104257 (fun s => s.RIP = 0x104257) (addR64R64Effect 0x104257 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[7, 13]
    (.letOp (n := 57) (.out 0x10425a (movR64R64Effect 0x10425a 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 58) (.exec 0x10425a (fun s => s.RIP = 0x10425a) (movR64R64Effect 0x10425a 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x10425d (callEffect (callMemPtr 0x10425d (.rip 0xffb6d)) (0x10425d + BitVec.ofNat 64 (callMemLen (.rip 0xffb6d)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10425d (GoesTo (CallMemPre 0x10425d (.rip 0xffb6d)) (callEffect (callMemPtr 0x10425d (.rip 0xffb6d)) (0x10425d + BitVec.ofNat 64 (callMemLen (.rip 0xffb6d)))) 0x12a820) (callEffect (callMemPtr 0x10425d (.rip 0xffb6d)) (0x10425d + BitVec.ofNat 64 (callMemLen (.rip 0xffb6d)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x104263⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 2), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l104263, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l104253 : List UInt8 :=
  [0x4C, 0x8D, 0x24, 0x13, 0x4C, 0x01, 0xEF, 0x48, 0x89, 0xDE, 0xFF, 0x15, 0x6D, 0xFB, 0x0F, 0x00]

theorem code_l104253 : ∀ x ∈ codeRange 0x104253 bytes_l104253, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4253 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104263 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104263 (StorePre 0x104263 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x104263 + BitVec.ofNat 64 8)) 8) (incMEffect 0x104263 8 64 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x10426b (movR32Imm32Effect 0x10426b 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 55) (.exec 0x10426b (fun s => s.RIP = 0x10426b) (movR32Imm32Effect 0x10426b 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.out 0x104270 (leaR64Effect 0x104270 7 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 57) (.exec 0x104270 (fun s => s.RIP = 0x104270) (leaR64Effect 0x104270 7 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x104278 (movR64R64Effect 0x104278 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 59) (.exec 0x104278 (fun s => s.RIP = 0x104278) (movR64R64Effect 0x104278 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 60) (.out 0x10427b (callEffect (fun _ => 0x1218e0) 0x104280) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x10427b (PushPre 0x10427b 5) (callEffect (fun _ => 0x1218e0) 0x104280) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x104280⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ { target := .l104280, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l104263 : List UInt8 :=
  [0x48, 0xFF, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC,
    0x24, 0x20, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xEE, 0xE8, 0x60, 0xD6, 0x01, 0x00]

theorem code_l104263 : ∀ x ∈ codeRange 0x104263 bytes_l104263, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4263 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104280 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104280 (StorePre 0x104280 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x104280 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x104280 (.sib 4 none 0 (.d32 0x11f)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x104288 (movR64R64Effect 0x104288 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[12]
    (.letOp (n := 55) (.exec 0x104288 (fun s => s.RIP = 0x104288) (movR64R64Effect 0x104288 3 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 56) (.out 0x10428b (movR64Imm64Effect 0x10428b 1 0x7fffffffffffffc0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 57) (.exec 0x10428b (fun s => s.RIP = 0x10428b) (movR64Imm64Effect 0x10428b 1 0x7fffffffffffffc0) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x104295 (movR64R64Effect 0x104295 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 59) (.exec 0x104295 (fun s => s.RIP = 0x104295) (movR64R64Effect 0x104295 2 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 60) (.out 0x104298 (shrR64Effect 0x104298 4 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[58]
    (.letOp (n := 61) (.out 0x104298 (shrR64Effect 0x104298 4 2 6) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[58]
    (.letOp (n := 62) (.exec 0x104298 (fun s => s.RIP = 0x104298) (shrR64Effect 0x104298 4 2 6) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[58]
    (.letOp (n := 63) (.pure (condOp 4)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l1042c0, RegMap.args [(0, 0), (1, 56), (2, 60), (3, 54), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l10429e, RegMap.args [(0, 0), (1, 56), (2, 60), (3, 54), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l104280 : List UInt8 :=
  [0xC6, 0x84, 0x24, 0x1F, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE3, 0x48, 0xB9, 0xC0, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x48, 0x89, 0xEA, 0x48, 0xC1, 0xEA, 0x06, 0x74, 0x22]

theorem code_l104280 : ∀ x ∈ codeRange 0x104280 bytes_l104280, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4280 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10429e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10429e (StorePre 0x10429e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10429e + BitVec.ofNat 64 8)) 8) (addMREffect 0x10429e 8 64 2 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 54) (.out 0x1042a6 (leaR64Effect 0x1042a6 7 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x1042a6 (fun s => s.RIP = 0x1042a6) (leaR64Effect 0x1042a6 7 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1042ae (movR64R64Effect 0x1042ae 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 57) (.exec 0x1042ae (fun s => s.RIP = 0x1042ae) (movR64R64Effect 0x1042ae 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 58) (.out 0x1042b1 (callEffect (fun _ => 0x1218e0) 0x1042b6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 59) (.exec 0x1042b1 (PushPre 0x1042b1 5) (callEffect (fun _ => 0x1218e0) 0x1042b6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.const ⟨64, 0x1042b6⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ { target := .l1042b6, kept := #v[], arity := rfl, guard := some (Fin.last 60) })))))))))

def bytes_l10429e : List UInt8 :=
  [0x48, 0x01, 0x94, 0x24, 0x40, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x20, 0x01, 0x00, 0x00,
    0x48, 0x89, 0xDE, 0xE8, 0x2A, 0xD6, 0x01, 0x00]

theorem code_l10429e : ∀ x ∈ codeRange 0x10429e bytes_l10429e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x429e 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1042b6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1042b6 (movR64Imm64Effect 0x1042b6 1 0x7fffffffffffffc0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x1042b6 (fun s => s.RIP = 0x1042b6) (movR64Imm64Effect 0x1042b6 1 0x7fffffffffffffc0) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1042c0, RegMap.args [(1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1042b6 : List UInt8 :=
  [0x48, 0xB9, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F]

theorem code_l1042b6 : ∀ x ∈ codeRange 0x1042b6 bytes_l1042b6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x42b6 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1042c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1042c0 (movR64R64Effect 0x1042c0 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 54) (.exec 0x1042c0 (fun s => s.RIP = 0x1042c0) (movR64R64Effect 0x1042c0 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x1042c3 (andR64R64Effect 0x1042c3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[53, 1]
    (.letOp (n := 56) (.exec 0x1042c3 (fun s => s.RIP = 0x1042c3) (andR64R64Effect 0x1042c3 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[53, 1]
    (.letOp (n := 57) (.out 0x1042c6 (andR32Imm8Effect 0x1042c6 3 5 0x3f) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 58) (.exec 0x1042c6 (fun s => s.RIP = 0x1042c6) (andR32Imm8Effect 0x1042c6 3 5 0x3f) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x1042c9 (addR64R64Effect 0x1042c9 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[3, 55]
    (.letOp (n := 60) (.exec 0x1042c9 (fun s => s.RIP = 0x1042c9) (addR64R64Effect 0x1042c9 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[3, 55]
    (.letOp (n := 61) (.exec 0x1042cc (StorePre 0x1042cc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x1042cc + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x1042cc 8 5 (.sib 4 none 0 (.d32 0x11f))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 62) (.out 0x1042d4 (movR64R64Effect 0x1042d4 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 63) (.exec 0x1042d4 (fun s => s.RIP = 0x1042d4) (movR64R64Effect 0x1042d4 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 64) (.out 0x1042d7 (movR64R64Effect 0x1042d7 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[59]
    (.letOp (n := 65) (.exec 0x1042d7 (fun s => s.RIP = 0x1042d7) (movR64R64Effect 0x1042d7 6 3) (Reg.operands [.gpr 3] [])) #v[59]
    (.letOp (n := 66) (.out 0x1042da (movR64R64Effect 0x1042da 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 67) (.exec 0x1042da (fun s => s.RIP = 0x1042da) (movR64R64Effect 0x1042da 2 5) (Reg.operands [.gpr 5] [])) #v[57]
    (.letOp (n := 68) (.out 0x1042dd (callEffect (callMemPtr 0x1042dd (.rip 0xffaed)) (0x1042dd + BitVec.ofNat 64 (callMemLen (.rip 0xffaed)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 69) (.exec 0x1042dd (GoesTo (CallMemPre 0x1042dd (.rip 0xffaed)) (callEffect (callMemPtr 0x1042dd (.rip 0xffaed)) (0x1042dd + BitVec.ofNat 64 (callMemLen (.rip 0xffaed)))) 0x12a820) (callEffect (callMemPtr 0x1042dd (.rip 0xffaed)) (0x1042dd + BitVec.ofNat 64 (callMemLen (.rip 0xffaed)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.const ⟨64, 0x1042e3⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 55), (1, 1), (2, 66), (3, 59), (4, 68), (5, 57), (6, 64), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l1042e3, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l1042c0 : List UInt8 :=
  [0x48, 0x89, 0xE8, 0x48, 0x21, 0xC8, 0x83, 0xE5, 0x3F, 0x48, 0x01, 0xC3, 0x40, 0x88, 0xAC, 0x24,
    0x1F, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x48, 0x89, 0xDE, 0x48, 0x89, 0xEA, 0xFF, 0x15, 0xED,
    0xFA, 0x0F, 0x00]

theorem code_l1042c0 : ∀ x ∈ codeRange 0x1042c0 bytes_l1042c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x42c0 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1042e3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1042e3 (addR64Imm8Effect 0x1042e3 15 0x10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 54) (.exec 0x1042e3 (fun s => s.RIP = 0x1042e3) (addR64Imm8Effect 0x1042e3 15 0x10) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x1042e7 (cmpR64M64Effect 0x1042e7 15 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 4] []) (.flag .ZF)) #v[53, 4]
    (.letOp (n := 56) (.exec 0x1042e7 (LoadPre 0x1042e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1042e7 + BitVec.ofNat 64 5)) 8) (cmpR64M64Effect 0x1042e7 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l10422b, RegMap.args [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1042f2, RegMap.args [(0, 0), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1042e3 : List UInt8 :=
  [0x49, 0x83, 0xC7, 0x10, 0x4C, 0x3B, 0x7C, 0x24, 0x08, 0x0F, 0x85, 0x39, 0xFF, 0xFF, 0xFF]

theorem code_l1042e3 : ∀ x ∈ codeRange 0x1042e3 bytes_l1042e3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x42e3 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1042f2 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l10430c, RegMap.args (entryMap (live .l1042f2)) 53⟩)

def bytes_l1042f2 : List UInt8 :=
  [0xEB, 0x18]

theorem code_l1042f2 : ∀ x ∈ codeRange 0x1042f2 bytes_l1042f2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x42f2 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1042f4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1042f4 (movR64R64Effect 0x1042f4 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 12] []) (.reg (.gpr 5))) #v[12]
    (.letOp (n := 54) (.exec 0x1042f4 (fun s => s.RIP = 0x1042f4) (movR64R64Effect 0x1042f4 5 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x1042f7 (movR64Imm64Effect 0x1042f7 1 0x7fffffffffffffc0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x1042f7 (fun s => s.RIP = 0x1042f7) (movR64Imm64Effect 0x1042f7 1 0x7fffffffffffffc0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x104301 (movR64R64Effect 0x104301 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 58) (.exec 0x104301 (fun s => s.RIP = 0x104301) (movR64R64Effect 0x104301 2 5) (Reg.operands [.gpr 5] [])) #v[53]
    (.letOp (n := 59) (.out 0x104304 (shrR64Effect 0x104304 4 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.out 0x104304 (shrR64Effect 0x104304 4 2 6) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[57]
    (.letOp (n := 61) (.exec 0x104304 (fun s => s.RIP = 0x104304) (shrR64Effect 0x104304 4 2 6) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 62) (.pure (condOp 5)) #v[60]
    (.terminate (.condBr (Fin.last 62) ⟨.l10429e, RegMap.args [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ ⟨.l10430a, RegMap.args [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l1042f4 : List UInt8 :=
  [0x4C, 0x89, 0xE5, 0x48, 0xB9, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x48, 0x89, 0xEA,
    0x48, 0xC1, 0xEA, 0x06, 0x75, 0x94]

theorem code_l1042f4 : ∀ x ∈ codeRange 0x1042f4 bytes_l1042f4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x42f4 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10430a : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1042c0, RegMap.args (entryMap (live .l10430a)) 53⟩)

def bytes_l10430a : List UInt8 :=
  [0xEB, 0xB4]

theorem code_l10430a : ∀ x ∈ codeRange 0x10430a bytes_l10430a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x430a 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10430c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10430c (leaR64Effect 0x10430c 3 (.sib 4 none 0 (.d32 0x1f0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x10430c (fun s => s.RIP = 0x10430c) (leaR64Effect 0x10430c 3 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104314 (leaR64Effect 0x104314 6 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x104314 (fun s => s.RIP = 0x104314) (leaR64Effect 0x104314 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10431c (movR32Imm32Effect 0x10431c 5 2 0xa8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10431c (fun s => s.RIP = 0x10431c) (movR32Imm32Effect 0x10431c 5 2 0xa8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x104321 (movR64R64Effect 0x104321 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 60) (.exec 0x104321 (fun s => s.RIP = 0x104321) (movR64R64Effect 0x104321 7 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 61) (.out 0x104324 (callEffect (callMemPtr 0x104324 (.rip 0xffaa6)) (0x104324 + BitVec.ofNat 64 (callMemLen (.rip 0xffaa6)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x104324 (GoesTo (CallMemPre 0x104324 (.rip 0xffaa6)) (callEffect (callMemPtr 0x104324 (.rip 0xffaa6)) (0x104324 + BitVec.ofNat 64 (callMemLen (.rip 0xffaa6)))) 0x12a820) (callEffect (callMemPtr 0x104324 (.rip 0xffaa6)) (0x104324 + BitVec.ofNat 64 (callMemLen (.rip 0xffaa6)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10432a⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 53), (4, 61), (5, 5), (6, 55), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10432a, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10430c : List UInt8 :=
  [0x48, 0x8D, 0x9C, 0x24, 0xF0, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0xBA, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0xFF, 0x15, 0xA6, 0xFA, 0x0F, 0x00]

theorem code_l10430c : ∀ x ∈ codeRange 0x10430c bytes_l10430c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x430c 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10432a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10432a (StorePre 0x10432a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10432a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10432a (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x104333 (StorePre 0x104333 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104333 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104333 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10433c (StorePre 0x10433c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10433c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10433c (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x104345 (StorePre 0x104345 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x104345 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104345 (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10434e (leaR64Effect 0x10434e 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x10434e (fun s => s.RIP = 0x10434e) (leaR64Effect 0x10434e 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x104353 (movR64R64Effect 0x104353 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 60) (.exec 0x104353 (fun s => s.RIP = 0x104353) (movR64R64Effect 0x104353 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 61) (.out 0x104356 (callEffect (fun _ => 0x107a50) 0x10435b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x104356 (PushPre 0x104356 5) (callEffect (fun _ => 0x107a50) 0x10435b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10435b⟩) #v[]
    (.terminate (.call ⟨.l107a50, RegMap.args [(1, 1), (3, 3), (4, 61), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10435b, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10432a : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x28,
    0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x10, 0x48, 0x89, 0xDF, 0xE8, 0xF5, 0x36, 0x00,
    0x00]

theorem code_l10432a : ∀ x ∈ codeRange 0x10432a bytes_l10432a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x432a 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10435b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10435b (movR64M64Effect 0x10435b 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10435b (LoadPre 0x10435b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10435b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10435b 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104360 (movR64M64Effect 0x104360 3 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 56) (.exec 0x104360 (LoadPre 0x104360 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x104360 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104360 3 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x104365 (StorePre 0x104365 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x104365 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104365 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 55]
    (.letOp (n := 58) (.out 0x104369 (movR64M64Effect 0x104369 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 59) (.exec 0x104369 (LoadPre 0x104369 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104369 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104369 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x10436e (StorePre 0x10436e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10436e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10436e 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[58, 55]
    (.letOp (n := 61) (.out 0x104372 (movR64M64Effect 0x104372 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 62) (.exec 0x104372 (LoadPre 0x104372 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104372 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104372 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x104377 (movR64M64Effect 0x104377 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 64) (.exec 0x104377 (LoadPre 0x104377 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104377 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104377 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x10437c (StorePre 0x10437c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10437c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10437c 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[63, 55]
    (.letOp (n := 66) (.exec 0x104380 (StorePre 0x104380 3 (fun s => AddrMode.addr (.base 3 .none) s (0x104380 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x104380 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[61, 55]
    (.letOp (n := 67) (.out 0x104383 (movR64R64Effect 0x104383 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 68) (.exec 0x104383 (fun s => s.RIP = 0x104383) (movR64R64Effect 0x104383 7 3) (Reg.operands [.gpr 3] [])) #v[55]
    (.letOp (n := 69) (.out 0x104386 (callEffect (fun _ => 0x104970) 0x10438b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x104386 (PushPre 0x104386 5) (callEffect (fun _ => 0x104970) 0x10438b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x10438b⟩) #v[]
    (.terminate (.call ⟨.l104970, RegMap.args [(0, 61), (1, 63), (3, 55), (4, 69), (5, 5), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l10438b, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l10435b : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x5C, 0x24, 0x78, 0x48, 0x89, 0x43, 0x18, 0x48, 0x8B,
    0x44, 0x24, 0x20, 0x48, 0x89, 0x43, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24,
    0x18, 0x48, 0x89, 0x4B, 0x08, 0x48, 0x89, 0x03, 0x48, 0x89, 0xDF, 0xE8, 0xE5, 0x05, 0x00, 0x00]

theorem code_l10435b : ∀ x ∈ codeRange 0x10435b bytes_l10435b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x435b 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10438b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10438b (StorePre 0x10438b 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x10438b + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10438b (.sib 4 none 0 (.d32 0x228)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x104397 (StorePre 0x104397 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x220)) s (0x104397 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x104397 (.sib 4 none 0 (.d32 0x220)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1043a3 (StorePre 0x1043a3 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x218)) s (0x1043a3 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1043a3 (.sib 4 none 0 (.d32 0x218)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1043af (StorePre 0x1043af 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x210)) s (0x1043af + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1043af (.sib 4 none 0 (.d32 0x210)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1043bb (movR64M64Effect 0x1043bb 0 (.base 3 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 58) (.exec 0x1043bb (LoadPre 0x1043bb (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1043bb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1043bb 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x1043bf (movR64M64Effect 0x1043bf 1 (.base 3 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 60) (.exec 0x1043bf (LoadPre 0x1043bf (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1043bf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1043bf 1 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 61) (.out 0x1043c3 (movR64M64Effect 0x1043c3 2 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 62) (.exec 0x1043c3 (LoadPre 0x1043c3 (fun s => AddrMode.addr (.base 3 .none) s (0x1043c3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1043c3 2 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 63) (.out 0x1043c6 (movR64M64Effect 0x1043c6 6 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 64) (.exec 0x1043c6 (LoadPre 0x1043c6 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1043c6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1043c6 6 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 65) (.exec 0x1043ca (StorePre 0x1043ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1043ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1043ca 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 66) (.exec 0x1043cf (StorePre 0x1043cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1043cf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1043cf 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 67) (.exec 0x1043d4 (StorePre 0x1043d4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1043d4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1043d4 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 68) (.exec 0x1043d9 (StorePre 0x1043d9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1043d9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1043d9 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 69) (.exec 0x1043de (StorePre 0x1043de 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1043de + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1043de (.sib 4 none 0 (.d8 0x50)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x1043e7 (StorePre 0x1043e7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1043e7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1043e7 (.sib 4 none 0 (.d8 0x58)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x1043f0 (StorePre 0x1043f0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1043f0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1043f0 (.sib 4 none 0 (.d8 0x60)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x1043f9 (StorePre 0x1043f9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1043f9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1043f9 (.sib 4 none 0 (.d8 0x68)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x104402 (movR32Imm32Effect 0x104402 5 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 74) (.exec 0x104402 (fun s => s.RIP = 0x104402) (movR32Imm32Effect 0x104402 5 0 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.exec 0x104407 (fun s => s.RIP = 0x104407) (fun _ => nopEffect 0x104407 9) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l104410, RegMap.args [(0, 73), (1, 59), (2, 61), (3, 3), (4, 4), (5, 5), (6, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l10438b : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0x28, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0x20, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x18, 0x02, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x10, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x43, 0x18, 0x48, 0x8B, 0x4B, 0x10, 0x48, 0x8B, 0x13, 0x48, 0x8B, 0x73, 0x08, 0x48,
    0x89, 0x54, 0x24, 0x30, 0x48, 0x89, 0x74, 0x24, 0x38, 0x48, 0x89, 0x4C, 0x24, 0x40, 0x48, 0x89,
    0x44, 0x24, 0x48, 0x48, 0xC7, 0x44, 0x24, 0x50, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24,
    0x58, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x60, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00, 0xB8, 0x03, 0x00, 0x00, 0x00, 0x66, 0x0F, 0x1F, 0x84,
    0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l10438b : ∀ x ∈ codeRange 0x10438b bytes_l10438b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x438b 133 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104410 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104410 (StorePre 0x104410 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x2d)) s (0x104410 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104410 5 (.sib 4 (some 0) 0 (.d8 0x2d)) 0x36) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 54) (.exec 0x104415 (StorePre 0x104415 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x2e)) s (0x104415 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104415 5 (.sib 4 (some 0) 0 (.d8 0x2e)) 0x36) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.exec 0x10441a (StorePre 0x10441a 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x2f)) s (0x10441a + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x10441a 5 (.sib 4 (some 0) 0 (.d8 0x2f)) 0x36) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 56) (.exec 0x10441f (StorePre 0x10441f 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x30)) s (0x10441f + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x10441f 5 (.sib 4 (some 0) 0 (.d8 0x30)) 0x36) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 57) (.out 0x104424 (addR64Imm8Effect 0x104424 0 0x4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 58) (.exec 0x104424 (fun s => s.RIP = 0x104424) (addR64Imm8Effect 0x104424 0 0x4) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x104428 (cmpR64Imm8Effect 0x104428 0 0x43) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[57]
    (.letOp (n := 60) (.exec 0x104428 (fun s => s.RIP = 0x104428) (cmpR64Imm8Effect 0x104428 0 0x43) (Reg.operands [.gpr 0] [])) #v[57]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l104410, RegMap.args [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l10442e, RegMap.args [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l104410 : List UInt8 :=
  [0x80, 0x74, 0x04, 0x2D, 0x36, 0x80, 0x74, 0x04, 0x2E, 0x36, 0x80, 0x74, 0x04, 0x2F, 0x36, 0x80,
    0x74, 0x04, 0x30, 0x36, 0x48, 0x83, 0xC0, 0x04, 0x48, 0x83, 0xF8, 0x43, 0x75, 0xE2]

theorem code_l104410 : ∀ x ∈ codeRange 0x104410 bytes_l104410, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4410 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10442e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10442e (leaR64Effect 0x10442e 13 (.sib 4 none 0 (.d32 0x188))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 54) (.exec 0x10442e (fun s => s.RIP = 0x10442e) (leaR64Effect 0x10442e 13 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104436 (movR64Imm64Effect 0x104436 0 0x5be0cd191f83d9ab) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x104436 (fun s => s.RIP = 0x104436) (movR64Imm64Effect 0x104436 0 0x5be0cd191f83d9ab) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.exec 0x104440 (StorePre 0x104440 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x104440 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104440 0 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x104448 (movR64Imm64Effect 0x104448 0 0x9b05688c510e527f) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 59) (.exec 0x104448 (fun s => s.RIP = 0x104448) (movR64Imm64Effect 0x104448 0 0x9b05688c510e527f) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.exec 0x104452 (StorePre 0x104452 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x104452 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104452 0 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x10445a (movR64Imm64Effect 0x10445a 0 0xa54ff53a3c6ef372) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 62) (.exec 0x10445a (fun s => s.RIP = 0x10445a) (movR64Imm64Effect 0x10445a 0 0xa54ff53a3c6ef372) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.exec 0x104464 (StorePre 0x104464 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x104464 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104464 0 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x10446c (movR64Imm64Effect 0x10446c 0 0xbb67ae856a09e667) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 65) (.exec 0x10446c (fun s => s.RIP = 0x10446c) (movR64Imm64Effect 0x10446c 0 0xbb67ae856a09e667) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.exec 0x104476 (StorePre 0x104476 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x104476 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104476 0 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x10447e (StorePre 0x10447e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x187)) s (0x10447e + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x10447e (.sib 4 none 0 (.d32 0x187)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x104486 (StorePre 0x104486 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x104486 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x104486 (.sib 4 none 0 (.d32 0x1a8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x104492 (leaR64Effect 0x104492 6 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x104492 (fun s => s.RIP = 0x104492) (leaR64Effect 0x104492 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x104497 (movR32Imm32Effect 0x104497 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 72) (.exec 0x104497 (fun s => s.RIP = 0x104497) (movR32Imm32Effect 0x104497 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x10449c (movR64R64Effect 0x10449c 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 74) (.exec 0x10449c (fun s => s.RIP = 0x10449c) (movR64R64Effect 0x10449c 7 13) (Reg.operands [.gpr 13] [])) #v[53]
    (.letOp (n := 75) (.out 0x10449f (callEffect (fun _ => 0x1218e0) 0x1044a4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 76) (.exec 0x10449f (PushPre 0x10449f 5) (callEffect (fun _ => 0x1218e0) 0x1044a4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.const ⟨64, 0x1044a4⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 64), (1, 1), (2, 71), (3, 3), (4, 75), (5, 5), (6, 69), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l1044a4, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l10442e : List UInt8 :=
  [0x4C, 0x8D, 0xAC, 0x24, 0x88, 0x01, 0x00, 0x00, 0x48, 0xB8, 0xAB, 0xD9, 0x83, 0x1F, 0x19, 0xCD,
    0xE0, 0x5B, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x01, 0x00, 0x00, 0x48, 0xB8, 0x7F, 0x52, 0x0E, 0x51,
    0x8C, 0x68, 0x05, 0x9B, 0x48, 0x89, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00, 0x48, 0xB8, 0x72, 0xF3,
    0x6E, 0x3C, 0x3A, 0xF5, 0x4F, 0xA5, 0x48, 0x89, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00, 0x48, 0xB8,
    0x67, 0xE6, 0x09, 0x6A, 0x85, 0xAE, 0x67, 0xBB, 0x48, 0x89, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00,
    0xC6, 0x84, 0x24, 0x87, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xA8, 0x01, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x30, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xEF, 0xE8, 0x3C, 0xD4, 0x01, 0x00]

theorem code_l10442e : ∀ x ∈ codeRange 0x10442e bytes_l10442e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x442e 118 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1044a4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1044a4 (StorePre 0x1044a4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x187)) s (0x1044a4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x1044a4 (.sib 4 none 0 (.d32 0x187)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x1044ac (movR32Imm32Effect 0x1044ac 5 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 55) (.exec 0x1044ac (fun s => s.RIP = 0x1044ac) (movR32Imm32Effect 0x1044ac 5 0 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.exec 0x1044b1 (fun s => s.RIP = 0x1044b1) (fun _ => nopEffect 0x1044b1 15) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1044c0, RegMap.args [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1044a4 : List UInt8 :=
  [0xC6, 0x84, 0x24, 0x87, 0x01, 0x00, 0x00, 0x00, 0xB8, 0x03, 0x00, 0x00, 0x00, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l1044a4 : ∀ x ∈ codeRange 0x1044a4 bytes_l1044a4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x44a4 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1044c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1044c0 (StorePre 0x1044c0 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x2d)) s (0x1044c0 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1044c0 5 (.sib 4 (some 0) 0 (.d8 0x2d)) 0x6a) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 54) (.exec 0x1044c5 (StorePre 0x1044c5 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x2e)) s (0x1044c5 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1044c5 5 (.sib 4 (some 0) 0 (.d8 0x2e)) 0x6a) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.exec 0x1044ca (StorePre 0x1044ca 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x2f)) s (0x1044ca + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1044ca 5 (.sib 4 (some 0) 0 (.d8 0x2f)) 0x6a) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 56) (.exec 0x1044cf (StorePre 0x1044cf 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x30)) s (0x1044cf + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1044cf 5 (.sib 4 (some 0) 0 (.d8 0x30)) 0x6a) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 57) (.out 0x1044d4 (addR64Imm8Effect 0x1044d4 0 0x4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 58) (.exec 0x1044d4 (fun s => s.RIP = 0x1044d4) (addR64Imm8Effect 0x1044d4 0 0x4) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x1044d8 (cmpR64Imm8Effect 0x1044d8 0 0x43) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[57]
    (.letOp (n := 60) (.exec 0x1044d8 (fun s => s.RIP = 0x1044d8) (cmpR64Imm8Effect 0x1044d8 0 0x43) (Reg.operands [.gpr 0] [])) #v[57]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l1044c0, RegMap.args [(0, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l1044de, RegMap.args [(0, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l1044c0 : List UInt8 :=
  [0x80, 0x74, 0x04, 0x2D, 0x6A, 0x80, 0x74, 0x04, 0x2E, 0x6A, 0x80, 0x74, 0x04, 0x2F, 0x6A, 0x80,
    0x74, 0x04, 0x30, 0x6A, 0x48, 0x83, 0xC0, 0x04, 0x48, 0x83, 0xF8, 0x43, 0x75, 0xE2]

theorem code_l1044c0 : ∀ x ∈ codeRange 0x1044c0 bytes_l1044c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x44c0 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1044de_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x10455e (leaR64Effect 0x10455e 7 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 85) (.exec 0x10455e (fun s => s.RIP = 0x10455e) (leaR64Effect 0x10455e 7 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.out 0x104566 (leaR64Effect 0x104566 6 (.sib 4 none 0 (.d32 0x1f0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 87) (.exec 0x104566 (fun s => s.RIP = 0x104566) (leaR64Effect 0x104566 6 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.out 0x10456e (movR32Imm32Effect 0x10456e 5 2 0xa8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 89) (.exec 0x10456e (fun s => s.RIP = 0x10456e) (movR32Imm32Effect 0x10456e 5 2 0xa8) (Reg.operands [] [])) #v[]
    (.letOp (n := 90) (.out 0x104573 (callEffect (callMemPtr 0x104573 (.rip 0xff857)) (0x104573 + BitVec.ofNat 64 (callMemLen (.rip 0xff857)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 91) (.exec 0x104573 (GoesTo (CallMemPre 0x104573 (.rip 0xff857)) (callEffect (callMemPtr 0x104573 (.rip 0xff857)) (0x104573 + BitVec.ofNat 64 (callMemLen (.rip 0xff857)))) 0x12a820) (callEffect (callMemPtr 0x104573 (.rip 0xff857)) (0x104573 + BitVec.ofNat 64 (callMemLen (.rip 0xff857)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.const ⟨64, 0x104579⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 78), (1, 80), (2, 88), (3, 3), (4, 90), (5, 5), (6, 86), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩ { target := .l104579, kept := #v[], arity := rfl, guard := some (Fin.last 92) }))))))))))

def bytes_l1044de_1 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0xF0, 0x01, 0x00, 0x00,
    0xBA, 0xA8, 0x00, 0x00, 0x00, 0xFF, 0x15, 0x57, 0xF8, 0x0F, 0x00]

theorem code_l1044de_1 : ∀ x ∈ codeRange 0x10455e bytes_l1044de_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x455e 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1044de : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1044de (leaR64Effect 0x1044de 7 (.sib 4 none 0 (.d32 0x230))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1044de (fun s => s.RIP = 0x1044de) (leaR64Effect 0x1044de 7 (.sib 4 none 0 (.d32 0x230))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1044e6 (leaR64Effect 0x1044e6 6 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x1044e6 (fun s => s.RIP = 0x1044e6) (leaR64Effect 0x1044e6 6 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1044ee (movR32Imm32Effect 0x1044ee 5 1 0xd) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x1044ee (fun s => s.RIP = 0x1044ee) (movR32Imm32Effect 0x1044ee 5 1 0xd) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x1044f3 (RepPre 0x1044f3 (RepMovsqPre 0x1044f3)) (repMovsqEffect 0x1044f3) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[55, 53, 57, 22]
    (.letOp (n := 60) (.out 0x1044f6 (movR64M64Effect 0x1044f6 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 61) (.exec 0x1044f6 (LoadPre 0x1044f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1044f6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1044f6 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x1044fb (StorePre 0x1044fb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x1044fb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1044fb 0 (.sib 4 none 0 (.d32 0x228))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x104503 (movR64M64Effect 0x104503 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x104503 (LoadPre 0x104503 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x104503 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104503 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x104508 (StorePre 0x104508 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x220)) s (0x104508 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104508 0 (.sib 4 none 0 (.d32 0x220))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x104510 (movR64M64Effect 0x104510 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 67) (.exec 0x104510 (LoadPre 0x104510 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x104510 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104510 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x104515 (StorePre 0x104515 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x218)) s (0x104515 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104515 0 (.sib 4 none 0 (.d32 0x218))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x10451d (movR64M64Effect 0x10451d 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 70) (.exec 0x10451d (LoadPre 0x10451d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10451d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10451d 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x104522 (StorePre 0x104522 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x210)) s (0x104522 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104522 0 (.sib 4 none 0 (.d32 0x210))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.out 0x10452a (movR64M64Effect 0x10452a 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 73) (.exec 0x10452a (LoadPre 0x10452a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10452a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10452a 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x10452f (StorePre 0x10452f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x208)) s (0x10452f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10452f 0 (.sib 4 none 0 (.d32 0x208))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x104537 (movR64M64Effect 0x104537 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 76) (.exec 0x104537 (LoadPre 0x104537 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x104537 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104537 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x10453c (StorePre 0x10453c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x200)) s (0x10453c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10453c 0 (.sib 4 none 0 (.d32 0x200))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x104544 (movR64M64Effect 0x104544 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 79) (.exec 0x104544 (LoadPre 0x104544 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x104544 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104544 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x104549 (movR64M64Effect 0x104549 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 81) (.exec 0x104549 (LoadPre 0x104549 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x104549 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104549 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x10454e (StorePre 0x10454e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f8)) s (0x10454e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10454e 1 (.sib 4 none 0 (.d32 0x1f8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.exec 0x104556 (StorePre 0x104556 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1f0)) s (0x104556 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104556 0 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 4]
    (b_l1044de_1)))))))))))))))))))))))))))))))

def bytes_l1044de : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x30, 0x02, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x48, 0x01, 0x00, 0x00,
    0xB9, 0x0D, 0x00, 0x00, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0x89, 0x84,
    0x24, 0x28, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x60, 0x48, 0x89, 0x84, 0x24, 0x20, 0x02,
    0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x89, 0x84, 0x24, 0x18, 0x02, 0x00, 0x00, 0x48,
    0x8B, 0x44, 0x24, 0x50, 0x48, 0x89, 0x84, 0x24, 0x10, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24,
    0x48, 0x48, 0x89, 0x84, 0x24, 0x08, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x89,
    0x84, 0x24, 0x00, 0x02, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x8B, 0x4C, 0x24, 0x38,
    0x48, 0x89, 0x8C, 0x24, 0xF8, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xF0, 0x01, 0x00, 0x00] ++ bytes_l1044de_1

theorem code_l1044de : ∀ x ∈ codeRange 0x1044de bytes_l1044de, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x44de 128 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1044de_1

@[cfg_block] def b_l104579 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104579 (leaR64Effect 0x104579 5 (.sib 4 none 0 (.d32 0x1c8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x104579 (fun s => s.RIP = 0x104579) (leaR64Effect 0x104579 5 (.sib 4 none 0 (.d32 0x1c8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104581 (movzxR32M8Effect 0x104581 8 3 (.sib 4 none 0 (.d32 0x1c7))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 56) (.exec 0x104581 (LoadPre 0x104581 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x104581 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x104581 8 3 (.sib 4 none 0 (.d32 0x1c7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x104589 (cmpR64Imm8Effect 0x104589 3 0x1f) (EffectPart.reads (.flag .CF) [.gpr 3] []) (.flag .CF)) #v[55]
    (.letOp (n := 58) (.out 0x104589 (cmpR64Imm8Effect 0x104589 3 0x1f) (EffectPart.reads (.flag .ZF) [.gpr 3] []) (.flag .ZF)) #v[55]
    (.letOp (n := 59) (.exec 0x104589 (fun s => s.RIP = 0x104589) (cmpR64Imm8Effect 0x104589 3 0x1f) (Reg.operands [.gpr 3] [])) #v[55]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l10471d, RegMap.args [(3, 55), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l104593, RegMap.args [(3, 55), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l104579 : List UInt8 :=
  [0x48, 0x8D, 0xAC, 0x24, 0xC8, 0x01, 0x00, 0x00, 0x0F, 0xB6, 0x9C, 0x24, 0xC7, 0x01, 0x00, 0x00,
    0x48, 0x83, 0xFB, 0x1F, 0x0F, 0x87, 0x8A, 0x01, 0x00, 0x00]

theorem code_l104579 : ∀ x ∈ codeRange 0x104579 bytes_l104579, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4579 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104593 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104593 (movR64M64Effect 0x104593 1 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x104593 (LoadPre 0x104593 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x104593 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104593 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104598 (movR64M64Effect 0x104598 0 (.base 1 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x104598 (LoadPre 0x104598 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x104598 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104598 0 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.exec 0x10459c (StorePre 0x10459c 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x18)) s (0x10459c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10459c 0 (.sib 13 (some 3) 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 13, .gpr 3] [])) #v[55, 13, 3]
    (.letOp (n := 58) (.out 0x1045a1 (movR64M64Effect 0x1045a1 0 (.base 1 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 59) (.exec 0x1045a1 (LoadPre 0x1045a1 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x1045a1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1045a1 0 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 60) (.exec 0x1045a5 (StorePre 0x1045a5 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x10)) s (0x1045a5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1045a5 0 (.sib 13 (some 3) 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 13, .gpr 3] [])) #v[58, 13, 3]
    (.letOp (n := 61) (.out 0x1045aa (movR64M64Effect 0x1045aa 0 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 62) (.exec 0x1045aa (LoadPre 0x1045aa (fun s => AddrMode.addr (.base 1 .none) s (0x1045aa + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1045aa 0 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 63) (.out 0x1045ad (movR64M64Effect 0x1045ad 1 (.base 1 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 64) (.exec 0x1045ad (LoadPre 0x1045ad (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x1045ad + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1045ad 1 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 65) (.exec 0x1045b1 (StorePre 0x1045b1 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x8)) s (0x1045b1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1045b1 1 (.sib 13 (some 3) 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 13, .gpr 3] [])) #v[63, 13, 3]
    (.letOp (n := 66) (.exec 0x1045b6 (StorePre 0x1045b6 5 (fun s => AddrMode.addr (.sib 13 (some 3) 0 (.d8 0x0)) s (0x1045b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1045b6 0 (.sib 13 (some 3) 0 (.d8 0x0))) (Reg.operands [.gpr 0, .gpr 13, .gpr 3] [])) #v[61, 13, 3]
    (.letOp (n := 67) (.out 0x1045bb (orR8Imm8Effect 0x1045bb 3 3 0x20) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 68) (.exec 0x1045bb (fun s => s.RIP = 0x1045bb) (orR8Imm8Effect 0x1045bb 3 3 0x20) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 69) (.exec 0x1045be (StorePre 0x1045be 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x1045be + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1045be 7 3 (.sib 4 none 0 (.d32 0x1c7))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x1045c5 (movR64M64Effect 0x1045c5 15 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 71) (.exec 0x1045c5 (LoadPre 0x1045c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1045c5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1045c5 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x1045ca (movzxR32R8Effect 0x1045ca 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 73) (.exec 0x1045ca (fun s => s.RIP = 0x1045ca) (movzxR32R8Effect 0x1045ca 3 0 3) (Reg.operands [.gpr 3] [])) #v[67]
    (.letOp (n := 74) (.out 0x1045cd (cmpAlImm8Effect 0x1045cd 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[72]
    (.letOp (n := 75) (.exec 0x1045cd (fun s => s.RIP = 0x1045cd) (cmpAlImm8Effect 0x1045cd 0x3f) (Reg.operands [.gpr 0] [])) #v[72]
    (.letOp (n := 76) (.pure (condOp 4)) #v[74]
    (.terminate (.condBr (Fin.last 76) ⟨.l104793, RegMap.args [(0, 72), (1, 63), (3, 67), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 70), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩ ⟨.l1045d5, RegMap.args [(0, 72), (1, 63), (3, 67), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 70), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l104593 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x70, 0x48, 0x8B, 0x41, 0x18, 0x49, 0x89, 0x44, 0x1D, 0x18, 0x48, 0x8B,
    0x41, 0x10, 0x49, 0x89, 0x44, 0x1D, 0x10, 0x48, 0x8B, 0x01, 0x48, 0x8B, 0x49, 0x08, 0x49, 0x89,
    0x4C, 0x1D, 0x08, 0x49, 0x89, 0x44, 0x1D, 0x00, 0x80, 0xCB, 0x20, 0x88, 0x9C, 0x24, 0xC7, 0x01,
    0x00, 0x00, 0x4C, 0x8B, 0x7C, 0x24, 0x08, 0x0F, 0xB6, 0xC3, 0x3C, 0x3F, 0x0F, 0x84, 0xBE, 0x01,
    0x00, 0x00]

theorem code_l104593 : ∀ x ∈ codeRange 0x104593 bytes_l104593, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4593 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1045d5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1045d5 (StorePre 0x1045d5 8 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d32 0x188)) s (0x1045d5 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x1045d5 (.sib 4 (some 0) 0 (.d32 0x188)) 0x1) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 54) (.out 0x1045dd (incR32Effect 0x1045dd 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 55) (.exec 0x1045dd (fun s => s.RIP = 0x1045dd) (incR32Effect 0x1045dd 2 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.terminate (.br ⟨.l1047c4, RegMap.args [(0, 54), (1, 1), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1045d5 : List UInt8 :=
  [0xC6, 0x84, 0x04, 0x88, 0x01, 0x00, 0x00, 0x01, 0xFF, 0xC0, 0xE9, 0xE0, 0x01, 0x00, 0x00]

theorem code_l1045d5 : ∀ x ∈ codeRange 0x1045d5 bytes_l1045d5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x45d5 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1045e4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1045e4 (movR32Imm32Effect 0x1045e4 5 2 0x40) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x1045e4 (fun s => s.RIP = 0x1045e4) (movR32Imm32Effect 0x1045e4 5 2 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1045e9 (subR64R64Effect 0x1045e9 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x1045e9 (fun s => s.RIP = 0x1045e9) (subR64R64Effect 0x1045e9 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.exec 0x1045ec (StorePre 0x1045ec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1045ec + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1045ec 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 58) (.out 0x1045f1 (leaR64Effect 0x1045f1 15 (.sib 6 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6, .gpr 2] []) (.reg (.gpr 15))) #v[6, 55]
    (.letOp (n := 59) (.exec 0x1045f1 (fun s => s.RIP = 0x1045f1) (leaR64Effect 0x1045f1 15 (.sib 6 (some 2) 0 .none)) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6, 55]
    (.letOp (n := 60) (.out 0x1045f5 (leaR64Effect 0x1045f5 7 (.sib 3 (some 13) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3, .gpr 13] []) (.reg (.gpr 7))) #v[3, 13]
    (.letOp (n := 61) (.exec 0x1045f5 (fun s => s.RIP = 0x1045f5) (leaR64Effect 0x1045f5 7 (.sib 3 (some 13) 0 .none)) (Reg.operands [.gpr 3, .gpr 13] [])) #v[3, 13]
    (.letOp (n := 62) (.out 0x1045f9 (addR64Imm8Effect 0x1045f9 3 0xe0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 63) (.exec 0x1045f9 (fun s => s.RIP = 0x1045f9) (addR64Imm8Effect 0x1045f9 3 0xe0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 64) (.out 0x1045fd (leaR64Effect 0x1045fd 12 (.rip 0x2621c)) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 65) (.exec 0x1045fd (fun s => s.RIP = 0x1045fd) (leaR64Effect 0x1045fd 12 (.rip 0x2621c)) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.out 0x104604 (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x104607) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 64]
    (.letOp (n := 67) (.exec 0x104604 (GoesTo (CallPre 0x104604 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x104607) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x104607) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 64]
    (.letOp (n := 68) (.const ⟨64, 0x104607⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 62), (4, 66), (5, 5), (6, 6), (7, 60), (9, 9), (10, 10), (11, 11), (12, 64), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l104607, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l1045e4 : List UInt8 :=
  [0xBA, 0x40, 0x00, 0x00, 0x00, 0x48, 0x29, 0xDA, 0x4C, 0x89, 0x7C, 0x24, 0x08, 0x4C, 0x8D, 0x3C,
    0x16, 0x4A, 0x8D, 0x3C, 0x2B, 0x48, 0x83, 0xC3, 0xE0, 0x4C, 0x8D, 0x25, 0x1C, 0x62, 0x02, 0x00,
    0x41, 0xFF, 0xD4]

theorem code_l1045e4 : ∀ x ∈ codeRange 0x1045e4 bytes_l1045e4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x45e4 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104607 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104607 (StorePre 0x104607 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x104607 + BitVec.ofNat 64 8)) 8) (incMEffect 0x104607 8 64 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x10460f (movR32Imm32Effect 0x10460f 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 55) (.exec 0x10460f (fun s => s.RIP = 0x10460f) (movR32Imm32Effect 0x10460f 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.out 0x104614 (leaR64Effect 0x104614 7 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 57) (.exec 0x104614 (fun s => s.RIP = 0x104614) (leaR64Effect 0x104614 7 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x10461c (movR64R64Effect 0x10461c 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 59) (.exec 0x10461c (fun s => s.RIP = 0x10461c) (movR64R64Effect 0x10461c 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 60) (.out 0x10461f (callEffect (fun _ => 0x1218e0) 0x104624) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x10461f (PushPre 0x10461f 5) (callEffect (fun _ => 0x1218e0) 0x104624) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x104624⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ { target := .l104624, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l104607 : List UInt8 :=
  [0x48, 0xFF, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC,
    0x24, 0x20, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xEE, 0xE8, 0xBC, 0xD2, 0x01, 0x00]

theorem code_l104607 : ∀ x ∈ codeRange 0x104607 bytes_l104607, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4607 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104624 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104624 (movR64R64Effect 0x104624 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 54) (.exec 0x104624 (fun s => s.RIP = 0x104624) (movR64R64Effect 0x104624 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x104627 (movR64Imm64Effect 0x104627 0 0x7fffffffffffffc0) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x104627 (fun s => s.RIP = 0x104627) (movR64Imm64Effect 0x104627 0 0x7fffffffffffffc0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x104631 (andR64R64Effect 0x104631 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x104631 (fun s => s.RIP = 0x104631) (andR64R64Effect 0x104631 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x104634 (addR64R64Effect 0x104634 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[57, 15]
    (.letOp (n := 60) (.exec 0x104634 (fun s => s.RIP = 0x104634) (addR64R64Effect 0x104634 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[57, 15]
    (.letOp (n := 61) (.out 0x104637 (movR64M64Effect 0x104637 15 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 62) (.exec 0x104637 (LoadPre 0x104637 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104637 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104637 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x10463c (StorePre 0x10463c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x10463c + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10463c 7 3 (.sib 4 none 0 (.d32 0x11f))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 64) (.out 0x104643 (movR64R64Effect 0x104643 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 65) (.exec 0x104643 (fun s => s.RIP = 0x104643) (movR64R64Effect 0x104643 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 66) (.out 0x104646 (movR64R64Effect 0x104646 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 67) (.exec 0x104646 (fun s => s.RIP = 0x104646) (movR64R64Effect 0x104646 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 68) (.out 0x104649 (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10464c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 12]
    (.letOp (n := 69) (.exec 0x104649 (GoesTo (CallPre 0x104649 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10464c) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10464c) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 70) (.const ⟨64, 0x10464c⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 55), (2, 66), (3, 3), (4, 68), (5, 5), (6, 59), (7, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l10464c, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l104624 : List UInt8 :=
  [0x48, 0x89, 0xDE, 0x48, 0xB8, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x48, 0x21, 0xC6,
    0x4C, 0x01, 0xFE, 0x4C, 0x8B, 0x7C, 0x24, 0x08, 0x88, 0x9C, 0x24, 0x1F, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0xEF, 0x48, 0x89, 0xDA, 0x41, 0xFF, 0xD4]

theorem code_l104624 : ∀ x ∈ codeRange 0x104624 bytes_l104624, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4624 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10464c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10464c (movzxR32M8Effect 0x10464c 8 3 (.sib 4 none 0 (.d32 0x11f))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x10464c (LoadPre 0x10464c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x10464c + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10464c 8 3 (.sib 4 none 0 (.d32 0x11f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104654 (movzxR32R8Effect 0x104654 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x104654 (fun s => s.RIP = 0x104654) (movzxR32R8Effect 0x104654 3 0 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 57) (.out 0x104657 (cmpAlImm8Effect 0x104657 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[55]
    (.letOp (n := 58) (.exec 0x104657 (fun s => s.RIP = 0x104657) (cmpAlImm8Effect 0x104657 0x3f) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1041c8, RegMap.args [(0, 55), (3, 53), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l10465f, RegMap.args [(0, 55), (3, 53), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l10464c : List UInt8 :=
  [0x0F, 0xB6, 0x9C, 0x24, 0x1F, 0x01, 0x00, 0x00, 0x0F, 0xB6, 0xC3, 0x3C, 0x3F, 0x0F, 0x85, 0x69,
    0xFB, 0xFF, 0xFF]

theorem code_l10464c : ∀ x ∈ codeRange 0x10464c bytes_l10464c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x464c 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10465f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10465f (movR32Imm32Effect 0x10465f 5 2 0x40) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x10465f (fun s => s.RIP = 0x10465f) (movR32Imm32Effect 0x10465f 5 2 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x104664 (subR64R64Effect 0x104664 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[53, 0]
    (.letOp (n := 56) (.exec 0x104664 (fun s => s.RIP = 0x104664) (subR64R64Effect 0x104664 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 57) (.out 0x104667 (leaR64Effect 0x104667 7 (.sib 0 (some 13) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0, .gpr 13] []) (.reg (.gpr 7))) #v[0, 13]
    (.letOp (n := 58) (.exec 0x104667 (fun s => s.RIP = 0x104667) (leaR64Effect 0x104667 7 (.sib 0 (some 13) 0 .none)) (Reg.operands [.gpr 0, .gpr 13] [])) #v[0, 13]
    (.letOp (n := 59) (.out 0x10466b (xorR32R32Effect 0x10466b 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 60) (.exec 0x10466b (fun s => s.RIP = 0x10466b) (xorR32R32Effect 0x10466b 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 61) (.out 0x10466d (xorR32R32Effect 0x10466d 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 62) (.exec 0x10466d (fun s => s.RIP = 0x10466d) (xorR32R32Effect 0x10466d 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 63) (.out 0x10466f (callEffect (callMemPtr 0x10466f (.rip 0xff79b)) (0x10466f + BitVec.ofNat 64 (callMemLen (.rip 0xff79b)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x10466f (GoesTo (CallMemPre 0x10466f (.rip 0xff79b)) (callEffect (callMemPtr 0x10466f (.rip 0xff79b)) (0x10466f + BitVec.ofNat 64 (callMemLen (.rip 0xff79b)))) 0x12a700) (callEffect (callMemPtr 0x10466f (.rip 0xff79b)) (0x10466f + BitVec.ofNat 64 (callMemLen (.rip 0xff79b)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x104675⟩) #v[]
    (.terminate (.call ⟨.l12a700, RegMap.args [(0, 0), (2, 55), (3, 59), (4, 63), (5, 5), (6, 61), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l104675, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l10465f : List UInt8 :=
  [0xBA, 0x40, 0x00, 0x00, 0x00, 0x48, 0x29, 0xC2, 0x4A, 0x8D, 0x3C, 0x28, 0x31, 0xDB, 0x31, 0xF6,
    0xFF, 0x15, 0x9B, 0xF7, 0x0F, 0x00]

theorem code_l10465f : ∀ x ∈ codeRange 0x10465f bytes_l10465f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x465f 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104675 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104675 (StorePre 0x104675 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x104675 + BitVec.ofNat 64 8)) 8) (incMEffect 0x104675 8 64 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x10467d (movR32Imm32Effect 0x10467d 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 55) (.exec 0x10467d (fun s => s.RIP = 0x10467d) (movR32Imm32Effect 0x10467d 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.out 0x104682 (leaR64Effect 0x104682 7 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 57) (.exec 0x104682 (fun s => s.RIP = 0x104682) (leaR64Effect 0x104682 7 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x10468a (movR64R64Effect 0x10468a 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 59) (.exec 0x10468a (fun s => s.RIP = 0x10468a) (movR64R64Effect 0x10468a 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 60) (.out 0x10468d (callEffect (fun _ => 0x1218e0) 0x104692) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x10468d (PushPre 0x10468d 5) (callEffect (fun _ => 0x1218e0) 0x104692) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x104692⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ { target := .l104692, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l104675 : List UInt8 :=
  [0x48, 0xFF, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC,
    0x24, 0x20, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xEE, 0xE8, 0x4E, 0xD2, 0x01, 0x00]

theorem code_l104675 : ∀ x ∈ codeRange 0x104675 bytes_l104675, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4675 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104692 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104692 (StorePre 0x104692 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11f)) s (0x104692 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x104692 7 3 (.sib 4 none 0 (.d32 0x11f))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 54) (.out 0x104699 (testR64R64Effect 0x104699 15 15) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 15] []) (.flag .ZF)) #v[15, 15]
    (.letOp (n := 55) (.exec 0x104699 (fun s => s.RIP = 0x104699) (testR64R64Effect 0x104699 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 56) (.pure (condOp 5)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l1041e3, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l1046a2, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l104692 : List UInt8 :=
  [0x88, 0x9C, 0x24, 0x1F, 0x01, 0x00, 0x00, 0x4D, 0x85, 0xFF, 0x0F, 0x85, 0x41, 0xFB, 0xFF, 0xFF]

theorem code_l104692 : ∀ x ∈ codeRange 0x104692 bytes_l104692, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4692 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1046a2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1046a2 (leaR64Effect 0x1046a2 3 (.sib 4 none 0 (.d32 0x1f0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x1046a2 (fun s => s.RIP = 0x1046a2) (leaR64Effect 0x1046a2 3 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1046aa (leaR64Effect 0x1046aa 6 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x1046aa (fun s => s.RIP = 0x1046aa) (leaR64Effect 0x1046aa 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1046b2 (movR32Imm32Effect 0x1046b2 5 2 0xa8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1046b2 (fun s => s.RIP = 0x1046b2) (movR32Imm32Effect 0x1046b2 5 2 0xa8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1046b7 (movR64R64Effect 0x1046b7 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 60) (.exec 0x1046b7 (fun s => s.RIP = 0x1046b7) (movR64R64Effect 0x1046b7 7 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 61) (.out 0x1046ba (callEffect (callMemPtr 0x1046ba (.rip 0xff710)) (0x1046ba + BitVec.ofNat 64 (callMemLen (.rip 0xff710)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x1046ba (GoesTo (CallMemPre 0x1046ba (.rip 0xff710)) (callEffect (callMemPtr 0x1046ba (.rip 0xff710)) (0x1046ba + BitVec.ofNat 64 (callMemLen (.rip 0xff710)))) 0x12a820) (callEffect (callMemPtr 0x1046ba (.rip 0xff710)) (0x1046ba + BitVec.ofNat 64 (callMemLen (.rip 0xff710)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x1046c0⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 53), (4, 61), (5, 5), (6, 55), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l1046c0, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l1046a2 : List UInt8 :=
  [0x48, 0x8D, 0x9C, 0x24, 0xF0, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0xBA, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0xFF, 0x15, 0x10, 0xF7, 0x0F, 0x00]

theorem code_l1046a2 : ∀ x ∈ codeRange 0x1046a2 bytes_l1046a2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x46a2 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1046c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1046c0 (StorePre 0x1046c0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1046c0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1046c0 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x1046c9 (StorePre 0x1046c9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1046c9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1046c9 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1046d2 (StorePre 0x1046d2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1046d2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1046d2 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1046db (StorePre 0x1046db 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1046db + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1046db (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1046e4 (leaR64Effect 0x1046e4 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x1046e4 (fun s => s.RIP = 0x1046e4) (leaR64Effect 0x1046e4 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1046e9 (movR64R64Effect 0x1046e9 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 60) (.exec 0x1046e9 (fun s => s.RIP = 0x1046e9) (movR64R64Effect 0x1046e9 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 61) (.out 0x1046ec (callEffect (fun _ => 0x107a50) 0x1046f1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x1046ec (PushPre 0x1046ec 5) (callEffect (fun _ => 0x107a50) 0x1046f1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x1046f1⟩) #v[]
    (.terminate (.call ⟨.l107a50, RegMap.args [(1, 1), (3, 3), (4, 61), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l1046f1, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l1046c0 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x28,
    0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x10, 0x48, 0x89, 0xDF, 0xE8, 0x5F, 0x33, 0x00,
    0x00]

theorem code_l1046c0 : ∀ x ∈ codeRange 0x1046c0 bytes_l1046c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x46c0 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1046f1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1046f1 (movR64M64Effect 0x1046f1 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1046f1 (LoadPre 0x1046f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1046f1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1046f1 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1046f6 (StorePre 0x1046f6 4 (fun s => AddrMode.addr (.base 5 (.d8 0x18)) s (0x1046f6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1046f6 0 (.base 5 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 56) (.out 0x1046fa (movR64M64Effect 0x1046fa 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1046fa (LoadPre 0x1046fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1046fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1046fa 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1046ff (StorePre 0x1046ff 4 (fun s => AddrMode.addr (.base 5 (.d8 0x10)) s (0x1046ff + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1046ff 0 (.base 5 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[56, 5]
    (.letOp (n := 59) (.out 0x104703 (movR64M64Effect 0x104703 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x104703 (LoadPre 0x104703 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104703 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104703 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x104708 (movR64M64Effect 0x104708 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x104708 (LoadPre 0x104708 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104708 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104708 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x10470d (StorePre 0x10470d 4 (fun s => AddrMode.addr (.base 5 (.d8 0x8)) s (0x10470d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10470d 1 (.base 5 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[61, 5]
    (.letOp (n := 64) (.exec 0x104711 (StorePre 0x104711 4 (fun s => AddrMode.addr (.base 5 (.d8 0x0)) s (0x104711 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104711 0 (.base 5 (.d8 0x0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[59, 5]
    (.letOp (n := 65) (.out 0x104715 (movR64R64Effect 0x104715 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 66) (.exec 0x104715 (fun s => s.RIP = 0x104715) (movR64R64Effect 0x104715 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.terminate (.br ⟨.l10494c, RegMap.args [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l1046f1 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x45, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89,
    0x45, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x4D, 0x08,
    0x48, 0x89, 0x45, 0x00, 0x48, 0x89, 0xEF, 0xE9, 0x2F, 0x02, 0x00, 0x00]

theorem code_l1046f1 : ∀ x ∈ codeRange 0x1046f1 bytes_l1046f1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x46f1 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10471d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10471d (movR32Imm32Effect 0x10471d 5 2 0x40) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x10471d (fun s => s.RIP = 0x10471d) (movR32Imm32Effect 0x10471d 5 2 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x104722 (subR64R64Effect 0x104722 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x104722 (fun s => s.RIP = 0x104722) (subR64R64Effect 0x104722 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x104725 (movR64M64Effect 0x104725 6 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x104725 (LoadPre 0x104725 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x104725 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104725 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10472a (leaR64Effect 0x10472a 15 (.sib 6 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6, .gpr 2] []) (.reg (.gpr 15))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x10472a (fun s => s.RIP = 0x10472a) (leaR64Effect 0x10472a 15 (.sib 6 (some 2) 0 .none)) (Reg.operands [.gpr 6, .gpr 2] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x10472e (leaR64Effect 0x10472e 7 (.sib 3 (some 13) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3, .gpr 13] []) (.reg (.gpr 7))) #v[3, 13]
    (.letOp (n := 62) (.exec 0x10472e (fun s => s.RIP = 0x10472e) (leaR64Effect 0x10472e 7 (.sib 3 (some 13) 0 .none)) (Reg.operands [.gpr 3, .gpr 13] [])) #v[3, 13]
    (.letOp (n := 63) (.out 0x104732 (addR64Imm8Effect 0x104732 3 0xe0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 64) (.exec 0x104732 (fun s => s.RIP = 0x104732) (addR64Imm8Effect 0x104732 3 0xe0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 65) (.out 0x104736 (leaR64Effect 0x104736 12 (.rip 0x260e3)) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 66) (.exec 0x104736 (fun s => s.RIP = 0x104736) (leaR64Effect 0x104736 12 (.rip 0x260e3)) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x10473d (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x104740) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 65]
    (.letOp (n := 68) (.exec 0x10473d (GoesTo (CallPre 0x10473d 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x104740) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x104740) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 65]
    (.letOp (n := 69) (.const ⟨64, 0x104740⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 63), (4, 67), (5, 5), (6, 57), (7, 61), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l104740, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l10471d : List UInt8 :=
  [0xBA, 0x40, 0x00, 0x00, 0x00, 0x48, 0x29, 0xDA, 0x48, 0x8B, 0x74, 0x24, 0x70, 0x4C, 0x8D, 0x3C,
    0x16, 0x4A, 0x8D, 0x3C, 0x2B, 0x48, 0x83, 0xC3, 0xE0, 0x4C, 0x8D, 0x25, 0xE3, 0x60, 0x02, 0x00,
    0x41, 0xFF, 0xD4]

theorem code_l10471d : ∀ x ∈ codeRange 0x10471d bytes_l10471d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x471d 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104740 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104740 (StorePre 0x104740 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x104740 + BitVec.ofNat 64 8)) 8) (incMEffect 0x104740 8 64 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x104748 (movR32Imm32Effect 0x104748 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 55) (.exec 0x104748 (fun s => s.RIP = 0x104748) (movR32Imm32Effect 0x104748 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.out 0x10474d (movR64R64Effect 0x10474d 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 57) (.exec 0x10474d (fun s => s.RIP = 0x10474d) (movR64R64Effect 0x10474d 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 58) (.out 0x104750 (movR64R64Effect 0x104750 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 59) (.exec 0x104750 (fun s => s.RIP = 0x104750) (movR64R64Effect 0x104750 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 60) (.out 0x104753 (callEffect (fun _ => 0x1218e0) 0x104758) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x104753 (PushPre 0x104753 5) (callEffect (fun _ => 0x1218e0) 0x104758) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x104758⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ { target := .l104758, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l104740 : List UInt8 :=
  [0x48, 0xFF, 0x84, 0x24, 0xE8, 0x01, 0x00, 0x00, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEF,
    0x4C, 0x89, 0xEE, 0xE8, 0x88, 0xD1, 0x01, 0x00]

theorem code_l104740 : ∀ x ∈ codeRange 0x104740 bytes_l104740, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4740 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104758 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104758 (movR64R64Effect 0x104758 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 54) (.exec 0x104758 (fun s => s.RIP = 0x104758) (movR64R64Effect 0x104758 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10475b (movR64Imm64Effect 0x10475b 0 0x7fffffffffffffc0) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x10475b (fun s => s.RIP = 0x10475b) (movR64Imm64Effect 0x10475b 0 0x7fffffffffffffc0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x104765 (andR64R64Effect 0x104765 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x104765 (fun s => s.RIP = 0x104765) (andR64R64Effect 0x104765 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x104768 (addR64R64Effect 0x104768 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[57, 15]
    (.letOp (n := 60) (.exec 0x104768 (fun s => s.RIP = 0x104768) (addR64R64Effect 0x104768 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[57, 15]
    (.letOp (n := 61) (.exec 0x10476b (StorePre 0x10476b 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x10476b + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10476b 7 3 (.sib 4 none 0 (.d32 0x1c7))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 62) (.out 0x104772 (movR64R64Effect 0x104772 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 63) (.exec 0x104772 (fun s => s.RIP = 0x104772) (movR64R64Effect 0x104772 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 64) (.out 0x104775 (movR64R64Effect 0x104775 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 65) (.exec 0x104775 (fun s => s.RIP = 0x104775) (movR64R64Effect 0x104775 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 66) (.out 0x104778 (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10477b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 12]
    (.letOp (n := 67) (.exec 0x104778 (GoesTo (CallPre 0x104778 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10477b) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10477b) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 68) (.const ⟨64, 0x10477b⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 55), (2, 64), (3, 3), (4, 66), (5, 5), (6, 59), (7, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l10477b, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l104758 : List UInt8 :=
  [0x48, 0x89, 0xDE, 0x48, 0xB8, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x48, 0x21, 0xC6,
    0x4C, 0x01, 0xFE, 0x88, 0x9C, 0x24, 0xC7, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x48, 0x89, 0xDA,
    0x41, 0xFF, 0xD4]

theorem code_l104758 : ∀ x ∈ codeRange 0x104758 bytes_l104758, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4758 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10477b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10477b (movzxR32M8Effect 0x10477b 8 3 (.sib 4 none 0 (.d32 0x1c7))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x10477b (LoadPre 0x10477b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x10477b + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10477b 8 3 (.sib 4 none 0 (.d32 0x1c7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104783 (movR64M64Effect 0x104783 15 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x104783 (LoadPre 0x104783 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104783 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104783 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x104788 (movzxR32R8Effect 0x104788 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 58) (.exec 0x104788 (fun s => s.RIP = 0x104788) (movzxR32R8Effect 0x104788 3 0 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 59) (.out 0x10478b (cmpAlImm8Effect 0x10478b 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[57]
    (.letOp (n := 60) (.exec 0x10478b (fun s => s.RIP = 0x10478b) (cmpAlImm8Effect 0x10478b 0x3f) (Reg.operands [.gpr 0] [])) #v[57]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l1045d5, RegMap.args [(0, 57), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l104793, RegMap.args [(0, 57), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l10477b : List UInt8 :=
  [0x0F, 0xB6, 0x9C, 0x24, 0xC7, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x7C, 0x24, 0x08, 0x0F, 0xB6, 0xC3,
    0x3C, 0x3F, 0x0F, 0x85, 0x42, 0xFE, 0xFF, 0xFF]

theorem code_l10477b : ∀ x ∈ codeRange 0x10477b bytes_l10477b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x477b 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104793 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104793 (movR32Imm32Effect 0x104793 5 2 0x40) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x104793 (fun s => s.RIP = 0x104793) (movR32Imm32Effect 0x104793 5 2 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x104798 (subR64R64Effect 0x104798 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[53, 0]
    (.letOp (n := 56) (.exec 0x104798 (fun s => s.RIP = 0x104798) (subR64R64Effect 0x104798 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 57) (.out 0x10479b (leaR64Effect 0x10479b 7 (.sib 0 (some 13) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0, .gpr 13] []) (.reg (.gpr 7))) #v[0, 13]
    (.letOp (n := 58) (.exec 0x10479b (fun s => s.RIP = 0x10479b) (leaR64Effect 0x10479b 7 (.sib 0 (some 13) 0 .none)) (Reg.operands [.gpr 0, .gpr 13] [])) #v[0, 13]
    (.letOp (n := 59) (.out 0x10479f (movR32Imm32Effect 0x10479f 5 6 0x1) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 60) (.exec 0x10479f (fun s => s.RIP = 0x10479f) (movR32Imm32Effect 0x10479f 5 6 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x1047a4 (callEffect (callMemPtr 0x1047a4 (.rip 0xff666)) (0x1047a4 + BitVec.ofNat 64 (callMemLen (.rip 0xff666)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x1047a4 (GoesTo (CallMemPre 0x1047a4 (.rip 0xff666)) (callEffect (callMemPtr 0x1047a4 (.rip 0xff666)) (0x1047a4 + BitVec.ofNat 64 (callMemLen (.rip 0xff666)))) 0x12a700) (callEffect (callMemPtr 0x1047a4 (.rip 0xff666)) (0x1047a4 + BitVec.ofNat 64 (callMemLen (.rip 0xff666)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x1047aa⟩) #v[]
    (.terminate (.call ⟨.l12a700, RegMap.args [(0, 0), (2, 55), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l1047aa, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l104793 : List UInt8 :=
  [0xBA, 0x40, 0x00, 0x00, 0x00, 0x48, 0x29, 0xC2, 0x4A, 0x8D, 0x3C, 0x28, 0xBE, 0x01, 0x00, 0x00,
    0x00, 0xFF, 0x15, 0x66, 0xF6, 0x0F, 0x00]

theorem code_l104793 : ∀ x ∈ codeRange 0x104793 bytes_l104793, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4793 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1047aa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1047aa (StorePre 0x1047aa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x1047aa + BitVec.ofNat 64 8)) 8) (incMEffect 0x1047aa 8 64 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x1047b2 (movR32Imm32Effect 0x1047b2 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 55) (.exec 0x1047b2 (fun s => s.RIP = 0x1047b2) (movR32Imm32Effect 0x1047b2 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.out 0x1047b7 (movR64R64Effect 0x1047b7 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 57) (.exec 0x1047b7 (fun s => s.RIP = 0x1047b7) (movR64R64Effect 0x1047b7 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 58) (.out 0x1047ba (movR64R64Effect 0x1047ba 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 59) (.exec 0x1047ba (fun s => s.RIP = 0x1047ba) (movR64R64Effect 0x1047ba 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 60) (.out 0x1047bd (callEffect (fun _ => 0x1218e0) 0x1047c2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x1047bd (PushPre 0x1047bd 5) (callEffect (fun _ => 0x1218e0) 0x1047c2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x1047c2⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ { target := .l1047c2, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l1047aa : List UInt8 :=
  [0x48, 0xFF, 0x84, 0x24, 0xE8, 0x01, 0x00, 0x00, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEF,
    0x4C, 0x89, 0xEE, 0xE8, 0x1E, 0xD1, 0x01, 0x00]

theorem code_l1047aa : ∀ x ∈ codeRange 0x1047aa bytes_l1047aa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x47aa 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1047c2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1047c2 (xorR32R32Effect 0x1047c2 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1047c2 (fun s => s.RIP = 0x1047c2) (xorR32R32Effect 0x1047c2 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l1047c4, RegMap.args [(0, 53), (1, 1), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1047c2 : List UInt8 :=
  [0x31, 0xC0]

theorem code_l1047c2 : ∀ x ∈ codeRange 0x1047c2 bytes_l1047c2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x47c2 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1047c4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1047c4 (StorePre 0x1047c4 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x1047c4 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1047c4 7 0 (.sib 4 none 0 (.d32 0x1c7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.terminate (.br ⟨.l1047fb, RegMap.args [(0, 0), (1, 1), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l1047c4 : List UInt8 :=
  [0x88, 0x84, 0x24, 0xC7, 0x01, 0x00, 0x00, 0xEB, 0x2E]

theorem code_l1047c4 : ∀ x ∈ codeRange 0x1047c4 bytes_l1047c4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x47c4 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1047d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1047d0 (movR32R32Effect 0x1047d0 3 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 54) (.exec 0x1047d0 (fun s => s.RIP = 0x1047d0) (movR32R32Effect 0x1047d0 3 15 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1047d3 (addR64R64Effect 0x1047d3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[7, 13]
    (.letOp (n := 56) (.exec 0x1047d3 (fun s => s.RIP = 0x1047d3) (addR64R64Effect 0x1047d3 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[7, 13]
    (.letOp (n := 57) (.out 0x1047d6 (movR64R64Effect 0x1047d6 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 58) (.exec 0x1047d6 (fun s => s.RIP = 0x1047d6) (movR64R64Effect 0x1047d6 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x1047d9 (callEffect (callMemPtr 0x1047d9 (.rip 0xff5f1)) (0x1047d9 + BitVec.ofNat 64 (callMemLen (.rip 0xff5f1)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1047d9 (GoesTo (CallMemPre 0x1047d9 (.rip 0xff5f1)) (callEffect (callMemPtr 0x1047d9 (.rip 0xff5f1)) (0x1047d9 + BitVec.ofNat 64 (callMemLen (.rip 0xff5f1)))) 0x12a820) (callEffect (callMemPtr 0x1047d9 (.rip 0xff5f1)) (0x1047d9 + BitVec.ofNat 64 (callMemLen (.rip 0xff5f1)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1047df⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1047df, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1047d0 : List UInt8 :=
  [0x41, 0x89, 0xFF, 0x4C, 0x01, 0xEF, 0x48, 0x89, 0xDA, 0xFF, 0x15, 0xF1, 0xF5, 0x0F, 0x00]

theorem code_l1047d0 : ∀ x ∈ codeRange 0x1047d0 bytes_l1047d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x47d0 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1047df : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1047df (addR8R8Effect 0x1047df 3 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[3, 15]
    (.letOp (n := 54) (.exec 0x1047df (fun s => s.RIP = 0x1047df) (addR8R8Effect 0x1047df 3 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[3, 15]
    (.letOp (n := 55) (.out 0x1047e2 (movR64M64Effect 0x1047e2 15 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x1047e2 (LoadPre 0x1047e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1047e2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1047e2 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1047e7 (StorePre 0x1047e7 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x1047e7 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1047e7 7 3 (.sib 4 none 0 (.d32 0x1c7))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.out 0x1047ee (addR64Imm8Effect 0x1047ee 14 0x10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 59) (.exec 0x1047ee (fun s => s.RIP = 0x1047ee) (addR64Imm8Effect 0x1047ee 14 0x10) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 60) (.out 0x1047f2 (cmpR64R64Effect 0x1047f2 14 15) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 15] []) (.flag .ZF)) #v[58, 55]
    (.letOp (n := 61) (.exec 0x1047f2 (fun s => s.RIP = 0x1047f2) (cmpR64R64Effect 0x1047f2 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[58, 55]
    (.letOp (n := 62) (.pure (condOp 4)) #v[60]
    (.terminate (.condBr (Fin.last 62) ⟨.l1048ba, RegMap.args [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 55), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ ⟨.l1047fb, RegMap.args [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 55), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l1047df : List UInt8 :=
  [0x44, 0x00, 0xFB, 0x4C, 0x8B, 0x7C, 0x24, 0x08, 0x88, 0x9C, 0x24, 0xC7, 0x01, 0x00, 0x00, 0x49,
    0x83, 0xC6, 0x10, 0x4D, 0x39, 0xFE, 0x0F, 0x84, 0xBF, 0x00, 0x00, 0x00]

theorem code_l1047df : ∀ x ∈ codeRange 0x1047df bytes_l1047df, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x47df 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1047fb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1047fb (movR64M64Effect 0x1047fb 6 (.base 14 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 54) (.exec 0x1047fb (LoadPre 0x1047fb (fun s => AddrMode.addr (.base 14 .none) s (0x1047fb + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1047fb 6 (.base 14 .none)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x1047fe (movR64M64Effect 0x1047fe 3 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 14] []) (.reg (.gpr 3))) #v[14]
    (.letOp (n := 56) (.exec 0x1047fe (LoadPre 0x1047fe (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1047fe + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1047fe 3 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x104802 (movzxR32M8Effect 0x104802 8 7 (.sib 4 none 0 (.d32 0x1c7))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x104802 (LoadPre 0x104802 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x104802 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x104802 8 7 (.sib 4 none 0 (.d32 0x1c7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10480a (movR32Imm32Effect 0x10480a 5 2 0x40) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x10480a (fun s => s.RIP = 0x10480a) (movR32Imm32Effect 0x10480a 5 2 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10480f (subR64R64Effect 0x10480f 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x10480f (fun s => s.RIP = 0x10480f) (subR64R64Effect 0x10480f 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x104812 (movR64R64Effect 0x104812 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 64) (.exec 0x104812 (fun s => s.RIP = 0x104812) (movR64R64Effect 0x104812 12 3) (Reg.operands [.gpr 3] [])) #v[55]
    (.letOp (n := 65) (.out 0x104815 (subR64R64Effect 0x104815 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[63, 61]
    (.letOp (n := 66) (.out 0x104815 (subR64R64Effect 0x104815 12 2) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 2] []) (.flag .CF)) #v[63, 61]
    (.letOp (n := 67) (.exec 0x104815 (fun s => s.RIP = 0x104815) (subR64R64Effect 0x104815 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[63, 61]
    (.letOp (n := 68) (.pure (condOp 2)) #v[66]
    (.terminate (.condBr (Fin.last 68) ⟨.l1047d0, RegMap.args [(0, 0), (1, 1), (2, 61), (3, 55), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (16, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ ⟨.l10481a, RegMap.args [(0, 0), (1, 1), (2, 61), (3, 55), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (16, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l1047fb : List UInt8 :=
  [0x49, 0x8B, 0x36, 0x49, 0x8B, 0x5E, 0x08, 0x0F, 0xB6, 0xBC, 0x24, 0xC7, 0x01, 0x00, 0x00, 0xBA,
    0x40, 0x00, 0x00, 0x00, 0x48, 0x29, 0xFA, 0x49, 0x89, 0xDC, 0x49, 0x29, 0xD4, 0x72, 0xB6]

theorem code_l1047fb : ∀ x ∈ codeRange 0x1047fb bytes_l1047fb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x47fb 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10481a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10481a (testR64R64Effect 0x10481a 7 7) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 7] []) (.flag .ZF)) #v[7, 7]
    (.letOp (n := 54) (.exec 0x10481a (fun s => s.RIP = 0x10481a) (testR64R64Effect 0x10481a 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1048ac, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l104823, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10481a : List UInt8 :=
  [0x48, 0x85, 0xFF, 0x0F, 0x84, 0x89, 0x00, 0x00, 0x00]

theorem code_l10481a : ∀ x ∈ codeRange 0x10481a bytes_l10481a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x481a 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104823 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104823 (leaR64Effect 0x104823 3 (.sib 6 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6, .gpr 2] []) (.reg (.gpr 3))) #v[6, 2]
    (.letOp (n := 54) (.exec 0x104823 (fun s => s.RIP = 0x104823) (leaR64Effect 0x104823 3 (.sib 6 (some 2) 0 .none)) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6, 2]
    (.letOp (n := 55) (.out 0x104827 (addR64R64Effect 0x104827 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[7, 13]
    (.letOp (n := 56) (.exec 0x104827 (fun s => s.RIP = 0x104827) (addR64R64Effect 0x104827 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[7, 13]
    (.letOp (n := 57) (.out 0x10482a (callEffect (callMemPtr 0x10482a (.rip 0xff5a0)) (0x10482a + BitVec.ofNat 64 (callMemLen (.rip 0xff5a0)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10482a (GoesTo (CallMemPre 0x10482a (.rip 0xff5a0)) (callEffect (callMemPtr 0x10482a (.rip 0xff5a0)) (0x10482a + BitVec.ofNat 64 (callMemLen (.rip 0xff5a0)))) 0x12a820) (callEffect (callMemPtr 0x10482a (.rip 0xff5a0)) (0x10482a + BitVec.ofNat 64 (callMemLen (.rip 0xff5a0)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x104830⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 2), (3, 53), (4, 57), (5, 5), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l104830, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l104823 : List UInt8 :=
  [0x48, 0x8D, 0x1C, 0x16, 0x4C, 0x01, 0xEF, 0xFF, 0x15, 0xA0, 0xF5, 0x0F, 0x00]

theorem code_l104823 : ∀ x ∈ codeRange 0x104823 bytes_l104823, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4823 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104830 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104830 (StorePre 0x104830 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x104830 + BitVec.ofNat 64 8)) 8) (incMEffect 0x104830 8 64 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x104838 (movR32Imm32Effect 0x104838 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 55) (.exec 0x104838 (fun s => s.RIP = 0x104838) (movR32Imm32Effect 0x104838 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.out 0x10483d (movR64R64Effect 0x10483d 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 57) (.exec 0x10483d (fun s => s.RIP = 0x10483d) (movR64R64Effect 0x10483d 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 58) (.out 0x104840 (movR64R64Effect 0x104840 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 59) (.exec 0x104840 (fun s => s.RIP = 0x104840) (movR64R64Effect 0x104840 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 60) (.out 0x104843 (callEffect (fun _ => 0x1218e0) 0x104848) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x104843 (PushPre 0x104843 5) (callEffect (fun _ => 0x1218e0) 0x104848) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x104848⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ { target := .l104848, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l104830 : List UInt8 :=
  [0x48, 0xFF, 0x84, 0x24, 0xE8, 0x01, 0x00, 0x00, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEF,
    0x4C, 0x89, 0xEE, 0xE8, 0x98, 0xD0, 0x01, 0x00]

theorem code_l104830 : ∀ x ∈ codeRange 0x104830 bytes_l104830, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4830 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104848 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104848 (StorePre 0x104848 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x104848 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x104848 (.sib 4 none 0 (.d32 0x1c7)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x104850 (movR64R64Effect 0x104850 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 55) (.exec 0x104850 (fun s => s.RIP = 0x104850) (movR64R64Effect 0x104850 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.out 0x104853 (movR64R64Effect 0x104853 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 57) (.exec 0x104853 (fun s => s.RIP = 0x104853) (movR64R64Effect 0x104853 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 58) (.out 0x104856 (shrR64Effect 0x104856 4 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[56]
    (.letOp (n := 59) (.out 0x104856 (shrR64Effect 0x104856 4 2 6) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[56]
    (.letOp (n := 60) (.exec 0x104856 (fun s => s.RIP = 0x104856) (shrR64Effect 0x104856 4 2 6) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 61) (.pure (condOp 4)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l104872, RegMap.args [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (5, 5), (6, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l10485c, RegMap.args [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (5, 5), (6, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l104848 : List UInt8 :=
  [0xC6, 0x84, 0x24, 0xC7, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDE, 0x4C, 0x89, 0xE2, 0x48, 0xC1,
    0xEA, 0x06, 0x74, 0x16]

theorem code_l104848 : ∀ x ∈ codeRange 0x104848 bytes_l104848, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4848 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10485c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10485c (StorePre 0x10485c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x10485c + BitVec.ofNat 64 8)) 8) (addMREffect 0x10485c 8 64 2 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 54) (.out 0x104864 (movR64R64Effect 0x104864 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 55) (.exec 0x104864 (fun s => s.RIP = 0x104864) (movR64R64Effect 0x104864 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 56) (.out 0x104867 (movR64R64Effect 0x104867 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 57) (.exec 0x104867 (fun s => s.RIP = 0x104867) (movR64R64Effect 0x104867 3 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 58) (.out 0x10486a (callEffect (fun _ => 0x1218e0) 0x10486f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 59) (.exec 0x10486a (PushPre 0x10486a 5) (callEffect (fun _ => 0x1218e0) 0x10486f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.const ⟨64, 0x10486f⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 56), (4, 58), (5, 5), (6, 6), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ { target := .l10486f, kept := #v[], arity := rfl, guard := some (Fin.last 60) })))))))))

def bytes_l10485c : List UInt8 :=
  [0x48, 0x01, 0x94, 0x24, 0xE8, 0x01, 0x00, 0x00, 0x48, 0x89, 0xEF, 0x48, 0x89, 0xF3, 0xE8, 0x71,
    0xD0, 0x01, 0x00]

theorem code_l10485c : ∀ x ∈ codeRange 0x10485c bytes_l10485c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x485c 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10486f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10486f (movR64R64Effect 0x10486f 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 54) (.exec 0x10486f (fun s => s.RIP = 0x10486f) (movR64R64Effect 0x10486f 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l104872, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l10486f : List UInt8 :=
  [0x48, 0x89, 0xDE]

theorem code_l10486f : ∀ x ∈ codeRange 0x10486f bytes_l10486f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x486f 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104872 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104872 (movR64R64Effect 0x104872 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 54) (.exec 0x104872 (fun s => s.RIP = 0x104872) (movR64R64Effect 0x104872 0 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x104875 (movR64Imm64Effect 0x104875 1 0x7fffffffffffffc0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x104875 (fun s => s.RIP = 0x104875) (movR64Imm64Effect 0x104875 1 0x7fffffffffffffc0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10487f (andR64R64Effect 0x10487f 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x10487f (fun s => s.RIP = 0x10487f) (andR64R64Effect 0x10487f 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x104882 (andR32Imm8Effect 0x104882 4 12 0x3f) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 60) (.exec 0x104882 (fun s => s.RIP = 0x104882) (andR32Imm8Effect 0x104882 4 12 0x3f) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 61) (.out 0x104886 (addR64R64Effect 0x104886 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[6, 57]
    (.letOp (n := 62) (.exec 0x104886 (fun s => s.RIP = 0x104886) (addR64R64Effect 0x104886 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[6, 57]
    (.letOp (n := 63) (.exec 0x104889 (StorePre 0x104889 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c7)) s (0x104889 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x104889 8 12 (.sib 4 none 0 (.d32 0x1c7))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 64) (.out 0x104891 (movR64R64Effect 0x104891 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 65) (.exec 0x104891 (fun s => s.RIP = 0x104891) (movR64R64Effect 0x104891 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 66) (.out 0x104894 (movR64R64Effect 0x104894 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 67) (.exec 0x104894 (fun s => s.RIP = 0x104894) (movR64R64Effect 0x104894 2 12) (Reg.operands [.gpr 12] [])) #v[59]
    (.letOp (n := 68) (.out 0x104897 (callEffect (callMemPtr 0x104897 (.rip 0xff533)) (0x104897 + BitVec.ofNat 64 (callMemLen (.rip 0xff533)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 69) (.exec 0x104897 (GoesTo (CallMemPre 0x104897 (.rip 0xff533)) (callEffect (callMemPtr 0x104897 (.rip 0xff533)) (0x104897 + BitVec.ofNat 64 (callMemLen (.rip 0xff533)))) 0x12a820) (callEffect (callMemPtr 0x104897 (.rip 0xff533)) (0x104897 + BitVec.ofNat 64 (callMemLen (.rip 0xff533)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.const ⟨64, 0x10489d⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 57), (1, 55), (2, 66), (3, 3), (4, 68), (5, 5), (6, 61), (7, 64), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l10489d, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l104872 : List UInt8 :=
  [0x4C, 0x89, 0xE0, 0x48, 0xB9, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x48, 0x21, 0xC8,
    0x41, 0x83, 0xE4, 0x3F, 0x48, 0x01, 0xC6, 0x44, 0x88, 0xA4, 0x24, 0xC7, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0xEF, 0x4C, 0x89, 0xE2, 0xFF, 0x15, 0x33, 0xF5, 0x0F, 0x00]

theorem code_l104872 : ∀ x ∈ codeRange 0x104872 bytes_l104872, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4872 43 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10489d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10489d (addR64Imm8Effect 0x10489d 14 0x10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 54) (.exec 0x10489d (fun s => s.RIP = 0x10489d) (addR64Imm8Effect 0x10489d 14 0x10) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x1048a1 (cmpR64R64Effect 0x1048a1 14 15) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 15] []) (.flag .ZF)) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1048a1 (fun s => s.RIP = 0x1048a1) (cmpR64R64Effect 0x1048a1 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1047fb, RegMap.args [(0, 0), (1, 1), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1048aa, RegMap.args [(0, 0), (1, 1), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l10489d : List UInt8 :=
  [0x49, 0x83, 0xC6, 0x10, 0x4D, 0x39, 0xFE, 0x0F, 0x85, 0x51, 0xFF, 0xFF, 0xFF]

theorem code_l10489d : ∀ x ∈ codeRange 0x10489d bytes_l10489d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x489d 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1048aa : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1048ba, RegMap.args (entryMap (live .l1048aa)) 53⟩)

def bytes_l1048aa : List UInt8 :=
  [0xEB, 0x0E]

theorem code_l1048aa : ∀ x ∈ codeRange 0x1048aa bytes_l1048aa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x48aa 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1048ac : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1048ac (movR64R64Effect 0x1048ac 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[3]
    (.letOp (n := 54) (.exec 0x1048ac (fun s => s.RIP = 0x1048ac) (movR64R64Effect 0x1048ac 12 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1048af (movR64R64Effect 0x1048af 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 56) (.exec 0x1048af (fun s => s.RIP = 0x1048af) (movR64R64Effect 0x1048af 2 12) (Reg.operands [.gpr 12] [])) #v[53]
    (.letOp (n := 57) (.out 0x1048b2 (shrR64Effect 0x1048b2 4 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 58) (.out 0x1048b2 (shrR64Effect 0x1048b2 4 2 6) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[55]
    (.letOp (n := 59) (.exec 0x1048b2 (fun s => s.RIP = 0x1048b2) (shrR64Effect 0x1048b2 4 2 6) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 60) (.pure (condOp 5)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l10485c, RegMap.args [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l1048b8, RegMap.args [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1048ac : List UInt8 :=
  [0x49, 0x89, 0xDC, 0x4C, 0x89, 0xE2, 0x48, 0xC1, 0xEA, 0x06, 0x75, 0xA4]

theorem code_l1048ac : ∀ x ∈ codeRange 0x1048ac bytes_l1048ac, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x48ac 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1048b8 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l104872, RegMap.args (entryMap (live .l1048b8)) 53⟩)

def bytes_l1048b8 : List UInt8 :=
  [0xEB, 0xB8]

theorem code_l1048b8 : ∀ x ∈ codeRange 0x1048b8 bytes_l1048b8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x48b8 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1048ba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1048ba (leaR64Effect 0x1048ba 3 (.sib 4 none 0 (.d32 0x1f0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x1048ba (fun s => s.RIP = 0x1048ba) (leaR64Effect 0x1048ba 3 (.sib 4 none 0 (.d32 0x1f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1048c2 (leaR64Effect 0x1048c2 6 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x1048c2 (fun s => s.RIP = 0x1048c2) (leaR64Effect 0x1048c2 6 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1048ca (movR32Imm32Effect 0x1048ca 5 2 0xa8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1048ca (fun s => s.RIP = 0x1048ca) (movR32Imm32Effect 0x1048ca 5 2 0xa8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1048cf (movR64R64Effect 0x1048cf 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 60) (.exec 0x1048cf (fun s => s.RIP = 0x1048cf) (movR64R64Effect 0x1048cf 7 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 61) (.out 0x1048d2 (callEffect (callMemPtr 0x1048d2 (.rip 0xff4f8)) (0x1048d2 + BitVec.ofNat 64 (callMemLen (.rip 0xff4f8)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x1048d2 (GoesTo (CallMemPre 0x1048d2 (.rip 0xff4f8)) (callEffect (callMemPtr 0x1048d2 (.rip 0xff4f8)) (0x1048d2 + BitVec.ofNat 64 (callMemLen (.rip 0xff4f8)))) 0x12a820) (callEffect (callMemPtr 0x1048d2 (.rip 0xff4f8)) (0x1048d2 + BitVec.ofNat 64 (callMemLen (.rip 0xff4f8)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x1048d8⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 53), (4, 61), (5, 5), (6, 55), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l1048d8, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l1048ba : List UInt8 :=
  [0x48, 0x8D, 0x9C, 0x24, 0xF0, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x48, 0x01, 0x00, 0x00,
    0xBA, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0xFF, 0x15, 0xF8, 0xF4, 0x0F, 0x00]

theorem code_l1048ba : ∀ x ∈ codeRange 0x1048ba bytes_l1048ba, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x48ba 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1048d8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1048d8 (StorePre 0x1048d8 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1048d8 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1048d8 (.sib 4 none 0 (.d32 0x80)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x1048e4 (StorePre 0x1048e4 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1048e4 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1048e4 (.sib 4 none 0 (.d32 0x88)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1048f0 (StorePre 0x1048f0 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1048f0 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1048f0 (.sib 4 none 0 (.d32 0x90)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1048fc (StorePre 0x1048fc 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1048fc + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1048fc (.sib 4 none 0 (.d32 0x98)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x104908 (leaR64Effect 0x104908 6 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x104908 (fun s => s.RIP = 0x104908) (leaR64Effect 0x104908 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x104910 (movR64R64Effect 0x104910 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 60) (.exec 0x104910 (fun s => s.RIP = 0x104910) (movR64R64Effect 0x104910 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 61) (.out 0x104913 (callEffect (fun _ => 0x107a50) 0x104918) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x104913 (PushPre 0x104913 5) (callEffect (fun _ => 0x107a50) 0x104918) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x104918⟩) #v[]
    (.terminate (.call ⟨.l107a50, RegMap.args [(1, 1), (3, 3), (4, 61), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l104918, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l1048d8 : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0xE8, 0x38, 0x31, 0x00, 0x00]

theorem code_l1048d8 : ∀ x ∈ codeRange 0x1048d8 bytes_l1048d8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x48d8 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104918 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104918 (movR64M64Effect 0x104918 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x104918 (LoadPre 0x104918 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x104918 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104918 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104920 (movR64M64Effect 0x104920 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x104920 (LoadPre 0x104920 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x104920 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104920 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x104925 (StorePre 0x104925 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x104925 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104925 0 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[53, 55]
    (.letOp (n := 58) (.out 0x104929 (movR64M64Effect 0x104929 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 59) (.exec 0x104929 (LoadPre 0x104929 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x104929 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104929 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x104931 (StorePre 0x104931 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x104931 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104931 0 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[58, 55]
    (.letOp (n := 61) (.out 0x104935 (movR64M64Effect 0x104935 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 62) (.exec 0x104935 (LoadPre 0x104935 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x104935 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x104935 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x10493d (movR64M64Effect 0x10493d 1 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 64) (.exec 0x10493d (LoadPre 0x10493d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10493d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10493d 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x104945 (StorePre 0x104945 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x104945 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104945 1 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[63, 55]
    (.letOp (n := 66) (.exec 0x104949 (StorePre 0x104949 3 (fun s => AddrMode.addr (.base 7 .none) s (0x104949 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x104949 0 (.base 7 .none)) (Reg.operands [.gpr 0, .gpr 7] [])) #v[61, 55]
    (.terminate (.br ⟨.l10494c, RegMap.args [(0, 61), (1, 63), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l104918 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x7C, 0x24, 0x78, 0x48, 0x89, 0x47,
    0x18, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x47, 0x10, 0x48, 0x8B, 0x84,
    0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4F,
    0x08, 0x48, 0x89, 0x07]

theorem code_l104918 : ∀ x ∈ codeRange 0x104918 bytes_l104918, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4918 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10494c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10494c (callEffect (fun _ => 0x104970) 0x104951) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x10494c (PushPre 0x10494c 5) (callEffect (fun _ => 0x104970) 0x104951) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.const ⟨64, 0x104951⟩) #v[]
    (.terminate (.call ⟨.l104970, RegMap.args [(3, 3), (4, 53), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ { target := .l104951, kept := #v[], arity := rfl, guard := some (Fin.last 55) }))))

def bytes_l10494c : List UInt8 :=
  [0xE8, 0x1F, 0x00, 0x00, 0x00]

theorem code_l10494c : ∀ x ∈ codeRange 0x10494c bytes_l10494c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x494c 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104951 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104951 (addR64Imm32Effect 0x104951 4 0x298) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x104951 (fun s => s.RIP = 0x104951) (addR64Imm32Effect 0x104951 4 0x298) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104958 (popR64Effect 0x104958 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x104958 (popR64Effect 0x104958 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x104958 (PopPre 0x104958) (popR64Effect 0x104958 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x104959 (popR64Effect 0x104959 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x104959 (popR64Effect 0x104959 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x104959 (PopPre 0x104959) (popR64Effect 0x104959 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x10495b (popR64Effect 0x10495b 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x10495b (popR64Effect 0x10495b 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x10495b (PopPre 0x10495b) (popR64Effect 0x10495b 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x10495d (popR64Effect 0x10495d 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x10495d (popR64Effect 0x10495d 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x10495d (PopPre 0x10495d) (popR64Effect 0x10495d 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x10495f (popR64Effect 0x10495f 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x10495f (popR64Effect 0x10495f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x10495f (PopPre 0x10495f) (popR64Effect 0x10495f 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x104961 (popR64Effect 0x104961 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x104961 (popR64Effect 0x104961 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x104961 (PopPre 0x104961) (popR64Effect 0x104961 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x104962 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x104962 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x104962 (RetPre 0x104962) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l104951 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0x98, 0x02, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l104951 : ∀ x ∈ codeRange 0x104951 bytes_l104951, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4951 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104970_1 : Block Op Label signature Reg.count 85 :=
  .letOp (n := 85) (.exec 0x1049d7 (StorePre 0x1049d7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1049d7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1049d7 (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 86) (.exec 0x1049e0 (StorePre 0x1049e0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1049e0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1049e0 (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 87) (.exec 0x1049e9 (StorePre 0x1049e9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1049e9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1049e9 (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 88) (.exec 0x1049f2 (StorePre 0x1049f2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1049f2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1049f2 (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 89) (.out 0x1049fb (movR32Imm32Effect 0x1049fb 5 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 90) (.exec 0x1049fb (fun s => s.RIP = 0x1049fb) (movR32Imm32Effect 0x1049fb 5 0 0x3) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l104a00, RegMap.args [(0, 89), (1, 75), (2, 77), (3, 67), (4, 65), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩)))))))

def bytes_l104970_1 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x40,
    0x00, 0x00, 0x00, 0x00, 0xB8, 0x03, 0x00, 0x00, 0x00]

theorem code_l104970_1 : ∀ x ∈ codeRange 0x1049d7 bytes_l104970_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x49d7 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104970 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104970 (pushR64Effect 0x104970 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x104970 (PushPre 0x104970 1) (pushR64Effect 0x104970 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x104971 (pushR64Effect 0x104971 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x104971 (PushPre 0x104971 2) (pushR64Effect 0x104971 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x104973 (pushR64Effect 0x104973 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x104973 (PushPre 0x104973 2) (pushR64Effect 0x104973 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x104975 (pushR64Effect 0x104975 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x104975 (PushPre 0x104975 2) (pushR64Effect 0x104975 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x104977 (pushR64Effect 0x104977 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x104977 (PushPre 0x104977 2) (pushR64Effect 0x104977 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x104979 (pushR64Effect 0x104979 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x104979 (PushPre 0x104979 1) (pushR64Effect 0x104979 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10497a (subR64Imm32Effect 0x10497a 4 0x1b8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10497a (fun s => s.RIP = 0x10497a) (subR64Imm32Effect 0x10497a 4 0x1b8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x104981 (movR64R64Effect 0x104981 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x104981 (fun s => s.RIP = 0x104981) (movR64R64Effect 0x104981 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.exec 0x104984 (StorePre 0x104984 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x104984 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x104984 (.sib 4 none 0 (.d32 0x148)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.exec 0x104990 (StorePre 0x104990 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x104990 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x104990 (.sib 4 none 0 (.d32 0x140)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 71) (.exec 0x10499c (StorePre 0x10499c 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x10499c + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10499c (.sib 4 none 0 (.d32 0x138)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 72) (.exec 0x1049a8 (StorePre 0x1049a8 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x1049a8 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1049a8 (.sib 4 none 0 (.d32 0x130)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 73) (.out 0x1049b4 (movR64M64Effect 0x1049b4 0 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 74) (.exec 0x1049b4 (LoadPre 0x1049b4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1049b4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1049b4 0 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 75) (.out 0x1049b8 (movR64M64Effect 0x1049b8 1 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 76) (.exec 0x1049b8 (LoadPre 0x1049b8 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x1049b8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1049b8 1 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 77) (.out 0x1049bc (movR64M64Effect 0x1049bc 2 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 78) (.exec 0x1049bc (LoadPre 0x1049bc (fun s => AddrMode.addr (.base 7 .none) s (0x1049bc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1049bc 2 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 79) (.out 0x1049bf (movR64M64Effect 0x1049bf 6 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 80) (.exec 0x1049bf (LoadPre 0x1049bf (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1049bf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1049bf 6 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 81) (.exec 0x1049c3 (StorePre 0x1049c3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1049c3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1049c3 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[77, 65]
    (.letOp (n := 82) (.exec 0x1049c8 (StorePre 0x1049c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1049c8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1049c8 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[79, 65]
    (.letOp (n := 83) (.exec 0x1049cd (StorePre 0x1049cd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1049cd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1049cd 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[75, 65]
    (.letOp (n := 84) (.exec 0x1049d2 (StorePre 0x1049d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1049d2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1049d2 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 65]
    (b_l104970_1))))))))))))))))))))))))))))))))

def bytes_l104970 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xB8, 0x01, 0x00,
    0x00, 0x48, 0x89, 0xFB, 0x48, 0xC7, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0x38, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x47, 0x18, 0x48, 0x8B, 0x4F, 0x10, 0x48, 0x8B, 0x17, 0x48,
    0x8B, 0x77, 0x08, 0x48, 0x89, 0x54, 0x24, 0x08, 0x48, 0x89, 0x74, 0x24, 0x10, 0x48, 0x89, 0x4C,
    0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x20] ++ bytes_l104970_1

theorem code_l104970 : ∀ x ∈ codeRange 0x104970 bytes_l104970, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4970 103 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l104970_1

@[cfg_block] def b_l104a00 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104a00 (StorePre 0x104a00 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x5)) s (0x104a00 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104a00 5 (.sib 4 (some 0) 0 (.d8 0x5)) 0x36) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 54) (.exec 0x104a05 (StorePre 0x104a05 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x6)) s (0x104a05 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104a05 5 (.sib 4 (some 0) 0 (.d8 0x6)) 0x36) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.exec 0x104a0a (StorePre 0x104a0a 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x7)) s (0x104a0a + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104a0a 5 (.sib 4 (some 0) 0 (.d8 0x7)) 0x36) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 56) (.exec 0x104a0f (StorePre 0x104a0f 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x8)) s (0x104a0f + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104a0f 5 (.sib 4 (some 0) 0 (.d8 0x8)) 0x36) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 57) (.out 0x104a14 (addR64Imm8Effect 0x104a14 0 0x4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 58) (.exec 0x104a14 (fun s => s.RIP = 0x104a14) (addR64Imm8Effect 0x104a14 0 0x4) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x104a18 (cmpR64Imm8Effect 0x104a18 0 0x43) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[57]
    (.letOp (n := 60) (.exec 0x104a18 (fun s => s.RIP = 0x104a18) (cmpR64Imm8Effect 0x104a18 0 0x43) (Reg.operands [.gpr 0] [])) #v[57]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l104a00, RegMap.args [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l104a1e, RegMap.args [(0, 57), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l104a00 : List UInt8 :=
  [0x80, 0x74, 0x04, 0x05, 0x36, 0x80, 0x74, 0x04, 0x06, 0x36, 0x80, 0x74, 0x04, 0x07, 0x36, 0x80,
    0x74, 0x04, 0x08, 0x36, 0x48, 0x83, 0xC0, 0x04, 0x48, 0x83, 0xF8, 0x43, 0x75, 0xE2]

theorem code_l104a00 : ∀ x ∈ codeRange 0x104a00 bytes_l104a00, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4a00 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104a1e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104a1e (leaR64Effect 0x104a1e 14 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x104a1e (fun s => s.RIP = 0x104a1e) (leaR64Effect 0x104a1e 14 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104a26 (movR64Imm64Effect 0x104a26 0 0x5be0cd191f83d9ab) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x104a26 (fun s => s.RIP = 0x104a26) (movR64Imm64Effect 0x104a26 0 0x5be0cd191f83d9ab) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.exec 0x104a30 (StorePre 0x104a30 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x104a30 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104a30 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x104a38 (movR64Imm64Effect 0x104a38 0 0x9b05688c510e527f) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 59) (.exec 0x104a38 (fun s => s.RIP = 0x104a38) (movR64Imm64Effect 0x104a38 0 0x9b05688c510e527f) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.exec 0x104a42 (StorePre 0x104a42 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x104a42 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104a42 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x104a4a (movR64Imm64Effect 0x104a4a 0 0xa54ff53a3c6ef372) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 62) (.exec 0x104a4a (fun s => s.RIP = 0x104a4a) (movR64Imm64Effect 0x104a4a 0 0xa54ff53a3c6ef372) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.exec 0x104a54 (StorePre 0x104a54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x104a54 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104a54 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x104a5c (movR64Imm64Effect 0x104a5c 0 0xbb67ae856a09e667) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 65) (.exec 0x104a5c (fun s => s.RIP = 0x104a5c) (movR64Imm64Effect 0x104a5c 0 0xbb67ae856a09e667) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.exec 0x104a66 (StorePre 0x104a66 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x104a66 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104a66 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x104a6e (StorePre 0x104a6e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x104a6e + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x104a6e (.sib 4 none 0 (.d32 0xa7)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x104a76 (StorePre 0x104a76 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x104a76 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x104a76 (.sib 4 none 0 (.d32 0xc8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x104a82 (leaR64Effect 0x104a82 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x104a82 (fun s => s.RIP = 0x104a82) (leaR64Effect 0x104a82 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x104a87 (movR32Imm32Effect 0x104a87 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 72) (.exec 0x104a87 (fun s => s.RIP = 0x104a87) (movR32Imm32Effect 0x104a87 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x104a8c (movR64R64Effect 0x104a8c 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 74) (.exec 0x104a8c (fun s => s.RIP = 0x104a8c) (movR64R64Effect 0x104a8c 7 14) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 75) (.out 0x104a8f (callEffect (fun _ => 0x1218e0) 0x104a94) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 76) (.exec 0x104a8f (PushPre 0x104a8f 5) (callEffect (fun _ => 0x1218e0) 0x104a94) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.const ⟨64, 0x104a94⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 64), (1, 1), (2, 71), (3, 3), (4, 75), (5, 5), (6, 69), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l104a94, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l104a1e : List UInt8 :=
  [0x4C, 0x8D, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0xB8, 0xAB, 0xD9, 0x83, 0x1F, 0x19, 0xCD,
    0xE0, 0x5B, 0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0xB8, 0x7F, 0x52, 0x0E, 0x51,
    0x8C, 0x68, 0x05, 0x9B, 0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0xB8, 0x72, 0xF3,
    0x6E, 0x3C, 0x3A, 0xF5, 0x4F, 0xA5, 0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0xB8,
    0x67, 0xE6, 0x09, 0x6A, 0x85, 0xAE, 0x67, 0xBB, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0xC6, 0x84, 0x24, 0xA7, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x08, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xF7, 0xE8, 0x4C, 0xCE, 0x01, 0x00]

theorem code_l104a1e : ∀ x ∈ codeRange 0x104a1e bytes_l104a1e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4a1e 118 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104a94 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104a94 (StorePre 0x104a94 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x104a94 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x104a94 (.sib 4 none 0 (.d32 0xa7)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x104a9c (movR32Imm32Effect 0x104a9c 5 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 55) (.exec 0x104a9c (fun s => s.RIP = 0x104a9c) (movR32Imm32Effect 0x104a9c 5 0 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.exec 0x104aa1 (fun s => s.RIP = 0x104aa1) (fun _ => nopEffect 0x104aa1 15) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l104ab0, RegMap.args [(0, 54), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l104a94 : List UInt8 :=
  [0xC6, 0x84, 0x24, 0xA7, 0x00, 0x00, 0x00, 0x00, 0xB8, 0x03, 0x00, 0x00, 0x00, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l104a94 : ∀ x ∈ codeRange 0x104a94 bytes_l104a94, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4a94 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104ab0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104ab0 (StorePre 0x104ab0 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x5)) s (0x104ab0 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104ab0 5 (.sib 4 (some 0) 0 (.d8 0x5)) 0x6a) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 54) (.exec 0x104ab5 (StorePre 0x104ab5 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x6)) s (0x104ab5 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104ab5 5 (.sib 4 (some 0) 0 (.d8 0x6)) 0x6a) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.exec 0x104aba (StorePre 0x104aba 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x7)) s (0x104aba + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104aba 5 (.sib 4 (some 0) 0 (.d8 0x7)) 0x6a) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 56) (.exec 0x104abf (StorePre 0x104abf 5 (fun s => AddrMode.addr (.sib 4 (some 0) 0 (.d8 0x8)) s (0x104abf + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104abf 5 (.sib 4 (some 0) 0 (.d8 0x8)) 0x6a) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 57) (.out 0x104ac4 (addR64Imm8Effect 0x104ac4 0 0x4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 58) (.exec 0x104ac4 (fun s => s.RIP = 0x104ac4) (addR64Imm8Effect 0x104ac4 0 0x4) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x104ac8 (cmpR64Imm8Effect 0x104ac8 0 0x43) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[57]
    (.letOp (n := 60) (.exec 0x104ac8 (fun s => s.RIP = 0x104ac8) (cmpR64Imm8Effect 0x104ac8 0 0x43) (Reg.operands [.gpr 0] [])) #v[57]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l104ab0, RegMap.args [(0, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l104ace, RegMap.args [(0, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l104ab0 : List UInt8 :=
  [0x80, 0x74, 0x04, 0x05, 0x6A, 0x80, 0x74, 0x04, 0x06, 0x6A, 0x80, 0x74, 0x04, 0x07, 0x6A, 0x80,
    0x74, 0x04, 0x08, 0x6A, 0x48, 0x83, 0xC0, 0x04, 0x48, 0x83, 0xF8, 0x43, 0x75, 0xE2]

theorem code_l104ab0 : ∀ x ∈ codeRange 0x104ab0 bytes_l104ab0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4ab0 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104ace_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x104b4b (leaR64Effect 0x104b4b 7 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 85) (.exec 0x104b4b (fun s => s.RIP = 0x104b4b) (leaR64Effect 0x104b4b 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.out 0x104b50 (leaR64Effect 0x104b50 6 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 87) (.exec 0x104b50 (fun s => s.RIP = 0x104b50) (leaR64Effect 0x104b50 6 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.out 0x104b58 (movR32Imm32Effect 0x104b58 5 2 0xa8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 89) (.exec 0x104b58 (fun s => s.RIP = 0x104b58) (movR32Imm32Effect 0x104b58 5 2 0xa8) (Reg.operands [] [])) #v[]
    (.letOp (n := 90) (.out 0x104b5d (callEffect (callMemPtr 0x104b5d (.rip 0xff26d)) (0x104b5d + BitVec.ofNat 64 (callMemLen (.rip 0xff26d)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 91) (.exec 0x104b5d (GoesTo (CallMemPre 0x104b5d (.rip 0xff26d)) (callEffect (callMemPtr 0x104b5d (.rip 0xff26d)) (0x104b5d + BitVec.ofNat 64 (callMemLen (.rip 0xff26d)))) 0x12a820) (callEffect (callMemPtr 0x104b5d (.rip 0xff26d)) (0x104b5d + BitVec.ofNat 64 (callMemLen (.rip 0xff26d)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.const ⟨64, 0x104b63⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 78), (1, 80), (2, 88), (3, 3), (4, 90), (5, 5), (6, 86), (7, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩ { target := .l104b63, kept := #v[], arity := rfl, guard := some (Fin.last 92) }))))))))))

def bytes_l104ace_1 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x68, 0x48, 0x8D, 0xB4, 0x24, 0x10, 0x01, 0x00, 0x00, 0xBA, 0xA8, 0x00,
    0x00, 0x00, 0xFF, 0x15, 0x6D, 0xF2, 0x0F, 0x00]

theorem code_l104ace_1 : ∀ x ∈ codeRange 0x104b4b bytes_l104ace_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4b4b 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104ace : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104ace (leaR64Effect 0x104ace 7 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x104ace (fun s => s.RIP = 0x104ace) (leaR64Effect 0x104ace 7 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104ad6 (leaR64Effect 0x104ad6 6 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x104ad6 (fun s => s.RIP = 0x104ad6) (leaR64Effect 0x104ad6 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x104adb (movR32Imm32Effect 0x104adb 5 1 0xd) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x104adb (fun s => s.RIP = 0x104adb) (movR32Imm32Effect 0x104adb 5 1 0xd) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x104ae0 (RepPre 0x104ae0 (RepMovsqPre 0x104ae0)) (repMovsqEffect 0x104ae0) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[55, 53, 57, 22]
    (.letOp (n := 60) (.out 0x104ae3 (movR64M64Effect 0x104ae3 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 61) (.exec 0x104ae3 (LoadPre 0x104ae3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x104ae3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104ae3 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x104ae8 (StorePre 0x104ae8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x104ae8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104ae8 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x104af0 (movR64M64Effect 0x104af0 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x104af0 (LoadPre 0x104af0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x104af0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104af0 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x104af5 (StorePre 0x104af5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x104af5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104af5 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x104afd (movR64M64Effect 0x104afd 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 67) (.exec 0x104afd (LoadPre 0x104afd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x104afd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104afd 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x104b02 (StorePre 0x104b02 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x104b02 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104b02 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x104b0a (movR64M64Effect 0x104b0a 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 70) (.exec 0x104b0a (LoadPre 0x104b0a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x104b0a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104b0a 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x104b0f (StorePre 0x104b0f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x104b0f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104b0f 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.out 0x104b17 (movR64M64Effect 0x104b17 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 73) (.exec 0x104b17 (LoadPre 0x104b17 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104b17 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104b17 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x104b1c (StorePre 0x104b1c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x104b1c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104b1c 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x104b24 (movR64M64Effect 0x104b24 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 76) (.exec 0x104b24 (LoadPre 0x104b24 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104b24 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104b24 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x104b29 (StorePre 0x104b29 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x104b29 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104b29 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x104b31 (movR64M64Effect 0x104b31 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 79) (.exec 0x104b31 (LoadPre 0x104b31 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104b31 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104b31 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x104b36 (movR64M64Effect 0x104b36 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 81) (.exec 0x104b36 (LoadPre 0x104b36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104b36 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104b36 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x104b3b (StorePre 0x104b3b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x104b3b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104b3b 1 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.exec 0x104b43 (StorePre 0x104b43 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x104b43 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104b43 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 4]
    (b_l104ace_1)))))))))))))))))))))))))))))))

def bytes_l104ace : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x68, 0xB9, 0x0D, 0x00,
    0x00, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x48, 0x01,
    0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x48,
    0x8B, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24,
    0x28, 0x48, 0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89,
    0x84, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x20,
    0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x8C,
    0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] ++ bytes_l104ace_1

theorem code_l104ace : ∀ x ∈ codeRange 0x104ace bytes_l104ace, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4ace 125 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l104ace_1

@[cfg_block] def b_l104b63 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104b63 (addR64Imm8Effect 0x104b63 3 0x20) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 54) (.exec 0x104b63 (fun s => s.RIP = 0x104b63) (addR64Imm8Effect 0x104b63 3 0x20) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x104b67 (movzxR32M8Effect 0x104b67 9 15 (.sib 4 none 0 (.d32 0xe7))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x104b67 (LoadPre 0x104b67 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe7)) s (0x104b67 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x104b67 9 15 (.sib 4 none 0 (.d32 0xe7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x104b70 (cmpR64Imm8Effect 0x104b70 15 0x1f) (EffectPart.reads (.flag .CF) [.gpr 15] []) (.flag .CF)) #v[55]
    (.letOp (n := 58) (.out 0x104b70 (cmpR64Imm8Effect 0x104b70 15 0x1f) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[55]
    (.letOp (n := 59) (.exec 0x104b70 (fun s => s.RIP = 0x104b70) (cmpR64Imm8Effect 0x104b70 15 0x1f) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l104ba6, RegMap.args [(3, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l104b76, RegMap.args [(3, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l104b63 : List UInt8 :=
  [0x48, 0x83, 0xC3, 0x20, 0x44, 0x0F, 0xB6, 0xBC, 0x24, 0xE7, 0x00, 0x00, 0x00, 0x49, 0x83, 0xFF,
    0x1F, 0x77, 0x30]

theorem code_l104b63 : ∀ x ∈ codeRange 0x104b63 bytes_l104b63, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4b63 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104b76 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104b76 (movR64M64Effect 0x104b76 0 (.base 3 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x104b76 (LoadPre 0x104b76 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x104b76 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104b76 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.exec 0x104b7a (StorePre 0x104b7a 5 (fun s => AddrMode.addr (.sib 14 (some 15) 0 (.d8 0x18)) s (0x104b7a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104b7a 0 (.sib 14 (some 15) 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 14, .gpr 15] [])) #v[53, 14, 15]
    (.letOp (n := 56) (.out 0x104b7f (movR64M64Effect 0x104b7f 0 (.base 3 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 57) (.exec 0x104b7f (LoadPre 0x104b7f (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x104b7f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104b7f 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 58) (.exec 0x104b83 (StorePre 0x104b83 5 (fun s => AddrMode.addr (.sib 14 (some 15) 0 (.d8 0x10)) s (0x104b83 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104b83 0 (.sib 14 (some 15) 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 14, .gpr 15] [])) #v[56, 14, 15]
    (.letOp (n := 59) (.out 0x104b88 (movR64M64Effect 0x104b88 0 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 60) (.exec 0x104b88 (LoadPre 0x104b88 (fun s => AddrMode.addr (.base 3 .none) s (0x104b88 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x104b88 0 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 61) (.out 0x104b8b (movR64M64Effect 0x104b8b 1 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 62) (.exec 0x104b8b (LoadPre 0x104b8b (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x104b8b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104b8b 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 63) (.exec 0x104b8f (StorePre 0x104b8f 5 (fun s => AddrMode.addr (.sib 14 (some 15) 0 (.d8 0x8)) s (0x104b8f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104b8f 1 (.sib 14 (some 15) 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14, .gpr 15] [])) #v[61, 14, 15]
    (.letOp (n := 64) (.exec 0x104b94 (StorePre 0x104b94 4 (fun s => AddrMode.addr (.sib 14 (some 15) 0 .none) s (0x104b94 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104b94 0 (.sib 14 (some 15) 0 .none)) (Reg.operands [.gpr 0, .gpr 14, .gpr 15] [])) #v[59, 14, 15]
    (.letOp (n := 65) (.out 0x104b98 (orR8Imm8Effect 0x104b98 4 15 0x20) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 66) (.exec 0x104b98 (fun s => s.RIP = 0x104b98) (orR8Imm8Effect 0x104b98 4 15 0x20) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 67) (.exec 0x104b9c (StorePre 0x104b9c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe7)) s (0x104b9c + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x104b9c 8 15 (.sib 4 none 0 (.d32 0xe7))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[65, 4]
    (.terminate (.br ⟨.l104c06, RegMap.args [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l104b76 : List UInt8 :=
  [0x48, 0x8B, 0x43, 0x18, 0x4B, 0x89, 0x44, 0x3E, 0x18, 0x48, 0x8B, 0x43, 0x10, 0x4B, 0x89, 0x44,
    0x3E, 0x10, 0x48, 0x8B, 0x03, 0x48, 0x8B, 0x4B, 0x08, 0x4B, 0x89, 0x4C, 0x3E, 0x08, 0x4B, 0x89,
    0x04, 0x3E, 0x41, 0x80, 0xCF, 0x20, 0x44, 0x88, 0xBC, 0x24, 0xE7, 0x00, 0x00, 0x00, 0xEB, 0x60]

theorem code_l104b76 : ∀ x ∈ codeRange 0x104b76 bytes_l104b76, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4b76 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104ba6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104ba6 (movR32Imm32Effect 0x104ba6 5 2 0x40) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x104ba6 (fun s => s.RIP = 0x104ba6) (movR32Imm32Effect 0x104ba6 5 2 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x104bab (subR64R64Effect 0x104bab 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x104bab (fun s => s.RIP = 0x104bab) (subR64R64Effect 0x104bab 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x104bae (leaR64Effect 0x104bae 12 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 58) (.exec 0x104bae (fun s => s.RIP = 0x104bae) (leaR64Effect 0x104bae 12 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x104bb6 (leaR64Effect 0x104bb6 13 (.sib 3 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3, .gpr 2] []) (.reg (.gpr 13))) #v[3, 55]
    (.letOp (n := 60) (.exec 0x104bb6 (fun s => s.RIP = 0x104bb6) (leaR64Effect 0x104bb6 13 (.sib 3 (some 2) 0 .none)) (Reg.operands [.gpr 3, .gpr 2] [])) #v[3, 55]
    (.letOp (n := 61) (.out 0x104bba (leaR64Effect 0x104bba 7 (.sib 14 (some 15) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14, .gpr 15] []) (.reg (.gpr 7))) #v[14, 15]
    (.letOp (n := 62) (.exec 0x104bba (fun s => s.RIP = 0x104bba) (leaR64Effect 0x104bba 7 (.sib 14 (some 15) 0 .none)) (Reg.operands [.gpr 14, .gpr 15] [])) #v[14, 15]
    (.letOp (n := 63) (.out 0x104bbe (addR64Imm8Effect 0x104bbe 15 0xe0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 64) (.exec 0x104bbe (fun s => s.RIP = 0x104bbe) (addR64Imm8Effect 0x104bbe 15 0xe0) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 65) (.out 0x104bc2 (leaR64Effect 0x104bc2 5 (.rip 0x25c57)) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 66) (.exec 0x104bc2 (fun s => s.RIP = 0x104bc2) (leaR64Effect 0x104bc2 5 (.rip 0x25c57)) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x104bc9 (movR64R64Effect 0x104bc9 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 68) (.exec 0x104bc9 (fun s => s.RIP = 0x104bc9) (movR64R64Effect 0x104bc9 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 69) (.out 0x104bcc (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x104bce) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 65]
    (.letOp (n := 70) (.exec 0x104bcc (GoesTo (CallPre 0x104bcc 2 (fun s => (Operand.reg 5 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x104bce) 0x12a820) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x104bce) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 65]
    (.letOp (n := 71) (.const ⟨64, 0x104bce⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 69), (5, 65), (6, 67), (7, 61), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l104bce, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l104ba6 : List UInt8 :=
  [0xBA, 0x40, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xFA, 0x4C, 0x8D, 0xA4, 0x24, 0xE8, 0x00, 0x00, 0x00,
    0x4C, 0x8D, 0x2C, 0x13, 0x4B, 0x8D, 0x3C, 0x3E, 0x49, 0x83, 0xC7, 0xE0, 0x48, 0x8D, 0x2D, 0x57,
    0x5C, 0x02, 0x00, 0x48, 0x89, 0xDE, 0xFF, 0xD5]

theorem code_l104ba6 : ∀ x ∈ codeRange 0x104ba6 bytes_l104ba6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4ba6 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104bce : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104bce (StorePre 0x104bce 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x104bce + BitVec.ofNat 64 8)) 8) (incMEffect 0x104bce 8 64 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x104bd6 (movR32Imm32Effect 0x104bd6 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 55) (.exec 0x104bd6 (fun s => s.RIP = 0x104bd6) (movR32Imm32Effect 0x104bd6 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.out 0x104bdb (movR64R64Effect 0x104bdb 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 57) (.exec 0x104bdb (fun s => s.RIP = 0x104bdb) (movR64R64Effect 0x104bdb 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 58) (.out 0x104bde (movR64R64Effect 0x104bde 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 59) (.exec 0x104bde (fun s => s.RIP = 0x104bde) (movR64R64Effect 0x104bde 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 60) (.out 0x104be1 (callEffect (fun _ => 0x1218e0) 0x104be6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x104be1 (PushPre 0x104be1 5) (callEffect (fun _ => 0x1218e0) 0x104be6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x104be6⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ { target := .l104be6, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l104bce : List UInt8 :=
  [0x48, 0xFF, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE7,
    0x4C, 0x89, 0xF6, 0xE8, 0xFA, 0xCC, 0x01, 0x00]

theorem code_l104bce : ∀ x ∈ codeRange 0x104bce bytes_l104bce, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4bce 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104be6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104be6 (movR64Imm64Effect 0x104be6 6 0x7fffffffffffffc0) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x104be6 (fun s => s.RIP = 0x104be6) (movR64Imm64Effect 0x104be6 6 0x7fffffffffffffc0) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x104bf0 (andR64R64Effect 0x104bf0 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x104bf0 (fun s => s.RIP = 0x104bf0) (andR64R64Effect 0x104bf0 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x104bf3 (addR64R64Effect 0x104bf3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x104bf3 (fun s => s.RIP = 0x104bf3) (addR64R64Effect 0x104bf3 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.exec 0x104bf6 (StorePre 0x104bf6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe7)) s (0x104bf6 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x104bf6 8 15 (.sib 4 none 0 (.d32 0xe7))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 60) (.out 0x104bfe (movR64R64Effect 0x104bfe 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 61) (.exec 0x104bfe (fun s => s.RIP = 0x104bfe) (movR64R64Effect 0x104bfe 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x104c01 (movR64R64Effect 0x104c01 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 63) (.exec 0x104c01 (fun s => s.RIP = 0x104c01) (movR64R64Effect 0x104c01 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x104c04 (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x104c06) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 65) (.exec 0x104c04 (GoesTo (CallPre 0x104c04 2 (fun s => (Operand.reg 5 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x104c06) 0x12a820) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x104c06) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 66) (.const ⟨64, 0x104c06⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 62), (3, 3), (4, 64), (5, 5), (6, 57), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l104c06, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l104be6 : List UInt8 :=
  [0x48, 0xBE, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x4C, 0x21, 0xFE, 0x4C, 0x01, 0xEE,
    0x44, 0x88, 0xBC, 0x24, 0xE7, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFA, 0xFF, 0xD5]

theorem code_l104be6 : ∀ x ∈ codeRange 0x104be6 bytes_l104be6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4be6 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104c06 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104c06 (leaR64Effect 0x104c06 14 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x104c06 (fun s => s.RIP = 0x104c06) (leaR64Effect 0x104c06 14 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104c0e (leaR64Effect 0x104c0e 6 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x104c0e (fun s => s.RIP = 0x104c0e) (leaR64Effect 0x104c0e 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x104c13 (movR32Imm32Effect 0x104c13 5 2 0xa8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x104c13 (fun s => s.RIP = 0x104c13) (movR32Imm32Effect 0x104c13 5 2 0xa8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x104c18 (movR64R64Effect 0x104c18 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 60) (.exec 0x104c18 (fun s => s.RIP = 0x104c18) (movR64R64Effect 0x104c18 7 14) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 61) (.out 0x104c1b (callEffect (callMemPtr 0x104c1b (.rip 0xff1af)) (0x104c1b + BitVec.ofNat 64 (callMemLen (.rip 0xff1af)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x104c1b (GoesTo (CallMemPre 0x104c1b (.rip 0xff1af)) (callEffect (callMemPtr 0x104c1b (.rip 0xff1af)) (0x104c1b + BitVec.ofNat 64 (callMemLen (.rip 0xff1af)))) 0x12a820) (callEffect (callMemPtr 0x104c1b (.rip 0xff1af)) (0x104c1b + BitVec.ofNat 64 (callMemLen (.rip 0xff1af)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x104c21⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 3), (4, 61), (5, 5), (6, 55), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l104c21, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l104c06 : List UInt8 :=
  [0x4C, 0x8D, 0xB4, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x68, 0xBA, 0xA8, 0x00,
    0x00, 0x00, 0x4C, 0x89, 0xF7, 0xFF, 0x15, 0xAF, 0xF1, 0x0F, 0x00]

theorem code_l104c06 : ∀ x ∈ codeRange 0x104c06 bytes_l104c06, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4c06 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104c21 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104c21 (StorePre 0x104c21 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x104c21 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104c21 (.sib 4 none 0 (.d8 0x48)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x104c2a (StorePre 0x104c2a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x104c2a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104c2a (.sib 4 none 0 (.d8 0x50)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x104c33 (StorePre 0x104c33 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x104c33 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104c33 (.sib 4 none 0 (.d8 0x58)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x104c3c (StorePre 0x104c3c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x104c3c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104c3c (.sib 4 none 0 (.d8 0x60)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x104c45 (leaR64Effect 0x104c45 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x104c45 (fun s => s.RIP = 0x104c45) (leaR64Effect 0x104c45 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x104c4a (movR64R64Effect 0x104c4a 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 60) (.exec 0x104c4a (fun s => s.RIP = 0x104c4a) (movR64R64Effect 0x104c4a 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x104c4d (callEffect (fun _ => 0x107a50) 0x104c52) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x104c4d (PushPre 0x104c4d 5) (callEffect (fun _ => 0x107a50) 0x104c52) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x104c52⟩) #v[]
    (.terminate (.call ⟨.l107a50, RegMap.args [(1, 1), (3, 3), (4, 61), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l104c52, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l104c21 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x48, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x50, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x58, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x60,
    0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x48, 0x4C, 0x89, 0xF7, 0xE8, 0xFE, 0x2D, 0x00,
    0x00]

theorem code_l104c21 : ∀ x ∈ codeRange 0x104c21 bytes_l104c21, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4c21 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104c52 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104c52 (movR64M64Effect 0x104c52 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x104c52 (LoadPre 0x104c52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x104c52 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104c52 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x104c57 (StorePre 0x104c57 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x104c57 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104c57 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x104c5b (movR64M64Effect 0x104c5b 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x104c5b (LoadPre 0x104c5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x104c5b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104c5b 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x104c60 (StorePre 0x104c60 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x104c60 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104c60 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x104c64 (movR64M64Effect 0x104c64 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x104c64 (LoadPre 0x104c64 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x104c64 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104c64 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x104c69 (movR64M64Effect 0x104c69 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x104c69 (LoadPre 0x104c69 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x104c69 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104c69 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x104c6e (StorePre 0x104c6e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x104c6e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104c6e 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 64) (.exec 0x104c72 (StorePre 0x104c72 3 (fun s => AddrMode.addr (.base 3 .none) s (0x104c72 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x104c72 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 65) (.out 0x104c75 (addR64Imm32Effect 0x104c75 4 0x1b8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x104c75 (fun s => s.RIP = 0x104c75) (addR64Imm32Effect 0x104c75 4 0x1b8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x104c7c (popR64Effect 0x104c7c 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 68) (.out 0x104c7c (popR64Effect 0x104c7c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x104c7c (PopPre 0x104c7c) (popR64Effect 0x104c7c 1 3) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x104c7d (popR64Effect 0x104c7d 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[68]
    (.letOp (n := 71) (.out 0x104c7d (popR64Effect 0x104c7d 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x104c7d (PopPre 0x104c7d) (popR64Effect 0x104c7d 2 12) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x104c7f (popR64Effect 0x104c7f 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 74) (.out 0x104c7f (popR64Effect 0x104c7f 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x104c7f (PopPre 0x104c7f) (popR64Effect 0x104c7f 2 13) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x104c81 (popR64Effect 0x104c81 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[74]
    (.letOp (n := 77) (.out 0x104c81 (popR64Effect 0x104c81 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x104c81 (PopPre 0x104c81) (popR64Effect 0x104c81 2 14) (Reg.operands [.gpr 4] [])) #v[74]
    (.letOp (n := 79) (.out 0x104c83 (popR64Effect 0x104c83 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[77]
    (.letOp (n := 80) (.out 0x104c83 (popR64Effect 0x104c83 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[77]
    (.letOp (n := 81) (.exec 0x104c83 (PopPre 0x104c83) (popR64Effect 0x104c83 2 15) (Reg.operands [.gpr 4] [])) #v[77]
    (.letOp (n := 82) (.out 0x104c85 (popR64Effect 0x104c85 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[80]
    (.letOp (n := 83) (.out 0x104c85 (popR64Effect 0x104c85 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[80]
    (.letOp (n := 84) (.exec 0x104c85 (PopPre 0x104c85) (popR64Effect 0x104c85 1 5) (Reg.operands [.gpr 4] [])) #v[80]
    (.letOp (n := 85) (.out 0x104c86 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[83]
    (.letOp (n := 86) (.out 0x104c86 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x104c86 (RetPre 0x104c86) (retEffect) (Reg.operands [.gpr 4] [])) #v[83]
    (.terminate (.ret (RegMap.args [(0, 59), (1, 61), (2, 2), (3, 67), (4, 86), (5, 82), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (15, 79), (22, 22), (39, 39), (50, 50), (51, 51)] 88) (some ⟨85, by decide⟩)))))))))))))))))))))))))))))))))))))

def bytes_l104c52 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x60, 0x48, 0x89, 0x43, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x89,
    0x43, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x4C, 0x24, 0x50, 0x48, 0x89, 0x4B, 0x08,
    0x48, 0x89, 0x03, 0x48, 0x81, 0xC4, 0xB8, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l104c52 : ∀ x ∈ codeRange 0x104c52 bytes_l104c52, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4c52 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104c90_1 : Block Op Label signature Reg.count 85 :=
  .letOp (n := 85) (.out 0x104cee (leaR64Effect 0x104cee 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 86) (.exec 0x104cee (fun s => s.RIP = 0x104cee) (leaR64Effect 0x104cee 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 87) (.out 0x104cf3 (callEffect (fun _ => 0x10a280) 0x104cf8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 88) (.exec 0x104cf3 (PushPre 0x104cf3 5) (callEffect (fun _ => 0x10a280) 0x104cf8) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 89) (.const ⟨64, 0x104cf8⟩) #v[]
    (.terminate (.call ⟨.l10a280, RegMap.args [(0, 73), (1, 75), (3, 65), (4, 87), (5, 5), (6, 85), (7, 83), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ { target := .l104cf8, kept := #v[], arity := rfl, guard := some (Fin.last 89) }))))))

def bytes_l104c90_1 : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x08, 0xE8, 0x88, 0x55, 0x00, 0x00]

theorem code_l104c90_1 : ∀ x ∈ codeRange 0x104cee bytes_l104c90_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4cee 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104c90 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104c90 (pushR64Effect 0x104c90 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x104c90 (PushPre 0x104c90 2) (pushR64Effect 0x104c90 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x104c92 (pushR64Effect 0x104c92 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x104c92 (PushPre 0x104c92 2) (pushR64Effect 0x104c92 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x104c94 (pushR64Effect 0x104c94 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[55, 12]
    (.letOp (n := 58) (.exec 0x104c94 (PushPre 0x104c94 2) (pushR64Effect 0x104c94 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[55, 12]
    (.letOp (n := 59) (.out 0x104c96 (pushR64Effect 0x104c96 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[57, 3]
    (.letOp (n := 60) (.exec 0x104c96 (PushPre 0x104c96 1) (pushR64Effect 0x104c96 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 61) (.out 0x104c97 (subR64Imm8Effect 0x104c97 4 0x68) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x104c97 (fun s => s.RIP = 0x104c97) (subR64Imm8Effect 0x104c97 4 0x68) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x104c9b (movR64R64Effect 0x104c9b 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 64) (.exec 0x104c9b (fun s => s.RIP = 0x104c9b) (movR64R64Effect 0x104c9b 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x104c9e (movR64R64Effect 0x104c9e 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 66) (.exec 0x104c9e (fun s => s.RIP = 0x104c9e) (movR64R64Effect 0x104c9e 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x104ca1 (movR64M64Effect 0x104ca1 0 (.base 6 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 68) (.exec 0x104ca1 (LoadPre 0x104ca1 (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x104ca1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104ca1 0 (.base 6 (.d8 0x38))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.exec 0x104ca5 (StorePre 0x104ca5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x104ca5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104ca5 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[67, 61]
    (.letOp (n := 70) (.out 0x104caa (movR64M64Effect 0x104caa 0 (.base 6 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 71) (.exec 0x104caa (LoadPre 0x104caa (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x104caa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104caa 0 (.base 6 (.d8 0x30))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 72) (.exec 0x104cae (StorePre 0x104cae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x104cae + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104cae 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 61]
    (.letOp (n := 73) (.out 0x104cb3 (movR64M64Effect 0x104cb3 0 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 74) (.exec 0x104cb3 (LoadPre 0x104cb3 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x104cb3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104cb3 0 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 75) (.out 0x104cb7 (movR64M64Effect 0x104cb7 1 (.base 6 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 76) (.exec 0x104cb7 (LoadPre 0x104cb7 (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x104cb7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104cb7 1 (.base 6 (.d8 0x28))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.exec 0x104cbb (StorePre 0x104cbb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x104cbb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104cbb 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[75, 61]
    (.letOp (n := 78) (.exec 0x104cc0 (StorePre 0x104cc0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x104cc0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104cc0 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 61]
    (.letOp (n := 79) (.exec 0x104cc5 (StorePre 0x104cc5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104cc5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104cc5 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 80) (.exec 0x104cce (StorePre 0x104cce 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104cce + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104cce (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 81) (.exec 0x104cd7 (StorePre 0x104cd7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104cd7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104cd7 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 82) (.exec 0x104ce0 (StorePre 0x104ce0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104ce0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104ce0 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 83) (.out 0x104ce9 (leaR64Effect 0x104ce9 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 84) (.exec 0x104ce9 (fun s => s.RIP = 0x104ce9) (leaR64Effect 0x104ce9 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[61]
    (b_l104c90_1))))))))))))))))))))))))))))))))

def bytes_l104c90 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x68, 0x49, 0x89, 0xF6, 0x48, 0x89,
    0xFB, 0x48, 0x8B, 0x46, 0x38, 0x48, 0x89, 0x44, 0x24, 0x40, 0x48, 0x8B, 0x46, 0x30, 0x48, 0x89,
    0x44, 0x24, 0x38, 0x48, 0x8B, 0x46, 0x20, 0x48, 0x8B, 0x4E, 0x28, 0x48, 0x89, 0x4C, 0x24, 0x30,
    0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x28] ++ bytes_l104c90_1

theorem code_l104c90 : ∀ x ∈ codeRange 0x104c90 bytes_l104c90, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4c90 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l104c90_1

@[cfg_block] def b_l104cf8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104cf8 (notR8Effect 0x104cf8 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x104cf8 (fun s => s.RIP = 0x104cf8) (notR8Effect 0x104cf8 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x104cfa (andAlImm8Effect 0x104cfa 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x104cfa (fun s => s.RIP = 0x104cfa) (andAlImm8Effect 0x104cfa 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x104cfc (movzxR32R8Effect 0x104cfc 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x104cfc (fun s => s.RIP = 0x104cfc) (movzxR32R8Effect 0x104cfc 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x104cff (callEffect (fun _ => 0x127d50) 0x104d04) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x104cff (PushPre 0x104cff 5) (callEffect (fun _ => 0x127d50) 0x104d04) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x104d04⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l104d04, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l104cf8 : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x4C, 0x30, 0x02, 0x00]

theorem code_l104cf8 : ∀ x ∈ codeRange 0x104cf8 bytes_l104cf8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4cf8 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104d04 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104d04 (StorePre 0x104d04 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104d04 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x104d04 4 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x104d08 (cmpAlImm8Effect 0x104d08 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 55) (.exec 0x104d08 (fun s => s.RIP = 0x104d08) (cmpAlImm8Effect 0x104d08 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 56) (.pure (condOp 5)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l104de5, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (13, 13), (14, 14), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l104d10, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (13, 13), (14, 14), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l104d04 : List UInt8 :=
  [0x88, 0x44, 0x24, 0x08, 0x3C, 0x01, 0x0F, 0x85, 0xD5, 0x00, 0x00, 0x00]

theorem code_l104d04 : ∀ x ∈ codeRange 0x104d04 bytes_l104d04, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4d04 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104d10 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104d10 (leaR64Effect 0x104d10 15 (.base 14 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 54) (.exec 0x104d10 (fun s => s.RIP = 0x104d10) (leaR64Effect 0x104d10 15 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x104d14 (movR64M64Effect 0x104d14 0 (.base 15 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x104d14 (LoadPre 0x104d14 (fun s => AddrMode.addr (.base 15 (.d8 0x18)) s (0x104d14 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d14 0 (.base 15 (.d8 0x18))) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 57) (.exec 0x104d18 (StorePre 0x104d18 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104d18 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104d18 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x104d1d (movR64M64Effect 0x104d1d 0 (.base 15 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 59) (.exec 0x104d1d (LoadPre 0x104d1d (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x104d1d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d1d 0 (.base 15 (.d8 0x10))) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 60) (.exec 0x104d21 (StorePre 0x104d21 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104d21 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104d21 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x104d26 (movR64M64Effect 0x104d26 0 (.base 15 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 62) (.exec 0x104d26 (LoadPre 0x104d26 (fun s => AddrMode.addr (.base 15 .none) s (0x104d26 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x104d26 0 (.base 15 .none)) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 63) (.out 0x104d29 (movR64M64Effect 0x104d29 1 (.base 15 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 64) (.exec 0x104d29 (LoadPre 0x104d29 (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x104d29 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d29 1 (.base 15 (.d8 0x8))) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 65) (.exec 0x104d2d (StorePre 0x104d2d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104d2d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104d2d 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.exec 0x104d32 (StorePre 0x104d32 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104d32 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x104d32 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 67) (.out 0x104d37 (leaR64Effect 0x104d37 12 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 68) (.exec 0x104d37 (fun s => s.RIP = 0x104d37) (leaR64Effect 0x104d37 12 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x104d3c (leaR64Effect 0x104d3c 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x104d3c (fun s => s.RIP = 0x104d3c) (leaR64Effect 0x104d3c 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x104d41 (movR64R64Effect 0x104d41 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[67]
    (.letOp (n := 72) (.exec 0x104d41 (fun s => s.RIP = 0x104d41) (movR64R64Effect 0x104d41 7 12) (Reg.operands [.gpr 12] [])) #v[67]
    (.letOp (n := 73) (.out 0x104d44 (callEffect (fun _ => 0x10a2d0) 0x104d49) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 74) (.exec 0x104d44 (PushPre 0x104d44 5) (callEffect (fun _ => 0x10a2d0) 0x104d49) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.const ⟨64, 0x104d49⟩) #v[]
    (.terminate (.call ⟨.l10a2d0, RegMap.args [(0, 61), (1, 63), (3, 3), (4, 73), (5, 5), (6, 69), (7, 71), (12, 67), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ { target := .l104d49, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l104d10 : List UInt8 :=
  [0x4D, 0x8D, 0x7E, 0x20, 0x49, 0x8B, 0x47, 0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x49, 0x8B, 0x47,
    0x10, 0x48, 0x89, 0x44, 0x24, 0x18, 0x49, 0x8B, 0x07, 0x49, 0x8B, 0x4F, 0x08, 0x48, 0x89, 0x4C,
    0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x8D, 0x64, 0x24, 0x48, 0x48, 0x8D, 0x74, 0x24,
    0x08, 0x4C, 0x89, 0xE7, 0xE8, 0x87, 0x55, 0x00, 0x00]

theorem code_l104d10 : ∀ x ∈ codeRange 0x104d10 bytes_l104d10, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4d10 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104d49 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104d49 (leaR64Effect 0x104d49 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x104d49 (fun s => s.RIP = 0x104d49) (leaR64Effect 0x104d49 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104d4e (movR64R64Effect 0x104d4e 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 56) (.exec 0x104d4e (fun s => s.RIP = 0x104d4e) (movR64R64Effect 0x104d4e 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x104d51 (callEffect (fun _ => 0x11c3f0) 0x104d56) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x104d51 (PushPre 0x104d51 5) (callEffect (fun _ => 0x11c3f0) 0x104d56) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x104d56⟩) #v[]
    (.terminate (.call ⟨.l11c3f0, RegMap.args [(2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l104d56, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l104d49 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xE6, 0xE8, 0x9A, 0x76, 0x01, 0x00]

theorem code_l104d49 : ∀ x ∈ codeRange 0x104d49 bytes_l104d49, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4d49 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104d56 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104d56 (movR64R64Effect 0x104d56 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 54) (.exec 0x104d56 (fun s => s.RIP = 0x104d56) (movR64R64Effect 0x104d56 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x104d59 (callEffect (fun _ => 0x108380) 0x104d5e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x104d59 (PushPre 0x104d59 5) (callEffect (fun _ => 0x108380) 0x104d5e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x104d5e⟩) #v[]
    (.terminate (.call ⟨.l108380, RegMap.args [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l104d5e, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l104d56 : List UInt8 :=
  [0x4C, 0x89, 0xFF, 0xE8, 0x22, 0x36, 0x00, 0x00]

theorem code_l104d56 : ∀ x ∈ codeRange 0x104d56 bytes_l104d56, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4d56 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104d5e_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.exec 0x104dac (StorePre 0x104dac 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x104dac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104dac 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[89, 3]
    (.letOp (n := 92) (.out 0x104db0 (movR64M64Effect 0x104db0 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 93) (.exec 0x104db0 (LoadPre 0x104db0 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x104db0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104db0 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 94) (.exec 0x104db4 (StorePre 0x104db4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x104db4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104db4 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[92, 3]
    (.letOp (n := 95) (.out 0x104db8 (movR64M64Effect 0x104db8 0 (.base 14 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 96) (.exec 0x104db8 (LoadPre 0x104db8 (fun s => AddrMode.addr (.base 14 .none) s (0x104db8 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x104db8 0 (.base 14 .none)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 97) (.out 0x104dbb (movR64M64Effect 0x104dbb 8 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[14]
    (.letOp (n := 98) (.exec 0x104dbb (LoadPre 0x104dbb (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x104dbb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104dbb 8 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 99) (.exec 0x104dbf (StorePre 0x104dbf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x104dbf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104dbf 8 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[97, 3]
    (.letOp (n := 100) (.exec 0x104dc3 (StorePre 0x104dc3 3 (fun s => AddrMode.addr (.base 3 .none) s (0x104dc3 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x104dc3 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[95, 3]
    (.letOp (n := 101) (.exec 0x104dc6 (StorePre 0x104dc6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x104dc6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104dc6 1 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 102) (.exec 0x104dca (StorePre 0x104dca 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x104dca + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104dca 2 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 103) (.exec 0x104dce (StorePre 0x104dce 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x104dce + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104dce 6 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[81, 3]
    (.letOp (n := 104) (.exec 0x104dd2 (StorePre 0x104dd2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x104dd2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104dd2 7 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[87, 3]
    (.letOp (n := 105) (.out 0x104dd6 (movR64R64Effect 0x104dd6 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 106) (.exec 0x104dd6 (fun s => s.RIP = 0x104dd6) (movR64R64Effect 0x104dd6 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 107) (.out 0x104dd9 (addR64Imm8Effect 0x104dd9 4 0x68) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 108) (.exec 0x104dd9 (fun s => s.RIP = 0x104dd9) (addR64Imm8Effect 0x104dd9 4 0x68) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 109) (.out 0x104ddd (popR64Effect 0x104ddd 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[107]
    (.letOp (n := 110) (.out 0x104ddd (popR64Effect 0x104ddd 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[107]
    (.letOp (n := 111) (.exec 0x104ddd (PopPre 0x104ddd) (popR64Effect 0x104ddd 1 3) (Reg.operands [.gpr 4] [])) #v[107]
    (.letOp (n := 112) (.out 0x104dde (popR64Effect 0x104dde 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[110]
    (.letOp (n := 113) (.out 0x104dde (popR64Effect 0x104dde 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[110]
    (.letOp (n := 114) (.exec 0x104dde (PopPre 0x104dde) (popR64Effect 0x104dde 2 12) (Reg.operands [.gpr 4] [])) #v[110]
    (.letOp (n := 115) (.out 0x104de0 (popR64Effect 0x104de0 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[113]
    (.letOp (n := 116) (.out 0x104de0 (popR64Effect 0x104de0 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[113]
    (.letOp (n := 117) (.exec 0x104de0 (PopPre 0x104de0) (popR64Effect 0x104de0 2 14) (Reg.operands [.gpr 4] [])) #v[113]
    (.letOp (n := 118) (.out 0x104de2 (popR64Effect 0x104de2 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[116]
    (.letOp (n := 119) (.out 0x104de2 (popR64Effect 0x104de2 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[116]
    (.letOp (n := 120) (.exec 0x104de2 (PopPre 0x104de2) (popR64Effect 0x104de2 2 15) (Reg.operands [.gpr 4] [])) #v[116]
    (.letOp (n := 121) (.out 0x104de4 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[119]
    (.letOp (n := 122) (.out 0x104de4 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[119]
    (.letOp (n := 123) (.exec 0x104de4 (RetPre 0x104de4) (retEffect) (Reg.operands [.gpr 4] [])) #v[119]
    (.terminate (.ret (RegMap.args [(0, 105), (1, 71), (2, 75), (3, 109), (4, 122), (5, 5), (6, 81), (7, 87), (8, 97), (9, 67), (10, 10), (11, 11), (12, 112), (13, 13), (14, 115), (15, 118), (22, 22), (39, 39), (50, 50), (51, 51)] 124) (some ⟨121, by decide⟩)))))))))))))))))))))))))))))))))))

def bytes_l104d5e_1 : List UInt8 :=
  [0x48, 0x89, 0x43, 0x18, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x43, 0x10, 0x49, 0x8B, 0x06, 0x4D,
    0x8B, 0x46, 0x08, 0x4C, 0x89, 0x43, 0x08, 0x48, 0x89, 0x03, 0x48, 0x89, 0x4B, 0x20, 0x48, 0x89,
    0x53, 0x28, 0x48, 0x89, 0x73, 0x30, 0x48, 0x89, 0x7B, 0x38, 0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4,
    0x68, 0x5B, 0x41, 0x5C, 0x41, 0x5E, 0x41, 0x5F, 0xC3]

theorem code_l104d5e_1 : ∀ x ∈ codeRange 0x104dac bytes_l104d5e_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4dac 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104d5e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104d5e (movR64M64Effect 0x104d5e 1 (.base 14 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 54) (.exec 0x104d5e (LoadPre 0x104d5e (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x104d5e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d5e 1 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x104d62 (movR64M64Effect 0x104d62 2 (.base 14 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 56) (.exec 0x104d62 (LoadPre 0x104d62 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x104d62 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d62 2 (.base 14 (.d8 0x28))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x104d66 (movR64M64Effect 0x104d66 6 (.base 14 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x104d66 (LoadPre 0x104d66 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x104d66 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d66 6 (.base 14 (.d8 0x30))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x104d6a (movR64M64Effect 0x104d6a 7 (.base 14 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 60) (.exec 0x104d6a (LoadPre 0x104d6a (fun s => AddrMode.addr (.base 14 (.d8 0x38)) s (0x104d6a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104d6a 7 (.base 14 (.d8 0x38))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.exec 0x104d6e (StorePre 0x104d6e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x104d6e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x104d6e 4 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 62) (.exec 0x104d72 (fun s => s.RIP = 0x104d72) (leaR64Effect 0x104d72 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x104d77 (movzxR32M8Effect 0x104d77 5 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x104d77 (LoadPre 0x104d77 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x104d77 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x104d77 5 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x104d7c (movR64M64Effect 0x104d7c 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 66) (.exec 0x104d7c (LoadPre 0x104d7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104d7c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104d7c 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x104d81 (movR64M64Effect 0x104d81 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 68) (.exec 0x104d81 (LoadPre 0x104d81 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104d81 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104d81 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x104d86 (testR8R8Effect 0x104d86 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[63, 63]
    (.letOp (n := 70) (.exec 0x104d86 (fun s => s.RIP = 0x104d86) (testR8R8Effect 0x104d86 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[63, 63]
    (.letOp (n := 71) (.out 0x104d88 (atFlags (condHolds 5) (cmovR64R64Effect 0x104d88 4 1 8)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[53, 65, 69]
    (.letOp (n := 72) (.exec 0x104d88 (fun s => s.RIP = 0x104d88) (atFlags (condHolds 5) (cmovR64R64Effect 0x104d88 4 1 8)) (Reg.operands [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[53, 65, 69]
    (.letOp (n := 73) (.out 0x104d8c (testR8R8Effect 0x104d8c 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[63, 63]
    (.letOp (n := 74) (.exec 0x104d8c (fun s => s.RIP = 0x104d8c) (testR8R8Effect 0x104d8c 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[63, 63]
    (.letOp (n := 75) (.out 0x104d8e (atFlags (condHolds 5) (cmovR64R64Effect 0x104d8e 4 2 9)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[55, 67, 73]
    (.letOp (n := 76) (.exec 0x104d8e (fun s => s.RIP = 0x104d8e) (atFlags (condHolds 5) (cmovR64R64Effect 0x104d8e 4 2 9)) (Reg.operands [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[55, 67, 73]
    (.letOp (n := 77) (.out 0x104d92 (movR64M64Effect 0x104d92 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 78) (.exec 0x104d92 (LoadPre 0x104d92 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104d92 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104d92 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x104d97 (testR8R8Effect 0x104d97 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[63, 63]
    (.letOp (n := 80) (.exec 0x104d97 (fun s => s.RIP = 0x104d97) (testR8R8Effect 0x104d97 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[63, 63]
    (.letOp (n := 81) (.out 0x104d99 (atFlags (condHolds 5) (cmovR64R64Effect 0x104d99 4 6 8)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[57, 77, 79]
    (.letOp (n := 82) (.exec 0x104d99 (fun s => s.RIP = 0x104d99) (atFlags (condHolds 5) (cmovR64R64Effect 0x104d99 4 6 8)) (Reg.operands [.gpr 6, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[57, 77, 79]
    (.letOp (n := 83) (.out 0x104d9d (movR64M64Effect 0x104d9d 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 84) (.exec 0x104d9d (LoadPre 0x104d9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104d9d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x104d9d 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x104da2 (testR8R8Effect 0x104da2 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[63, 63]
    (.letOp (n := 86) (.exec 0x104da2 (fun s => s.RIP = 0x104da2) (testR8R8Effect 0x104da2 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[63, 63]
    (.letOp (n := 87) (.out 0x104da4 (atFlags (condHolds 5) (cmovR64R64Effect 0x104da4 4 7 8)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[59, 83, 85]
    (.letOp (n := 88) (.exec 0x104da4 (fun s => s.RIP = 0x104da4) (atFlags (condHolds 5) (cmovR64R64Effect 0x104da4 4 7 8)) (Reg.operands [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[59, 83, 85]
    (.letOp (n := 89) (.out 0x104da8 (movR64M64Effect 0x104da8 0 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 90) (.exec 0x104da8 (LoadPre 0x104da8 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x104da8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104da8 0 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (b_l104d5e_1))))))))))))))))))))))))))))))))))))))

def bytes_l104d5e : List UInt8 :=
  [0x49, 0x8B, 0x4E, 0x20, 0x49, 0x8B, 0x56, 0x28, 0x49, 0x8B, 0x76, 0x30, 0x49, 0x8B, 0x7E, 0x38,
    0x88, 0x44, 0x24, 0x28, 0x48, 0x8D, 0x44, 0x24, 0x28, 0x0F, 0xB6, 0x44, 0x24, 0x28, 0x4C, 0x8B,
    0x44, 0x24, 0x08, 0x4C, 0x8B, 0x4C, 0x24, 0x10, 0x84, 0xC0, 0x49, 0x0F, 0x45, 0xC8, 0x84, 0xC0,
    0x49, 0x0F, 0x45, 0xD1, 0x4C, 0x8B, 0x44, 0x24, 0x18, 0x84, 0xC0, 0x49, 0x0F, 0x45, 0xF0, 0x4C,
    0x8B, 0x44, 0x24, 0x20, 0x84, 0xC0, 0x49, 0x0F, 0x45, 0xF8, 0x49, 0x8B, 0x46, 0x18] ++ bytes_l104d5e_1

theorem code_l104d5e : ∀ x ∈ codeRange 0x104d5e bytes_l104d5e, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4d5e 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l104d5e_1

@[cfg_block] def b_l104de5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104de5 (leaR64Effect 0x104de5 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x104de5 (fun s => s.RIP = 0x104de5) (leaR64Effect 0x104de5 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104dea (xorR32R32Effect 0x104dea 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 56) (.exec 0x104dea (fun s => s.RIP = 0x104dea) (xorR32R32Effect 0x104dea 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 57) (.out 0x104dec (movR64Imm32Effect 0x104dec 2 0x2022e8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x104dec (fun s => s.RIP = 0x104dec) (movR64Imm32Effect 0x104dec 2 0x2022e8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x104df3 (xorR32R32Effect 0x104df3 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 60) (.exec 0x104df3 (fun s => s.RIP = 0x104df3) (xorR32R32Effect 0x104df3 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 61) (.out 0x104df5 (movR64Imm32Effect 0x104df5 9 0x2022f0) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 62) (.exec 0x104df5 (fun s => s.RIP = 0x104df5) (movR64Imm32Effect 0x104df5 9 0x2022f0) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x104dfc (callEffect (fun _ => 0x115408) 0x104e01) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x104dfc (PushPre 0x104dfc 5) (callEffect (fun _ => 0x115408) 0x104e01) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x104e01⟩) #v[]
    (.terminate (.call ⟨.l115408, RegMap.args [(1, 59), (2, 57), (4, 63), (5, 5), (6, 53), (7, 55), (8, 8), (9, 61)] 66⟩ { target := .l104e01, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l104de5 : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x08, 0x31, 0xFF, 0x48, 0xC7, 0xC2, 0xE8, 0x22, 0x20, 0x00, 0x31, 0xC9,
    0x49, 0xC7, 0xC1, 0xF0, 0x22, 0x20, 0x00, 0xE8, 0x07, 0x06, 0x01, 0x00]

theorem code_l104de5 : ∀ x ∈ codeRange 0x104de5 bytes_l104de5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4de5 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104e01 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104e01 (fun s => s.RIP = 0x104e01) (fun _ => nopEffect 0x104e01 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x104e0b (fun s => s.RIP = 0x104e0b) (fun _ => nopEffect 0x104e0b 5) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x104e10 (movR64M64Effect 0x104e10 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 56) (.exec 0x104e10 (LoadPre 0x104e10 (fun s => AddrMode.addr (.base 7 .none) s (0x104e10 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x104e10 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x104e13 (cmpMImm8Effect 0x104e13 3 32 (.base 0 .none) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[55]
    (.letOp (n := 58) (.exec 0x104e13 (LoadPre 0x104e13 (fun s => AddrMode.addr (.base 0 .none) s (0x104e13 + BitVec.ofNat 64 3)) 4) (cmpMImm8Effect 0x104e13 3 32 (.base 0 .none) 0x1) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l104e41, RegMap.args [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57)] 60⟩ ⟨.l104e18, RegMap.args [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57)] 60⟩))))))))

def bytes_l104e01 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0F, 0x1F, 0x44, 0x00, 0x00, 0x48,
    0x8B, 0x07, 0x83, 0x38, 0x01, 0x75, 0x29]

theorem code_l104e01 : ∀ x ∈ codeRange 0x104e01 bytes_l104e01, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4e01 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104e18 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104e18 (pushR64Effect 0x104e18 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[4, 0]
    (.letOp (n := 54) (.exec 0x104e18 (PushPre 0x104e18 1) (pushR64Effect 0x104e18 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.out 0x104e19 (addR64Imm8Effect 0x104e19 0 0x4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 56) (.exec 0x104e19 (fun s => s.RIP = 0x104e19) (addR64Imm8Effect 0x104e19 0 0x4) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.exec 0x104e1d (StorePre 0x104e1d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x104e1d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x104e1d 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 53]
    (.letOp (n := 58) (.out 0x104e21 (movR64R64Effect 0x104e21 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 59) (.exec 0x104e21 (fun s => s.RIP = 0x104e21) (movR64R64Effect 0x104e21 1 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 60) (.out 0x104e24 (movR32Imm32Effect 0x104e24 5 2 0x4) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 61) (.exec 0x104e24 (fun s => s.RIP = 0x104e24) (movR32Imm32Effect 0x104e24 5 2 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x104e29 (movR64R64Effect 0x104e29 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 63) (.exec 0x104e29 (fun s => s.RIP = 0x104e29) (movR64R64Effect 0x104e29 7 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.exec 0x104e2c (fun s => s.RIP = 0x104e2c) (movR64Imm32Effect 0x104e2c 6 0x202399) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x104e33 (movR64Imm32Effect 0x104e33 8 0x2023e0) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 66) (.exec 0x104e33 (fun s => s.RIP = 0x104e33) (movR64Imm32Effect 0x104e33 8 0x2023e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x104e3a (callEffect (fun _ => 0x128e40) 0x104e3f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 68) (.exec 0x104e3a (PushPre 0x104e3a 5) (callEffect (fun _ => 0x128e40) 0x104e3f) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 69) (.const ⟨64, 0x104e3f⟩) #v[]
    (.terminate (.call ⟨.l128e40, RegMap.args [(0, 55), (1, 58), (2, 60), (3, 3), (4, 67), (5, 5), (7, 62), (8, 65), (12, 12), (13, 13), (14, 14), (15, 15)] 70⟩ { target := .l104e3f, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l104e18 : List UInt8 :=
  [0x50, 0x48, 0x83, 0xC0, 0x04, 0x48, 0x89, 0x04, 0x24, 0x48, 0x89, 0xE1, 0xBA, 0x04, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xF7, 0x48, 0xC7, 0xC6, 0x99, 0x23, 0x20, 0x00, 0x49, 0xC7, 0xC0, 0xE0, 0x23,
    0x20, 0x00, 0xE8, 0x01, 0x40, 0x02, 0x00]

theorem code_l104e18 : ∀ x ∈ codeRange 0x104e18 bytes_l104e18, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4e18 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104e3f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104e3f (popR64Effect 0x104e3f 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.out 0x104e3f (popR64Effect 0x104e3f 1 1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x104e3f (PopPre 0x104e3f) (popR64Effect 0x104e3f 1 1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x104e40 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[54]
    (.letOp (n := 57) (.out 0x104e40 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 58) (.exec 0x104e40 (RetPre 0x104e40) (retEffect) (Reg.operands [.gpr 4] [])) #v[54]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59) (some ⟨56, by decide⟩))))))))

def bytes_l104e3f : List UInt8 :=
  [0x59, 0xC3]

theorem code_l104e3f : ∀ x ∈ codeRange 0x104e3f bytes_l104e3f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4e3f 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104e41 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104e41 (fun s => s.RIP = 0x104e41) (movR32Imm32Effect 0x104e41 5 2 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.out 0x104e46 (movR64R64Effect 0x104e46 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 55) (.exec 0x104e46 (fun s => s.RIP = 0x104e46) (movR64R64Effect 0x104e46 7 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.exec 0x104e49 (fun s => s.RIP = 0x104e49) (movR64Imm32Effect 0x104e49 6 0x202395) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l129390, RegMap.args [(7, 54)] 57⟩)))))

def bytes_l104e41 : List UInt8 :=
  [0xBA, 0x04, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF7, 0x48, 0xC7, 0xC6, 0x95, 0x23, 0x20, 0x00, 0xE9,
    0x3B, 0x45, 0x02, 0x00]

theorem code_l104e41 : ∀ x ∈ codeRange 0x104e41 bytes_l104e41, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4e41 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104f20_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.exec 0x104f77 (StorePre 0x104f77 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104f77 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104f77 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 89) (.exec 0x104f80 (StorePre 0x104f80 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x104f80 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104f80 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 90) (.exec 0x104f89 (StorePre 0x104f89 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104f89 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104f89 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 91) (.out 0x104f92 (leaR64Effect 0x104f92 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 92) (.exec 0x104f92 (fun s => s.RIP = 0x104f92) (leaR64Effect 0x104f92 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 93) (.out 0x104f9a (leaR64Effect 0x104f9a 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[63]
    (.letOp (n := 94) (.exec 0x104f9a (fun s => s.RIP = 0x104f9a) (leaR64Effect 0x104f9a 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 95) (.out 0x104f9f (callEffect (fun _ => 0x10a280) 0x104fa4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 96) (.exec 0x104f9f (PushPre 0x104f9f 5) (callEffect (fun _ => 0x10a280) 0x104fa4) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 97) (.const ⟨64, 0x104fa4⟩) #v[]
    (.terminate (.call ⟨.l10a280, RegMap.args [(0, 81), (1, 83), (2, 2), (3, 73), (4, 95), (5, 5), (6, 93), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 69), (13, 67), (14, 71), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 98⟩ { target := .l104fa4, kept := #v[], arity := rfl, guard := some (Fin.last 97) })))))))))))

def bytes_l104f20_1 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x08, 0xE8, 0xDC, 0x52, 0x00, 0x00]

theorem code_l104f20_1 : ∀ x ∈ codeRange 0x104f77 bytes_l104f20_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4f77 45 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104f20 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104f20 (pushR64Effect 0x104f20 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x104f20 (PushPre 0x104f20 2) (pushR64Effect 0x104f20 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x104f22 (pushR64Effect 0x104f22 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x104f22 (PushPre 0x104f22 2) (pushR64Effect 0x104f22 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x104f24 (pushR64Effect 0x104f24 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x104f24 (PushPre 0x104f24 2) (pushR64Effect 0x104f24 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x104f26 (pushR64Effect 0x104f26 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x104f26 (PushPre 0x104f26 2) (pushR64Effect 0x104f26 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x104f28 (pushR64Effect 0x104f28 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x104f28 (PushPre 0x104f28 1) (pushR64Effect 0x104f28 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x104f29 (subR64Imm32Effect 0x104f29 4 0x1c0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x104f29 (fun s => s.RIP = 0x104f29) (subR64Imm32Effect 0x104f29 4 0x1c0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x104f30 (movR64R64Effect 0x104f30 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[8]
    (.letOp (n := 66) (.exec 0x104f30 (fun s => s.RIP = 0x104f30) (movR64R64Effect 0x104f30 15 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 67) (.out 0x104f33 (movR64R64Effect 0x104f33 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[1]
    (.letOp (n := 68) (.exec 0x104f33 (fun s => s.RIP = 0x104f33) (movR64R64Effect 0x104f33 13 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 69) (.out 0x104f36 (movR64R64Effect 0x104f36 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2]
    (.letOp (n := 70) (.exec 0x104f36 (fun s => s.RIP = 0x104f36) (movR64R64Effect 0x104f36 12 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x104f39 (movR64R64Effect 0x104f39 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 72) (.exec 0x104f39 (fun s => s.RIP = 0x104f39) (movR64R64Effect 0x104f39 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x104f3c (movR64R64Effect 0x104f3c 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 74) (.exec 0x104f3c (fun s => s.RIP = 0x104f3c) (movR64R64Effect 0x104f3c 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 75) (.out 0x104f3f (movR64M64Effect 0x104f3f 0 (.base 8 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 76) (.exec 0x104f3f (LoadPre 0x104f3f (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x104f3f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104f3f 0 (.base 8 (.d8 0x18))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 77) (.exec 0x104f43 (StorePre 0x104f43 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x104f43 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104f43 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 63]
    (.letOp (n := 78) (.out 0x104f4b (movR64M64Effect 0x104f4b 0 (.base 8 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 79) (.exec 0x104f4b (LoadPre 0x104f4b (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x104f4b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104f4b 0 (.base 8 (.d8 0x10))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 80) (.exec 0x104f4f (StorePre 0x104f4f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x104f4f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104f4f 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 63]
    (.letOp (n := 81) (.out 0x104f57 (movR64M64Effect 0x104f57 0 (.base 8 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 82) (.exec 0x104f57 (LoadPre 0x104f57 (fun s => AddrMode.addr (.base 8 .none) s (0x104f57 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x104f57 0 (.base 8 .none)) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 83) (.out 0x104f5a (movR64M64Effect 0x104f5a 1 (.base 8 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 84) (.exec 0x104f5a (LoadPre 0x104f5a (fun s => AddrMode.addr (.base 8 (.d8 0x8)) s (0x104f5a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104f5a 1 (.base 8 (.d8 0x8))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 85) (.exec 0x104f5e (StorePre 0x104f5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x104f5e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104f5e 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[83, 63]
    (.letOp (n := 86) (.exec 0x104f66 (StorePre 0x104f66 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x104f66 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104f66 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 63]
    (.letOp (n := 87) (.exec 0x104f6e (StorePre 0x104f6e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104f6e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x104f6e (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[63]
    (b_l104f20_1)))))))))))))))))))))))))))))))))))

def bytes_l104f20 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xC0, 0x01, 0x00, 0x00,
    0x4D, 0x89, 0xC7, 0x49, 0x89, 0xCD, 0x49, 0x89, 0xD4, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFB, 0x49,
    0x8B, 0x40, 0x18, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x40, 0x10, 0x48,
    0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x00, 0x49, 0x8B, 0x48, 0x08, 0x48, 0x89,
    0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] ++ bytes_l104f20_1

theorem code_l104f20 : ∀ x ∈ codeRange 0x104f20 bytes_l104f20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4f20 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l104f20_1

@[cfg_block] def b_l104fa4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104fa4 (notR8Effect 0x104fa4 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x104fa4 (fun s => s.RIP = 0x104fa4) (notR8Effect 0x104fa4 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x104fa6 (andAlImm8Effect 0x104fa6 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x104fa6 (fun s => s.RIP = 0x104fa6) (andAlImm8Effect 0x104fa6 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x104fa8 (movzxR32R8Effect 0x104fa8 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x104fa8 (fun s => s.RIP = 0x104fa8) (movzxR32R8Effect 0x104fa8 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x104fab (callEffect (fun _ => 0x127d50) 0x104fb0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x104fab (PushPre 0x104fab 5) (callEffect (fun _ => 0x127d50) 0x104fb0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x104fb0⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l104fb0, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l104fa4 : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0xA0, 0x2D, 0x02, 0x00]

theorem code_l104fa4 : ∀ x ∈ codeRange 0x104fa4 bytes_l104fa4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4fa4 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104fb0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104fb0 (StorePre 0x104fb0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x104fb0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x104fb0 4 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x104fb4 (cmpAlImm8Effect 0x104fb4 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 55) (.exec 0x104fb4 (fun s => s.RIP = 0x104fb4) (cmpAlImm8Effect 0x104fb4 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 56) (.pure (condOp 5)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l105393, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l104fbc, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l104fb0 : List UInt8 :=
  [0x88, 0x44, 0x24, 0x08, 0x3C, 0x01, 0x0F, 0x85, 0xD7, 0x03, 0x00, 0x00]

theorem code_l104fb0 : ∀ x ∈ codeRange 0x104fb0 bytes_l104fb0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4fb0 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104fbc_1 : Block Op Label signature Reg.count 81 :=
  .letOp (n := 81) (.out 0x10503f (leaR64Effect 0x10503f 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 82) (.exec 0x10503f (fun s => s.RIP = 0x10503f) (leaR64Effect 0x10503f 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x105047 (leaR64Effect 0x105047 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 84) (.exec 0x105047 (fun s => s.RIP = 0x105047) (leaR64Effect 0x105047 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x10504c (callEffect (fun _ => 0x10a280) 0x105051) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 86) (.exec 0x10504c (PushPre 0x10504c 5) (callEffect (fun _ => 0x10a280) 0x105051) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.const ⟨64, 0x105051⟩) #v[]
    (.terminate (.call ⟨.l10a280, RegMap.args [(0, 71), (1, 73), (3, 3), (4, 85), (5, 5), (6, 83), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 88⟩ { target := .l105051, kept := #v[], arity := rfl, guard := some (Fin.last 87) }))))))))

def bytes_l104fbc_1 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x08, 0xE8, 0x2F, 0x52,
    0x00, 0x00]

theorem code_l104fbc_1 : ∀ x ∈ codeRange 0x10503f bytes_l104fbc_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x503f 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104fbc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104fbc (movR64M64Effect 0x104fbc 0 (.base 15 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x104fbc (LoadPre 0x104fbc (fun s => AddrMode.addr (.base 15 .none) s (0x104fbc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x104fbc 0 (.base 15 .none)) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x104fbf (movR64M64Effect 0x104fbf 1 (.base 15 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 56) (.exec 0x104fbf (LoadPre 0x104fbf (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x104fbf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104fbf 1 (.base 15 (.d8 0x8))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.exec 0x104fc3 (StorePre 0x104fc3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x104fc3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104fc3 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x104fcb (StorePre 0x104fcb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x104fcb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104fcb 1 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x104fd3 (movR64M64Effect 0x104fd3 0 (.base 15 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 60) (.exec 0x104fd3 (LoadPre 0x104fd3 (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x104fd3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104fd3 0 (.base 15 (.d8 0x10))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.exec 0x104fd7 (StorePre 0x104fd7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x104fd7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104fd7 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x104fdf (movR64M64Effect 0x104fdf 0 (.base 15 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 63) (.exec 0x104fdf (LoadPre 0x104fdf (fun s => AddrMode.addr (.base 15 (.d8 0x18)) s (0x104fdf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104fdf 0 (.base 15 (.d8 0x18))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.exec 0x104fe3 (StorePre 0x104fe3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x104fe3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104fe3 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x104feb (movR64M64Effect 0x104feb 0 (.base 15 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 66) (.exec 0x104feb (LoadPre 0x104feb (fun s => AddrMode.addr (.base 15 (.d8 0x38)) s (0x104feb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104feb 0 (.base 15 (.d8 0x38))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 67) (.exec 0x104fef (StorePre 0x104fef 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x104fef + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104fef 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x104ff7 (movR64M64Effect 0x104ff7 0 (.base 15 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 69) (.exec 0x104ff7 (LoadPre 0x104ff7 (fun s => AddrMode.addr (.base 15 (.d8 0x30)) s (0x104ff7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x104ff7 0 (.base 15 (.d8 0x30))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 70) (.exec 0x104ffb (StorePre 0x104ffb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x104ffb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104ffb 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x105003 (movR64M64Effect 0x105003 0 (.base 15 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 72) (.exec 0x105003 (LoadPre 0x105003 (fun s => AddrMode.addr (.base 15 (.d8 0x20)) s (0x105003 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105003 0 (.base 15 (.d8 0x20))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 73) (.out 0x105007 (movR64M64Effect 0x105007 1 (.base 15 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 74) (.exec 0x105007 (LoadPre 0x105007 (fun s => AddrMode.addr (.base 15 (.d8 0x28)) s (0x105007 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105007 1 (.base 15 (.d8 0x28))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 75) (.exec 0x10500b (StorePre 0x10500b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10500b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10500b 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.exec 0x105013 (StorePre 0x105013 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x105013 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105013 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 77) (.exec 0x10501b (StorePre 0x10501b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10501b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10501b (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x105024 (StorePre 0x105024 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105024 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105024 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x10502d (StorePre 0x10502d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10502d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10502d (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.exec 0x105036 (StorePre 0x105036 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105036 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105036 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l104fbc_1))))))))))))))))))))))))))))

def bytes_l104fbc : List UInt8 :=
  [0x49, 0x8B, 0x07, 0x49, 0x8B, 0x4F, 0x08, 0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48,
    0x89, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00, 0x49, 0x8B, 0x47, 0x10, 0x48, 0x89, 0x84, 0x24, 0x10,
    0x01, 0x00, 0x00, 0x49, 0x8B, 0x47, 0x18, 0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x49,
    0x8B, 0x47, 0x38, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x47, 0x30, 0x48,
    0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x47, 0x20, 0x49, 0x8B, 0x4F, 0x28, 0x48,
    0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00,
    0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00,
    0x00, 0x00, 0x00] ++ bytes_l104fbc_1

theorem code_l104fbc : ∀ x ∈ codeRange 0x104fbc bytes_l104fbc, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4fbc 131 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l104fbc_1

@[cfg_block] def b_l105051 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105051 (notR8Effect 0x105051 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x105051 (fun s => s.RIP = 0x105051) (notR8Effect 0x105051 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x105053 (andAlImm8Effect 0x105053 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x105053 (fun s => s.RIP = 0x105053) (andAlImm8Effect 0x105053 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x105055 (movzxR32R8Effect 0x105055 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x105055 (fun s => s.RIP = 0x105055) (movzxR32R8Effect 0x105055 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x105058 (callEffect (fun _ => 0x127d50) 0x10505d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x105058 (PushPre 0x105058 5) (callEffect (fun _ => 0x127d50) 0x10505d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10505d⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10505d, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l105051 : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0xF3, 0x2C, 0x02, 0x00]

theorem code_l105051 : ∀ x ∈ codeRange 0x105051 bytes_l105051, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5051 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10505d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10505d (StorePre 0x10505d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10505d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10505d 4 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x105061 (cmpAlImm8Effect 0x105061 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 55) (.exec 0x105061 (fun s => s.RIP = 0x105061) (cmpAlImm8Effect 0x105061 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 56) (.pure (condOp 5)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l105393, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l105069, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l10505d : List UInt8 :=
  [0x88, 0x44, 0x24, 0x08, 0x3C, 0x01, 0x0F, 0x85, 0x2A, 0x03, 0x00, 0x00]

theorem code_l10505d : ∀ x ∈ codeRange 0x10505d bytes_l10505d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x505d 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105069 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105069 (leaR64Effect 0x105069 0 (.base 15 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x105069 (fun s => s.RIP = 0x105069) (leaR64Effect 0x105069 0 (.base 15 (.d8 0x20))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x10506d (movR64M64Effect 0x10506d 1 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x10506d (LoadPre 0x10506d (fun s => AddrMode.addr (.base 0 .none) s (0x10506d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10506d 1 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x105070 (movR64M64Effect 0x105070 2 (.base 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 58) (.exec 0x105070 (LoadPre 0x105070 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x105070 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105070 2 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.exec 0x105074 (StorePre 0x105074 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x105074 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105074 1 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 60) (.exec 0x10507c (StorePre 0x10507c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10507c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10507c 2 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 61) (.out 0x105084 (movR64M64Effect 0x105084 1 (.base 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 62) (.exec 0x105084 (LoadPre 0x105084 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x105084 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105084 1 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 63) (.exec 0x105088 (StorePre 0x105088 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x105088 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105088 1 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x105090 (movR64M64Effect 0x105090 0 (.base 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 65) (.exec 0x105090 (LoadPre 0x105090 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x105090 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105090 0 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 66) (.exec 0x105094 (StorePre 0x105094 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x105094 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105094 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x10509c (leaR64Effect 0x10509c 7 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 68) (.exec 0x10509c (fun s => s.RIP = 0x10509c) (leaR64Effect 0x10509c 7 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x1050a4 (callEffect (fun _ => 0x10a170) 0x1050a9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x1050a4 (PushPre 0x1050a4 5) (callEffect (fun _ => 0x10a170) 0x1050a9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x1050a9⟩) #v[]
    (.terminate (.call ⟨.l10a170, RegMap.args [(0, 64), (1, 61), (2, 57), (3, 3), (4, 69), (5, 5), (7, 67), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l1050a9, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l105069 : List UInt8 :=
  [0x49, 0x8D, 0x47, 0x20, 0x48, 0x8B, 0x08, 0x48, 0x8B, 0x50, 0x08, 0x48, 0x89, 0x8C, 0x24, 0xE0,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x48, 0x10, 0x48,
    0x89, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x40, 0x18, 0x48, 0x89, 0x84, 0x24, 0xF8,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0xE8, 0xC7, 0x50, 0x00, 0x00]

theorem code_l105069 : ∀ x ∈ codeRange 0x105069 bytes_l105069, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5069 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1050a9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1050a9 (testR8R8Effect 0x1050a9 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1050a9 (fun s => s.RIP = 0x1050a9) (testR8R8Effect 0x1050a9 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1050c1, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1050ad, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1050a9 : List UInt8 :=
  [0x84, 0xC0, 0x74, 0x14]

theorem code_l1050a9 : ∀ x ∈ codeRange 0x1050a9 bytes_l1050a9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x50a9 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1050ad : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1050ad (StorePre 0x1050ad 8 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1050ad + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1050ad (.base 3 (.d8 0x8)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 54) (.exec 0x1050b5 (StorePre 0x1050b5 7 (fun s => AddrMode.addr (.base 3 .none) s (0x1050b5 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x1050b5 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l10537f, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1050ad : List UInt8 :=
  [0x48, 0xC7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00, 0xE9,
    0xBE, 0x02, 0x00, 0x00]

theorem code_l1050ad : ∀ x ∈ codeRange 0x1050ad bytes_l1050ad, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x50ad 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1050c1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1050c1 (StorePre 0x1050c1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1050c1 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1050c1 (.sib 4 none 0 (.d8 0x8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x1050c6 (leaR64Effect 0x1050c6 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 55) (.exec 0x1050c6 (fun s => s.RIP = 0x1050c6) (leaR64Effect 0x1050c6 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1050cb (StorePre 0x1050cb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1050cb + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1050cb (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1050d0 (StorePre 0x1050d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1050d0 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1050d0 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1050d5 (StorePre 0x1050d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1050d5 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1050d5 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1050da (cmpR64Imm8Effect 0x1050da 13 0x20) (EffectPart.reads (.flag .CF) [.gpr 13] []) (.flag .CF)) #v[13]
    (.letOp (n := 60) (.exec 0x1050da (fun s => s.RIP = 0x1050da) (cmpR64Imm8Effect 0x1050da 13 0x20) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x1050de (movR32Imm32Effect 0x1050de 5 6 0x20) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 62) (.exec 0x1050de (fun s => s.RIP = 0x1050de) (movR32Imm32Effect 0x1050de 5 6 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x1050e3 (atFlags (condHolds 2) (cmovR64R64Effect 0x1050e3 4 6 13)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[61, 13, 59]
    (.letOp (n := 64) (.exec 0x1050e3 (fun s => s.RIP = 0x1050e3) (atFlags (condHolds 2) (cmovR64R64Effect 0x1050e3 4 6 13)) (Reg.operands [.gpr 6, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[61, 13, 59]
    (.letOp (n := 65) (.exec 0x1050e7 (StorePre 0x1050e7 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1050e7 + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x1050e7 11 (.sib 4 none 0 (.d32 0x140)) 0x100) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1050f2 (StorePre 0x1050f2 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1050f2 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1050f2 (.sib 4 none 0 (.d32 0xa0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1050fe (StorePre 0x1050fe 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1050fe + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1050fe (.sib 4 none 0 (.d32 0x98)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x10510a (StorePre 0x10510a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10510a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10510a (.sib 4 none 0 (.d32 0x90)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x105116 (StorePre 0x105116 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x105116 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105116 (.sib 4 none 0 (.d32 0x88)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x105122 (leaR64Effect 0x105122 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x105122 (fun s => s.RIP = 0x105122) (leaR64Effect 0x105122 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x10512a (movR32Imm32Effect 0x10512a 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 73) (.exec 0x10512a (fun s => s.RIP = 0x10512a) (movR32Imm32Effect 0x10512a 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 74) (.out 0x10512f (movR64R64Effect 0x10512f 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 75) (.exec 0x10512f (fun s => s.RIP = 0x10512f) (movR64R64Effect 0x10512f 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 76) (.out 0x105132 (movR32Imm32Effect 0x105132 6 8 0x100) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 77) (.exec 0x105132 (fun s => s.RIP = 0x105132) (movR32Imm32Effect 0x105132 6 8 0x100) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x105138 (callEffect (fun _ => 0x127d70) 0x10513d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 79) (.exec 0x105138 (PushPre 0x105138 5) (callEffect (fun _ => 0x127d70) 0x10513d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.const ⟨64, 0x10513d⟩) #v[]
    (.terminate (.call ⟨.l127d70, RegMap.args [(0, 54), (1, 72), (2, 70), (3, 3), (4, 78), (5, 5), (6, 63), (7, 74), (8, 76), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩ { target := .l10513d, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l1050c1 : List UInt8 :=
  [0xC6, 0x44, 0x24, 0x08, 0x01, 0x48, 0x8D, 0x44, 0x24, 0x08, 0xC6, 0x44, 0x24, 0x08, 0x00, 0xC6,
    0x44, 0x24, 0x08, 0x00, 0xC6, 0x44, 0x24, 0x08, 0x00, 0x49, 0x83, 0xFD, 0x20, 0xBE, 0x20, 0x00,
    0x00, 0x00, 0x49, 0x0F, 0x42, 0xF5, 0xC7, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00,
    0x00, 0x48, 0xC7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84,
    0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x90, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xE7, 0x41, 0xB8, 0x00, 0x01, 0x00, 0x00, 0xE8, 0x33, 0x2C, 0x02, 0x00]

theorem code_l1050c1 : ∀ x ∈ codeRange 0x1050c1 bytes_l1050c1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x50c1 124 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10513d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10513d (cmpAlImm8Effect 0x10513d 0xff) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x10513d (fun s => s.RIP = 0x10513d) (cmpAlImm8Effect 0x10513d 0xff) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1053af, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l105145, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10513d : List UInt8 :=
  [0x3C, 0xFF, 0x0F, 0x85, 0x6A, 0x02, 0x00, 0x00]

theorem code_l10513d : ∀ x ∈ codeRange 0x10513d bytes_l10513d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x513d 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105145 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105145 (movR64M64Effect 0x105145 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x105145 (LoadPre 0x105145 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x105145 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105145 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10514d (StorePre 0x10514d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10514d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10514d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x105152 (movR64M64Effect 0x105152 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x105152 (LoadPre 0x105152 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x105152 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105152 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10515a (StorePre 0x10515a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10515a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10515a 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x10515f (movR64M64Effect 0x10515f 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x10515f (LoadPre 0x10515f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10515f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10515f 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x105167 (movR64M64Effect 0x105167 1 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x105167 (LoadPre 0x105167 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x105167 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105167 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x10516f (StorePre 0x10516f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10516f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10516f 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x105174 (StorePre 0x105174 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105174 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105174 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x105179 (leaR64Effect 0x105179 7 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x105179 (fun s => s.RIP = 0x105179) (leaR64Effect 0x105179 7 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x105181 (leaR64Effect 0x105181 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x105181 (fun s => s.RIP = 0x105181) (leaR64Effect 0x105181 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x105186 (callEffect (fun _ => 0x109f80) 0x10518b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x105186 (PushPre 0x105186 5) (callEffect (fun _ => 0x109f80) 0x10518b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x10518b⟩) #v[]
    (.terminate (.call ⟨.l109f80, RegMap.args [(0, 59), (1, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l10518b, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l105145 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84,
    0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24, 0x88, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48,
    0x89, 0x44, 0x24, 0x08, 0x48, 0x8D, 0xBC, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24,
    0x08, 0xE8, 0xF5, 0x4D, 0x00, 0x00]

theorem code_l105145 : ∀ x ∈ codeRange 0x105145 bytes_l105145, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5145 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10518b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10518b (leaR64Effect 0x10518b 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10518b (fun s => s.RIP = 0x10518b) (leaR64Effect 0x10518b 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105190 (leaR64Effect 0x105190 6 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x105190 (fun s => s.RIP = 0x105190) (leaR64Effect 0x105190 6 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x105198 (callEffect (fun _ => 0x10a0c0) 0x10519d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x105198 (PushPre 0x105198 5) (callEffect (fun _ => 0x10a0c0) 0x10519d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x10519d⟩) #v[]
    (.terminate (.call ⟨.l10a0c0, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l10519d, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l10518b : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0x8D, 0xB4, 0x24, 0xE0, 0x00, 0x00, 0x00, 0xE8, 0x23, 0x4F,
    0x00, 0x00]

theorem code_l10518b : ∀ x ∈ codeRange 0x10518b bytes_l10518b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x518b 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10519d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10519d (movzxR32M8Effect 0x10519d 5 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10519d (LoadPre 0x10519d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10519d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10519d 5 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1051a2 (StorePre 0x1051a2 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1051a2 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1051a2 7 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1051a9 (cmpAlImm8Effect 0x1051a9 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 57) (.exec 0x1051a9 (fun s => s.RIP = 0x1051a9) (cmpAlImm8Effect 0x1051a9 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 58) (.pure (condOp 5)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l1053cb, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l1051b1, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l10519d : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x28, 0x88, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x3C, 0x01, 0x0F, 0x85,
    0x1A, 0x02, 0x00, 0x00]

theorem code_l10519d : ∀ x ∈ codeRange 0x10519d bytes_l10519d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x519d 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1051b1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1051b1 (movR64M64Effect 0x1051b1 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1051b1 (LoadPre 0x1051b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1051b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1051b1 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1051b6 (movR64M64Effect 0x1051b6 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1051b6 (LoadPre 0x1051b6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1051b6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1051b6 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1051bb (StorePre 0x1051bb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x1051bb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1051bb 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x1051c3 (StorePre 0x1051c3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1051c3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1051c3 1 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x1051cb (movR64M64Effect 0x1051cb 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x1051cb (LoadPre 0x1051cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1051cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1051cb 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1051d0 (StorePre 0x1051d0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x1051d0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1051d0 2 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1051d8 (movR64M64Effect 0x1051d8 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 63) (.exec 0x1051d8 (LoadPre 0x1051d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1051d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1051d8 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1051dd (StorePre 0x1051dd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1051dd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1051dd 6 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.exec 0x1051e5 (StorePre 0x1051e5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1051e5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1051e5 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 66) (.exec 0x1051ea (StorePre 0x1051ea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1051ea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1051ea 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 67) (.exec 0x1051ef (StorePre 0x1051ef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1051ef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1051ef 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 68) (.exec 0x1051f4 (StorePre 0x1051f4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1051f4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1051f4 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 69) (.out 0x1051f9 (leaR64Effect 0x1051f9 12 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 70) (.exec 0x1051f9 (fun s => s.RIP = 0x1051f9) (leaR64Effect 0x1051f9 12 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x105201 (leaR64Effect 0x105201 6 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 72) (.exec 0x105201 (fun s => s.RIP = 0x105201) (leaR64Effect 0x105201 6 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x105209 (leaR64Effect 0x105209 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 74) (.exec 0x105209 (fun s => s.RIP = 0x105209) (leaR64Effect 0x105209 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x10520e (movR64R64Effect 0x10520e 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[69]
    (.letOp (n := 76) (.exec 0x10520e (fun s => s.RIP = 0x10520e) (movR64R64Effect 0x10520e 7 12) (Reg.operands [.gpr 12] [])) #v[69]
    (.letOp (n := 77) (.out 0x105211 (callEffect (fun _ => 0x109f60) 0x105216) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 78) (.exec 0x105211 (PushPre 0x105211 5) (callEffect (fun _ => 0x109f60) 0x105216) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.const ⟨64, 0x105216⟩) #v[]
    (.terminate (.call ⟨.l109f60, RegMap.args [(0, 53), (1, 55), (2, 73), (3, 3), (4, 77), (5, 5), (6, 71), (7, 75), (12, 69), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩ { target := .l105216, kept := #v[], arity := rfl, guard := some (Fin.last 79) }))))))))))))))))))))))))))))

def bytes_l1051b1 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x84, 0x24, 0x20, 0x01,
    0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x18, 0x48,
    0x89, 0x94, 0x24, 0x30, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x20, 0x48, 0x89, 0xB4, 0x24,
    0x38, 0x01, 0x00, 0x00, 0x48, 0x89, 0x74, 0x24, 0x20, 0x48, 0x89, 0x54, 0x24, 0x18, 0x48, 0x89,
    0x4C, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x8D, 0xA4, 0x24, 0x80, 0x01, 0x00, 0x00,
    0x48, 0x8D, 0xB4, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x54, 0x24, 0x08, 0x4C, 0x89, 0xE7,
    0xE8, 0x4A, 0x4D, 0x00, 0x00]

theorem code_l1051b1 : ∀ x ∈ codeRange 0x1051b1 bytes_l1051b1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x51b1 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105216 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105216 (movR64M64Effect 0x105216 0 (.base 15 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x105216 (LoadPre 0x105216 (fun s => AddrMode.addr (.base 15 (.d8 0x18)) s (0x105216 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105216 0 (.base 15 (.d8 0x18))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.exec 0x10521a (StorePre 0x10521a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10521a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10521a 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10521f (movR64M64Effect 0x10521f 0 (.base 15 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 57) (.exec 0x10521f (LoadPre 0x10521f (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x10521f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10521f 0 (.base 15 (.d8 0x10))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 58) (.exec 0x105223 (StorePre 0x105223 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105223 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105223 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x105228 (movR64M64Effect 0x105228 0 (.base 15 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 60) (.exec 0x105228 (LoadPre 0x105228 (fun s => AddrMode.addr (.base 15 .none) s (0x105228 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x105228 0 (.base 15 .none)) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.out 0x10522b (movR64M64Effect 0x10522b 1 (.base 15 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 62) (.exec 0x10522b (LoadPre 0x10522b (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x10522b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10522b 1 (.base 15 (.d8 0x8))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 63) (.exec 0x10522f (StorePre 0x10522f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10522f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10522f 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x105234 (StorePre 0x105234 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105234 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105234 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x105239 (leaR64Effect 0x105239 15 (.sib 4 none 0 (.d32 0x1a0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 66) (.exec 0x105239 (fun s => s.RIP = 0x105239) (leaR64Effect 0x105239 15 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x105241 (leaR64Effect 0x105241 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x105241 (fun s => s.RIP = 0x105241) (leaR64Effect 0x105241 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x105246 (leaR64Effect 0x105246 2 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 70) (.exec 0x105246 (fun s => s.RIP = 0x105246) (leaR64Effect 0x105246 2 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x10524e (movR64R64Effect 0x10524e 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 72) (.exec 0x10524e (fun s => s.RIP = 0x10524e) (movR64R64Effect 0x10524e 7 15) (Reg.operands [.gpr 15] [])) #v[65]
    (.letOp (n := 73) (.out 0x105251 (callEffect (fun _ => 0x109f60) 0x105256) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 74) (.exec 0x105251 (PushPre 0x105251 5) (callEffect (fun _ => 0x109f60) 0x105256) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.const ⟨64, 0x105256⟩) #v[]
    (.terminate (.call ⟨.l109f60, RegMap.args [(0, 59), (1, 61), (2, 69), (3, 3), (4, 73), (5, 5), (6, 67), (7, 71), (12, 12), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ { target := .l105256, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l105216 : List UInt8 :=
  [0x49, 0x8B, 0x47, 0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x49, 0x8B, 0x47, 0x10, 0x48, 0x89, 0x44,
    0x24, 0x18, 0x49, 0x8B, 0x07, 0x49, 0x8B, 0x4F, 0x08, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0x89,
    0x44, 0x24, 0x08, 0x4C, 0x8D, 0xBC, 0x24, 0xA0, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x08,
    0x48, 0x8D, 0x94, 0x24, 0x20, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0xE8, 0x0A, 0x4D, 0x00, 0x00]

theorem code_l105216 : ∀ x ∈ codeRange 0x105216 bytes_l105216, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5216 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105256 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105256 (leaR64Effect 0x105256 13 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 54) (.exec 0x105256 (fun s => s.RIP = 0x105256) (leaR64Effect 0x105256 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10525b (movR64R64Effect 0x10525b 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10525b (fun s => s.RIP = 0x10525b) (movR64R64Effect 0x10525b 7 13) (Reg.operands [.gpr 13] [])) #v[53]
    (.letOp (n := 57) (.out 0x10525e (movR64R64Effect 0x10525e 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x10525e (fun s => s.RIP = 0x10525e) (movR64R64Effect 0x10525e 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x105261 (movR64R64Effect 0x105261 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 60) (.exec 0x105261 (fun s => s.RIP = 0x105261) (movR64R64Effect 0x105261 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.out 0x105264 (movR64R64Effect 0x105264 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 62) (.exec 0x105264 (fun s => s.RIP = 0x105264) (movR64R64Effect 0x105264 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 63) (.out 0x105267 (callEffect (fun _ => 0x10fb20) 0x10526c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x105267 (PushPre 0x105267 5) (callEffect (fun _ => 0x10fb20) 0x10526c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x10526c⟩) #v[]
    (.terminate (.call ⟨.l10fb20, RegMap.args [(1, 61), (2, 59), (3, 3), (4, 63), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l10526c, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l105256 : List UInt8 :=
  [0x4C, 0x8D, 0x6C, 0x24, 0x08, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xE6, 0x4C, 0x89, 0xFA, 0x4C, 0x89,
    0xF1, 0xE8, 0xB4, 0xA8, 0x00, 0x00]

theorem code_l105256 : ∀ x ∈ codeRange 0x105256 bytes_l105256, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5256 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10526c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10526c (leaR64Effect 0x10526c 14 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x10526c (fun s => s.RIP = 0x10526c) (leaR64Effect 0x10526c 14 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105274 (movR64R64Effect 0x105274 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x105274 (fun s => s.RIP = 0x105274) (movR64R64Effect 0x105274 7 14) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 57) (.out 0x105277 (movR64R64Effect 0x105277 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 58) (.exec 0x105277 (fun s => s.RIP = 0x105277) (movR64R64Effect 0x105277 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x10527a (callEffect (fun _ => 0x10fe50) 0x10527f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10527a (PushPre 0x10527a 5) (callEffect (fun _ => 0x10fe50) 0x10527f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10527f⟩) #v[]
    (.terminate (.call ⟨.l10fe50, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10527f, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10526c : List UInt8 :=
  [0x4C, 0x8D, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xEE, 0xE8, 0xD1,
    0xAB, 0x00, 0x00]

theorem code_l10526c : ∀ x ∈ codeRange 0x10526c bytes_l10526c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x526c 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10527f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10527f (leaR64Effect 0x10527f 15 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x10527f (fun s => s.RIP = 0x10527f) (leaR64Effect 0x10527f 15 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105287 (movR64R64Effect 0x105287 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x105287 (fun s => s.RIP = 0x105287) (movR64R64Effect 0x105287 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 57) (.out 0x10528a (movR64R64Effect 0x10528a 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10528a (fun s => s.RIP = 0x10528a) (movR64R64Effect 0x10528a 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x10528d (callEffect (fun _ => 0x120350) 0x105292) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10528d (PushPre 0x10528d 5) (callEffect (fun _ => 0x120350) 0x105292) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x105292⟩) #v[]
    (.terminate (.call ⟨.l120350, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l105292, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10527f : List UInt8 :=
  [0x4C, 0x8D, 0xBC, 0x24, 0x40, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xF6, 0xE8, 0xBE,
    0xB0, 0x01, 0x00]

theorem code_l10527f : ∀ x ∈ codeRange 0x10527f bytes_l10527f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x527f 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105292 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x105292 (StorePre 0x105292 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105292 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105292 (.sib 4 none 0 (.d8 0x8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x105297 (leaR64Effect 0x105297 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 55) (.exec 0x105297 (fun s => s.RIP = 0x105297) (leaR64Effect 0x105297 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x10529c (StorePre 0x10529c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10529c + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10529c (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1052a1 (StorePre 0x1052a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1052a1 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1052a1 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1052a6 (StorePre 0x1052a6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1052a6 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1052a6 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x1052ab (StorePre 0x1052ab 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x1052ab + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x1052ab 11 (.sib 4 none 0 (.d32 0x84)) 0x100) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1052b6 (StorePre 0x1052b6 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1052b6 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1052b6 (.sib 4 none 0 (.d32 0xa0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1052c2 (StorePre 0x1052c2 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1052c2 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1052c2 (.sib 4 none 0 (.d32 0x98)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x1052ce (StorePre 0x1052ce 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1052ce + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1052ce (.sib 4 none 0 (.d32 0x90)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x1052da (StorePre 0x1052da 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1052da + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1052da (.sib 4 none 0 (.d32 0x88)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1052e6 (leaR64Effect 0x1052e6 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x1052e6 (fun s => s.RIP = 0x1052e6) (leaR64Effect 0x1052e6 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x1052ee (movR32Imm32Effect 0x1052ee 5 6 0x20) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 67) (.exec 0x1052ee (fun s => s.RIP = 0x1052ee) (movR32Imm32Effect 0x1052ee 5 6 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 68) (.out 0x1052f3 (movR32Imm32Effect 0x1052f3 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 69) (.exec 0x1052f3 (fun s => s.RIP = 0x1052f3) (movR32Imm32Effect 0x1052f3 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 70) (.out 0x1052f8 (movR64R64Effect 0x1052f8 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 71) (.exec 0x1052f8 (fun s => s.RIP = 0x1052f8) (movR64R64Effect 0x1052f8 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 72) (.out 0x1052fb (movR32Imm32Effect 0x1052fb 6 8 0x100) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 73) (.exec 0x1052fb (fun s => s.RIP = 0x1052fb) (movR32Imm32Effect 0x1052fb 6 8 0x100) (Reg.operands [] [])) #v[]
    (.letOp (n := 74) (.out 0x105301 (callEffect (fun _ => 0x127d70) 0x105306) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 75) (.exec 0x105301 (PushPre 0x105301 5) (callEffect (fun _ => 0x127d70) 0x105306) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.const ⟨64, 0x105306⟩) #v[]
    (.terminate (.call ⟨.l127d70, RegMap.args [(0, 54), (1, 68), (2, 64), (3, 3), (4, 74), (5, 5), (6, 66), (7, 70), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩ { target := .l105306, kept := #v[], arity := rfl, guard := some (Fin.last 76) })))))))))))))))))))))))))

def bytes_l105292 : List UInt8 :=
  [0xC6, 0x44, 0x24, 0x08, 0x01, 0x48, 0x8D, 0x44, 0x24, 0x08, 0xC6, 0x44, 0x24, 0x08, 0x00, 0xC6,
    0x44, 0x24, 0x08, 0x00, 0xC6, 0x44, 0x24, 0x08, 0x00, 0xC7, 0x84, 0x24, 0x84, 0x00, 0x00, 0x00,
    0x00, 0x01, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0xBE, 0x20, 0x00, 0x00,
    0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x41, 0xB8, 0x00, 0x01, 0x00, 0x00, 0xE8,
    0x6A, 0x2A, 0x02, 0x00]

theorem code_l105292 : ∀ x ∈ codeRange 0x105292 bytes_l105292, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5292 116 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105306 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105306 (cmpAlImm8Effect 0x105306 0xff) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x105306 (fun s => s.RIP = 0x105306) (cmpAlImm8Effect 0x105306 0xff) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1053d5, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10530e, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l105306 : List UInt8 :=
  [0x3C, 0xFF, 0x0F, 0x85, 0xC7, 0x00, 0x00, 0x00]

theorem code_l105306 : ∀ x ∈ codeRange 0x105306 bytes_l105306, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5306 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10530e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10530e (movR64M64Effect 0x10530e 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10530e (LoadPre 0x10530e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10530e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10530e 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105316 (StorePre 0x105316 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105316 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105316 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10531b (movR64M64Effect 0x10531b 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x10531b (LoadPre 0x10531b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10531b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10531b 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x105323 (StorePre 0x105323 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105323 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105323 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x105328 (movR64M64Effect 0x105328 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x105328 (LoadPre 0x105328 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x105328 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105328 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x105330 (movR64M64Effect 0x105330 1 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x105330 (LoadPre 0x105330 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x105330 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105330 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x105338 (StorePre 0x105338 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105338 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105338 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x10533d (StorePre 0x10533d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10533d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10533d 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x105342 (leaR64Effect 0x105342 14 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 66) (.exec 0x105342 (fun s => s.RIP = 0x105342) (leaR64Effect 0x105342 14 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x10534a (leaR64Effect 0x10534a 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x10534a (fun s => s.RIP = 0x10534a) (leaR64Effect 0x10534a 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x10534f (movR64R64Effect 0x10534f 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 70) (.exec 0x10534f (fun s => s.RIP = 0x10534f) (movR64R64Effect 0x10534f 7 14) (Reg.operands [.gpr 14] [])) #v[65]
    (.letOp (n := 71) (.out 0x105352 (callEffect (fun _ => 0x109f80) 0x105357) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x105352 (PushPre 0x105352 5) (callEffect (fun _ => 0x109f80) 0x105357) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x105357⟩) #v[]
    (.terminate (.call ⟨.l109f80, RegMap.args [(0, 59), (1, 61), (3, 3), (4, 71), (5, 5), (6, 67), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l105357, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l10530e : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84,
    0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24, 0x88, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48,
    0x89, 0x44, 0x24, 0x08, 0x4C, 0x8D, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24,
    0x08, 0x4C, 0x89, 0xF7, 0xE8, 0x29, 0x4C, 0x00, 0x00]

theorem code_l10530e : ∀ x ∈ codeRange 0x10530e bytes_l10530e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x530e 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105357 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105357 (leaR64Effect 0x105357 7 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x105357 (fun s => s.RIP = 0x105357) (leaR64Effect 0x105357 7 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10535f (movR64R64Effect 0x10535f 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x10535f (fun s => s.RIP = 0x10535f) (movR64R64Effect 0x10535f 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x105362 (callEffect (fun _ => 0x10a2a0) 0x105367) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x105362 (PushPre 0x105362 5) (callEffect (fun _ => 0x10a2a0) 0x105367) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x105367⟩) #v[]
    (.terminate (.call ⟨.l10a2a0, RegMap.args [(0, 0), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l105367, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l105357 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xE8, 0x39, 0x4F, 0x00, 0x00]

theorem code_l105357 : ∀ x ∈ codeRange 0x105357 bytes_l105357, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5357 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105367 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105367 (testR8R8Effect 0x105367 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x105367 (fun s => s.RIP = 0x105367) (testR8R8Effect 0x105367 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10536f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10536b, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l105367 : List UInt8 :=
  [0x84, 0xC0, 0x74, 0x04]

theorem code_l105367 : ∀ x ∈ codeRange 0x105367 bytes_l105367, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5367 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10536b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10536b (xorR32R32Effect 0x10536b 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x10536b (fun s => s.RIP = 0x10536b) (xorR32R32Effect 0x10536b 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l10537c, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l10536b : List UInt8 :=
  [0x31, 0xC0, 0xEB, 0x0D]

theorem code_l10536b : ∀ x ∈ codeRange 0x10536b bytes_l10536b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x536b 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10536f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10536f (StorePre 0x10536f 8 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10536f + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10536f (.base 3 (.d8 0x8)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 54) (.out 0x105377 (movR32Imm32Effect 0x105377 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 55) (.exec 0x105377 (fun s => s.RIP = 0x105377) (movR32Imm32Effect 0x105377 5 0 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l10537c, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10536f : List UInt8 :=
  [0x48, 0xC7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00, 0xB8, 0x01, 0x00, 0x00, 0x00]

theorem code_l10536f : ∀ x ∈ codeRange 0x10536f bytes_l10536f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x536f 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10537c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10537c (StorePre 0x10537c 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10537c + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10537c 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.terminate (.br ⟨.l10537f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l10537c : List UInt8 :=
  [0x48, 0x89, 0x03]

theorem code_l10537c : ∀ x ∈ codeRange 0x10537c bytes_l10537c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x537c 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10537f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10537f (movR64R64Effect 0x10537f 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x10537f (fun s => s.RIP = 0x10537f) (movR64R64Effect 0x10537f 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x105382 (addR64Imm32Effect 0x105382 4 0x1c0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x105382 (fun s => s.RIP = 0x105382) (addR64Imm32Effect 0x105382 4 0x1c0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x105389 (popR64Effect 0x105389 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x105389 (popR64Effect 0x105389 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x105389 (PopPre 0x105389) (popR64Effect 0x105389 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x10538a (popR64Effect 0x10538a 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x10538a (popR64Effect 0x10538a 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x10538a (PopPre 0x10538a) (popR64Effect 0x10538a 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x10538c (popR64Effect 0x10538c 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x10538c (popR64Effect 0x10538c 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x10538c (PopPre 0x10538c) (popR64Effect 0x10538c 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x10538e (popR64Effect 0x10538e 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x10538e (popR64Effect 0x10538e 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x10538e (PopPre 0x10538e) (popR64Effect 0x10538e 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x105390 (popR64Effect 0x105390 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x105390 (popR64Effect 0x105390 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x105390 (PopPre 0x105390) (popR64Effect 0x105390 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x105392 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[70]
    (.letOp (n := 73) (.out 0x105392 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x105392 (RetPre 0x105392) (retEffect) (Reg.operands [.gpr 4] [])) #v[70]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 75) (some ⟨72, by decide⟩))))))))))))))))))))))))

def bytes_l10537f : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xC0, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0xC3]

theorem code_l10537f : ∀ x ∈ codeRange 0x10537f bytes_l10537f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x537f 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105393 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105393 (leaR64Effect 0x105393 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x105393 (fun s => s.RIP = 0x105393) (leaR64Effect 0x105393 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l105398, RegMap.args [(1, 1), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8)] 55⟩)))

def bytes_l105393 : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x08]

theorem code_l105393 : ∀ x ∈ codeRange 0x105393 bytes_l105393, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5393 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105398 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105398 (xorR32R32Effect 0x105398 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x105398 (fun s => s.RIP = 0x105398) (xorR32R32Effect 0x105398 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.out 0x10539a (movR64Imm32Effect 0x10539a 2 0x2022e8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x10539a (fun s => s.RIP = 0x10539a) (movR64Imm32Effect 0x10539a 2 0x2022e8) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1053a1 (xorR32R32Effect 0x1053a1 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 58) (.exec 0x1053a1 (fun s => s.RIP = 0x1053a1) (xorR32R32Effect 0x1053a1 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 59) (.out 0x1053a3 (movR64Imm32Effect 0x1053a3 9 0x2022f0) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 60) (.exec 0x1053a3 (fun s => s.RIP = 0x1053a3) (movR64Imm32Effect 0x1053a3 9 0x2022f0) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x1053aa (callEffect (fun _ => 0x115408) 0x1053af) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x1053aa (PushPre 0x1053aa 5) (callEffect (fun _ => 0x115408) 0x1053af) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x1053af⟩) #v[]
    (.terminate (.call ⟨.l115408, RegMap.args [(1, 57), (2, 55), (4, 61), (5, 5), (6, 6), (7, 53), (8, 8), (9, 59)] 64⟩ { target := .l1053af, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l105398 : List UInt8 :=
  [0x31, 0xFF, 0x48, 0xC7, 0xC2, 0xE8, 0x22, 0x20, 0x00, 0x31, 0xC9, 0x49, 0xC7, 0xC1, 0xF0, 0x22,
    0x20, 0x00, 0xE8, 0x59, 0x00, 0x01, 0x00]

theorem code_l105398 : ∀ x ∈ codeRange 0x105398 bytes_l105398, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5398 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1053af : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1053af (StorePre 0x1053af 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1053af + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1053af (.sib 4 none 0 (.d8 0x8)) 0x202498) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x1053b8 (StorePre 0x1053b8 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1053b8 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1053b8 (.sib 4 none 0 (.d8 0x10)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1053c1 (leaR64Effect 0x1053c1 0 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1053c1 (fun s => s.RIP = 0x1053c1) (leaR64Effect 0x1053c1 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1053ef, RegMap.args [(0, 55), (4, 4), (5, 5)] 57⟩)))))

def bytes_l1053af : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1,
    0x12, 0x00, 0x48, 0x8D, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0xEB, 0x24]

theorem code_l1053af : ∀ x ∈ codeRange 0x1053af bytes_l1053af, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x53af 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1053cb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1053cb (leaR64Effect 0x1053cb 6 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1053cb (fun s => s.RIP = 0x1053cb) (leaR64Effect 0x1053cb 6 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l105398, RegMap.args [(1, 1), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8)] 55⟩)))

def bytes_l1053cb : List UInt8 :=
  [0x48, 0x8D, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0xEB, 0xC3]

theorem code_l1053cb : ∀ x ∈ codeRange 0x1053cb bytes_l1053cb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x53cb 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1053d5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1053d5 (StorePre 0x1053d5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1053d5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1053d5 (.sib 4 none 0 (.d8 0x8)) 0x202498) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x1053de (StorePre 0x1053de 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1053de + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1053de (.sib 4 none 0 (.d8 0x10)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1053e7 (leaR64Effect 0x1053e7 0 (.sib 4 none 0 (.d32 0x84))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1053e7 (fun s => s.RIP = 0x1053e7) (leaR64Effect 0x1053e7 0 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1053ef, RegMap.args [(0, 55), (4, 4), (5, 5)] 57⟩)))))

def bytes_l1053d5 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1,
    0x12, 0x00, 0x48, 0x8D, 0x84, 0x24, 0x84, 0x00, 0x00, 0x00]

theorem code_l1053d5 : ∀ x ∈ codeRange 0x1053d5 bytes_l1053d5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x53d5 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1053ef : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1053ef (StorePre 0x1053ef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1053ef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1053ef 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.exec 0x1053f4 (StorePre 0x1053f4 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1053f4 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1053f4 (.sib 4 none 0 (.d8 0x20)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1053fd (leaR64Effect 0x1053fd 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x1053fd (fun s => s.RIP = 0x1053fd) (leaR64Effect 0x1053fd 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x105402 (movR64Imm32Effect 0x105402 7 0x20028f) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 58) (.exec 0x105402 (fun s => s.RIP = 0x105402) (movR64Imm32Effect 0x105402 7 0x20028f) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x105409 (movR64Imm32Effect 0x105409 2 0x202518) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x105409 (fun s => s.RIP = 0x105409) (movR64Imm32Effect 0x105409 2 0x202518) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x105410 (callEffect (fun _ => 0x129770) 0x105415) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x105410 (PushPre 0x105410 5) (callEffect (fun _ => 0x129770) 0x105415) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x105415⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(0, 0), (2, 59), (4, 61), (5, 5), (6, 55), (7, 57)] 64⟩ { target := .l105415, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l1053ef : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0xC7, 0x44, 0x24, 0x20, 0x90, 0xA1, 0x12, 0x00, 0x48, 0x8D,
    0x74, 0x24, 0x08, 0x48, 0xC7, 0xC7, 0x8F, 0x02, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0x18, 0x25, 0x20,
    0x00, 0xE8, 0x5B, 0x43, 0x02, 0x00]

theorem code_l1053ef : ∀ x ∈ codeRange 0x1053ef bytes_l1053ef, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x53ef 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105415_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x105495 (StorePre 0x105495 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x227)) s (0x105495 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x105495 (.sib 4 none 0 (.d32 0x227)) 0x0) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 85) (.out 0x10549d (testR64R64Effect 0x10549d 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 86) (.exec 0x10549d (fun s => s.RIP = 0x10549d) (testR64R64Effect 0x10549d 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 87) (.pure (condOp 4)) #v[85]
    (.terminate (.condBr (Fin.last 87) ⟨.l1055bf, RegMap.args [(0, 80), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)] 88⟩ ⟨.l1054a6, RegMap.args [(0, 80), (1, 1), (2, 2), (3, 3), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)] 88⟩)))))

def bytes_l105415_1 : List UInt8 :=
  [0xC6, 0x84, 0x24, 0x27, 0x02, 0x00, 0x00, 0x00, 0x48, 0x85, 0xC9, 0x0F, 0x84, 0x19, 0x01, 0x00,
    0x00]

theorem code_l105415_1 : ∀ x ∈ codeRange 0x105495 bytes_l105415_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5495 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105415 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x105415 (fun s => s.RIP = 0x105415) (fun _ => nopEffect 0x105415 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x10541f (fun s => s.RIP = 0x10541f) (fun _ => nopEffect 0x10541f 1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x105420 (pushR64Effect 0x105420 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 56) (.exec 0x105420 (PushPre 0x105420 1) (pushR64Effect 0x105420 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 57) (.out 0x105421 (pushR64Effect 0x105421 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[55, 15]
    (.letOp (n := 58) (.exec 0x105421 (PushPre 0x105421 2) (pushR64Effect 0x105421 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[55, 15]
    (.letOp (n := 59) (.out 0x105423 (pushR64Effect 0x105423 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[57, 14]
    (.letOp (n := 60) (.exec 0x105423 (PushPre 0x105423 2) (pushR64Effect 0x105423 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[57, 14]
    (.letOp (n := 61) (.out 0x105425 (pushR64Effect 0x105425 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[59, 13]
    (.letOp (n := 62) (.exec 0x105425 (PushPre 0x105425 2) (pushR64Effect 0x105425 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[59, 13]
    (.letOp (n := 63) (.out 0x105427 (pushR64Effect 0x105427 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[61, 12]
    (.letOp (n := 64) (.exec 0x105427 (PushPre 0x105427 2) (pushR64Effect 0x105427 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[61, 12]
    (.letOp (n := 65) (.out 0x105429 (pushR64Effect 0x105429 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[63, 3]
    (.letOp (n := 66) (.exec 0x105429 (PushPre 0x105429 1) (pushR64Effect 0x105429 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 67) (.out 0x10542a (subR64Imm32Effect 0x10542a 4 0x2f8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 68) (.exec 0x10542a (fun s => s.RIP = 0x10542a) (subR64Imm32Effect 0x10542a 4 0x2f8) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 69) (.exec 0x105431 (StorePre 0x105431 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x105431 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105431 6 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 67]
    (.letOp (n := 70) (.exec 0x105439 (StorePre 0x105439 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x105439 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105439 7 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 67]
    (.letOp (n := 71) (.out 0x105441 (movR64Imm64Effect 0x105441 0 0x5be0cd191f83d9ab) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 72) (.exec 0x105441 (fun s => s.RIP = 0x105441) (movR64Imm64Effect 0x105441 0 0x5be0cd191f83d9ab) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.exec 0x10544b (StorePre 0x10544b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x240)) s (0x10544b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10544b 0 (.sib 4 none 0 (.d32 0x240))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 67]
    (.letOp (n := 74) (.out 0x105453 (movR64Imm64Effect 0x105453 0 0x9b05688c510e527f) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 75) (.exec 0x105453 (fun s => s.RIP = 0x105453) (movR64Imm64Effect 0x105453 0 0x9b05688c510e527f) (Reg.operands [] [])) #v[]
    (.letOp (n := 76) (.exec 0x10545d (StorePre 0x10545d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x238)) s (0x10545d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10545d 0 (.sib 4 none 0 (.d32 0x238))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 67]
    (.letOp (n := 77) (.out 0x105465 (movR64Imm64Effect 0x105465 0 0xa54ff53a3c6ef372) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 78) (.exec 0x105465 (fun s => s.RIP = 0x105465) (movR64Imm64Effect 0x105465 0 0xa54ff53a3c6ef372) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.exec 0x10546f (StorePre 0x10546f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x230)) s (0x10546f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10546f 0 (.sib 4 none 0 (.d32 0x230))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[77, 67]
    (.letOp (n := 80) (.out 0x105477 (movR64Imm64Effect 0x105477 0 0xbb67ae856a09e667) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 81) (.exec 0x105477 (fun s => s.RIP = 0x105477) (movR64Imm64Effect 0x105477 0 0xbb67ae856a09e667) (Reg.operands [] [])) #v[]
    (.letOp (n := 82) (.exec 0x105481 (StorePre 0x105481 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x105481 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105481 0 (.sib 4 none 0 (.d32 0x228))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 67]
    (.letOp (n := 83) (.exec 0x105489 (StorePre 0x105489 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x248)) s (0x105489 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105489 (.sib 4 none 0 (.d32 0x248)) 0x0) (Reg.operands [.gpr 4] [])) #v[67]
    (b_l105415_1)))))))))))))))))))))))))))))))

def bytes_l105415 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x90, 0x55, 0x41, 0x57, 0x41, 0x56,
    0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xF8, 0x02, 0x00, 0x00, 0x48, 0x89, 0xB4, 0x24,
    0x58, 0x01, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24, 0xA0, 0x01, 0x00, 0x00, 0x48, 0xB8, 0xAB, 0xD9,
    0x83, 0x1F, 0x19, 0xCD, 0xE0, 0x5B, 0x48, 0x89, 0x84, 0x24, 0x40, 0x02, 0x00, 0x00, 0x48, 0xB8,
    0x7F, 0x52, 0x0E, 0x51, 0x8C, 0x68, 0x05, 0x9B, 0x48, 0x89, 0x84, 0x24, 0x38, 0x02, 0x00, 0x00,
    0x48, 0xB8, 0x72, 0xF3, 0x6E, 0x3C, 0x3A, 0xF5, 0x4F, 0xA5, 0x48, 0x89, 0x84, 0x24, 0x30, 0x02,
    0x00, 0x00, 0x48, 0xB8, 0x67, 0xE6, 0x09, 0x6A, 0x85, 0xAE, 0x67, 0xBB, 0x48, 0x89, 0x84, 0x24,
    0x28, 0x02, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x48, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ++ bytes_l105415_1

theorem code_l105415 : ∀ x ∈ codeRange 0x105415 bytes_l105415, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5415 128 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l105415_1

@[cfg_block] def b_l1054a6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1054a6 (movR64R64Effect 0x1054a6 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[1]
    (.letOp (n := 54) (.exec 0x1054a6 (fun s => s.RIP = 0x1054a6) (movR64R64Effect 0x1054a6 3 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x1054a9 (movR64R64Effect 0x1054a9 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 56) (.exec 0x1054a9 (fun s => s.RIP = 0x1054a9) (movR64R64Effect 0x1054a9 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 57) (.out 0x1054ac (shlR64Effect 0x1054ac 4 3 4) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 58) (.exec 0x1054ac (fun s => s.RIP = 0x1054ac) (shlR64Effect 0x1054ac 4 3 4) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 59) (.out 0x1054b0 (addR64R64Effect 0x1054b0 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[57, 2]
    (.letOp (n := 60) (.exec 0x1054b0 (fun s => s.RIP = 0x1054b0) (addR64R64Effect 0x1054b0 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[57, 2]
    (.letOp (n := 61) (.out 0x1054b3 (leaR64Effect 0x1054b3 15 (.rip 0x25366)) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 62) (.exec 0x1054b3 (fun s => s.RIP = 0x1054b3) (leaR64Effect 0x1054b3 15 (.rip 0x25366)) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1054e9, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 59), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l1054a6 : List UInt8 :=
  [0x48, 0x89, 0xCB, 0x49, 0x89, 0xD6, 0x48, 0xC1, 0xE3, 0x04, 0x48, 0x01, 0xD3, 0x4C, 0x8D, 0x3D,
    0x66, 0x53, 0x02, 0x00, 0xEB, 0x2D]

theorem code_l1054a6 : ∀ x ∈ codeRange 0x1054a6 bytes_l1054a6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x54a6 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1054c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1054c0 (leaR64Effect 0x1054c0 7 (.sib 4 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 12] []) (.reg (.gpr 7))) #v[4, 12]
    (.letOp (n := 54) (.exec 0x1054c0 (fun s => s.RIP = 0x1054c0) (leaR64Effect 0x1054c0 7 (.sib 4 (some 12) 0 .none)) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 55) (.out 0x1054c4 (addR64Imm32Effect 0x1054c4 7 0x1e8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x1054c4 (fun s => s.RIP = 0x1054c4) (addR64Imm32Effect 0x1054c4 7 0x1e8) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x1054cb (movR64R64Effect 0x1054cb 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 58) (.exec 0x1054cb (fun s => s.RIP = 0x1054cb) (movR64R64Effect 0x1054cb 2 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x1054ce (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x1054d1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 60) (.exec 0x1054ce (GoesTo (CallPre 0x1054ce 3 (fun s => (Operand.reg 15 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x1054d1) 0x12a820) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x1054d1) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 61) (.const ⟨64, 0x1054d1⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1054d1, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1054c0 : List UInt8 :=
  [0x4A, 0x8D, 0x3C, 0x24, 0x48, 0x81, 0xC7, 0xE8, 0x01, 0x00, 0x00, 0x48, 0x89, 0xEA, 0x41, 0xFF,
    0xD7]

theorem code_l1054c0 : ∀ x ∈ codeRange 0x1054c0 bytes_l1054c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x54c0 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1054d1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1054d1 (addR8R8Effect 0x1054d1 3 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[5, 12]
    (.letOp (n := 54) (.exec 0x1054d1 (fun s => s.RIP = 0x1054d1) (addR8R8Effect 0x1054d1 3 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[5, 12]
    (.letOp (n := 55) (.exec 0x1054d4 (StorePre 0x1054d4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x227)) s (0x1054d4 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x1054d4 8 5 (.sib 4 none 0 (.d32 0x227))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1054dc (addR64Imm8Effect 0x1054dc 14 0x10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 57) (.exec 0x1054dc (fun s => s.RIP = 0x1054dc) (addR64Imm8Effect 0x1054dc 14 0x10) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x1054e0 (cmpR64R64Effect 0x1054e0 14 3) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 3] []) (.flag .ZF)) #v[56, 3]
    (.letOp (n := 59) (.exec 0x1054e0 (fun s => s.RIP = 0x1054e0) (cmpR64R64Effect 0x1054e0 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 60) (.pure (condOp 4)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l1055bf, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l1054e9, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1054d1 : List UInt8 :=
  [0x44, 0x00, 0xE5, 0x40, 0x88, 0xAC, 0x24, 0x27, 0x02, 0x00, 0x00, 0x49, 0x83, 0xC6, 0x10, 0x49,
    0x39, 0xDE, 0x0F, 0x84, 0xD6, 0x00, 0x00, 0x00]

theorem code_l1054d1 : ∀ x ∈ codeRange 0x1054d1 bytes_l1054d1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x54d1 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1054e9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1054e9 (movR64M64Effect 0x1054e9 6 (.base 14 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 54) (.exec 0x1054e9 (LoadPre 0x1054e9 (fun s => AddrMode.addr (.base 14 .none) s (0x1054e9 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1054e9 6 (.base 14 .none)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x1054ec (movR64M64Effect 0x1054ec 5 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 14] []) (.reg (.gpr 5))) #v[14]
    (.letOp (n := 56) (.exec 0x1054ec (LoadPre 0x1054ec (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1054ec + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1054ec 5 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x1054f0 (movzxR32M8Effect 0x1054f0 9 12 (.sib 4 none 0 (.d32 0x227))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 58) (.exec 0x1054f0 (LoadPre 0x1054f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x227)) s (0x1054f0 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1054f0 9 12 (.sib 4 none 0 (.d32 0x227))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1054f9 (movR32Imm32Effect 0x1054f9 5 2 0x40) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x1054f9 (fun s => s.RIP = 0x1054f9) (movR32Imm32Effect 0x1054f9 5 2 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x1054fe (subR64R64Effect 0x1054fe 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x1054fe (fun s => s.RIP = 0x1054fe) (subR64R64Effect 0x1054fe 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x105501 (movR64R64Effect 0x105501 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 5] []) (.reg (.gpr 13))) #v[55]
    (.letOp (n := 64) (.exec 0x105501 (fun s => s.RIP = 0x105501) (movR64R64Effect 0x105501 13 5) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 65) (.out 0x105504 (subR64R64Effect 0x105504 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[63, 61]
    (.letOp (n := 66) (.out 0x105504 (subR64R64Effect 0x105504 13 2) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 2] []) (.flag .CF)) #v[63, 61]
    (.letOp (n := 67) (.exec 0x105504 (fun s => s.RIP = 0x105504) (subR64R64Effect 0x105504 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[63, 61]
    (.letOp (n := 68) (.pure (condOp 2)) #v[66]
    (.terminate (.condBr (Fin.last 68) ⟨.l1054c0, RegMap.args [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 65), (14, 14), (15, 15), (16, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ ⟨.l105509, RegMap.args [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 65), (14, 14), (15, 15), (16, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l1054e9 : List UInt8 :=
  [0x49, 0x8B, 0x36, 0x49, 0x8B, 0x6E, 0x08, 0x44, 0x0F, 0xB6, 0xA4, 0x24, 0x27, 0x02, 0x00, 0x00,
    0xBA, 0x40, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xE2, 0x49, 0x89, 0xED, 0x49, 0x29, 0xD5, 0x72, 0xB7]

theorem code_l1054e9 : ∀ x ∈ codeRange 0x1054e9 bytes_l1054e9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x54e9 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105509 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105509 (testR64R64Effect 0x105509 12 12) (EffectPart.reads (.flag .ZF) [.gpr 12, .gpr 12] []) (.flag .ZF)) #v[12, 12]
    (.letOp (n := 54) (.exec 0x105509 (fun s => s.RIP = 0x105509) (testR64R64Effect 0x105509 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1055b1, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l105512, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l105509 : List UInt8 :=
  [0x4D, 0x85, 0xE4, 0x0F, 0x84, 0x9F, 0x00, 0x00, 0x00]

theorem code_l105509 : ∀ x ∈ codeRange 0x105509 bytes_l105509, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5509 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105512 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105512 (leaR64Effect 0x105512 5 (.sib 6 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6, .gpr 2] []) (.reg (.gpr 5))) #v[6, 2]
    (.letOp (n := 54) (.exec 0x105512 (fun s => s.RIP = 0x105512) (leaR64Effect 0x105512 5 (.sib 6 (some 2) 0 .none)) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6, 2]
    (.letOp (n := 55) (.out 0x105516 (leaR64Effect 0x105516 7 (.sib 4 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 12] []) (.reg (.gpr 7))) #v[4, 12]
    (.letOp (n := 56) (.exec 0x105516 (fun s => s.RIP = 0x105516) (leaR64Effect 0x105516 7 (.sib 4 (some 12) 0 .none)) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 57) (.out 0x10551a (addR64Imm32Effect 0x10551a 7 0x1e8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x10551a (fun s => s.RIP = 0x10551a) (addR64Imm32Effect 0x10551a 7 0x1e8) (Reg.operands [.gpr 7] [])) #v[55]
    (.letOp (n := 59) (.out 0x105521 (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x105524) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 60) (.exec 0x105521 (GoesTo (CallPre 0x105521 3 (fun s => (Operand.reg 15 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x105524) 0x12a820) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x105524) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 61) (.const ⟨64, 0x105524⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 2), (3, 3), (4, 59), (5, 53), (6, 6), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l105524, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l105512 : List UInt8 :=
  [0x48, 0x8D, 0x2C, 0x16, 0x4A, 0x8D, 0x3C, 0x24, 0x48, 0x81, 0xC7, 0xE8, 0x01, 0x00, 0x00, 0x41,
    0xFF, 0xD7]

theorem code_l105512 : ∀ x ∈ codeRange 0x105512 bytes_l105512, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5512 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105524 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x105524 (StorePre 0x105524 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x248)) s (0x105524 + BitVec.ofNat 64 8)) 8) (incMEffect 0x105524 8 64 (.sib 4 none 0 (.d32 0x248))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x10552c (movR32Imm32Effect 0x10552c 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 55) (.exec 0x10552c (fun s => s.RIP = 0x10552c) (movR32Imm32Effect 0x10552c 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.out 0x105531 (leaR64Effect 0x105531 7 (.sib 4 none 0 (.d32 0x228))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 57) (.exec 0x105531 (fun s => s.RIP = 0x105531) (leaR64Effect 0x105531 7 (.sib 4 none 0 (.d32 0x228))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x105539 (leaR64Effect 0x105539 6 (.sib 4 none 0 (.d32 0x1e8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 59) (.exec 0x105539 (fun s => s.RIP = 0x105539) (leaR64Effect 0x105539 6 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x105541 (callEffect (fun _ => 0x1218e0) 0x105546) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x105541 (PushPre 0x105541 5) (callEffect (fun _ => 0x1218e0) 0x105546) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x105546⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 0), (1, 1), (2, 54), (3, 3), (4, 60), (5, 5), (6, 58), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ { target := .l105546, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l105524 : List UInt8 :=
  [0x48, 0xFF, 0x84, 0x24, 0x48, 0x02, 0x00, 0x00, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC,
    0x24, 0x28, 0x02, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0xE8, 0x01, 0x00, 0x00, 0xE8, 0x9A, 0xC3,
    0x01, 0x00]

theorem code_l105524 : ∀ x ∈ codeRange 0x105524 bytes_l105524, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5524 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105546 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x105546 (StorePre 0x105546 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x227)) s (0x105546 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x105546 (.sib 4 none 0 (.d32 0x227)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x10554e (movR64R64Effect 0x10554e 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 55) (.exec 0x10554e (fun s => s.RIP = 0x10554e) (movR64R64Effect 0x10554e 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 56) (.out 0x105551 (movR64R64Effect 0x105551 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 57) (.exec 0x105551 (fun s => s.RIP = 0x105551) (movR64R64Effect 0x105551 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 58) (.out 0x105554 (shrR64Effect 0x105554 4 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[56]
    (.letOp (n := 59) (.out 0x105554 (shrR64Effect 0x105554 4 2 6) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[56]
    (.letOp (n := 60) (.exec 0x105554 (fun s => s.RIP = 0x105554) (shrR64Effect 0x105554 4 2 6) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 61) (.pure (condOp 4)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l105575, RegMap.args [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (5, 5), (6, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l10555a, RegMap.args [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (5, 5), (6, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l105546 : List UInt8 :=
  [0xC6, 0x84, 0x24, 0x27, 0x02, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEE, 0x4C, 0x89, 0xEA, 0x48, 0xC1,
    0xEA, 0x06, 0x74, 0x1B]

theorem code_l105546 : ∀ x ∈ codeRange 0x105546 bytes_l105546, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5546 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10555a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10555a (StorePre 0x10555a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x248)) s (0x10555a + BitVec.ofNat 64 8)) 8) (addMREffect 0x10555a 8 64 2 (.sib 4 none 0 (.d32 0x248))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 54) (.out 0x105562 (leaR64Effect 0x105562 7 (.sib 4 none 0 (.d32 0x228))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x105562 (fun s => s.RIP = 0x105562) (leaR64Effect 0x105562 7 (.sib 4 none 0 (.d32 0x228))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x10556a (movR64R64Effect 0x10556a 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 57) (.exec 0x10556a (fun s => s.RIP = 0x10556a) (movR64R64Effect 0x10556a 5 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 58) (.out 0x10556d (callEffect (fun _ => 0x1218e0) 0x105572) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 59) (.exec 0x10556d (PushPre 0x10556d 5) (callEffect (fun _ => 0x1218e0) 0x105572) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.const ⟨64, 0x105572⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (5, 56), (6, 6), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ { target := .l105572, kept := #v[], arity := rfl, guard := some (Fin.last 60) })))))))))

def bytes_l10555a : List UInt8 :=
  [0x48, 0x01, 0x94, 0x24, 0x48, 0x02, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x28, 0x02, 0x00, 0x00,
    0x48, 0x89, 0xF5, 0xE8, 0x6E, 0xC3, 0x01, 0x00]

theorem code_l10555a : ∀ x ∈ codeRange 0x10555a bytes_l10555a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x555a 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105572 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105572 (movR64R64Effect 0x105572 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 54) (.exec 0x105572 (fun s => s.RIP = 0x105572) (movR64R64Effect 0x105572 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.terminate (.br ⟨.l105575, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l105572 : List UInt8 :=
  [0x48, 0x89, 0xEE]

theorem code_l105572 : ∀ x ∈ codeRange 0x105572 bytes_l105572, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5572 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105575 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105575 (movR64R64Effect 0x105575 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 54) (.exec 0x105575 (fun s => s.RIP = 0x105575) (movR64R64Effect 0x105575 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x105578 (movR64Imm64Effect 0x105578 1 0x7fffffffffffffc0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x105578 (fun s => s.RIP = 0x105578) (movR64Imm64Effect 0x105578 1 0x7fffffffffffffc0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x105582 (andR64R64Effect 0x105582 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x105582 (fun s => s.RIP = 0x105582) (andR64R64Effect 0x105582 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x105585 (andR32Imm8Effect 0x105585 4 13 0x3f) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 60) (.exec 0x105585 (fun s => s.RIP = 0x105585) (andR32Imm8Effect 0x105585 4 13 0x3f) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x105589 (addR64R64Effect 0x105589 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[6, 57]
    (.letOp (n := 62) (.exec 0x105589 (fun s => s.RIP = 0x105589) (addR64R64Effect 0x105589 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[6, 57]
    (.letOp (n := 63) (.exec 0x10558c (StorePre 0x10558c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x227)) s (0x10558c + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x10558c 8 13 (.sib 4 none 0 (.d32 0x227))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 64) (.out 0x105594 (leaR64Effect 0x105594 7 (.sib 4 none 0 (.d32 0x1e8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 65) (.exec 0x105594 (fun s => s.RIP = 0x105594) (leaR64Effect 0x105594 7 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x10559c (movR64R64Effect 0x10559c 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 67) (.exec 0x10559c (fun s => s.RIP = 0x10559c) (movR64R64Effect 0x10559c 2 13) (Reg.operands [.gpr 13] [])) #v[59]
    (.letOp (n := 68) (.out 0x10559f (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x1055a2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 69) (.exec 0x10559f (GoesTo (CallPre 0x10559f 3 (fun s => (Operand.reg 15 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x1055a2) 0x12a820) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x1055a2) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 70) (.const ⟨64, 0x1055a2⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 57), (1, 55), (2, 66), (3, 3), (4, 68), (5, 5), (6, 61), (7, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l1055a2, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l105575 : List UInt8 :=
  [0x4C, 0x89, 0xE8, 0x48, 0xB9, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x48, 0x21, 0xC8,
    0x41, 0x83, 0xE5, 0x3F, 0x48, 0x01, 0xC6, 0x44, 0x88, 0xAC, 0x24, 0x27, 0x02, 0x00, 0x00, 0x48,
    0x8D, 0xBC, 0x24, 0xE8, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xEA, 0x41, 0xFF, 0xD7]

theorem code_l105575 : ∀ x ∈ codeRange 0x105575 bytes_l105575, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5575 45 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1055a2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1055a2 (addR64Imm8Effect 0x1055a2 14 0x10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 54) (.exec 0x1055a2 (fun s => s.RIP = 0x1055a2) (addR64Imm8Effect 0x1055a2 14 0x10) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x1055a6 (cmpR64R64Effect 0x1055a6 14 3) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 3] []) (.flag .ZF)) #v[53, 3]
    (.letOp (n := 56) (.exec 0x1055a6 (fun s => s.RIP = 0x1055a6) (cmpR64R64Effect 0x1055a6 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1054e9, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1055af, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1055a2 : List UInt8 :=
  [0x49, 0x83, 0xC6, 0x10, 0x49, 0x39, 0xDE, 0x0F, 0x85, 0x3A, 0xFF, 0xFF, 0xFF]

theorem code_l1055a2 : ∀ x ∈ codeRange 0x1055a2 bytes_l1055a2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x55a2 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1055af : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1055bf, RegMap.args (entryMap (live .l1055af)) 53⟩)

def bytes_l1055af : List UInt8 :=
  [0xEB, 0x0E]

theorem code_l1055af : ∀ x ∈ codeRange 0x1055af bytes_l1055af, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x55af 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1055b1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1055b1 (movR64R64Effect 0x1055b1 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 5] []) (.reg (.gpr 13))) #v[5]
    (.letOp (n := 54) (.exec 0x1055b1 (fun s => s.RIP = 0x1055b1) (movR64R64Effect 0x1055b1 13 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x1055b4 (movR64R64Effect 0x1055b4 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 56) (.exec 0x1055b4 (fun s => s.RIP = 0x1055b4) (movR64R64Effect 0x1055b4 2 13) (Reg.operands [.gpr 13] [])) #v[53]
    (.letOp (n := 57) (.out 0x1055b7 (shrR64Effect 0x1055b7 4 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 58) (.out 0x1055b7 (shrR64Effect 0x1055b7 4 2 6) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[55]
    (.letOp (n := 59) (.exec 0x1055b7 (fun s => s.RIP = 0x1055b7) (shrR64Effect 0x1055b7 4 2 6) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 60) (.pure (condOp 5)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l10555a, RegMap.args [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l1055bd, RegMap.args [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1055b1 : List UInt8 :=
  [0x49, 0x89, 0xED, 0x4C, 0x89, 0xEA, 0x48, 0xC1, 0xEA, 0x06, 0x75, 0x9D]

theorem code_l1055b1 : ∀ x ∈ codeRange 0x1055b1 bytes_l1055b1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x55b1 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1055bd : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l105575, RegMap.args (entryMap (live .l1055bd)) 53⟩)

def bytes_l1055bd : List UInt8 :=
  [0xEB, 0xB6]

theorem code_l1055bd : ∀ x ∈ codeRange 0x1055bd bytes_l1055bd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x55bd 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1055bf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1055bf (leaR64Effect 0x1055bf 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1055bf (fun s => s.RIP = 0x1055bf) (leaR64Effect 0x1055bf 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1055c4 (leaR64Effect 0x1055c4 6 (.sib 4 none 0 (.d32 0x1e8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x1055c4 (fun s => s.RIP = 0x1055c4) (leaR64Effect 0x1055c4 6 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1055cc (movR32Imm32Effect 0x1055cc 5 1 0xd) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x1055cc (fun s => s.RIP = 0x1055cc) (movR32Imm32Effect 0x1055cc 5 1 0xd) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1055d1 (repMovsqEffect 0x1055d1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[55, 53, 57, 22]
    (.letOp (n := 60) (.exec 0x1055d1 (RepPre 0x1055d1 (RepMovsqPre 0x1055d1)) (repMovsqEffect 0x1055d1) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[55, 53, 57, 22]
    (.letOp (n := 61) (.out 0x1055d4 (movzxR32M8Effect 0x1055d4 6 15 (.sib 4 none 0 (.d8 0x47))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 62) (.exec 0x1055d4 (LoadPre 0x1055d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x1055d4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1055d4 6 15 (.sib 4 none 0 (.d8 0x47))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1055da (movR64M64Effect 0x1055da 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x1055da (LoadPre 0x1055da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1055da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1055da 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1055df (shlR64Effect 0x1055df 4 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[63]
    (.letOp (n := 66) (.exec 0x1055df (fun s => s.RIP = 0x1055df) (shlR64Effect 0x1055df 4 0 9) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 67) (.out 0x1055e3 (movR64R64Effect 0x1055e3 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 15] []) (.reg (.gpr 14))) #v[61]
    (.letOp (n := 68) (.exec 0x1055e3 (fun s => s.RIP = 0x1055e3) (movR64R64Effect 0x1055e3 14 15) (Reg.operands [.gpr 15] [])) #v[61]
    (.letOp (n := 69) (.exec 0x1055e6 (StorePre 0x1055e6 6 (fun s => AddrMode.addr (.sib 4 (some 15) 0 (.d8 0x8)) s (0x1055e6 + BitVec.ofNat 64 6)) 1) (movM8Imm8RexEffect 0x1055e6 (.sib 4 (some 15) 0 (.d8 0x8)) 0x80) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 61]
    (.letOp (n := 70) (.out 0x1055ec (leaR64Effect 0x1055ec 7 (.sib 4 (some 15) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 15] []) (.reg (.gpr 7))) #v[4, 61]
    (.letOp (n := 71) (.exec 0x1055ec (fun s => s.RIP = 0x1055ec) (leaR64Effect 0x1055ec 7 (.sib 4 (some 15) 0 .none)) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 61]
    (.letOp (n := 72) (.out 0x1055f0 (addR64Imm8Effect 0x1055f0 7 0x9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[70]
    (.letOp (n := 73) (.exec 0x1055f0 (fun s => s.RIP = 0x1055f0) (addR64Imm8Effect 0x1055f0 7 0x9) (Reg.operands [.gpr 7] [])) #v[70]
    (.letOp (n := 74) (.out 0x1055f4 (shlR32Effect 0x1055f4 4 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[61]
    (.letOp (n := 75) (.exec 0x1055f4 (fun s => s.RIP = 0x1055f4) (shlR32Effect 0x1055f4 4 15 3) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 76) (.out 0x1055f8 (orR64R64Effect 0x1055f8 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[74, 65]
    (.letOp (n := 77) (.exec 0x1055f8 (fun s => s.RIP = 0x1055f8) (orR64R64Effect 0x1055f8 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[74, 65]
    (.letOp (n := 78) (.out 0x1055fb (leaR64Effect 0x1055fb 3 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 79) (.exec 0x1055fb (fun s => s.RIP = 0x1055fb) (leaR64Effect 0x1055fb 3 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x105600 (bswapR64Effect 0x105600 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[76]
    (.letOp (n := 81) (.exec 0x105600 (fun s => s.RIP = 0x105600) (bswapR64Effect 0x105600 3 15) (Reg.operands [.gpr 15] [])) #v[76]
    (.letOp (n := 82) (.out 0x105603 (xorR64Imm8Effect 0x105603 14 0x3f) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[67]
    (.letOp (n := 83) (.exec 0x105603 (fun s => s.RIP = 0x105603) (xorR64Imm8Effect 0x105603 14 0x3f) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 84) (.out 0x105607 (xorR32R32Effect 0x105607 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[59, 59]
    (.letOp (n := 85) (.exec 0x105607 (fun s => s.RIP = 0x105607) (xorR32R32Effect 0x105607 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[59, 59]
    (.letOp (n := 86) (.out 0x105609 (movR64R64Effect 0x105609 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[82]
    (.letOp (n := 87) (.exec 0x105609 (fun s => s.RIP = 0x105609) (movR64R64Effect 0x105609 2 14) (Reg.operands [.gpr 14] [])) #v[82]
    (.letOp (n := 88) (.out 0x10560c (callEffect (callMemPtr 0x10560c (.rip 0xfe7fe)) (0x10560c + BitVec.ofNat 64 (callMemLen (.rip 0xfe7fe)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 89) (.exec 0x10560c (GoesTo (CallMemPre 0x10560c (.rip 0xfe7fe)) (callEffect (callMemPtr 0x10560c (.rip 0xfe7fe)) (0x10560c + BitVec.ofNat 64 (callMemLen (.rip 0xfe7fe)))) 0x12a700) (callEffect (callMemPtr 0x10560c (.rip 0xfe7fe)) (0x10560c + BitVec.ofNat 64 (callMemLen (.rip 0xfe7fe)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.const ⟨64, 0x105612⟩) #v[]
    (.terminate (.call ⟨.l12a700, RegMap.args [(0, 65), (2, 86), (3, 78), (4, 88), (5, 5), (6, 84), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩ { target := .l105612, kept := #v[], arity := rfl, guard := some (Fin.last 90) })))))))))))))))))))))))))))))))))))))))

def bytes_l1055bf : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0x8D, 0xB4, 0x24, 0xE8, 0x01, 0x00, 0x00, 0xB9, 0x0D, 0x00,
    0x00, 0x00, 0xF3, 0x48, 0xA5, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x47, 0x48, 0x8B, 0x44, 0x24, 0x68,
    0x48, 0xC1, 0xE0, 0x09, 0x4D, 0x89, 0xFE, 0x42, 0xC6, 0x44, 0x3C, 0x08, 0x80, 0x4A, 0x8D, 0x3C,
    0x3C, 0x48, 0x83, 0xC7, 0x09, 0x41, 0xC1, 0xE7, 0x03, 0x49, 0x09, 0xC7, 0x48, 0x8D, 0x5C, 0x24,
    0x48, 0x49, 0x0F, 0xCF, 0x49, 0x83, 0xF6, 0x3F, 0x31, 0xF6, 0x4C, 0x89, 0xF2, 0xFF, 0x15, 0xFE,
    0xE7, 0x0F, 0x00]

theorem code_l1055bf : ∀ x ∈ codeRange 0x1055bf bytes_l1055bf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x55bf 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105612 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105612 (cmpR64Imm8Effect 0x105612 14 0x7) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[14]
    (.letOp (n := 54) (.out 0x105612 (cmpR64Imm8Effect 0x105612 14 0x7) (EffectPart.reads (.flag .ZF) [.gpr 14] []) (.flag .ZF)) #v[14]
    (.letOp (n := 55) (.exec 0x105612 (fun s => s.RIP = 0x105612) (cmpR64Imm8Effect 0x105612 14 0x7) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.pure (condOp 7)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l1056d8, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l10561c, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l105612 : List UInt8 :=
  [0x49, 0x83, 0xFE, 0x07, 0x0F, 0x87, 0xBC, 0x00, 0x00, 0x00]

theorem code_l105612 : ∀ x ∈ codeRange 0x105612 bytes_l105612, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5612 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10561c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10561c (movR64M64Effect 0x10561c 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10561c (LoadPre 0x10561c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10561c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10561c 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105621 (StorePre 0x105621 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x105621 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105621 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x105629 (movR64M64Effect 0x105629 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x105629 (LoadPre 0x105629 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x105629 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105629 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10562e (StorePre 0x10562e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10562e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10562e 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x105636 (movR64M64Effect 0x105636 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x105636 (LoadPre 0x105636 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105636 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105636 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x10563b (StorePre 0x10563b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x10563b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10563b 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x105643 (movR64M64Effect 0x105643 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x105643 (LoadPre 0x105643 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105643 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105643 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x105648 (StorePre 0x105648 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x105648 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105648 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x105650 (movR64M64Effect 0x105650 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x105650 (LoadPre 0x105650 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105650 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105650 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x105655 (StorePre 0x105655 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x105655 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105655 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x10565d (movR64M64Effect 0x10565d 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x10565d (LoadPre 0x10565d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10565d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10565d 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x105662 (StorePre 0x105662 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x105662 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105662 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x10566a (movR64M64Effect 0x10566a 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x10566a (LoadPre 0x10566a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10566a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10566a 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x10566f (movR64M64Effect 0x10566f 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 74) (.exec 0x10566f (LoadPre 0x10566f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10566f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10566f 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x105674 (StorePre 0x105674 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x105674 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105674 1 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.exec 0x10567c (StorePre 0x10567c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10567c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10567c 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 77) (.out 0x105684 (leaR64Effect 0x105684 6 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 78) (.exec 0x105684 (fun s => s.RIP = 0x105684) (leaR64Effect 0x105684 6 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x10568c (movR32Imm32Effect 0x10568c 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 80) (.exec 0x10568c (fun s => s.RIP = 0x10568c) (movR32Imm32Effect 0x10568c 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 81) (.out 0x105691 (movR64R64Effect 0x105691 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 82) (.exec 0x105691 (fun s => s.RIP = 0x105691) (movR64R64Effect 0x105691 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 83) (.out 0x105694 (callEffect (fun _ => 0x1218e0) 0x105699) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x105694 (PushPre 0x105694 5) (callEffect (fun _ => 0x1218e0) 0x105699) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.const ⟨64, 0x105699⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 71), (1, 73), (2, 79), (3, 3), (4, 83), (5, 5), (6, 77), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l105699, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l10561c : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44,
    0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48,
    0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24,
    0x20, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00,
    0x00, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x8B,
    0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x00, 0x01, 0x00, 0x00,
    0xBA, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0xE8, 0x47, 0xC2, 0x01, 0x00]

theorem code_l10561c : ∀ x ∈ codeRange 0x10561c bytes_l10561c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x561c 125 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105699 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x105699 (StorePre 0x105699 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105699 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105699 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x1056a2 (StorePre 0x1056a2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1056a2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1056a2 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1056ab (StorePre 0x1056ab 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1056ab + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1056ab (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1056b4 (StorePre 0x1056b4 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1056b4 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1056b4 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1056bd (StorePre 0x1056bd 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1056bd + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1056bd (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1056c6 (StorePre 0x1056c6 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1056c6 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1056c6 (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x1056cf (StorePre 0x1056cf 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1056cf + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1056cf (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1056d8, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l105699 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x30, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00]

theorem code_l105699 : ∀ x ∈ codeRange 0x105699 bytes_l105699, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5699 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1056d8_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x105753 (callEffect (fun _ => 0x1218e0) 0x105758) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 85) (.exec 0x105753 (PushPre 0x105753 5) (callEffect (fun _ => 0x1218e0) 0x105758) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.const ⟨64, 0x105758⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 70), (1, 72), (2, 78), (3, 3), (4, 84), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 76), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 87⟩ { target := .l105758, kept := #v[], arity := rfl, guard := some (Fin.last 86) }))))

def bytes_l1056d8_1 : List UInt8 :=
  [0xE8, 0x88, 0xC1, 0x01, 0x00]

theorem code_l1056d8_1 : ∀ x ∈ codeRange 0x105753 bytes_l1056d8_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5753 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1056d8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1056d8 (StorePre 0x1056d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1056d8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1056d8 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 54) (.exec 0x1056dd (StorePre 0x1056dd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1056dd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1056dd 15 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 55) (.out 0x1056e5 (movR64M64Effect 0x1056e5 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1056e5 (LoadPre 0x1056e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1056e5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1056e5 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1056ea (StorePre 0x1056ea 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x1056ea + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1056ea 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x1056f2 (movR64M64Effect 0x1056f2 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 59) (.exec 0x1056f2 (LoadPre 0x1056f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1056f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1056f2 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1056f7 (StorePre 0x1056f7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1056f7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1056f7 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x1056ff (movR64M64Effect 0x1056ff 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 62) (.exec 0x1056ff (LoadPre 0x1056ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1056ff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1056ff 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x105704 (StorePre 0x105704 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x105704 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105704 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x10570c (movR64M64Effect 0x10570c 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 65) (.exec 0x10570c (LoadPre 0x10570c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10570c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10570c 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x105711 (StorePre 0x105711 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x105711 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105711 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x105719 (movR64M64Effect 0x105719 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 68) (.exec 0x105719 (LoadPre 0x105719 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105719 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105719 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x10571e (StorePre 0x10571e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10571e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10571e 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x105726 (movR64M64Effect 0x105726 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 71) (.exec 0x105726 (LoadPre 0x105726 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105726 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105726 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x10572b (movR64M64Effect 0x10572b 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 73) (.exec 0x10572b (LoadPre 0x10572b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10572b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10572b 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x105730 (StorePre 0x105730 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x105730 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105730 1 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.exec 0x105738 (StorePre 0x105738 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x105738 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105738 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 76) (.out 0x105740 (leaR64Effect 0x105740 13 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 77) (.exec 0x105740 (fun s => s.RIP = 0x105740) (leaR64Effect 0x105740 13 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x105748 (movR32Imm32Effect 0x105748 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 79) (.exec 0x105748 (fun s => s.RIP = 0x105748) (movR32Imm32Effect 0x105748 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 80) (.out 0x10574d (movR64R64Effect 0x10574d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 81) (.exec 0x10574d (fun s => s.RIP = 0x10574d) (movR64R64Effect 0x10574d 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 82) (.out 0x105750 (movR64R64Effect 0x105750 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[76]
    (.letOp (n := 83) (.exec 0x105750 (fun s => s.RIP = 0x105750) (movR64R64Effect 0x105750 6 13) (Reg.operands [.gpr 13] [])) #v[76]
    (b_l1056d8_1)))))))))))))))))))))))))))))))

def bytes_l1056d8 : List UInt8 :=
  [0x4C, 0x89, 0x7C, 0x24, 0x40, 0x4C, 0x89, 0xBC, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44,
    0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48,
    0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24,
    0x20, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00,
    0x00, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x8B,
    0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x8D, 0xAC, 0x24, 0x00, 0x01, 0x00, 0x00,
    0xBA, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xEE] ++ bytes_l1056d8_1

theorem code_l1056d8 : ∀ x ∈ codeRange 0x1056d8 bytes_l1056d8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x56d8 123 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1056d8_1

@[cfg_block] def b_l105758_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.exec 0x1057aa (StorePre 0x1057aa 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x1057aa + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1057aa 7 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 90) (.exec 0x1057b1 (StorePre 0x1057b1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x174)) s (0x1057b1 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x1057b1 8 (.sib 4 none 0 (.d32 0x174))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 91) (.exec 0x1057b9 (StorePre 0x1057b9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x1057b9 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x1057b9 9 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 92) (.exec 0x1057c1 (StorePre 0x1057c1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x17c)) s (0x1057c1 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x1057c1 10 (.sib 4 none 0 (.d32 0x17c))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 93) (.out 0x1057c9 (movR64Imm64Effect 0x1057c9 0 0xbaaedce6af48a03b) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 94) (.exec 0x1057c9 (fun s => s.RIP = 0x1057c9) (movR64Imm64Effect 0x1057c9 0 0xbaaedce6af48a03b) (Reg.operands [] [])) #v[]
    (.letOp (n := 95) (.exec 0x1057d3 (StorePre 0x1057d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x258)) s (0x1057d3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1057d3 0 (.sib 4 none 0 (.d32 0x258))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[93, 4]
    (.letOp (n := 96) (.out 0x1057db (movR64Imm64Effect 0x1057db 0 0xbfd25e8cd0364141) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 97) (.exec 0x1057db (fun s => s.RIP = 0x1057db) (movR64Imm64Effect 0x1057db 0 0xbfd25e8cd0364141) (Reg.operands [] [])) #v[]
    (.letOp (n := 98) (.exec 0x1057e5 (StorePre 0x1057e5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x250)) s (0x1057e5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1057e5 0 (.sib 4 none 0 (.d32 0x250))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[96, 4]
    (.letOp (n := 99) (.exec 0x1057ed (StorePre 0x1057ed 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x268)) s (0x1057ed + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1057ed (.sib 4 none 0 (.d32 0x268)) 0xffffffff) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 100) (.exec 0x1057f9 (StorePre 0x1057f9 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x260)) s (0x1057f9 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1057f9 (.sib 4 none 0 (.d32 0x260)) 0xfffffffe) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 101) (.out 0x105805 (leaR64Effect 0x105805 12 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 102) (.exec 0x105805 (fun s => s.RIP = 0x105805) (leaR64Effect 0x105805 12 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 103) (.out 0x10580a (movR64R64Effect 0x10580a 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[101]
    (.letOp (n := 104) (.exec 0x10580a (fun s => s.RIP = 0x10580a) (movR64R64Effect 0x10580a 7 12) (Reg.operands [.gpr 12] [])) #v[101]
    (.letOp (n := 105) (.out 0x10580d (movR64M64Effect 0x10580d 6 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 106) (.exec 0x10580d (LoadPre 0x10580d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10580d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10580d 6 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 107) (.out 0x105815 (callEffect (fun _ => 0x109e30) 0x10581a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 108) (.exec 0x105815 (PushPre 0x105815 5) (callEffect (fun _ => 0x109e30) 0x10581a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 109) (.const ⟨64, 0x10581a⟩) #v[]
    (.terminate (.call ⟨.l109e30, RegMap.args [(0, 96), (1, 59), (2, 63), (3, 3), (4, 107), (5, 5), (6, 105), (7, 103), (8, 75), (9, 79), (10, 83), (11, 11), (12, 101), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 110⟩ { target := .l10581a, kept := #v[], arity := rfl, guard := some (Fin.last 109) }))))))))))))))))))))))

def bytes_l105758_1 : List UInt8 :=
  [0x89, 0xBC, 0x24, 0x70, 0x01, 0x00, 0x00, 0x44, 0x89, 0x84, 0x24, 0x74, 0x01, 0x00, 0x00, 0x44,
    0x89, 0x8C, 0x24, 0x78, 0x01, 0x00, 0x00, 0x44, 0x89, 0x94, 0x24, 0x7C, 0x01, 0x00, 0x00, 0x48,
    0xB8, 0x3B, 0xA0, 0x48, 0xAF, 0xE6, 0xDC, 0xAE, 0xBA, 0x48, 0x89, 0x84, 0x24, 0x58, 0x02, 0x00,
    0x00, 0x48, 0xB8, 0x41, 0x41, 0x36, 0xD0, 0x8C, 0x5E, 0xD2, 0xBF, 0x48, 0x89, 0x84, 0x24, 0x50,
    0x02, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x68, 0x02, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x48,
    0xC7, 0x84, 0x24, 0x60, 0x02, 0x00, 0x00, 0xFE, 0xFF, 0xFF, 0xFF, 0x4C, 0x8D, 0x64, 0x24, 0x08,
    0x4C, 0x89, 0xE7, 0x48, 0x8B, 0xB4, 0x24, 0x58, 0x01, 0x00, 0x00, 0xE8, 0x16, 0x46, 0x00, 0x00]

theorem code_l105758_1 : ∀ x ∈ codeRange 0x1057aa bytes_l105758_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x57aa 112 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105758 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105758 (movR32M32LowEffect 0x105758 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x105758 (LoadPre 0x105758 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x105758 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105758 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10575c (movR32M32LowEffect 0x10575c 1 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x10575c (LoadPre 0x10575c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x10575c + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10575c 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x105760 (bswapR32Effect 0x105760 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 58) (.exec 0x105760 (fun s => s.RIP = 0x105760) (bswapR32Effect 0x105760 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x105762 (bswapR32Effect 0x105762 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 60) (.exec 0x105762 (fun s => s.RIP = 0x105762) (bswapR32Effect 0x105762 2 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 61) (.out 0x105764 (movR32M32LowEffect 0x105764 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x105764 (LoadPre 0x105764 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x105764 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105764 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x105768 (bswapR32Effect 0x105768 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 64) (.exec 0x105768 (fun s => s.RIP = 0x105768) (bswapR32Effect 0x105768 2 2) (Reg.operands [.gpr 2] [])) #v[61]
    (.letOp (n := 65) (.out 0x10576a (movR32M32LowEffect 0x10576a 6 (.sib 4 none 0 (.d8 0x54))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x10576a (LoadPre 0x10576a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x10576a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10576a 6 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x10576e (bswapR32Effect 0x10576e 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 68) (.exec 0x10576e (fun s => s.RIP = 0x10576e) (bswapR32Effect 0x10576e 2 6) (Reg.operands [.gpr 6] [])) #v[65]
    (.letOp (n := 69) (.out 0x105770 (movR32M32LowEffect 0x105770 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x105770 (LoadPre 0x105770 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x105770 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105770 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x105774 (bswapR32Effect 0x105774 2 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[69]
    (.letOp (n := 72) (.exec 0x105774 (fun s => s.RIP = 0x105774) (bswapR32Effect 0x105774 2 7) (Reg.operands [.gpr 7] [])) #v[69]
    (.letOp (n := 73) (.out 0x105776 (movR32M32Effect 0x105776 8 (.sib 4 none 0 (.d8 0x5c))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 74) (.exec 0x105776 (LoadPre 0x105776 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x105776 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x105776 8 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x10577b (bswapR32Effect 0x10577b 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[73]
    (.letOp (n := 76) (.exec 0x10577b (fun s => s.RIP = 0x10577b) (bswapR32Effect 0x10577b 3 8) (Reg.operands [.gpr 8] [])) #v[73]
    (.letOp (n := 77) (.out 0x10577e (movR32M32Effect 0x10577e 9 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 78) (.exec 0x10577e (LoadPre 0x10577e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10577e + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x10577e 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x105783 (bswapR32Effect 0x105783 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[77]
    (.letOp (n := 80) (.exec 0x105783 (fun s => s.RIP = 0x105783) (bswapR32Effect 0x105783 3 9) (Reg.operands [.gpr 9] [])) #v[77]
    (.letOp (n := 81) (.out 0x105786 (movR32M32Effect 0x105786 10 (.sib 4 none 0 (.d8 0x64))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 82) (.exec 0x105786 (LoadPre 0x105786 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x105786 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x105786 10 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x10578b (bswapR32Effect 0x10578b 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[81]
    (.letOp (n := 84) (.exec 0x10578b (fun s => s.RIP = 0x10578b) (bswapR32Effect 0x10578b 3 10) (Reg.operands [.gpr 10] [])) #v[81]
    (.letOp (n := 85) (.exec 0x10578e (StorePre 0x10578e 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x10578e + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10578e 0 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 86) (.exec 0x105795 (StorePre 0x105795 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x164)) s (0x105795 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105795 1 (.sib 4 none 0 (.d32 0x164))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 87) (.exec 0x10579c (StorePre 0x10579c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10579c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10579c 2 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 88) (.exec 0x1057a3 (StorePre 0x1057a3 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16c)) s (0x1057a3 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1057a3 6 (.sib 4 none 0 (.d32 0x16c))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[67, 4]
    (b_l105758_1))))))))))))))))))))))))))))))))))))

def bytes_l105758 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x48, 0x8B, 0x4C, 0x24, 0x4C, 0x0F, 0xC8, 0x0F, 0xC9, 0x8B, 0x54, 0x24, 0x50,
    0x0F, 0xCA, 0x8B, 0x74, 0x24, 0x54, 0x0F, 0xCE, 0x8B, 0x7C, 0x24, 0x58, 0x0F, 0xCF, 0x44, 0x8B,
    0x44, 0x24, 0x5C, 0x41, 0x0F, 0xC8, 0x44, 0x8B, 0x4C, 0x24, 0x60, 0x41, 0x0F, 0xC9, 0x44, 0x8B,
    0x54, 0x24, 0x64, 0x41, 0x0F, 0xCA, 0x89, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00, 0x89, 0x8C, 0x24,
    0x64, 0x01, 0x00, 0x00, 0x89, 0x94, 0x24, 0x68, 0x01, 0x00, 0x00, 0x89, 0xB4, 0x24, 0x6C, 0x01,
    0x00, 0x00] ++ bytes_l105758_1

theorem code_l105758 : ∀ x ∈ codeRange 0x105758 bytes_l105758, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5758 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l105758_1

end K256.Proofs.Verify.LIR
